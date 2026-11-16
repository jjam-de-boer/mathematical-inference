import Thesis.Causality.CausalOrder
import Thesis.Causality.HardIntervention
import Thesis.Causality.HiddenDAGObservedIndex
import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.OrderedConditionals
import Thesis.Probability.QualitativeUrn

namespace Thesis.Causality
open Probability
open Probability.ClaytonWaddington Probability.ClaytonWaddington.UrnRatio
universe u v

/-!
# Qualitative experimental laws before causal urn recipes

The finite variables, their acyclic full wiring, and which values are recorded
are supplied structural data. An ordinary finite urn represents each whole
experiment, reusing the existing rational probability foundation. These urns
do NOT supply local recipes, random source tickets, an SCM, factorization or
Pearl soundness. The representation proof must construct that causal content.

The user-approved qualitative requirements are:

* **Effectiveness:** If experiment I sets variable v to a, the event v=a
  has the same plausibility as the certain event.
* **Parent sufficiency:** In any experiment I leaving v unset, for every
  supported complete earlier history h and every event E concerning v, the
  conditional plausibility of E given h equals its conditional plausibility
  given only the parent values specified by h. Support of h implies support
  of those parent values.
* **Experimental stability:** For any experiments I and J both leaving v
  unset, any parent configuration p supported in both experiments, and every
  event E concerning v, the conditional plausibility of E given p is the
  same in I and J.

Support means positive EVIDENCE probability, never positivity of the outcome
event. A null-evidence conditional remains undefined. All requirements range
over the full declared system, including unrecorded values. Settings target
recorded variables only. Complete earlier histories include unrelated nodes;
they are not restricted to graph ancestors or to strictly smaller ranks.

One shared faithful Clayton scale compares all experiments. Thus the causal
requirements are qualitative equalities; the existing count-ratio theorem
recovers numerical equalities when the representation proof needs them.
-/

/-- Structural alphabets and ordinary whole-experiment laws. None of the
fields is a local causal recipe or a certificate of causal soundness. -/
structure CausalExperimentData (S : ObservedSignature.{u}) (P : FiniteLatentProjection S) where
  Value : Fin P.hiddenDAG.count → Type u
  values : (node : Fin P.hiddenDAG.count) → List (Value node)
  complete : ∀ node value, value ∈ values node
  valueEq : (node : Fin P.hiddenDAG.count) → DecidableEq (Value node)
  defaultValue : (node : Fin P.hiddenDAG.count) → Value node
  recordedValue : (node : Fin S.count) →
    ValueEquivalence (Value (P.hiddenDAG.observedNode node)) (S.Value node)
  order : CausalOrder P.hiddenDAG
  slice : HardIntervention S → UrnProb ((node : Fin P.hiddenDAG.count) → Value node)

namespace CausalExperimentData
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

abbrev Assignment (data : CausalExperimentData S P) :=
  (node : Fin P.hiddenDAG.count) → data.Value node

instance (data : CausalExperimentData S P) (node) : DecidableEq (data.Value node) := data.valueEq node

instance (data : CausalExperimentData S P) : DecidableEq data.Assignment :=
  FiniteProduct.assignmentDecidableEq _ _ data.valueEq

abbrev Parents (data : CausalExperimentData S P) (child) :=
  P.hiddenDAG.ParentValues data.Value child

instance (data : CausalExperimentData S P) (child) : DecidableEq (data.Parents child) :=
  FiniteProduct.assignmentDecidableEq _ _
    (fun parent => ProofFunction.decidableEq (P.hiddenDAG.edge parent child = true))

def parents (data : CausalExperimentData S P) (child) (a : data.Assignment) : data.Parents child :=
  fun parent _ => a parent

def parentEvent (data : CausalExperimentData S P) (child) (pa : data.Parents child) : Event data.Assignment :=
  fun a => decide (data.parents child a = pa)

def history (data : CausalExperimentData S P) (child : Fin P.hiddenDAG.count)
    (reference : data.Assignment) : Event data.Assignment :=
  OrderedHistory.history (data.order.earlier child) reference

def nodeEvent (data : CausalExperimentData S P) (child) (event : Event (data.Value child)) : Event data.Assignment :=
  fun a => event (a child)

/-- Event locality is a deterministic statement about which coordinates a
test inspects. It is not a probabilistic independence assumption. -/
def DependsBefore (data : CausalExperimentData S P) (child : Fin P.hiddenDAG.count)
    (event : Event data.Assignment) : Prop :=
  ∀ first second, (∀ node, data.order.nodes.idxOf node < data.order.nodes.idxOf child →
    first node = second node) → event first = event second

theorem history_dependsBefore (data : CausalExperimentData S P) (child)
    (reference : data.Assignment) : data.DependsBefore child (data.history child reference) := by
  intro first second agree
  apply Bool.eq_iff_iff.mpr
  simp only [history, OrderedHistory.history, List.all_eq_true]
  constructor
  · intro selected node listed
    have equal := agree node ((data.order.mem_earlier_iff node child).mp listed)
    simpa only [OrderedHistory.coordinate, equal] using selected node listed
  · intro selected node listed
    have equal := agree node ((data.order.mem_earlier_iff node child).mp listed)
    simpa only [OrderedHistory.coordinate, equal] using selected node listed

theorem parentEvent_dependsBefore (data : CausalExperimentData S P) (child)
    (pa : data.Parents child) : data.DependsBefore child (data.parentEvent child pa) := by
  intro first second agree
  have sameParents : data.parents child first = data.parents child second := by
    funext parent edge
    exact agree parent (data.order.parent_before parent child edge)
  simp only [parentEvent, sameParents]

/-- A setting has a value at an internal node precisely when that node is
recorded and selected by the public hard intervention. Hidden nodes are not
silently promoted to additional intervention targets. -/
def forcedAt (data : CausalExperimentData S P) (setting : HardIntervention S)
    (node : Fin P.hiddenDAG.count) : Option (data.Value node) :=
  match found : P.hiddenDAG.observedIndex node with
  | none => none
  | some observed => match setting.value observed with
    | none => none
    | some value => some
      (P.hiddenDAG.observedIndex_sound node observed found ▸ (data.recordedValue observed).backward value)

theorem forcedAt_hidden (data : CausalExperimentData S P) (setting) (node)
    (hidden : P.hiddenDAG.hidden node = true) : data.forcedAt setting node = none := by
  unfold forcedAt
  split
  · rfl
  · rename_i observed found
    rw [P.hiddenDAG.observedIndex_hidden node hidden] at found
    cases found

def record (data : CausalExperimentData S P) (a : data.Assignment) : S.Assignment :=
  fun node => (data.recordedValue node).forward (a (P.hiddenDAG.observedNode node))

/-- Complete earlier information includes every parent, so retaining that
history implies retaining its parent configuration, even when either has
zero probability. This is a Boolean event implication before probability. -/
theorem history_implies_parent (data : CausalExperimentData S P) (child)
    (reference a : data.Assignment) (selected : data.history child reference a = true) :
    data.parentEvent child (data.parents child reference) a = true := by
  apply decide_eq_true
  funext parent edge
  have same := (List.all_eq_true.mp selected) parent (data.order.parent_mem_earlier parent child edge)
  exact of_decide_eq_true same

theorem parents_supported_of_history (data : CausalExperimentData S P) (setting) (child)
    (reference : data.Assignment)
    (supported : 0 < (data.slice setting).probNum (data.history child reference)) :
    0 < (data.slice setting).probNum (data.parentEvent child (data.parents child reference)) := by
  exact Nat.lt_of_lt_of_le supported (count_mono (fun a => data.history_implies_parent child reference a))

def eventPlaus (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (setting : HardIntervention S) (event : Event data.Assignment) : scale.Plaus :=
  scale.ratioPlaus (ofUrnEvent (data.slice setting) event)

def conditionalRatio (data : CausalExperimentData S P) (setting : HardIntervention S)
    (event evidence : Event data.Assignment)
    (supported : 0 < (data.slice setting).probNum evidence) : UrnRatio where
  N := (data.slice setting).probNum evidence
  k := (data.slice setting).probNum (inter event evidence)
  pos := supported
  le := count_mono (fun _ selected => (Bool.and_eq_true_iff.mp selected).2)

def conditionalPlaus (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (setting : HardIntervention S) (event evidence : Event data.Assignment)
    (supported : 0 < (data.slice setting).probNum evidence) : scale.Plaus :=
  scale.ratioPlaus (data.conditionalRatio setting event evidence supported)

/-- Failed evidence has no conditional plausibility. In particular, a zero
numerator never bypasses the independent positive-denominator check. -/
def conditional (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (setting : HardIntervention S) (event evidence : Event data.Assignment) : Option scale.Plaus :=
  if supported : 0 < (data.slice setting).probNum evidence then
    some (data.conditionalPlaus scale setting event evidence supported)
  else none

theorem conditional_none_iff (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (setting) (event evidence : Event data.Assignment) :
    data.conditional scale setting event evidence = none ↔
      ¬ 0 < (data.slice setting).probNum evidence := by
  simp only [conditional]
  split <;> simp_all

/-- Faithfulness applies across experiments with different urn sizes as
well: equal plausibilities mean equal rational values, not equal raw counts. -/
theorem eventPlaus_eqv_iff (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (first second) (left right : Event data.Assignment) :
    scale.eqv (data.eventPlaus scale first left) (data.eventPlaus scale second right) ↔
      QProb.Equiv ((data.slice first).probVal left) ((data.slice second).probVal right) :=
  scale.eqv_iff_sameRatio _ _

theorem conditionalPlaus_eqv_iff (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (first second) (leftEvent leftEvidence rightEvent rightEvidence : Event data.Assignment)
    (leftSupported : 0 < (data.slice first).probNum leftEvidence)
    (rightSupported : 0 < (data.slice second).probNum rightEvidence) :
    scale.eqv (data.conditionalPlaus scale first leftEvent leftEvidence leftSupported)
      (data.conditionalPlaus scale second rightEvent rightEvidence rightSupported) ↔
      QProb.Equiv ((data.slice first).condVal leftEvent leftEvidence leftSupported)
        ((data.slice second).condVal rightEvent rightEvidence rightSupported) :=
  scale.eqv_iff_sameRatio _ _

def recordedUrn (data : CausalExperimentData S P) (setting : HardIntervention S) : UrnProb S.Assignment :=
  (data.slice setting).map data.record

def recordedLaw (data : CausalExperimentData S P) (setting : HardIntervention S) : FiniteProbRecord S.Assignment :=
  FiniteProbRecord.ofUrn (data.recordedUrn setting)

end CausalExperimentData

/-- The approved qualitative requirements, as hypotheses about ordinary
experimental laws. This structure supplies no recipes, mechanisms, game,
source coupling, factorization or semantic do-calculus certificate. -/
structure QualitativeCausalRules {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}
    (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v}) : Prop where
  /-- **Effectiveness.** If experiment I sets variable v to a, the event
  v=a has the same plausibility as the certain event. The lifted setting
  makes this statement cover full-system variables without setting hidden
  variables: their antecedent is never satisfied. -/
  effectiveness : ∀ setting child value, data.forcedAt setting child = some value →
    scale.eqv (data.eventPlaus scale setting (data.nodeEvent child (fun actual => decide (actual = value))))
      (data.eventPlaus scale setting topEvent)
  /-- **Parent sufficiency.** In any experiment I leaving v unset, for
  every supported complete earlier history h and every event E concerning
  v, the conditional plausibility of E given h equals its conditional
  plausibility given only the parent values specified by h. Support of h
  implies support of those parent values, proved from event inclusion. -/
  parentSufficiency : ∀ setting child reference (event : Event (data.Value child)),
    data.forcedAt setting child = none →
    ∀ supported : 0 < (data.slice setting).probNum (data.history child reference),
    scale.eqv (data.conditionalPlaus scale setting (data.nodeEvent child event)
      (data.history child reference) supported)
      (data.conditionalPlaus scale setting (data.nodeEvent child event)
        (data.parentEvent child (data.parents child reference))
        (data.parents_supported_of_history setting child reference supported))
  /-- **Experimental stability.** For any experiments I and J both leaving
  v unset, any parent configuration p supported in both experiments, and
  every event E concerning v, the conditional plausibility of E given p
  is the same in I and J. Outcome E itself may have probability zero. -/
  experimentalStability : ∀ first second child (parents : data.Parents child)
    (event : Event (data.Value child)),
    data.forcedAt first child = none → data.forcedAt second child = none →
    ∀ (firstSupported : 0 < (data.slice first).probNum (data.parentEvent child parents))
      (secondSupported : 0 < (data.slice second).probNum (data.parentEvent child parents)),
    scale.eqv (data.conditionalPlaus scale first (data.nodeEvent child event)
      (data.parentEvent child parents) firstSupported)
      (data.conditionalPlaus scale second (data.nodeEvent child event)
        (data.parentEvent child parents) secondSupported)

end Thesis.Causality
