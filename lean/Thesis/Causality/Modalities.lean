import Thesis.Causality.Core
import Thesis.Causality.ModalDerivation

namespace Thesis
namespace Causality

open Probability

namespace HardIntervention

/-- Extend a dependent intervention by setting every selected node. -/
def setNodes (intervention : HardIntervention S) (nodes : NodeSet S)
    (reference : S.Assignment) : HardIntervention S where
  value := fun i =>
    if nodes i then some (reference i) else intervention.value i

theorem targets_setNodes (intervention : HardIntervention S)
    (nodes : NodeSet S) (reference : S.Assignment) (i : Fin S.count) :
    (intervention.setNodes nodes reference).targets i =
      NodeSet.union intervention.targets nodes i := by
  cases selected : nodes i <;>
    simp [setNodes, targets, NodeSet.union, selected]

/-- From the empty mode, executing an action lock is exactly kernel intervention. -/
theorem empty_setNodes_eq_kernel_intervention (kernel : Kernel S)
    (reference : S.Assignment) (i : Fin S.count) :
    ((HardIntervention.empty S).setNodes kernel.action reference).value i =
      kernel.intervention reference i := by
  cases selected : kernel.action i <;>
    simp [setNodes, HardIntervention.empty, FiniteLatentSCM.noIntervention,
      Kernel.intervention, selected]

/-- Execute a list of primitive single-node settings from left to right. -/
def setVariablesSequentially (intervention : HardIntervention S)
    (reference : S.Assignment) :
    List (Fin S.count) -> HardIntervention S
  | [] => intervention
  | node :: rest =>
      setVariablesSequentially
        (intervention.set node (reference node)) reference rest

theorem setVariablesSequentially_value
    (intervention : HardIntervention S) (reference : S.Assignment)
    (nodes : List (Fin S.count)) (node : Fin S.count) :
    (intervention.setVariablesSequentially reference nodes).value node =
      if node ∈ nodes then some (reference node)
      else intervention.value node := by
  induction nodes generalizing intervention with
  | nil => simp [setVariablesSequentially]
  | cons selected rest ih =>
      rw [setVariablesSequentially, ih]
      by_cases inRest : node ∈ rest
      · simp [inRest]
      · by_cases same : node = selected
        · subst selected
          rw [if_neg inRest, if_pos (by simp)]
          exact intervention.set_at_target node (reference node)
        · simp only [List.mem_cons, same, false_or, inRest, if_false]
          exact intervention.set_away_from_target selected node
            (reference selected) same

end HardIntervention

/-!
Proof-carrying epistemic transitions for the graph-aware causal model.

Operations are ordinary executable record transformations.  A transition does
not perform an operation by inspecting a context; it stores source and target
modes together with a proof that the named operation relates their records.
Conditioning updates `belief`, not the model's product prior.
-/

structure CausalEpistemicRecord (S : ObservedSignature) where
  model : ExactModel S
  belief : FiniteProbRecord model.latent.Assignment
  intervention : HardIntervention S

namespace CausalEpistemicRecord

def initial (model : ExactModel S) : CausalEpistemicRecord S where
  model := model
  belief := model.prior
  intervention := HardIntervention.empty S

def observedDist (R : CausalEpistemicRecord S) :
    FiniteProbRecord S.Assignment :=
  R.belief.map (R.model.evalUnder R.intervention.value)

def observedValue (R : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) : QProb :=
  R.observedDist.probVal event

/-- The latent event implementing observation of selected nodes at a valuation. -/
def nodeObservationEvidence (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment)
    (u : R.model.latent.Assignment) : Bool :=
  Kernel.agreesOn nodes reference
    (R.model.evalUnder R.intervention.value u)

def conditionLatent (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief.conditionOn evidence hEvidence
  intervention := R.intervention

def conditionObservation (R : CausalEpistemicRecord S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : R.observedDist.EventPositive evidence) :
    CausalEpistemicRecord S :=
  R.conditionLatent
    (fun u => evidence (R.model.evalUnder R.intervention.value u)) (by
      simpa [observedDist, FiniteProbRecord.EventPositive,
        FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using
          hEvidence)

def setVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.set target value

/-- Execute a simultaneous finite hard intervention at a reference valuation. -/
def interveneNodes (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) : CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.setNodes nodes reference

/-- Execute a list of single-node interventions from left to right. -/
def setVariablesSequentially (R : CausalEpistemicRecord S)
    (reference : S.Assignment) (nodes : List (Fin S.count)) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention :=
    R.intervention.setVariablesSequentially reference nodes

/-- The canonical duplicate-free list selected by a Boolean node set. -/
def selectedNodeList (S : ObservedSignature) (nodes : NodeSet S) :
    List (Fin S.count) :=
  (List.finRange S.count).filter fun node => nodes node

theorem mem_selectedNodeList (nodes : NodeSet S) (node : Fin S.count) :
    node ∈ selectedNodeList S nodes <-> nodes node = true := by
  simp [selectedNodeList]

/-- The number of nodes classified as true. -/
def selectedNodeCount (nodes : NodeSet S) : Nat :=
  (selectedNodeList S nodes).length

/--
The canonical embedding of the selected nodes, in ambient index order.
This is the map \(j_S\) of the finite node-set selection proposition.
-/
def selectedEmbed (nodes : NodeSet S)
    (i : Fin (selectedNodeCount nodes)) : Fin S.count :=
  (selectedNodeList S nodes).get i

theorem pairwise_get_of_lt {α : Type _} {R : α -> α -> Prop}
    {values : List α} (h : values.Pairwise R)
    (i j : Fin values.length) (hij : i.val < j.val) :
    R (values.get i) (values.get j) := by
  induction values with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp h
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (Nat.lt_irrefl 0 hij).elim
          | succ j' =>
              exact parts.1 (tail.get j') (List.get_mem tail j')
      | succ i' =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero _ hij).elim
          | succ j' =>
              exact ih parts.2 i' j' (Nat.succ_lt_succ_iff.mp hij)

theorem finRange_pairwise_lt (n : Nat) :
    (List.finRange n).Pairwise (fun a b => a.val < b.val) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro b hb
        rcases List.mem_map.mp hb with ⟨k, _, eq⟩
        cases eq
        exact Nat.succ_pos k.val
      · exact List.Pairwise.map Fin.succ
          (fun _ _ hlt => Nat.succ_lt_succ hlt) ih

theorem selectedNodeList_pairwise_lt (nodes : NodeSet S) :
    (selectedNodeList S nodes).Pairwise
      (fun a b => a.val < b.val) :=
  (finRange_pairwise_lt S.count).filter (fun node => nodes node)

theorem selectedNodeList_nodup (nodes : NodeSet S) :
    (selectedNodeList S nodes).Nodup :=
  (selectedNodeList_pairwise_lt nodes).imp
    (fun hlt => Fin.ne_of_val_ne (Nat.ne_of_lt hlt))

theorem selectedEmbed_mem (nodes : NodeSet S)
    (i : Fin (selectedNodeCount nodes)) :
    nodes (selectedEmbed nodes i) = true :=
  (mem_selectedNodeList nodes (selectedEmbed nodes i)).mp
    (List.get_mem (selectedNodeList S nodes) i)

theorem selectedEmbed_strict_mono (nodes : NodeSet S)
    {i j : Fin (selectedNodeCount nodes)}
    (hij : i.val < j.val) :
    (selectedEmbed nodes i).val < (selectedEmbed nodes j).val :=
  pairwise_get_of_lt (selectedNodeList_pairwise_lt nodes) i j hij

theorem selectedEmbed_inj (nodes : NodeSet S)
    {i j : Fin (selectedNodeCount nodes)}
    (h : selectedEmbed nodes i = selectedEmbed nodes j) : i = j := by
  apply Fin.ext
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have mono := selectedEmbed_strict_mono nodes hlt
    rw [h] at mono
    exact (Nat.lt_irrefl _ mono).elim
  · exact heq
  · have mono := selectedEmbed_strict_mono nodes hgt
    rw [h] at mono
    exact (Nat.lt_irrefl _ mono).elim

theorem selectedEmbed_lt_reflect (nodes : NodeSet S)
    {i j : Fin (selectedNodeCount nodes)}
    (hlt : (selectedEmbed nodes i).val < (selectedEmbed nodes j).val) :
    i.val < j.val := by
  rcases Nat.lt_trichotomy i.val j.val with h | h | h
  · exact h
  · have same : i = j := Fin.ext h
    rw [same] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · have mono := selectedEmbed_strict_mono nodes h
    exact (Nat.lt_asymm hlt mono).elim

theorem exists_selectedEmbed_of_mem (nodes : NodeSet S)
    {node : Fin S.count} (h : nodes node = true) :
    Exists fun i : Fin (selectedNodeCount nodes) =>
      selectedEmbed nodes i = node := by
  have hmem : node ∈ selectedNodeList S nodes :=
    (mem_selectedNodeList nodes node).mpr h
  refine ⟨⟨(selectedNodeList S nodes).idxOf node,
    List.idxOf_lt_length_of_mem hmem⟩, ?_⟩
  apply beq_iff_eq.mp
  change
    ((selectedNodeList S nodes).get
      ⟨(selectedNodeList S nodes).idxOf node,
        List.idxOf_lt_length_of_mem hmem⟩ == node) = true
  simpa [List.get_eq_getElem, List.idxOf] using
    (List.findIdx_getElem
      (p := fun value => value == node)
      (xs := selectedNodeList S nodes)
      (w := List.idxOf_lt_length_of_mem hmem))

theorem mem_iff_exists_selectedEmbed (nodes : NodeSet S)
    (node : Fin S.count) :
    nodes node = true <->
      Exists fun i : Fin (selectedNodeCount nodes) =>
        selectedEmbed nodes i = node := by
  constructor
  · intro h
    exact exists_selectedEmbed_of_mem nodes h
  · intro ⟨i, hi⟩
    simpa [hi] using selectedEmbed_mem nodes i

theorem setVariablesSequentially_intervention_value
    (R : CausalEpistemicRecord S) (reference : S.Assignment)
    (nodes : List (Fin S.count)) (node : Fin S.count) :
    (R.setVariablesSequentially reference nodes).intervention.value node =
      if node ∈ nodes then some (reference node)
      else R.intervention.value node := by
  exact R.intervention.setVariablesSequentially_value reference nodes node

/-- The sequential implementation of a simultaneous node-set intervention. -/
def interveneNodesSequentially (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment) :
    CausalEpistemicRecord S :=
  R.setVariablesSequentially reference (selectedNodeList S nodes)

theorem interveneNodesSequentially_intervention_value
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) (node : Fin S.count) :
    (R.interveneNodesSequentially nodes reference).intervention.value node =
      (R.interveneNodes nodes reference).intervention.value node := by
  rw [interveneNodesSequentially,
    setVariablesSequentially_intervention_value]
  cases selected : nodes node <;>
    simp [mem_selectedNodeList, selected, interveneNodes,
      HardIntervention.setNodes]

/--
Simultaneous finite intervention is the order-free macro obtained by folding
the corresponding single-node settings.
-/
theorem interveneNodes_eq_sequential
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) :
    R.interveneNodes nodes reference =
      R.interveneNodesSequentially nodes reference := by
  have interventionEq :
      R.intervention.setNodes nodes reference =
        R.intervention.setVariablesSequentially reference
          (selectedNodeList S nodes) := by
    apply HardIntervention.extensional
    intro node
    exact (interveneNodesSequentially_intervention_value
      R nodes reference node).symm
  unfold interveneNodes interveneNodesSequentially
    CausalEpistemicRecord.setVariablesSequentially
  rw [interventionEq]

def unsetVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) : CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.unset target

theorem conditioning_keeps_model (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).model = R.model := by
  rfl

theorem conditioning_keeps_product_prior (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).model.prior = R.model.prior := by
  rfl

theorem setting_keeps_belief (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).belief = R.belief := by
  rfl

theorem unsetting_keeps_belief (R : CausalEpistemicRecord S)
    (target : Fin S.count) :
    (R.unsetVariable target).belief = R.belief := by
  rfl

theorem setVariable_at_target (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).intervention.value target = some value := by
  exact R.intervention.set_at_target target value

theorem conditionLatent_probVal (R : CausalEpistemicRecord S)
    (evidence event : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    QProb.Equiv
      ((R.conditionLatent evidence hEvidence).belief.probVal event)
      (QProb.div
        (R.belief.probVal (fun u => evidence u && event u))
        (R.belief.probVal evidence) hEvidence) :=
  R.belief.conditionOn_probVal evidence event hEvidence

theorem observedDist_probVal (R : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (R.observedDist.probVal event)
      (R.belief.probVal
        (fun u => event (R.model.evalUnder R.intervention.value u))) :=
  FiniteProbRecord.map_probVal R.belief
    (R.model.evalUnder R.intervention.value) event

end CausalEpistemicRecord

inductive CausalTransitionLabel where
  | conditioning
  | setting
  | unsetting
  deriving DecidableEq, Repr

inductive CausalRecordStep :
    CausalTransitionLabel ->
      CausalEpistemicRecord S -> CausalEpistemicRecord S -> Type 1
  | conditioning (R : CausalEpistemicRecord S)
      (evidence : R.model.latent.Assignment -> Bool)
      (hEvidence : R.belief.EventPositive evidence) :
      CausalRecordStep .conditioning R (R.conditionLatent evidence hEvidence)
  | setting (R : CausalEpistemicRecord S)
      (target : Fin S.count) (value : S.Value target) :
      CausalRecordStep .setting R (R.setVariable target value)
  | intervening (R : CausalEpistemicRecord S) (nodes : NodeSet S)
      (reference : S.Assignment) :
      CausalRecordStep .setting R (R.interveneNodes nodes reference)
  | unsetting (R : CausalEpistemicRecord S) (target : Fin S.count) :
      CausalRecordStep .unsetting R (R.unsetVariable target)

theorem CausalRecordStep.model_eq
    (step : CausalRecordStep label source target) :
    target.model = source.model := by
  cases step <;> rfl

structure CausalMode (S : ObservedSignature) where
  name : String
  record : CausalEpistemicRecord S

structure CausalTransition (S : ObservedSignature) where
  label : CausalTransitionLabel
  source : CausalMode S
  target : CausalMode S
  valid : CausalRecordStep label source.record target.record

namespace CausalTransition

theorem model_eq (transition : CausalTransition S) :
    transition.target.record.model = transition.source.record.model :=
  transition.valid.model_eq

def conditioning (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) : CausalTransition S where
  label := .conditioning
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.conditionLatent evidence hEvidence⟩
  valid := CausalRecordStep.conditioning R evidence hEvidence

/-- A concrete observation transition realising an observation lock. -/
def observing (sourceName targetName : String)
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) : CausalTransition S :=
  CausalTransition.conditioning sourceName targetName R
    (R.nodeObservationEvidence nodes reference) hEvidence

def setting (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) : CausalTransition S where
  label := .setting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.setVariable target value⟩
  valid := CausalRecordStep.setting R target value

/-- Execute every action lock in a kernel as one finite record transformation. -/
def intervening (sourceName targetName : String)
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) : CausalTransition S where
  label := .setting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.interveneNodes nodes reference⟩
  valid := CausalRecordStep.intervening R nodes reference

def unsetting (sourceName targetName : String)
    (R : CausalEpistemicRecord S) (target : Fin S.count) :
    CausalTransition S where
  label := .unsetting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.unsetVariable target⟩
  valid := CausalRecordStep.unsetting R target

/-- Executable transitions that realise one of the symbolic query locks. -/
inductive Realizes : CausalTransition S -> CausalQueryModality S -> Prop
  | setting (sourceName targetName : String)
      (R : CausalEpistemicRecord S) (target : Fin S.count)
      (value : S.Value target) :
      Realizes
        (CausalTransition.setting sourceName targetName R target value)
        (.intervene (NodeSet.singleton target))
  | intervening (sourceName targetName : String)
      (R : CausalEpistemicRecord S) (nodes : NodeSet S)
      (reference : S.Assignment) :
      Realizes
        (CausalTransition.intervening sourceName targetName R nodes reference)
        (.intervene nodes)
  | observing (sourceName targetName : String)
      (R : CausalEpistemicRecord S) (nodes : NodeSet S)
      (reference : S.Assignment)
      (hEvidence : R.belief.EventPositive
        (R.nodeObservationEvidence nodes reference)) :
      Realizes
        (CausalTransition.observing sourceName targetName R nodes reference
          hEvidence)
        (.observe nodes)

theorem setting_realizes_intervention
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    Realizes (CausalTransition.setting sourceName targetName R target value)
      (.intervene (NodeSet.singleton target)) :=
  .setting sourceName targetName R target value

theorem intervening_realizes_intervention
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment) :
    Realizes
      (CausalTransition.intervening sourceName targetName R nodes reference)
      (.intervene nodes) :=
  .intervening sourceName targetName R nodes reference

theorem kernel_action_realized
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (kernel : Kernel S) (reference : S.Assignment) :
    Realizes
      (CausalTransition.intervening sourceName targetName R kernel.action
        reference)
      (.intervene kernel.action) :=
  intervening_realizes_intervention sourceName targetName R kernel.action
    reference

theorem observing_realizes_observation
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) :
    Realizes
      (CausalTransition.observing sourceName targetName R nodes reference
        hEvidence)
      (.observe nodes) :=
  .observing sourceName targetName R nodes reference hEvidence

theorem setting_adds_intervention_target
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) (i : Fin S.count) :
    (CausalTransition.setting sourceName targetName R target value).target.record.intervention.targets i =
      NodeSet.union R.intervention.targets (NodeSet.singleton target) i := by
  by_cases same : i = target
  · subst i
    simp [CausalTransition.setting, CausalEpistemicRecord.setVariable,
      HardIntervention.targets, HardIntervention.set, NodeSet.union,
      NodeSet.singleton]
  · simp [CausalTransition.setting, CausalEpistemicRecord.setVariable,
      HardIntervention.targets, HardIntervention.set, NodeSet.union,
      NodeSet.singleton, same]

theorem intervening_adds_action_targets
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment) (i : Fin S.count) :
    (CausalTransition.intervening sourceName targetName R nodes reference).target.record.intervention.targets i =
      NodeSet.union R.intervention.targets nodes i :=
  R.intervention.targets_setNodes nodes reference i

end CausalTransition

end Causality
end Thesis
