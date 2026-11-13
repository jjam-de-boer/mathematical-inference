import Thesis.CausalTransport.HedgeCompensatedPreimage
import Thesis.CausalTransport.HedgeReadoutNoise
import Thesis.Causality.LocalEventComparison

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Full interventional cylinders in the compensated carrier pair

Conditioners on installed rows cannot use protected-mechanism closure.
Instead, fixing the genuine fresh inputs makes each forest row impose one
ordinary or nested incidence equation and a common full-label background
test.  A cylinder on a parent-closed coordinate set leaves an inner incidence
equation untested whenever that set omits a small-forest vertex.  Weighted
partial-incidence counting can then compare the two actual old priors,
before slice integration restores every independent fresh factor.

Closure concerns the original kept map and the composed outcome-flow map,
not every arrow of the ambient graph.  The omitted vertex need not be a
common root or a sink: its old or new descendants may lie outside the
inspected set.  The earlier unused-common-root marginal is recovered as a
special case.  Background constraints and intervention consistency are
retained, including zero-mass full-label targets and arbitrary intervention
labels.  These are equalities in the actual compensated pair, not claims
that every such marginal is identifiable across all compatible models.
-/

/-- A coordinate set contains the declared parents used by the original
kept map and the common compensated flow whenever it inspects their child.

Unused ambient arrows impose no closure condition.  This structural
invariant is shared by the two carrier mechanisms, including their
full-value background response.  It permits omitted vertices with genuine
outgoing routes, provided those routes do not enter the inspected set. -/
def HedgeWitness.CarrierFlowParentClosed {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nodes : NodeSet S) : Prop :=
  forall parent child, S.directed parent child = true ->
    (w.child parent = some child ∨ w.largeOutcomeFlowSuccessor parent = some child) ->
      nodes child = true -> nodes parent = true

/-- Every topological prefix is closed for the actual carrier-flow parent
maps: their used parents are declared graph parents and hence earlier.
The boundary is excluded, so a small-forest boundary supplies an untested
incidence equation even when it has later responding descendants. -/
def hedgeCarrierPrefixNodes (boundary : Fin S.count) : NodeSet S :=
  fun node => decide (node.val < boundary.val)

theorem HedgeWitness.carrierFlowParentClosed_prefix
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (boundary : Fin S.count) : w.CarrierFlowParentClosed (hedgeCarrierPrefixNodes boundary) := by
  intro parent child edge _used selected
  exact decide_eq_true (Nat.lt_trans (S.directed_earlier edge) (of_decide_eq_true selected))

namespace HedgeCompensatedMarginal

variable {G : ObservedGraph S} {q : JointKernelQuery S}

private abbrev OldUnit (G : ObservedGraph S) :=
  (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root

/-- A uniform notation for the existing pair, not a new SCM construction.
Its latent extension and prior are literally the same on both sides. -/
private def baseModel (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool) : ExactModel S :=
  hedgeCarrierDefectModel G rich w.actionRoot
    (if nested then (w.smallParityModel rich).mechanism else (w.largeParityModel rich).mechanism)

private def model (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool) : ExactModel S :=
  (baseModel w rich nested).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)

private def kept (w : HedgeWitness G q) (nested : Bool) (child : Fin S.count) : ForestChild S :=
  if nested && w.small child then restrictChild w.small w.child else w.child

private def incidence (w : HedgeWitness G q) (nested : Bool) (child : Fin S.count)
    (pairBits : Fin (pairRootCount G) -> Bool) : Bool :=
  if nested then hedgeNestedXorPairBitsWithinFrom G w.large w.small child pairBits
  else hedgeXorPairBitsWithinFrom G w.large child pairBits

private def background (G : ObservedGraph S) (unit : OldUnit G) (child : Fin S.count) : S.Value child :=
  hedgePrivateDecode S child (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit) child)

private theorem base_mechanism (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (unit : OldUnit G) (child : Fin S.count) (parents : S.ParentValues child) :
    (baseModel w rich nested).mechanism child parents (fun root _incident => unit root) =
      hedgeParityCarrierValue rich child
        (Bool.xor
          (if w.large child then Bool.xor
            (incidence w nested child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)))
            (hedgeForestParentBitsFrom rich (kept w nested child) child parents)
          else hedgeIsSecond rich child (background G unit child))
          (if child = w.actionRoot then hedgeDefectBitOf G unit else false))
        (background G unit child) := by
  cases nested with
  | false =>
      simpa only [incidence, kept, Bool.false_eq_true, if_false, Bool.false_and, background] using
        w.largeCarrierDefectParityModel_mechanism_incidence rich child parents unit
  | true =>
      simpa only [incidence, kept, Bool.true_and, if_true, background] using
        w.smallCarrierDefectParityModel_mechanism_incidence rich child parents unit

/-- Distinct installation supplies the exact local response; absent rows
retain their original mechanism and decoded old inputs. -/
private theorem folded_mechanism (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool)
    (bits : Fin S.count -> Bool) (unit : OldUnit G) (child : Fin S.count) (parents : S.ParentValues child) :
    (model w rich noise nested).mechanism child parents
        (fun root _incident => (baseModel w rich nested).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit root) =
      if w.smallOutcomeFlowNodes child then
        hedgeNoisyReadout rich child (w.carrierFlowReadoutStep rich noise child).injectOld
          (w.carrierFlowReadoutStep rich noise child).parentSignal parents
          ((baseModel w rich nested).mechanism child parents (fun root _incident => unit root)) (bits child)
      else (baseModel w rich nested).mechanism child parents (fun root _incident => unit root) := by
  by_cases selected : w.smallOutcomeFlowNodes child = true
  · rw [if_pos selected]
    have listed : w.carrierFlowReadoutStep rich noise child ∈ w.carrierFlowReadoutPlan rich noise :=
      List.mem_map.mpr ⟨child, (NodeSet.mem_members_iff w.smallOutcomeFlowNodes child).mpr selected, rfl⟩
    exact FiniteLatentSCM.withHedgeReadouts_mechanism_of_mem (baseModel w rich nested) rich _
      (w.carrierFlowReadoutPlan_pivots_distinct rich noise) _ listed bits unit parents
  · rw [if_neg selected]
    apply FiniteLatentSCM.withHedgeReadouts_mechanism_of_off
    intro step listed same
    rcases List.mem_map.mp listed with ⟨node, member, equal⟩
    subst step
    have installed := (NodeSet.mem_members_iff w.smallOutcomeFlowNodes node).mp member
    have sameNode : child = node := same
    subst node
    exact selected installed

/-- At a fixed requested value and fixed fresh input, installed forest
rows invert their common readout; unmodified rows inspect their literal bit. -/
private def requiredBit (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (bits : Fin S.count -> Bool)
    (child : Fin S.count) (parents : S.ParentValues child) (target : S.Value child) : Bool :=
  if w.smallOutcomeFlowNodes child then
    hedgeReadoutRequiredCarrierBit rich child (w.carrierFlowReadoutStep rich noise child).parentSignal parents (bits child) target
  else hedgeIsSecond rich child target

private def rowTarget (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool) (bits : Fin S.count -> Bool)
    (child : Fin S.count) (parents : S.ParentValues child) (target : S.Value child) (defect : Bool) : Bool :=
  Bool.xor (Bool.xor (requiredBit w rich noise bits child parents target)
    (hedgeForestParentBitsFrom rich (kept w nested child) child parents))
    (if child = w.actionRoot then defect else false)

/-- The common full-label test, with no incidence coordinate hidden in it.
Outside the forest, a routed row uses its original private value and only
the new flow signal; absent outside rows retain that private value literally. -/
private def rowPrivate (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (bits : Fin S.count -> Bool)
    (child : Fin S.count) (parents : S.ParentValues child) (target : S.Value child)
    (backgrounds : HedgePrivateCoordinates S) : Bool :=
  if w.large child then
    if w.smallOutcomeFlowNodes child then
      hedgeReadoutCarrierBackgroundFits rich child (w.carrierFlowReadoutStep rich noise child).parentSignal
        parents (bits child) target (hedgePrivateDecode S child (backgrounds child))
    else decide (hedgeParityCarrierValue rich child (hedgeIsSecond rich child target)
      (hedgePrivateDecode S child (backgrounds child)) = target)
  else decide ((if w.smallOutcomeFlowNodes child then
    hedgeNoisyReadout rich child false (w.carrierFlowReadoutStep rich noise child).parentSignal parents
      (hedgePrivateDecode S child (backgrounds child)) (bits child)
    else hedgePrivateDecode S child (backgrounds child)) = target)

private theorem carrier_preimage (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (source : Bool) (background target : S.Value child) :
    decide (hedgeParityCarrierValue rich child source background = target) =
      (decide (source = hedgeIsSecond rich child target) &&
        decide (hedgeParityCarrierValue rich child (hedgeIsSecond rich child target) background = target)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true_iff]
  constructor
  · intro equal
    have bit := congrArg (hedgeIsSecond rich child) equal
    rw [hedgeIsSecond_parityCarrierValue] at bit
    exact ⟨bit, by rw [← bit]; exact equal⟩
  · intro parts
    rw [parts.1]
    exact parts.2

private theorem xor_equation (source parents defect required : Bool) :
    decide (Bool.xor (Bool.xor source parents) defect = required) =
      decide (source = Bool.xor (Bool.xor required parents) defect) := by
  cases source <;> cases parents <;> cases defect <;> cases required <;> rfl

/-- Exact row preimage for every actual current parent input.  Only the
incidence target depends on which carrier is selected; the background
predicate is identical.  No row's bit is substituted for its full value. -/
private theorem row_preimage (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool)
    (bits : Fin S.count -> Bool) (unit : OldUnit G) (child : Fin S.count)
    (parents : S.ParentValues child) (target : S.Value child) :
    decide ((model w rich noise nested).mechanism child parents
        (fun root _incident => (baseModel w rich nested).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit root) = target) =
      ((if w.large child then decide
        (incidence w nested child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) =
          rowTarget w rich noise nested bits child parents target (hedgeDefectBitOf G unit)) else true) &&
        rowPrivate w rich noise bits child parents target (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))) := by
  rw [folded_mechanism, base_mechanism]
  by_cases inside : w.large child = true
  · by_cases installed : w.smallOutcomeFlowNodes child = true
    · simp only [rowPrivate, rowTarget, requiredBit, HedgeWitness.carrierFlowReadoutStep, inside, installed, if_true]
      rw [hedgeNoisyReadout_carrier_preimage, xor_equation]
      rfl
    · simp only [rowPrivate, rowTarget, requiredBit, inside, if_true, if_neg installed]
      rw [carrier_preimage, xor_equation]
      rfl
  · have different : child ≠ w.actionRoot := by
      intro same
      subst child
      exact inside w.actionRoot_in_large
    have outside : w.large child = false := Bool.eq_false_iff.mpr inside
    simp only [rowPrivate, HedgeWitness.carrierFlowReadoutStep, if_neg different, outside,
      Bool.false_eq_true, if_false,
      Bool.xor_false, hedgeParityCarrierValue_reconstruct, Bool.true_and, background]

/-! ## Selected rows use only selected parents -/

private theorem kept_subset (w : HedgeWitness G q) (nested : Bool) (child parent : Fin S.count)
    (found : kept w nested child parent = some child) : w.child parent = some child := by
  unfold kept at found
  split at found
  · unfold restrictChild at found
    split at found
    · exact found
    · cases found
  · exact found

private theorem parent_bits_congr (rich : ObservedSignature.ValueRich S) (map : ForestChild S)
    (nodes : NodeSet S) (child : Fin S.count)
    (closed : forall parent, S.directed parent child = true -> map parent = some child -> nodes parent = true)
    (first second : S.ParentValues child)
    (agree : forall parent (edge : S.directed parent child = true), nodes parent = true -> first parent edge = second parent edge) :
    hedgeForestParentBitsFrom rich map child first = hedgeForestParentBitsFrom rich map child second := by
  apply hedgeForestParentBitsFrom_congr_of_kept
  intro parent edge found
  exact congrArg (hedgeIsSecond rich parent) (agree parent edge (closed parent edge found))

/-- Only the old kept maps and the actual common readout signals are
inspected.  Closure of these maps gives full mechanism congruence at each
selected row; no global non-influence of omitted vertices is asserted. -/
private theorem folded_mechanism_congr (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool)
    (bits : Fin S.count -> Bool) (unit : OldUnit G) (nodes : NodeSet S)
    (closed : w.CarrierFlowParentClosed nodes) (child : Fin S.count) (selected : nodes child = true)
    (first second : S.ParentValues child)
    (agree : forall parent (edge : S.directed parent child = true), nodes parent = true -> first parent edge = second parent edge) :
    (model w rich noise nested).mechanism child first
        (fun root _incident => (baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit root) =
      (model w rich noise nested).mechanism child second
        (fun root _incident => (baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit root) := by
  have oldParents := parent_bits_congr rich (kept w nested child) nodes child
    (fun parent edge found => closed parent child edge (.inl (kept_subset w nested child parent found)) selected) first second agree
  have original : (baseModel w rich nested).mechanism child first (fun root _incident => unit root) =
      (baseModel w rich nested).mechanism child second (fun root _incident => unit root) := by
    rw [base_mechanism, base_mechanism, oldParents]
  have outerParents := parent_bits_congr rich w.child nodes child
    (fun parent edge found => closed parent child edge (.inl found) selected) first second agree
  have flowParents := parent_bits_congr rich w.largeOutcomeFlowSuccessor nodes child
    (fun parent edge found => closed parent child edge (.inr found) selected) first second agree
  have signal : (w.carrierFlowReadoutStep rich noise child).parentSignal first =
      (w.carrierFlowReadoutStep rich noise child).parentSignal second := by
    dsimp only [HedgeWitness.carrierFlowReadoutStep]
    rw [outerParents, flowParents]
  rw [folded_mechanism, folded_mechanism, original]
  split
  · unfold hedgeNoisyReadout
    rw [signal]
  · rfl

/-! ## The exact finite cylinder tests -/

private theorem agrees_iff (nodes : NodeSet S) (target sample : S.Assignment) :
    Kernel.agreesOn nodes target sample = true ↔
      forall node, nodes node = true -> sample node = target node := by
  unfold Kernel.agreesOn
  constructor
  · intro agreement node selected
    have row := (finAll_eq_true_iff _).mp agreement node
    simpa only [selected, if_true, decide_eq_true_eq] using row
  · intro agree
    apply (finAll_eq_true_iff _).mpr
    intro node
    cases selected : nodes node with
    | false => simp only [Bool.false_eq_true, if_false]
    | true => exact decide_eq_true (agree node selected)

private def freeNodes (nodes : NodeSet S) (intervention : (node : Fin S.count) -> Option (S.Value node)) : NodeSet S :=
  fun node => nodes node && (intervention node).isNone

private theorem free_spec (nodes : NodeSet S) (intervention : (node : Fin S.count) -> Option (S.Value node)) (node : Fin S.count) :
    freeNodes nodes intervention node = true ↔ nodes node = true ∧ intervention node = none := by
  cases atNode : intervention node <;>
    simp only [freeNodes, atNode, Option.isNone, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, reduceCtorEq, and_true, and_false]

private def consistent (nodes : NodeSet S) (intervention : (node : Fin S.count) -> Option (S.Value node))
    (target : S.Assignment) : Bool :=
  finAll S.count fun node => if nodes node then
    match intervention node with
    | none => true
    | some value => decide (value = target node)
    else true

private theorem consistent_spec (nodes : NodeSet S) (intervention : (node : Fin S.count) -> Option (S.Value node))
    (target : S.Assignment) (valid : consistent nodes intervention target = true)
    (child : Fin S.count) (selected : nodes child = true) (value : S.Value child)
    (fixed : intervention child = some value) : value = target child := by
  have row := (finAll_eq_true_iff _).mp valid child
  simpa only [selected, if_true, fixed, decide_eq_true_eq] using row

private def pairTarget (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool) (bits : Fin S.count -> Bool)
    (target : S.Assignment) (defect : Bool) (child : Fin S.count) : Bool :=
  rowTarget w rich noise nested bits child (fun parent _edge => target parent) (target child) defect

private def pairTest (w : HedgeWitness G q) (nested : Bool) (tested : NodeSet S)
    (target : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool) : Bool :=
  if nested then hedgePartialNestedPairBitsRealizes G w.large w.small tested target pairBits
  else hedgePartialPairBitsRealizes G w.large tested target pairBits

private theorem pairTest_spec (w : HedgeWitness G q) (nested : Bool) (tested : NodeSet S)
    (target : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool)
    (valid : pairTest w nested tested target pairBits = true) (child : Fin S.count) (selected : tested child = true) :
    incidence w nested child pairBits = target child := by
  cases nested with
  | false => exact hedgePartialPairBitsRealizes_spec G w.large tested target pairBits valid child selected
  | true => exact hedgePartialNestedPairBitsRealizes_spec G w.large w.small tested target pairBits valid child selected

private theorem pairTest_of (w : HedgeWitness G q) (nested : Bool) (tested : NodeSet S)
    (target : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool)
    (agree : forall child, tested child = true -> incidence w nested child pairBits = target child) :
    pairTest w nested tested target pairBits = true := by
  cases nested with
  | false => exact hedgePartialPairBitsRealizes_of G w.large tested target pairBits agree
  | true => exact hedgePartialNestedPairBitsRealizes_of G w.large w.small tested target pairBits agree

private def privateTest (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (bits : Fin S.count -> Bool)
    (free : NodeSet S) (target : S.Assignment) (backgrounds : HedgePrivateCoordinates S) : Bool :=
  finAll S.count fun child => if free child then
    rowPrivate w rich noise bits child (fun parent _edge => target parent) (target child) backgrounds
  else true

/-- Factual cylinder agreement supplies the exact row tests at a free
coordinate.  All used parents agree by structural closure, including
parents whose rows themselves carry a responding readout. -/
private theorem row_checks_of_agreement (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool)
    (bits : Fin S.count -> Bool) (unit : OldUnit G) (nodes : NodeSet S)
    (closed : w.CarrierFlowParentClosed nodes)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment)
    (agree : forall node, nodes node = true ->
      (model w rich noise nested).evalUnder intervention
        ((baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit) node = target node)
    (child : Fin S.count) (selected : nodes child = true) (free : intervention child = none) :
    ((if w.large child then decide
      (incidence w nested child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) =
        pairTarget w rich noise nested bits target (hedgeDefectBitOf G unit) child) else true) &&
      rowPrivate w rich noise bits child (fun parent _edge => target parent) (target child)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))) = true := by
  let augmented := (baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit
  have equation : (model w rich noise nested).evalUnder intervention augmented child =
      (model w rich noise nested).mechanism child
        (fun parent _edge => (model w rich noise nested).evalUnder intervention augmented parent)
        (fun root _incident => augmented root) := by
    change (model w rich noise nested).evalNodeUnder intervention augmented child = _
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder
    rw [free]
    rfl
  have parents := folded_mechanism_congr w rich noise nested bits unit nodes closed child selected
    (fun parent _edge => (model w rich noise nested).evalUnder intervention augmented parent)
    (fun parent _edge => target parent) (fun parent _edge selectedParent => agree parent selectedParent)
  have equal := parents.symm.trans (equation.symm.trans (agree child selected))
  exact (row_preimage w rich noise nested bits unit child _ (target child)).symm.trans (decide_eq_true equal)

private theorem agreement_implies_tests (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool)
    (bits : Fin S.count -> Bool) (unit : OldUnit G) (nodes : NodeSet S)
    (closed : w.CarrierFlowParentClosed nodes)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment)
    (agreement : Kernel.agreesOn nodes target
      ((model w rich noise nested).evalUnder intervention
        ((baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit)) = true) :
    consistent nodes intervention target = true ∧
      pairTest w nested (NodeSet.inter w.large (freeNodes nodes intervention))
        (pairTarget w rich noise nested bits target (hedgeDefectBitOf G unit))
        (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) = true ∧
      privateTest w rich noise bits (freeNodes nodes intervention) target
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) = true := by
  have agree := (agrees_iff nodes target _).mp agreement
  refine ⟨?_, ?_, ?_⟩
  · apply (finAll_eq_true_iff _).mpr
    intro child
    by_cases selected : nodes child = true
    · simp only [selected, if_true]
      cases fixed : intervention child with
      | none => rfl
      | some value =>
          exact decide_eq_true
            (((model w rich noise nested).evalUnder_effectiveness intervention _ child value fixed).symm.trans (agree child selected))
    · simp only [if_neg selected]
  · apply pairTest_of
    intro child selected
    have parts := Bool.and_eq_true_iff.mp selected
    have freeParts := (free_spec nodes intervention child).mp parts.2
    have row := (Bool.and_eq_true_iff.mp
      (row_checks_of_agreement w rich noise nested bits unit nodes closed intervention target agree child freeParts.1 freeParts.2)).1
    simpa only [parts.1, if_true, decide_eq_true_eq] using row
  · apply (finAll_eq_true_iff _).mpr
    intro child
    cases selected : freeNodes nodes intervention child with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
        have freeParts := (free_spec nodes intervention child).mp selected
        simp only [if_true]
        exact (Bool.and_eq_true_iff.mp
          (row_checks_of_agreement w rich noise nested bits unit nodes closed intervention target agree child freeParts.1 freeParts.2)).2

/-- Conversely, the complete finite tests reconstruct the actual full
evaluation on the selected set.  Recursive calls inspect declared earlier
selected parents, as guaranteed by the proved mechanism congruence.
Intervened rows use effectiveness and impose no structural/background test. -/
private theorem eval_target_of_tests (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool)
    (bits : Fin S.count -> Bool) (unit : OldUnit G) (nodes : NodeSet S)
    (closed : w.CarrierFlowParentClosed nodes)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment)
    (valid : consistent nodes intervention target = true)
    (realizes : pairTest w nested (NodeSet.inter w.large (freeNodes nodes intervention))
      (pairTarget w rich noise nested bits target (hedgeDefectBitOf G unit))
      (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) = true)
    (fits : privateTest w rich noise bits (freeNodes nodes intervention) target
      (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) = true)
    (child : Fin S.count) (selected : nodes child = true) :
    (model w rich noise nested).evalUnder intervention
      ((baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit) child = target child := by
  let augmented := (baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit
  cases fixed : intervention child with
  | some value =>
      exact ((model w rich noise nested).evalUnder_effectiveness intervention augmented child value fixed).trans
        (consistent_spec nodes intervention target valid child selected value fixed)
  | none =>
      have free : freeNodes nodes intervention child = true := (free_spec nodes intervention child).mpr ⟨selected, fixed⟩
      have background := (finAll_eq_true_iff _).mp fits child
      simp only [free, if_true] at background
      have row : ((if w.large child then decide
          (incidence w nested child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) =
            pairTarget w rich noise nested bits target (hedgeDefectBitOf G unit) child) else true) &&
          rowPrivate w rich noise bits child (fun parent _edge => target parent) (target child)
            (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))) = true := by
        apply Bool.and_eq_true_iff.mpr
        refine ⟨?_, background⟩
        by_cases inside : w.large child = true
        · rw [if_pos inside]
          exact decide_eq_true (pairTest_spec w nested _ _ _ realizes child (Bool.and_eq_true_iff.mpr ⟨inside, free⟩))
        · exact if_neg inside
      have targetRow : (model w rich noise nested).mechanism child (fun parent _edge => target parent)
          (fun root _incident => augmented root) = target child :=
        of_decide_eq_true ((row_preimage w rich noise nested bits unit child _ (target child)).trans row)
      change (model w rich noise nested).evalNodeUnder intervention augmented child = target child
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder
      rw [fixed]
      refine (folded_mechanism_congr w rich noise nested bits unit nodes closed child selected
        (fun parent _edge => (model w rich noise nested).evalUnder intervention augmented parent)
        (fun parent _edge => target parent) ?_).trans targetRow
      intro parent edge selectedParent
      exact eval_target_of_tests w rich noise nested bits unit nodes closed intervention target valid realizes fits parent selectedParent
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Exact Boolean pullback, including intervention-inconsistent and
impossible full-alphabet cylinders.  This is the semantic bridge required
before applying any raw weighted incidence comparison. -/
private theorem agreement_eq_tests (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (nested : Bool)
    (bits : Fin S.count -> Bool) (unit : OldUnit G) (nodes : NodeSet S)
    (closed : w.CarrierFlowParentClosed nodes)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) :
    Kernel.agreesOn nodes target
      ((model w rich noise nested).evalUnder intervention
        ((baseModel w rich nested).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit)) =
      (consistent nodes intervention target &&
        (pairTest w nested (NodeSet.inter w.large (freeNodes nodes intervention))
          (pairTarget w rich noise nested bits target (hedgeDefectBitOf G unit))
          (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) &&
          privateTest w rich noise bits (freeNodes nodes intervention) target
            (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)))) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro agreement
    have parts := agreement_implies_tests w rich noise nested bits unit nodes closed intervention target agreement
    exact Bool.and_eq_true_iff.mpr ⟨parts.1, Bool.and_eq_true_iff.mpr parts.2⟩
  · intro tests
    have parts := Bool.and_eq_true_iff.mp tests
    have freeParts := Bool.and_eq_true_iff.mp parts.2
    apply (agrees_iff nodes target _).mpr
    intro child selected
    exact eval_target_of_tests w rich noise nested bits unit nodes closed intervention target parts.1 freeParts.1 freeParts.2 child selected

/-! ## Weighted comparison on every fixed fresh-input slice -/

/-- The global pullback has the same private test on both sides, but may
have different defect-dependent incidence targets.  Omitting any small-
forest vertex releases one inner equation, exactly as required by the existing
weighted partial-incidence comparison.  Inconsistent interventions give a
common empty event and are included rather than discarded by support. -/
private theorem fixed_slice_equiv (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (bits : Fin S.count -> Bool)
    (nodes : NodeSet S) (closed : w.CarrierFlowParentClosed nodes)
    (balance : Fin S.count) (inside : w.small balance = true) (omitted : nodes balance = false)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) :
    QProb.Equiv
      ((baseModel w rich false).prior.probVal (fun unit => Kernel.agreesOn nodes target
        ((model w rich noise false).evalUnder intervention
          ((baseModel w rich false).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit))))
      ((baseModel w rich true).prior.probVal (fun unit => Kernel.agreesOn nodes target
        ((model w rich noise true).evalUnder intervention
          ((baseModel w rich true).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit)))) := by
  let free := freeNodes nodes intervention
  let tested := NodeSet.inter w.large free
  let backgrounds := fun (_defect : Bool) => privateTest w rich noise bits free target
  let leftEvent := hedgePartialIncidenceLatentEvent G w.large tested (pairTarget w rich noise false bits target) backgrounds
  let rightEvent := hedgePartialNestedIncidenceLatentEvent G w.large w.small tested (pairTarget w rich noise true bits target) backgrounds
  have leftPullback : (fun unit => Kernel.agreesOn nodes target
      ((model w rich noise false).evalUnder intervention
        ((baseModel w rich false).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit))) =
      (fun unit => consistent nodes intervention target && leftEvent unit) := by
    funext unit
    exact agreement_eq_tests w rich noise false bits unit nodes closed intervention target
  have rightPullback : (fun unit => Kernel.agreesOn nodes target
      ((model w rich noise true).evalUnder intervention
        ((baseModel w rich true).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit))) =
      (fun unit => consistent nodes intervention target && rightEvent unit) := by
    funext unit
    exact agreement_eq_tests w rich noise true bits unit nodes closed intervention target
  rw [leftPullback, rightPullback]
  cases valid : consistent nodes intervention target with
  | false =>
      simp only [Bool.false_and]
      exact QProb.equiv_refl _
  | true =>
      simp only [Bool.true_and]
      have testedSubset : NodeSet.Subset tested w.large := fun node selected => (Bool.and_eq_true_iff.mp selected).1
      have untested : tested balance = false := by
        simp only [tested, free, NodeSet.inter, freeNodes, omitted, Bool.false_and, Bool.and_false]
      exact w.large_forest.component.partialIncidence_probVal_equiv_nested G w.large w.small tested
        w.small_forest.component w.small_subset_large testedSubset balance inside untested
        (pairTarget w rich noise false bits target) (pairTarget w rich noise true bits target) backgrounds

end HedgeCompensatedMarginal

/-! ## Integrating every real fresh factor of the actual plan -/

/-- Every interventional full-value cylinder on a carrier-flow closed set
omitting one small-forest vertex has the same probability in the actual
compensated carrier pair.  The omitted vertex may have outgoing kept or
new-flow edges to coordinates outside the selected set.

The fixed-input fibre comparison is integrated against the literal private
product priors.  The canonical plan has distinct pivots, so no two independent
coordinates are identified by its node-indexed encoding.  Noise records may
be arbitrary and need not have support or bias.  Route permission is not
required by this marginal theorem; observational equality and numerator
separation of a countermodel remain separate obligations. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_agreesOn_probVal_equiv_of_parentClosed
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (nodes : NodeSet S) (closed : w.CarrierFlowParentClosed nodes)
    (balance : Fin S.count) (inside : w.small balance = true) (omitted : nodes balance = false)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) :
    QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => Kernel.agreesOn nodes target
          (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich
            (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit)))
      (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => Kernel.agreesOn nodes target
          (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich
            (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit))) := by
  apply FiniteLatentSCM.withHedgeReadouts_prior_equiv_of_encodedSlices _ _ rich _
    (w.carrierFlowReadoutPlan_pivots_distinct rich noise)
  intro bits
  exact HedgeCompensatedMarginal.fixed_slice_equiv w rich noise bits nodes closed balance inside omitted intervention target

/-- Equality extends from the selected full-value cylinders to every
event depending only on that set.  Finite projected singleton comparison
retains the full observed alphabet and arbitrary old/new latent spaces and
denominators.  No positivity or support restriction is imposed on events. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_interventional_probVal_equiv_of_parentClosed
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (nodes : NodeSet S) (closed : w.CarrierFlowParentClosed nodes)
    (balance : Fin S.count) (inside : w.small balance = true) (omitted : nodes balance = false)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : Event S.Assignment) (localEvent : EventDependsOnlyOn nodes event) :
    QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => event (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich
          (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit)))
      (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => event (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich
          (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit))) := by
  let left := (w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
  let right := (w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
  let leftEval := left.evalUnder intervention
  let rightEval := right.evalUnder intervention
  have cylinders (target : S.Assignment) :
      QProb.Equiv ((left.prior.map leftEval).probVal (Kernel.agreesOn nodes target))
        ((right.prior.map rightEval).probVal (Kernel.agreesOn nodes target)) :=
    QProb.equiv_trans (left.prior.map_probVal leftEval _)
      (QProb.equiv_trans
        (w.carrierDefectParityModels_carrierFlowReadoutPlan_agreesOn_probVal_equiv_of_parentClosed rich noise nodes closed balance inside omitted intervention target)
        (QProb.equiv_symm (right.prior.map_probVal rightEval _)))
  have projected := FiniteProbRecord.probVal_equiv_of_agreementCylinders
    (left.prior.map leftEval) (right.prior.map rightEval) nodes cylinders event localEvent
  exact QProb.equiv_trans (QProb.equiv_symm (left.prior.map_probVal leftEval event))
    (QProb.equiv_trans projected (right.prior.map_probVal rightEval event))

/-- Any joint kernel whose outcomes lie in a carrier-flow closed set
omitting a small-forest vertex agrees in the actual compensated pair.
Selected coordinates may be installed, including internal responding rows
and other roots.  The action set and its full-value labels are arbitrary,
and the empty-action branch is included.

This is equality in this particular pair, not semantic identifiability of
the denominator across all compatible models. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_parentClosed
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (nodes : NodeSet S) (closed : w.CarrierFlowParentClosed nodes)
    (balance : Fin S.count) (inside : w.small balance = true) (omitted : nodes balance = false)
    (query : JointKernelQuery S) (within : NodeSet.Subset query.outcome nodes) :
    query.ValueEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise))
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)) := by
  intro reference
  let left := (w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
  let right := (w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
  let kernel := query.operationKernel
  let event := Kernel.agreesOn query.outcome reference
  have localEvent : EventDependsOnlyOn nodes event := by
    intro first second agree
    apply Kernel.agreesOn_sample_congr
    intro child selected
    exact agree child (within child selected)
  have underEqual (intervention : (node : Fin S.count) -> Option (S.Value node)) :=
    w.carrierDefectParityModels_carrierFlowReadoutPlan_interventional_probVal_equiv_of_parentClosed
      rich noise nodes closed balance inside omitted intervention event localEvent
  have cylinderEqual : QProb.Equiv ((kernel.distribution left reference).probVal event)
      ((kernel.distribution right reference).probVal event) := by
    unfold Kernel.distribution
    split
    · exact QProb.equiv_trans (left.interventionalValue_eq (kernel.intervention reference) event)
        (QProb.equiv_trans (underEqual (kernel.intervention reference))
          (QProb.equiv_symm (right.interventionalValue_eq (kernel.intervention reference) event)))
    · exact QProb.equiv_trans (left.observationalValue_eq event)
        (QProb.equiv_trans (underEqual (FiniteLatentSCM.noIntervention S))
          (QProb.equiv_symm (right.observationalValue_eq event)))
  exact ⟨ProbabilityResult.trans (Kernel.unconditionalDenote left query.outcome query.action reference)
    (ProbabilityResult.trans (.value cylinderEqual)
      (ProbabilityResult.symm (Kernel.unconditionalDenote right query.outcome query.action reference)))⟩

/-! ## The unused-common-root specialization -/

/-- An unused common root may be removed from the full node set.  Common
roothood rules out an original kept child, while the explicit unused-flow
premise rules out a newly installed child.  Other ambient arrows are allowed. -/
theorem HedgeWitness.carrierFlowParentClosed_rootOmitted
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (balance : Fin S.count) (root : w.roots balance = true)
    (unused : w.largeOutcomeFlowSuccessor balance = none) :
    w.CarrierFlowParentClosed (hedgeRootOmittedNodes balance) := by
  intro parent child _edge used _selected
  apply decide_eq_true
  intro same
  subst parent
  cases used with
  | inl original =>
      rw [((w.large_forest.roots_exact balance).mp root).2] at original
      cases original
  | inr routed => rw [unused] at routed; cases routed

/-- The earlier root-omitted cylinder API is a corollary of the general
closed-set comparison, with no duplicated evaluation or counting proof. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_agreesOn_rootOmitted_probVal_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (balance : Fin S.count) (root : w.roots balance = true) (unused : w.largeOutcomeFlowSuccessor balance = none)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) :
    QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich
            (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit)))
      (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich
            (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit))) :=
  w.carrierDefectParityModels_carrierFlowReadoutPlan_agreesOn_probVal_equiv_of_parentClosed rich noise
    (hedgeRootOmittedNodes balance) (w.carrierFlowParentClosed_rootOmitted balance root unused) balance
    ((w.small_forest.roots_exact balance).mp root).1 (by simp only [hedgeRootOmittedNodes, ne_self_iff_false, decide_false])
    intervention target

/-- Every event ignoring an unused common root agrees; this specializes
the general local-event comparison and retains arbitrary interventions. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_interventional_probVal_equiv_of_rootOmitted
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (balance : Fin S.count) (root : w.roots balance = true) (unused : w.largeOutcomeFlowSuccessor balance = none)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : Event S.Assignment) (localEvent : EventDependsOnlyOn (hedgeRootOmittedNodes balance) event) :
    QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => event (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich
          (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit)))
      (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).prior.probVal
        (fun unit => event (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich
          (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention unit))) :=
  w.carrierDefectParityModels_carrierFlowReadoutPlan_interventional_probVal_equiv_of_parentClosed rich noise
    (hedgeRootOmittedNodes balance) (w.carrierFlowParentClosed_rootOmitted balance root unused) balance
    ((w.small_forest.roots_exact balance).mp root).1 (by simp only [hedgeRootOmittedNodes, ne_self_iff_false, decide_false])
    intervention event localEvent

/-- Any joint kernel omitting an unused common root agrees in this actual
pair, including installed responding outcomes and empty actions. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_rootOmitted
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (balance : Fin S.count) (root : w.roots balance = true) (unused : w.largeOutcomeFlowSuccessor balance = none)
    (query : JointKernelQuery S) (omitted : query.outcome balance = false) :
    query.ValueEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise))
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)) := by
  apply w.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_parentClosed rich noise
    (hedgeRootOmittedNodes balance) (w.carrierFlowParentClosed_rootOmitted balance root unused) balance
    ((w.small_forest.roots_exact balance).mp root).1 (by simp only [hedgeRootOmittedNodes, ne_self_iff_false, decide_false]) query
  intro child selected
  apply decide_eq_true
  intro same
  subst child
  rw [omitted] at selected
  cases selected

/-- A common root already requested by the original joint query remains
unused by the composed flow: canonical routes stop at queried outcomes,
and the original kept map has no child at a common root. -/
theorem HedgeWitness.largeOutcomeFlowSuccessor_none_of_root_in_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (balance : Fin S.count) (root : w.roots balance = true) (inOutcome : q.outcome balance = true) :
    w.largeOutcomeFlowSuccessor balance = none := by
  have original := ((w.large_forest.roots_exact balance).mp root).2
  have routed := w.rootReadoutSuccessor_of_outcome inOutcome
  simp only [HedgeWitness.largeOutcomeFlowSuccessor, forestChildPrioritize, original, routed]
  split <;> rfl

end Causality
end Thesis
