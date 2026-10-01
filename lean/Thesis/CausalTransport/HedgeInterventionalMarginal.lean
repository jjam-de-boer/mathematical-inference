import Thesis.CausalTransport.HedgePartialIncidenceProbability

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature}

/-!
# Interventional carrier marginals with an omitted common root

The large and small carriers need not agree on the whole interventional law:
their common-root parity is precisely the separating signal.  A common root
has no kept child, however.  Its value is not read by another forest equation,
and mechanisms outside the large forest ignore their directed parents.
Consequently omitting that root removes one incidence equation without
leaving a hidden dependency on its unspecified observed value.

This module connects the weighted partial-incidence comparison to the actual
SCMs.  The private helpers describe the two existing mechanisms uniformly;
they do not introduce a different countermodel pair.  Target agreement off
the root is reduced to intervention consistency, free forest incidence
equations, and the common full-alphabet background test.  Topological
recursion proves the reverse implication, checking all kept parent values
before a child's equation.  Intervened nodes skip both their structural
equation and their background constraint.
-/

/-! ## A private uniform description of the unchanged carrier pair -/

private def carrierModel {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool) : ExactModel S :=
  hedgeCarrierDefectModel G rich w.actionRoot
    (if nested then (w.smallParityModel rich).mechanism else (w.largeParityModel rich).mechanism)

private def carrierKept {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nested : Bool) (child : Fin S.count) : ForestChild S :=
  if nested && w.small child then restrictChild w.small w.child else w.child

private def carrierIncidence {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nested : Bool) (child : Fin S.count)
    (pairBits : Fin (pairRootCount G) -> Bool) : Bool :=
  if nested then hedgeNestedXorPairBitsWithinFrom G w.large w.small child pairBits
  else hedgeXorPairBitsWithinFrom G w.large child pairBits

private def carrierBackground (G : ObservedGraph S)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root)
    (child : Fin S.count) : S.Value child :=
  hedgePrivateDecode S child (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit) child)

/-- A common root is unused by every selected kept-edge map, on both sides
of the pair.  This concerns constructed mechanisms, not all directed edges
of the ambient ADMG, which may include extra outgoing arrows at that root. -/
private theorem carrierKept_root_none {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nested : Bool) (child balance : Fin S.count)
    (root : w.roots balance = true) : carrierKept w nested child balance = none := by
  have noChild := ((w.large_forest.roots_exact balance).mp root).2
  simp only [carrierKept]
  split
  · simp only [restrictChild, noChild]
    split <;> rfl
  · exact noChild

/-- Complete value equation at any augmented latent assignment.  The
private background is retained in this formula; extracting only its second
bit would lose precisely the nonbinary labels needed by the mass comparison. -/
private theorem carrierModel_mechanism {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (child : Fin S.count) (parents : S.ParentValues child)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :
    (carrierModel w rich nested).mechanism child parents (fun root _incident => unit root) =
      hedgeParityCarrierValue rich child
        (Bool.xor
          (if w.large child then Bool.xor
            (carrierIncidence w nested child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)))
            (hedgeForestParentBitsFrom rich (carrierKept w nested child) child parents)
          else hedgeIsSecond rich child (carrierBackground G unit child))
          (if child = w.actionRoot then hedgeDefectBitOf G unit else false))
        (carrierBackground G unit child) := by
  let old := hedgeDefectOldAssignment G unit
  have oldInputs := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot child unit
  have defect := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child unit
  simp only [carrierModel, hedgeCarrierDefectModel]
  rw [oldInputs, defect]
  cases inLarge : w.large child with
  | false =>
      have notSmall : w.small child = false := Bool.eq_false_iff.mpr (fun selected =>
        Bool.false_ne_true (inLarge.symm.trans (w.small_subset_large child selected)))
      cases nested <;>
        simp only [Bool.false_eq_true, if_false, if_true, HedgeWitness.largeParityModel,
          HedgeWitness.smallParityModel, hedgeForestParityModel, hedgeNestedForestParityModel,
          hedgeForestParityOutput, inLarge, notSmall, carrierBackground, hedgePrivateCoordinatesOf]
  | true =>
      have baseBit : hedgeIsSecond rich child
          ((if nested then (w.smallParityModel rich).mechanism else (w.largeParityModel rich).mechanism)
            child parents (fun root _incident => old root)) =
          Bool.xor (carrierIncidence w nested child (hedgePairBitsOf G old))
            (hedgeForestParentBitsFrom rich (carrierKept w nested child) child parents) := by
        cases nested with
        | false =>
            simpa only [Bool.false_eq_true, if_false, carrierIncidence, carrierKept, Bool.false_and,
              hedgeXorPairBitsWithin_pairBitsOf] using
              hedgeForestParityOutput_bit_of_mem G rich w.large w.child child parents
                (fun root _incident => old root) inLarge
        | true =>
            simp only [if_true]
            cases inSmall : w.small child with
            | false =>
                rw [← w.parityMechanism_eq_of_not_small rich child parents _ inSmall]
                simpa only [carrierIncidence, carrierKept, hedgeNestedXorPairBitsWithinFrom,
                  inSmall, Bool.true_and, Bool.false_eq_true, if_false, if_true,
                  hedgeXorPairBitsWithin_pairBitsOf] using
                  hedgeForestParityOutput_bit_of_mem G rich w.large w.child child parents
                    (fun root _incident => old root) inLarge
            | true =>
                rw [w.smallParityMechanism_of_small rich child parents _ inSmall]
                simpa only [carrierIncidence, carrierKept, hedgeNestedXorPairBitsWithinFrom,
                  inSmall, Bool.true_and, if_true, hedgeXorPairBitsWithin_pairBitsOf] using
                  hedgeForestParityOutput_bit_of_mem G rich w.small (restrictChild w.small w.child)
                    child parents (fun root _incident => old root) inSmall
      simpa only [if_true, old, carrierBackground, hedgePrivateCoordinatesOf] using congrArg
        (fun bit => hedgeParityCarrierValue rich child
          (Bool.xor bit (if child = w.actionRoot then hedgeDefectBitOf G unit else false))
          (carrierBackground G unit child)) baseBit

private theorem carrierModel_eval_free {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root)
    (child : Fin S.count) (free : intervention child = none) :
    (carrierModel w rich nested).evalUnder intervention unit child =
      hedgeParityCarrierValue rich child
        (Bool.xor
          (if w.large child then Bool.xor
            (carrierIncidence w nested child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)))
            (hedgeForestParentBitsFrom rich (carrierKept w nested child) child
              (fun parent _edge => (carrierModel w rich nested).evalUnder intervention unit parent))
          else hedgeIsSecond rich child (carrierBackground G unit child))
          (if child = w.actionRoot then hedgeDefectBitOf G unit else false))
        (carrierBackground G unit child) := by
  change (carrierModel w rich nested).evalNodeUnder intervention unit child = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  exact carrierModel_mechanism w rich nested child _ unit

/-! ## Retained-state equations for a changed parent input -/

private theorem carrierModel_mechanism_parent_response
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root)
    (child : Fin S.count) (parents : S.ParentValues child) :
    (carrierModel w rich nested).mechanism child parents (fun root _incident => unit root) =
      if w.large child then hedgeParityCarrierValue rich child
        (Bool.xor
          (Bool.xor (hedgeIsSecond rich child ((carrierModel w rich nested).eval unit child))
            (hedgeForestParentBitsFrom rich (carrierKept w nested child) child
              (fun parent _edge => (carrierModel w rich nested).eval unit parent)))
          (hedgeForestParentBitsFrom rich (carrierKept w nested child) child parents))
        (carrierBackground G unit child)
      else (carrierModel w rich nested).eval unit child := by
  have original := carrierModel_eval_free w rich nested (FiniteLatentSCM.noIntervention S) unit child rfl
  rw [carrierModel_mechanism]
  cases inside : w.large child with
  | false =>
      simp only [inside, Bool.false_eq_true, if_false] at original ⊢
      exact original.symm
  | true =>
      have bit := congrArg (hedgeIsSecond rich child) original
      rw [hedgeIsSecond_parityCarrierValue] at bit
      simp only [FiniteLatentSCM.evalUnder_noIntervention] at bit
      simp only [inside, if_true] at bit ⊢
      congr 1
      rw [bit]
      generalize carrierIncidence w nested child _ = incidence
      generalize hedgeForestParentBitsFrom rich (carrierKept w nested child) child
        (fun parent _edge => (carrierModel w rich nested).eval unit parent) = oldParents
      generalize hedgeForestParentBitsFrom rich (carrierKept w nested child) child parents = newParents
      generalize (if child = w.actionRoot then hedgeDefectBitOf G unit else false) = defect
      cases incidence <;> cases oldParents <;> cases newParents <;> cases defect <;> rfl

/-- Reconstruct the large carrier's response to arbitrary new parent values
from its factual observed assignment and retained private backgrounds.

The original pair incidence and defect cancel from the bit difference.  They
are not reselected or read by the replay.  Background coordinates must be
retained: an old `second` output alone cannot determine the full label emitted
after its bit changes.  Outside the forest the mechanism ignores all parents. -/
theorem HedgeWitness.largeCarrierDefectParityModel_mechanism_parent_response
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (parents : S.ParentValues child) :
    (w.largeCarrierDefectParityModel rich).mechanism child parents (fun root _incident => unit root) =
      if w.large child then hedgeParityCarrierValue rich child
        (Bool.xor
          (Bool.xor (hedgeIsSecond rich child ((w.largeCarrierDefectParityModel rich).eval unit child))
            (hedgeForestParentBitsFrom rich w.child child
              (fun parent _edge => (w.largeCarrierDefectParityModel rich).eval unit parent)))
          (hedgeForestParentBitsFrom rich w.child child parents))
        (hedgePrivateDecode S child (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit) child))
      else (w.largeCarrierDefectParityModel rich).eval unit child :=
  carrierModel_mechanism_parent_response w rich false unit child parents

/-- The nested carrier has the same retained-state response equation, with
its selected kept map.  Only rows in the small forest use the restricted map;
outer-only rows retain the original large-forest parent inputs.  Proving a
common replay must therefore account for changes at those outer-only parents,
not silently replace the nested map by the large map everywhere. -/
theorem HedgeWitness.smallCarrierDefectParityModel_mechanism_parent_response
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (parents : S.ParentValues child) :
    let kept := if w.small child then restrictChild w.small w.child else w.child
    (w.smallCarrierDefectParityModel rich).mechanism child parents (fun root _incident => unit root) =
      if w.large child then hedgeParityCarrierValue rich child
        (Bool.xor
          (Bool.xor (hedgeIsSecond rich child ((w.smallCarrierDefectParityModel rich).eval unit child))
            (hedgeForestParentBitsFrom rich kept child
              (fun parent _edge => (w.smallCarrierDefectParityModel rich).eval unit parent)))
          (hedgeForestParentBitsFrom rich kept child parents))
        (hedgePrivateDecode S child (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit) child))
      else (w.smallCarrierDefectParityModel rich).eval unit child := by
  simpa only [carrierKept, Bool.true_and] using
    carrierModel_mechanism_parent_response w rich true unit child parents

/-! ## The exact partial target event -/

/-- Every observed coordinate except one supplied common root.  The root
membership proof belongs to the marginal theorem, not to this Boolean mask. -/
def hedgeRootOmittedNodes (balance : Fin S.count) : NodeSet S :=
  fun node => decide (node ≠ balance)

private theorem agrees_except_iff (balance : Fin S.count) (target sample : S.Assignment) :
    Kernel.agreesOn (hedgeRootOmittedNodes balance) target sample = true ↔
      forall node, node ≠ balance -> sample node = target node := by
  unfold Kernel.agreesOn
  rw [finAll_eq_true_iff]
  constructor
  · intro all node different
    have row := all node
    simpa only [hedgeRootOmittedNodes, decide_eq_true different, if_true, decide_eq_true_eq] using row
  · intro agrees node
    by_cases different : node = balance
    · subst node
      simp only [hedgeRootOmittedNodes, ne_self_iff_false, decide_false, Bool.false_eq_true, if_false]
    · simp only [hedgeRootOmittedNodes, decide_eq_true different, if_true]
      exact decide_eq_true (agrees node different)

private def freeNodes (balance : Fin S.count)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) : NodeSet S :=
  fun node => decide (node ≠ balance) && (intervention node).isNone

private theorem freeNodes_spec (balance : Fin S.count)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (node : Fin S.count) :
    freeNodes balance intervention node = true ↔ node ≠ balance ∧ intervention node = none := by
  cases interventionAt : intervention node <;>
    simp only [freeNodes, interventionAt, Option.isNone, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, decide_eq_true_eq, reduceCtorEq, and_true, and_false]

private def interventionConsistent (balance : Fin S.count)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) : Bool :=
  finAll S.count fun node => if node = balance then true else
    match intervention node with
    | none => true
    | some value => decide (value = target node)

private theorem interventionConsistent_spec (balance : Fin S.count)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment)
    (consistent : interventionConsistent balance intervention target = true)
    (node : Fin S.count) (different : node ≠ balance) (value : S.Value node)
    (fixed : intervention node = some value) : value = target node := by
  have row := (finAll_eq_true_iff _).mp consistent node
  simpa only [if_neg different, fixed, decide_eq_true_eq] using row

private def carrierPrivateTest (rich : ObservedSignature.ValueRich S) (outer free : NodeSet S)
    (target : S.Assignment) (backgrounds : HedgePrivateCoordinates S) : Bool :=
  finAll S.count fun child => if free child then
    if outer child then decide (hedgeParityCarrierValue rich child (hedgeIsSecond rich child (target child))
      (hedgePrivateDecode S child (backgrounds child)) = target child)
    else decide (hedgePrivateDecode S child (backgrounds child) = target child)
  else true

private def carrierTarget {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (target : S.Assignment) (defect : Bool) : Fin S.count -> Bool :=
  hedgeDefectAdjustedTargetBy w.actionRoot defect (fun child => Bool.xor
    (hedgeIsSecond rich child (target child))
    (hedgeForestParentBitsFrom rich (carrierKept w nested child) child (fun parent _edge => target parent)))

private def carrierPairTest {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nested : Bool) (tested : NodeSet S)
    (target : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool) : Bool :=
  if nested then hedgePartialNestedPairBitsRealizes G w.large w.small tested target pairBits
  else hedgePartialPairBitsRealizes G w.large tested target pairBits

private theorem carrierPairTest_spec {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nested : Bool) (tested : NodeSet S)
    (target : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool)
    (realizes : carrierPairTest w nested tested target pairBits = true)
    (child : Fin S.count) (selected : tested child = true) :
    carrierIncidence w nested child pairBits = target child := by
  cases nested with
  | false => exact hedgePartialPairBitsRealizes_spec G w.large tested target pairBits realizes child selected
  | true => exact hedgePartialNestedPairBitsRealizes_spec G w.large w.small tested target pairBits realizes child selected

private theorem carrierPairTest_of {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nested : Bool) (tested : NodeSet S)
    (target : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool)
    (agrees : forall child, tested child = true -> carrierIncidence w nested child pairBits = target child) :
    carrierPairTest w nested tested target pairBits = true := by
  cases nested with
  | false => exact hedgePartialPairBitsRealizes_of G w.large tested target pairBits agrees
  | true => exact hedgePartialNestedPairBitsRealizes_of G w.large w.small tested target pairBits agrees

/-- Agreement off the omitted root makes every kept parent contribution
agree.  Its unused directed edges are not accidentally included in the proof. -/
private theorem carrierParents_congr {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (balance : Fin S.count) (root : w.roots balance = true) (child : Fin S.count)
    (left right : S.Assignment) (agrees : forall node, node ≠ balance -> left node = right node) :
    hedgeForestParentBitsFrom rich (carrierKept w nested child) child (fun parent _edge => left parent) =
      hedgeForestParentBitsFrom rich (carrierKept w nested child) child (fun parent _edge => right parent) := by
  apply hedgeForestParentBitsFrom_congr_of_kept
  intro parent edge selected
  have different : parent ≠ balance := by
    intro equal
    subst parent
    rw [carrierKept_root_none w nested child balance root] at selected
    cases selected
  exact congrArg (hedgeIsSecond rich parent) (agrees parent different)

private theorem incidence_of_output (output pair parents defect : Bool)
    (equation : output = Bool.xor (Bool.xor pair parents) defect) :
    pair = Bool.xor (Bool.xor output parents) defect := by
  rw [equation]
  cases pair <;> cases parents <;> cases defect <;> rfl

/-- Actual target agreement implies precisely the free incidence and
background constraints.  Unlike observational support, this implication
does not force the defect to the target's total parity: the omitted root's
equation and every intervened equation are absent from the partial test. -/
private theorem carrierModel_agreement_implies_tests {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (balance : Fin S.count) (root : w.roots balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root)
    (agreement : Kernel.agreesOn (hedgeRootOmittedNodes balance) target
      ((carrierModel w rich nested).evalUnder intervention unit) = true) :
    interventionConsistent balance intervention target = true ∧
      carrierPairTest w nested (NodeSet.inter w.large (freeNodes balance intervention))
        (carrierTarget w rich nested target (hedgeDefectBitOf G unit))
        (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) = true ∧
      carrierPrivateTest rich w.large (freeNodes balance intervention) target
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) = true := by
  have agrees := (agrees_except_iff balance target _).mp agreement
  refine ⟨?_, ?_, ?_⟩
  · apply (finAll_eq_true_iff _).mpr
    intro child
    by_cases same : child = balance
    · simp only [if_pos same]
    · simp only [if_neg same]
      cases fixed : intervention child with
      | none => rfl
      | some value =>
          exact decide_eq_true
            (((carrierModel w rich nested).evalUnder_effectiveness intervention unit child value fixed).symm.trans
              (agrees child same))
  · apply carrierPairTest_of
    intro child selected
    have parts := Bool.and_eq_true_iff.mp selected
    have freeParts := (freeNodes_spec balance intervention child).mp parts.2
    have equation := carrierModel_eval_free w rich nested intervention unit child freeParts.2
    rw [agrees child freeParts.1] at equation
    have bit := congrArg (hedgeIsSecond rich child) equation
    rw [hedgeIsSecond_parityCarrierValue] at bit
    simp only [parts.1, if_true] at bit
    rw [carrierParents_congr w rich nested balance root child _ target agrees] at bit
    exact incidence_of_output _ _ _ _ bit
  · apply (finAll_eq_true_iff _).mpr
    intro child
    cases selected : freeNodes balance intervention child with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
        have freeParts := (freeNodes_spec balance intervention child).mp selected
        have equation := carrierModel_eval_free w rich nested intervention unit child freeParts.2
        rw [agrees child freeParts.1] at equation
        simp only [if_true]
        cases inside : w.large child with
        | false =>
            have notRoot : child ≠ w.actionRoot := by
              intro same
              subst child
              rw [w.actionRoot_in_large] at inside
              cases inside
            have background : carrierBackground G unit child = target child := by
              simpa only [inside, Bool.false_eq_true, if_false, if_neg notRoot, Bool.xor_false,
                hedgeParityCarrierValue_reconstruct] using equation.symm
            simpa only [inside, Bool.false_eq_true, if_false, carrierBackground] using decide_eq_true background
        | true =>
            have bit := congrArg (hedgeIsSecond rich child) equation
            rw [hedgeIsSecond_parityCarrierValue] at bit
            have background := (congrArg
              (fun value => hedgeParityCarrierValue rich child value (carrierBackground G unit child)) bit).trans equation.symm
            simpa only [inside, if_true, carrierBackground] using decide_eq_true background

/-- The reverse implication is checked against the actual topological
evaluation.  Kept parents cannot be the omitted root, so recursion needs no
equation at that root.  Each intervened coordinate is checked only against
its fixed value, and each free coordinate uses its exact full-value carrier. -/
private theorem carrierModel_eval_target_of_tests {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (balance : Fin S.count) (root : w.roots balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root)
    (consistent : interventionConsistent balance intervention target = true)
    (realizes : carrierPairTest w nested (NodeSet.inter w.large (freeNodes balance intervention))
      (carrierTarget w rich nested target (hedgeDefectBitOf G unit))
      (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) = true)
    (privateFits : carrierPrivateTest rich w.large (freeNodes balance intervention) target
      (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) = true)
    (child : Fin S.count) (different : child ≠ balance) :
    (carrierModel w rich nested).evalUnder intervention unit child = target child := by
  cases fixed : intervention child with
  | some value =>
      exact ((carrierModel w rich nested).evalUnder_effectiveness intervention unit child value fixed).trans
        (interventionConsistent_spec balance intervention target consistent child different value fixed)
  | none =>
      have free : freeNodes balance intervention child = true :=
        (freeNodes_spec balance intervention child).mpr ⟨different, fixed⟩
      rw [carrierModel_eval_free w rich nested intervention unit child fixed]
      have background := (finAll_eq_true_iff _).mp privateFits child
      simp only [free, if_true] at background
      cases inside : w.large child with
      | false =>
          have notRoot : child ≠ w.actionRoot := by
            intro same
            subst child
            rw [w.actionRoot_in_large] at inside
            cases inside
          simp only [Bool.false_eq_true, if_false, if_neg notRoot, Bool.xor_false,
            hedgeParityCarrierValue_reconstruct]
          simpa only [inside, Bool.false_eq_true, if_false, decide_eq_true_eq, carrierBackground] using background
      | true =>
          have parents : hedgeForestParentBitsFrom rich (carrierKept w nested child) child
              (fun parent _edge => (carrierModel w rich nested).evalUnder intervention unit parent) =
              hedgeForestParentBitsFrom rich (carrierKept w nested child) child (fun parent _edge => target parent) := by
            apply hedgeForestParentBitsFrom_congr_of_kept
            intro parent edge selected
            have notBalance : parent ≠ balance := by
              intro same
              subst parent
              rw [carrierKept_root_none w nested child balance root] at selected
              cases selected
            exact congrArg (hedgeIsSecond rich parent)
              (carrierModel_eval_target_of_tests w rich nested balance root intervention target unit
                consistent realizes privateFits parent notBalance)
          have selected : NodeSet.inter w.large (freeNodes balance intervention) child = true :=
            Bool.and_eq_true_iff.mpr ⟨inside, free⟩
          simp only [if_true]
          rw [parents, carrierPairTest_spec w nested _ _ _ realizes child selected]
          have cancel : Bool.xor
              (Bool.xor (carrierTarget w rich nested target (hedgeDefectBitOf G unit) child)
                (hedgeForestParentBitsFrom rich (carrierKept w nested child) child (fun parent _edge => target parent)))
              (if child = w.actionRoot then hedgeDefectBitOf G unit else false) = hedgeIsSecond rich child (target child) := by
            unfold carrierTarget hedgeDefectAdjustedTargetBy
            dsimp only
            generalize hedgeIsSecond rich child (target child) = bit
            generalize hedgeForestParentBitsFrom rich (carrierKept w nested child) child _ = parentBit
            generalize (if child = w.actionRoot then hedgeDefectBitOf G unit else false) = defect
            cases bit <;> cases parentBit <;> cases defect <;> rfl
          rw [cancel]
          simpa only [inside, if_true, decide_eq_true_eq, carrierBackground] using background
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Exact semantic pullback, including inconsistent targets and empty
events.  This identity is the connection needed before applying a weighted
incidence-law theorem to any SCM marginal; it is not a supplied premise. -/
private theorem carrierModel_agreement_eq_tests {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (balance : Fin S.count) (root : w.roots balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :
    Kernel.agreesOn (hedgeRootOmittedNodes balance) target ((carrierModel w rich nested).evalUnder intervention unit) =
      (interventionConsistent balance intervention target &&
        (carrierPairTest w nested (NodeSet.inter w.large (freeNodes balance intervention))
          (carrierTarget w rich nested target (hedgeDefectBitOf G unit))
          (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) &&
          carrierPrivateTest rich w.large (freeNodes balance intervention) target
            (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)))) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro agreement
    have tests := carrierModel_agreement_implies_tests w rich nested balance root intervention target unit agreement
    exact Bool.and_eq_true_iff.mpr ⟨tests.1, Bool.and_eq_true_iff.mpr tests.2⟩
  · intro tests
    have parts := Bool.and_eq_true_iff.mp tests
    have freeParts := Bool.and_eq_true_iff.mp parts.2
    apply (agrees_except_iff balance target _).mpr
    intro child different
    exact carrierModel_eval_target_of_tests w rich nested balance root intervention target unit
      parts.1 freeParts.1 freeParts.2 child different

/-! ## Actual interventional cylinder masses -/

/-- Every complete cylinder omitting a common root has exactly the same
natural mass in the large and small carriers under any intervention.

This is now a statement about the actual evaluated SCMs, not raw incidence
events.  The preceding pullback supplies those events, with the same private
background test on both sides.  The omitted root lies in the small component
and is untested even if it is free, so the weighted cross-map theorem applies.
No restriction is placed on the other intervention coordinates or values. -/
theorem HedgeWitness.carrierDefectParityModels_agreesOn_rootOmitted_eventMass_eq
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (balance : Fin S.count) (root : w.roots balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) :
    FiniteProbRecord.eventMass (w.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)) =
      FiniteProbRecord.eventMass (w.smallCarrierDefectParityModel rich).prior.atoms
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit)) := by
  let free := freeNodes balance intervention
  let tested := NodeSet.inter w.large free
  let privateTest := fun (_defect : Bool) => carrierPrivateTest rich w.large free target
  let leftEvent := hedgePartialIncidenceLatentEvent G w.large tested (carrierTarget w rich false target) privateTest
  let rightEvent := hedgePartialNestedIncidenceLatentEvent G w.large w.small tested (carrierTarget w rich true target) privateTest
  have leftPullback : (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes balance) target
      ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)) =
      (fun unit => interventionConsistent balance intervention target && leftEvent unit) := by
    funext unit
    exact carrierModel_agreement_eq_tests w rich false balance root intervention target unit
  have rightPullback : (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes balance) target
      ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit)) =
      (fun unit => interventionConsistent balance intervention target && rightEvent unit) := by
    funext unit
    exact carrierModel_agreement_eq_tests w rich true balance root intervention target unit
  rw [leftPullback, rightPullback]
  cases consistent : interventionConsistent balance intervention target with
  | false =>
      simp only [Bool.false_and]
      rfl
  | true =>
      simp only [Bool.true_and]
      have testedSubset : NodeSet.Subset tested w.large := fun node selected => (Bool.and_eq_true_iff.mp selected).1
      have inside : w.small balance = true := ((w.small_forest.roots_exact balance).mp root).1
      have untested : tested balance = false := by
        simp only [tested, NodeSet.inter, free, freeNodes, ne_self_iff_false, decide_false, Bool.false_and, Bool.and_false]
      exact w.large_forest.component.partialIncidence_eventMass_eq_nested G w.large w.small tested
        w.small_forest.component w.small_subset_large testedSubset balance inside untested
        (carrierTarget w rich false target) (carrierTarget w rich true target) privateTest

/-- Common prior denominators turn the exact cylinder numerator comparison
into rational probability equivalence.  This includes zero-probability and
intervention-inconsistent targets; no positivity premise is needed. -/
theorem HedgeWitness.carrierDefectParityModels_agreesOn_rootOmitted_probVal_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (balance : Fin S.count) (root : w.roots balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) :
    QProb.Equiv
      ((w.largeCarrierDefectParityModel rich).prior.probVal (fun unit =>
        Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)))
      ((w.smallCarrierDefectParityModel rich).prior.probVal (fun unit =>
        Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit))) := by
  unfold QProb.Equiv FiniteProbRecord.probVal
  rw [w.carrierDefectParityModels_agreesOn_rootOmitted_eventMass_eq rich balance root intervention target]
  rfl

/-! ## Every event local to the root-omitted marginal -/

/-- A finite presentation of the marginal: replace only the omitted root
by the signature's already supplied default value.  This does not alter a
model or choose a value from a nonempty type. -/
private def projectRoot (balance : Fin S.count) (sample : S.Assignment) : S.Assignment :=
  fun node => if node = balance then S.defaultValue node else sample node

private theorem projectRoot_singleton_eq (balance : Fin S.count) (target sample : S.Assignment) :
    FiniteProbRecord.singletonEvent target (projectRoot balance sample) =
      (decide (target balance = S.defaultValue balance) &&
        Kernel.agreesOn (hedgeRootOmittedNodes balance) target sample) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro selected
    have equal : projectRoot balance sample = target := of_decide_eq_true selected
    have atRoot := congrFun equal balance
    have rootValue : target balance = S.defaultValue balance := by
      simpa only [projectRoot, if_pos rfl] using atRoot.symm
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true rootValue, (agrees_except_iff balance target sample).mpr ?_⟩
    intro node different
    simpa only [projectRoot, if_neg different] using congrFun equal node
  · intro selected
    have parts := Bool.and_eq_true_iff.mp selected
    have rootValue : target balance = S.defaultValue balance := of_decide_eq_true parts.1
    have agrees := (agrees_except_iff balance target sample).mp parts.2
    apply decide_eq_true
    funext node
    by_cases same : node = balance
    · subst node
      simpa only [projectRoot, if_pos rfl] using rootValue.symm
    · simpa only [projectRoot, if_neg same] using agrees node same

private theorem projected_singletons_equiv {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (root : w.roots balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (target : S.Assignment) :
    QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).prior.map (fun unit => projectRoot balance
        ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit))).probVal
        (FiniteProbRecord.singletonEvent target))
      (((w.smallCarrierDefectParityModel rich).prior.map (fun unit => projectRoot balance
        ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit))).probVal
        (FiniteProbRecord.singletonEvent target)) := by
  have leftEq : (fun unit => FiniteProbRecord.singletonEvent target (projectRoot balance
      ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit))) =
      (fun unit => decide (target balance = S.defaultValue balance) &&
        Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)) := by
    funext unit
    exact projectRoot_singleton_eq balance target _
  have rightEq : (fun unit => FiniteProbRecord.singletonEvent target (projectRoot balance
      ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit))) =
      (fun unit => decide (target balance = S.defaultValue balance) &&
        Kernel.agreesOn (hedgeRootOmittedNodes balance) target
          ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit)) := by
    funext unit
    exact projectRoot_singleton_eq balance target _
  have pullback : QProb.Equiv
      ((w.largeCarrierDefectParityModel rich).prior.probVal (fun unit =>
        FiniteProbRecord.singletonEvent target (projectRoot balance
          ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit))))
      ((w.smallCarrierDefectParityModel rich).prior.probVal (fun unit =>
        FiniteProbRecord.singletonEvent target (projectRoot balance
          ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit)))) := by
    rw [leftEq, rightEq]
    cases allowed : decide (target balance = S.defaultValue balance) with
    | false =>
        simp only [Bool.false_and]
        exact QProb.equiv_refl _
    | true =>
        simp only [Bool.true_and]
        exact w.carrierDefectParityModels_agreesOn_rootOmitted_probVal_equiv rich balance root intervention target
  exact QProb.equiv_trans
    ((w.largeCarrierDefectParityModel rich).prior.map_probVal _ _)
    (QProb.equiv_trans pullback
      (QProb.equiv_symm ((w.smallCarrierDefectParityModel rich).prior.map_probVal _ _)))

/-- The large and small carrier pair has the same probability for *every*
observed event that does not inspect one common root, under any intervention.

Exact singleton cylinders first determine the finite projected law using the
signature's existing duplicate-free enumeration.  Event locality then removes
the harmless default-root presentation.  This argument includes arbitrary
conditioning cylinders and nonbinary labels, not just one parity event.
It makes no claim that either model agrees on the omitted root itself. -/
theorem HedgeWitness.carrierDefectParityModels_interventional_probVal_equiv_of_rootOmitted
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (balance : Fin S.count) (root : w.roots balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : Event S.Assignment) (eventLocal : EventDependsOnlyOn (hedgeRootOmittedNodes balance) event) :
    QProb.Equiv
      ((w.largeCarrierDefectParityModel rich).prior.probVal
        (fun unit => event ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)))
      ((w.smallCarrierDefectParityModel rich).prior.probVal
        (fun unit => event ((w.smallCarrierDefectParityModel rich).evalUnder intervention unit))) := by
  let left := w.largeCarrierDefectParityModel rich
  let right := w.smallCarrierDefectParityModel rich
  let leftMap := fun unit => projectRoot balance (left.evalUnder intervention unit)
  let rightMap := fun unit => projectRoot balance (right.evalUnder intervention unit)
  have preserved (sample : S.Assignment) : event sample = event (projectRoot balance sample) := by
    apply eventLocal
    intro node selected
    have different : node ≠ balance := of_decide_eq_true selected
    simp only [projectRoot, if_neg different]
  have projected := FiniteProbRecord.probVal_extensional_of_singletons
    (left.prior.map leftMap) (right.prior.map rightMap)
    S.assignmentEnumeration S.assignmentEnumeration_nodup S.assignmentEnumeration_complete
    (projected_singletons_equiv w rich balance root intervention) event
  exact QProb.equiv_trans
    (left.prior.probVal_congr _ _ (fun unit => preserved (left.evalUnder intervention unit)))
    (QProb.equiv_trans (QProb.equiv_symm (left.prior.map_probVal leftMap event))
      (QProb.equiv_trans projected
        (QProb.equiv_trans (right.prior.map_probVal rightMap event)
          (QProb.equiv_symm (right.prior.probVal_congr _ _ (fun unit => preserved (right.evalUnder intervention unit)))))))

/-! ## Joint kernels provide conditioning denominators of the same pair -/

/-- Any joint kernel whose outcomes omit a common root agrees in the same
large/small carrier pair, for any action set.  Outcomes may otherwise lie
inside the large forest, and may include other common roots.  The result is
denotational kernel agreement, not denominator identifiability across all
compatible models.  Both the empty-action and interventional branches are
retained by the unconditional kernel semantics. -/
theorem HedgeWitness.carrierDefectParityModels_valueEquivalent_of_rootOmitted
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (balance : Fin S.count) (root : w.roots balance = true)
    (query : JointKernelQuery S) (omitted : query.outcome balance = false) :
    query.ValueEquivalent (w.largeCarrierDefectParityModel rich) (w.smallCarrierDefectParityModel rich) := by
  intro reference
  let left := w.largeCarrierDefectParityModel rich
  let right := w.smallCarrierDefectParityModel rich
  let kernel : Kernel S := ⟨query.outcome, query.action, NodeSet.empty⟩
  let event := Kernel.agreesOn query.outcome reference
  have eventLocal : EventDependsOnlyOn (hedgeRootOmittedNodes balance) event := by
    intro first second agrees
    apply Kernel.agreesOn_sample_congr
    intro node selected
    have different : node ≠ balance := by
      intro same
      subst node
      rw [omitted] at selected
      cases selected
    exact agrees node (decide_eq_true different)
  have underEqual (intervention : (node : Fin S.count) -> Option (S.Value node)) :=
    w.carrierDefectParityModels_interventional_probVal_equiv_of_rootOmitted rich balance root intervention event eventLocal
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

end Causality
end Thesis
