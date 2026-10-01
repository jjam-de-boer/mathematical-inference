import Thesis.CausalTransport.HedgePartialIncidence

namespace Thesis
namespace Causality

open Probability

/-!
# Full-alphabet interventional support at a fixed private defect

The observational carrier construction chooses its defect bit from the
target's root parity.  Reusing that observational section under an
intervention would impose an equation at a vertex whose mechanism is no
longer evaluated.  It would also obscure the important fact that the large
model can realize every consistent target with either private defect bit.

Here an explicitly supplied intervened vertex of the large forest absorbs
the incidence parity correction.  Its equation is skipped by the SCM, while
all free equations are met by the constructive partial-incidence section.
The private defect remains the independently specified bit, and every
observed private coordinate retains the target's actual full-alphabet label.
Topological induction proves evaluation of the complete target, including
intervened vertices outside the forest and arbitrary intervention values.

The resulting joint latent event has strictly positive mass in each defect
stratum.  An explicit additional pair-root translation compensates for
flipping that defect and preserves the complete evaluated assignment under
the same intervention.  This is stronger than unrestricted interventional
support, but it is not an equality of weighted stratum probabilities: the
finite translations must still be connected to the prior weights before
proving a common conditional denominator.  Nor does this alone route root
parity to an arbitrary outcome.
The module retains the original SCMs and imports no soundness implementation.
-/

/-! ## A concrete pair-root section with a freely specified defect -/

/-- Incidence required by a target when the private defect is specified
independently.  XORing that defect out at the common root leaves exactly
the pair-root incidence needed by each free forest equation. -/
def HedgeWitness.largeCarrierInterventionalIncidence
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment) (defect : Bool)
    (child : Fin S.count) : Bool :=
  Bool.xor (hedgeForestRequiredIncidence rich w.child target child)
    (if child = w.actionRoot then defect else false)

/-- Correct the remaining total incidence parity at a vertex whose
mechanism will be intervened on.  The vector is actual finite-search data;
no latent realization is selected from an existential proposition. -/
def HedgeWitness.largeCarrierInterventionalPairBits
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (target : S.Assignment) (defect : Bool) : Fin (pairRootCount G) -> Bool :=
  w.large_forest.component.partialTargetPairBits G w.large balance inside
    (w.largeCarrierInterventionalIncidence rich target defect)

/-- Every large-forest incidence equation except the balancing one is
realized literally.  The balancing vertex need not be a root or a sink. -/
theorem HedgeWitness.largeCarrierInterventionalPairBits_spec
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (target : S.Assignment) (defect : Bool)
    (child : Fin S.count) (selected : w.large child = true) (different : child ≠ balance) :
    hedgeXorPairBitsWithinFrom G w.large child
      (w.largeCarrierInterventionalPairBits rich balance inside target defect) =
      w.largeCarrierInterventionalIncidence rich target defect child := by
  let tested := NodeSet.diff w.large (NodeSet.singleton balance)
  have untested : tested balance = false := by
    simp only [tested, NodeSet.diff, NodeSet.singleton, decide_true, Bool.not_true, Bool.and_false]
  have selectedTest : tested child = true := by
    simpa only [tested, NodeSet.diff, NodeSet.singleton, decide_eq_false different,
      Bool.not_false, Bool.and_true] using selected
  exact w.large_forest.component.partialTargetPairBits_spec G w.large tested
    (NodeSet.diff_subset_left w.large (NodeSet.singleton balance)) balance inside untested
    (w.largeCarrierInterventionalIncidence rich target defect) child selectedTest

/-- Prefix the prescribed defect onto the computed old pair-root and
private-background assignment.  All observed labels are retained, not just
the two distinguished parity labels. -/
def HedgeWitness.largeCarrierInterventionalSupportLatent
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (target : S.Assignment) (defect : Bool) :
    (w.largeCarrierDefectParityModel rich).latent.Assignment :=
  hedgeDefectAssignment G
    (hedgeCarrierSupportLatent G target
      (w.largeCarrierInterventionalPairBits rich balance inside target defect)) defect

theorem HedgeWitness.largeCarrierInterventionalSupportLatent_defect
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (target : S.Assignment) (defect : Bool) :
    hedgeDefectBitOf G (w.largeCarrierInterventionalSupportLatent rich balance inside target defect) = defect :=
  hedgeDefectBitOf_assignment G _ defect

/-! ## Actual SCM evaluation under arbitrary compatible interventions -/

/-- The computed unit realizes the whole target under an arbitrary
intervention fixing `balance`.  Target consistency is required exactly at
intervened coordinates; no condition is imposed on the target's free bits
or on the independently prescribed private defect.

At an intervened vertex the mechanism is skipped.  At a free forest vertex
the balancing vertex is necessarily different, so its requested incidence
equation holds.  Earlier parent outputs already match by recursion.  Outside
the large forest the unchanged private background returns the target label. -/
theorem HedgeWitness.largeCarrierDefectParityModel_evalNodeUnder_interventional_support
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (fixed : intervention balance ≠ none)
    (target : S.Assignment)
    (consistent : forall node value, intervention node = some value -> target node = value)
    (defect : Bool) (child : Fin S.count) :
    (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention
        (w.largeCarrierInterventionalSupportLatent rich balance inside target defect) child =
      target child := by
  let pairBits := w.largeCarrierInterventionalPairBits rich balance inside target defect
  let oldSupport := hedgeCarrierSupportLatent G target pairBits
  let support := hedgeDefectAssignment G oldSupport defect
  have oldInputsEq : hedgeDefectOldInputs G w.actionRoot child
      (fun root _incident => support root) = (fun root _incident => oldSupport root) :=
    hedgeDefectOldInputs_assignment G w.actionRoot child oldSupport defect
  have background : hedgePrivateDecode S child
      (hedgePrivateIndex G child (fun root _incident => oldSupport root)) = target child :=
    hedgeCarrierSupportLatent_privateDecode G target pairBits child
  have defectAt : hedgeIndependentDefectBit G w.actionRoot child
      (fun root _incident => support root) = if child = w.actionRoot then defect else false := by
    by_cases equal : child = w.actionRoot
    · subst child
      simpa using hedgeIndependentDefectBit_assignment_same G w.actionRoot oldSupport defect
    · simpa only [if_neg equal] using
        hedgeIndependentDefectBit_assignment_other G w.actionRoot child equal oldSupport defect
  change (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention support child = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases interventionAt : intervention child with
  | some value => exact (consistent child value interventionAt).symm
  | none =>
      simp only [HedgeWitness.largeCarrierDefectParityModel, hedgeCarrierDefectModel]
      rw [oldInputsEq, background, defectAt]
      refine (congrArg (fun bit => hedgeParityCarrierValue rich child bit (target child)) ?_).trans
        (hedgeParityCarrierValue_reconstruct rich child (target child))
      change Bool.xor
          (hedgeIsSecond rich child ((w.largeParityModel rich).mechanism child
            (fun parent _edge => (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention support parent)
            (fun root _incident => oldSupport root)))
          (if child = w.actionRoot then defect else false) = hedgeIsSecond rich child (target child)
      cases selected : w.large child with
      | false =>
          have different : child ≠ w.actionRoot := by
            intro equal
            subst child
            rw [w.actionRoot_in_large] at selected
            cases selected
          have baseOutside : hedgeIsSecond rich child ((w.largeParityModel rich).mechanism child
              (fun parent _edge => (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention support parent)
              (fun root _incident => oldSupport root)) = hedgeIsSecond rich child (target child) := by
            simp only [HedgeWitness.largeParityModel, hedgeForestParityModel, hedgeForestParityOutput,
              selected, Bool.false_eq_true, if_false, background]
          rw [baseOutside]
          simp only [if_neg different, Bool.xor_false]
      | true =>
          have different : child ≠ balance := by
            intro equal
            subst child
            exact fixed interventionAt
          have parentsEq : hedgeForestParentBitsFrom rich w.child child
              (fun parent _edge => (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention support parent) =
              hedgeForestParentBitsFrom rich w.child child (fun parent _edge => target parent) :=
            hedgeForestParentBitsFrom_congr rich child (fun _parent => rfl) (fun parent edge =>
              w.largeCarrierDefectParityModel_evalNodeUnder_interventional_support rich balance inside
                intervention fixed target consistent defect parent)
          have pairEq : hedgeXorPairBitsWithin G w.large child (fun root _incident => oldSupport root) =
              w.largeCarrierInterventionalIncidence rich target defect child := by
            rw [hedgeXorPairBitsWithin_pairBitsOf, hedgePairBitsOf_carrierSupportLatent]
            exact w.largeCarrierInterventionalPairBits_spec rich balance inside target defect child selected different
          have baseBit := hedgeForestParityOutput_bit_of_mem G rich w.large w.child child
            (fun parent _edge => (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention support parent)
            (fun root _incident => oldSupport root) selected
          change hedgeIsSecond rich child ((w.largeParityModel rich).mechanism child
            (fun parent _edge => (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention support parent)
            (fun root _incident => oldSupport root)) = _ at baseBit
          rw [baseBit, pairEq, parentsEq]
          unfold HedgeWitness.largeCarrierInterventionalIncidence hedgeForestRequiredIncidence
          by_cases equal : child = w.actionRoot <;> simp only [equal, if_true, if_false]
          all_goals
            generalize hedgeIsSecond rich child (target child) = output
            generalize hedgeForestParentBitsFrom rich w.child child (fun parent _edge => target parent) = parents
            cases output <;> cases parents <;> cases defect <;> rfl
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Assignment-level form of the same explicit interventional section. -/
theorem HedgeWitness.largeCarrierDefectParityModel_evalUnder_interventional_support
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (fixed : intervention balance ≠ none)
    (target : S.Assignment)
    (consistent : forall node value, intervention node = some value -> target node = value)
    (defect : Bool) :
    (w.largeCarrierDefectParityModel rich).evalUnder intervention
      (w.largeCarrierInterventionalSupportLatent rich balance inside target defect) = target := by
  funext child
  exact w.largeCarrierDefectParityModel_evalNodeUnder_interventional_support rich balance inside
    intervention fixed target consistent defect child

/-- Every consistent full-alphabet target has positive prior mass jointly
with either prescribed defect bit.  The positive singleton at the explicit
unit is contained in this joint event; no realization is chosen and no
factorization of the nonrectangular event is assumed. -/
theorem HedgeWitness.largeCarrierDefectParityModel_interventional_target_defect_positive
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (fixed : intervention balance ≠ none)
    (target : S.Assignment)
    (consistent : forall node value, intervention node = some value -> target node = value)
    (defect : Bool) :
    (w.largeCarrierDefectParityModel rich).prior.EventPositive (fun unit =>
      (hedgeDefectBitOf G unit == defect) &&
        FiniteProbRecord.singletonEvent target ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)) := by
  let support := w.largeCarrierInterventionalSupportLatent rich balance inside target defect
  have positive : (w.largeCarrierDefectParityModel rich).prior.EventPositive
      (FiniteProbRecord.singletonEvent support) := hedgeDefectPrior_singleton_mass_pos G support
  apply Nat.lt_of_lt_of_le positive
  apply FiniteProbRecord.eventMass_mono
  intro unit singleton
  have equal : unit = support := of_decide_eq_true singleton
  subst unit
  rw [w.largeCarrierInterventionalSupportLatent_defect rich balance inside target defect,
    w.largeCarrierDefectParityModel_evalUnder_interventional_support rich balance inside
      intervention fixed target consistent defect]
  simp only [beq_self_eq_true, FiniteProbRecord.singletonEvent, decide_true, Bool.and_self]

/-! ## An explicit interventional compensation for flipping the defect -/

/-- A fixed pair-root shift whose free incidence is one at the common
defect root and zero elsewhere.  The balancing vertex absorbs the remaining
parity.  If it is itself the root, its skipped equation absorbs everything. -/
def HedgeWitness.largeCarrierDefectCompensation
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (balance : Fin S.count) (inside : w.large balance = true) : Fin (pairRootCount G) -> Bool :=
  w.large_forest.component.partialTargetPairBits G w.large balance inside
    (fun node => decide (node = w.actionRoot))

theorem HedgeWitness.largeCarrierDefectCompensation_spec
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (balance : Fin S.count) (inside : w.large balance = true)
    (child : Fin S.count) (selected : w.large child = true) (different : child ≠ balance) :
    hedgeXorPairBitsWithinFrom G w.large child
      (w.largeCarrierDefectCompensation balance inside) = decide (child = w.actionRoot) := by
  let tested := NodeSet.diff w.large (NodeSet.singleton balance)
  have untested : tested balance = false := by simp [tested, NodeSet.diff, NodeSet.singleton]
  have selectedTest : tested child = true := by
    simpa only [tested, NodeSet.diff, NodeSet.singleton, decide_eq_false different,
      Bool.not_false, Bool.and_true] using selected
  exact w.large_forest.component.partialTargetPairBits_spec G w.large tested
    (NodeSet.diff_subset_left w.large (NodeSet.singleton balance)) balance inside untested
    (fun node => decide (node = w.actionRoot)) child selectedTest

private theorem privateDecode_of_coordinates (G : ObservedGraph S)
    (pairBits : Fin (pairRootCount G) -> Bool) (backgrounds : HedgePrivateCoordinates S)
    (child : Fin S.count) :
    hedgePrivateDecode S child (hedgePrivateIndex G child
      (fun root _incident => hedgeLatentOfCoordinates G pairBits backgrounds root)) =
      hedgePrivateDecode S child (backgrounds child) :=
  congrArg (hedgePrivateDecode S child)
    (congrFun (hedgePrivateCoordinatesOf_latentOfCoordinates G pairBits backgrounds) child)

/-- Expose the complete value equation at explicitly supplied latent
coordinates.  This private helper retains the background label so the
compensation proof below concerns full observed values, not just bits. -/
private theorem largeCarrierMechanism_of_coordinates
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count) (parents : S.ParentValues child)
    (pairBits : Fin (pairRootCount G) -> Bool) (backgrounds : HedgePrivateCoordinates S) (defect : Bool) :
    (w.largeCarrierDefectParityModel rich).mechanism child parents
        (fun root _incident => hedgeDefectAssignment G (hedgeLatentOfCoordinates G pairBits backgrounds) defect root) =
      hedgeParityCarrierValue rich child
        (Bool.xor
          (if w.large child then Bool.xor (hedgeXorPairBitsWithinFrom G w.large child pairBits)
            (hedgeForestParentBitsFrom rich w.child child parents)
          else hedgeIsSecond rich child (hedgePrivateDecode S child (backgrounds child)))
          (if child = w.actionRoot then defect else false))
        (hedgePrivateDecode S child (backgrounds child)) := by
  let old := hedgeLatentOfCoordinates G pairBits backgrounds
  have defectAt : hedgeIndependentDefectBit G w.actionRoot child
      (fun root _incident => hedgeDefectAssignment G old defect root) =
      if child = w.actionRoot then defect else false := by
    by_cases equal : child = w.actionRoot
    · subst child
      simpa using hedgeIndependentDefectBit_assignment_same G w.actionRoot old defect
    · simpa only [if_neg equal] using
        hedgeIndependentDefectBit_assignment_other G w.actionRoot child equal old defect
  simp only [HedgeWitness.largeCarrierDefectParityModel, hedgeCarrierDefectModel,
    hedgeDefectOldInputs_assignment]
  rw [privateDecode_of_coordinates G pairBits backgrounds child, defectAt]
  cases selected : w.large child with
  | false =>
      simp only [HedgeWitness.largeParityModel, hedgeForestParityModel, hedgeForestParityOutput,
        selected, Bool.false_eq_true, if_false, privateDecode_of_coordinates]
  | true =>
      have baseBit := hedgeForestParityOutput_bit_of_mem G rich w.large w.child child parents
        (fun root _incident => old root) selected
      change hedgeIsSecond rich child ((w.largeParityModel rich).mechanism child parents
        (fun root _incident => old root)) = _ at baseBit
      dsimp only [old] at baseBit
      have pairEq : hedgeXorPairBitsWithin G w.large child
          (fun root _incident => hedgeLatentOfCoordinates G pairBits backgrounds root) =
          hedgeXorPairBitsWithinFrom G w.large child pairBits := by
        rw [hedgeXorPairBitsWithin_pairBitsOf, hedgePairBitsOf_latentOfCoordinates]
      have bitEq := baseBit.trans (congrArg
        (fun incidence => Bool.xor incidence (hedgeForestParentBitsFrom rich w.child child parents)) pairEq)
      simpa only [if_true] using congrArg
        (fun bit => hedgeParityCarrierValue rich child
          (Bool.xor bit (if child = w.actionRoot then defect else false))
          (hedgePrivateDecode S child (backgrounds child))) bitEq

/-- Flipping the private defect and adding its fixed pair-root compensation
leaves every interventional observed value unchanged when `balance` is fixed.
The statement is pointwise in all old pair roots and all full-alphabet
background coordinates, not an equality assumed for their distributions.

At a free forest vertex the pair shift toggles exactly the same root bit
that the defect toggles, so the two changes cancel.  Intervened vertices skip
their equations; outside the forest the unchanged backgrounds are returned.
Topological recursion matches all earlier parents before comparing a child.
Both directions use the same pair shift, which is an explicit involution.
Connecting this to weighted priors is a separate probability step. -/
theorem HedgeWitness.largeCarrierDefectParityModel_evalNodeUnder_compensate_defect
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (fixed : intervention balance ≠ none)
    (pairBits : Fin (pairRootCount G) -> Bool) (backgrounds : HedgePrivateCoordinates S)
    (defect : Bool) (child : Fin S.count) :
    (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention
        (hedgeDefectAssignment G (hedgeLatentOfCoordinates G pairBits backgrounds) defect) child =
      (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention
        (hedgeDefectAssignment G (hedgeLatentOfCoordinates G
          (hedgePairBitsXor G pairBits (w.largeCarrierDefectCompensation balance inside)) backgrounds) (!defect)) child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases interventionAt : intervention child with
  | some value => rfl
  | none =>
      have parentsEqual :
          (fun parent (_edge : S.directed parent child = true) =>
            (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention
              (hedgeDefectAssignment G (hedgeLatentOfCoordinates G pairBits backgrounds) defect) parent) =
          (fun parent (_edge : S.directed parent child = true) =>
            (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention
              (hedgeDefectAssignment G (hedgeLatentOfCoordinates G
                (hedgePairBitsXor G pairBits (w.largeCarrierDefectCompensation balance inside)) backgrounds) (!defect)) parent) := by
        funext parent edge
        exact w.largeCarrierDefectParityModel_evalNodeUnder_compensate_defect rich balance inside
          intervention fixed pairBits backgrounds defect parent
      rw [parentsEqual, largeCarrierMechanism_of_coordinates, largeCarrierMechanism_of_coordinates]
      cases selected : w.large child with
      | false =>
          have different : child ≠ w.actionRoot := by
            intro equal
            subst child
            rw [w.actionRoot_in_large] at selected
            cases selected
          simp only [Bool.false_eq_true, if_false, if_neg different]
      | true =>
          have different : child ≠ balance := by
            intro equal
            subst child
            exact fixed interventionAt
          simp only [if_true]
          rw [hedgeXorPairBitsWithinFrom_xor,
            w.largeCarrierDefectCompensation_spec balance inside child selected different]
          congr 1
          generalize hedgeXorPairBitsWithinFrom G w.large child pairBits = incidence
          generalize hedgeForestParentBitsFrom rich w.child child _ = parents
          by_cases root : child = w.actionRoot <;> simp only [root, decide_true, decide_false, if_true, if_false]
          all_goals
            cases incidence <;> cases parents <;> cases defect <;> rfl
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Complete-assignment form of the explicit defect compensation. -/
theorem HedgeWitness.largeCarrierDefectParityModel_evalUnder_compensate_defect
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (fixed : intervention balance ≠ none)
    (pairBits : Fin (pairRootCount G) -> Bool) (backgrounds : HedgePrivateCoordinates S) (defect : Bool) :
    (w.largeCarrierDefectParityModel rich).evalUnder intervention
        (hedgeDefectAssignment G (hedgeLatentOfCoordinates G pairBits backgrounds) defect) =
      (w.largeCarrierDefectParityModel rich).evalUnder intervention
        (hedgeDefectAssignment G (hedgeLatentOfCoordinates G
          (hedgePairBitsXor G pairBits (w.largeCarrierDefectCompensation balance inside)) backgrounds) (!defect)) := by
  funext child
  exact w.largeCarrierDefectParityModel_evalNodeUnder_compensate_defect rich balance inside
    intervention fixed pairBits backgrounds defect child

/-! ## The original hedge action supplies the balancing vertex internally -/

private theorem doSecond_consistent (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (target : S.Assignment)
    (agrees : forall node, action node = true -> target node = rich.second node) :
    forall node value, hedgeDoSecond rich action node = some value -> target node = value := by
  intro node value selected
  cases actionAt : action node with
  | false =>
      rw [hedgeDoSecond_of_false rich action actionAt] at selected
      cases selected
  | true =>
      rw [hedgeDoSecond_of_true rich action actionAt] at selected
      exact (agrees node actionAt).trans (Option.some.inj selected)

/-- Fixed-defect support under the actual original hedge action.  The
witness's action seed is a large-forest vertex already fixed by that action,
so callers supply neither a balancing vertex nor a parity condition.
Composite actions and full observed alphabets are retained verbatim. -/
theorem HedgeWitness.largeCarrierDefectParityModel_doSecond_target_defect_positive
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment)
    (agrees : forall node, q.action node = true -> target node = rich.second node)
    (defect : Bool) :
    (w.largeCarrierDefectParityModel rich).prior.EventPositive (fun unit =>
      (hedgeDefectBitOf G unit == defect) && FiniteProbRecord.singletonEvent target
        ((w.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action) unit)) := by
  apply w.largeCarrierDefectParityModel_interventional_target_defect_positive rich
    w.actionSeed w.actionSeed_in_large (hedgeDoSecond rich q.action)
  · rw [hedgeDoSecond_of_true rich q.action w.actionSeed_in_action]
    exact Option.some_ne_none _
  · exact doSecond_consistent rich q.action target agrees

end Causality
end Thesis
