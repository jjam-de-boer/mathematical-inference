import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# Positive support for the kernel-generated derivation fragment

The positive ID/IDC compilers construct a symbolic derivation from a kernel.
Their certificate support fields are indexed by canonical graph-model classes,
but the underlying positivity argument needs neither canonical incidence nor
graph compatibility.  This module exposes that weaker boundary directly.

`ProbabilityTerm.ZeroFree` excludes the *literal zero constructor*, not zero
probabilities from the SCM layer.  Every derivation preserves this syntactic
property in both directions.  Consequently every term and every intermediate
subderivation reachable from a kernel has positive support in an observationally
positive finite SCM, including a root model with three or more children.

Support is built by finite syntax recursion.  No value is selected from a
propositional existence proof, and no semantic soundness theorem is imported
or used to establish support.  This is a positive-model bridge only: it must
not be used to discharge local support in models containing observational
zeros.  Their guarded and branch-specific support obligations remain explicit.
-/

namespace ProbabilityTerm

/-- The kernel-generated positive fragment.  This is a syntactic invariant,
not a claim that every kernel in an arbitrary model has positive value. -/
def ZeroFree : ProbabilityTerm S -> Prop
  | .zero => False
  | .kernel _ => True
  | .marginalize _ term => term.ZeroFree
  | .evaluateAt _ term => term.ZeroFree
  | .add left right => left.ZeroFree /\ right.ZeroFree
  | .multiply left right => left.ZeroFree /\ right.ZeroFree
  | .weightedMultiply weight factor => weight.ZeroFree /\ factor.ZeroFree
  | .divide numerator denominator => numerator.ZeroFree /\ denominator.ZeroFree

end ProbabilityTerm

/-- Every constructor preserves the kernel-generated fragment, including
symmetry and intermediate terms of transitivity.  The claim is purely
syntactic and holds for any choice of do-rule separation relation. -/
theorem DoCalculusDerivation.zeroFree_iff
    {G : ObservedGraph S} [RuleSeparation G]
    {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right) :
    left.ZeroFree <-> right.ZeroFree := by
  induction derivation with
  | refl => exact Iff.rfl
  | symm inner ih => exact ih.symm
  | trans first second firstIH secondIH => exact firstIH.trans secondIH
  | doRule => exact Iff.rfl
  | marginalization => exact Iff.rfl
  | conditioning => simp only [ProbabilityTerm.ZeroFree, true_and]
  | chain => simp only [ProbabilityTerm.ZeroFree, true_and]
  | weightedChain => simp only [ProbabilityTerm.ZeroFree, true_and]
  | multiplyComm => exact And.comm
  | multiplyAssoc => exact and_assoc
  | marginalizeCongr nodes inner ih => exact ih
  | evaluateAtCongr fixed inner ih => exact ih
  | addCongr first second firstIH secondIH => exact and_congr firstIH secondIH
  | multiplyCongr first second firstIH secondIH => exact and_congr firstIH secondIH
  | weightedMultiplyCongr first second firstIH secondIH => exact and_congr firstIH secondIH
  | divideCongr numerator denominator numeratorIH denominatorIH =>
      exact and_congr numeratorIH denominatorIH
  | eqCongr hleft hright inner ih => simpa only [hleft, hright] using ih

namespace ProbabilityResult

/-- Two positive supported summands have positive supported sum.  The
displayed value is constructed from the two retained rational values. -/
def PositiveSupportedValue.add {left right : Result}
    (leftPositive : PositiveSupportedValue left)
    (rightPositive : PositiveSupportedValue right) :
    PositiveSupportedValue (add left right) where
  value := QProb.add leftPositive.value rightPositive.value
  equivalent := add_congr leftPositive.equivalent rightPositive.equivalent
  positive := by
    have leading := Nat.mul_pos leftPositive.positive rightPositive.value.den_pos
    change 0 < leftPositive.value.num * rightPositive.value.den +
      rightPositive.value.num * leftPositive.value.den
    omega

end ProbabilityResult

namespace ProbabilityTerm

/-- Construct a positive rational support value for every term in the
kernel-generated fragment.  Kernel positivity uses SCM consistency, not
do-calculus or graph compatibility.  A marginal contains the reference
assignment itself, so its positive sum is never empty.

For a guarded product, both operands are positive here and the existing
agreement with strict multiplication applies.  This does not claim that
guarded products generally require positive factors at zero weights. -/
noncomputable def positiveSupportedValue_of_zeroFree
    (model : ExactModel S) (positive : ObservationallyPositive model)
    (term : ProbabilityTerm S) (zeroFree : term.ZeroFree)
    (assignment : S.Assignment) :
    ProbabilityResult.PositiveSupportedValue (term.denote model assignment) := by
  induction term generalizing assignment with
  | zero => exact False.elim zeroFree
  | kernel kernel => exact positive.kernelPositiveSupportedValue kernel assignment
  | marginalize nodes inner ih =>
      exact marginalizePositiveSupportedValue model nodes inner assignment
        (fun variant => ih zeroFree variant)
  | evaluateAt fixed inner ih => exact ih zeroFree fixed
  | add left right leftIH rightIH =>
      exact (leftIH zeroFree.1 assignment).add (rightIH zeroFree.2 assignment)
  | multiply left right leftIH rightIH =>
      exact (leftIH zeroFree.1 assignment).multiply (rightIH zeroFree.2 assignment)
  | weightedMultiply weight factor weightIH factorIH =>
      let weightPositive := weightIH zeroFree.1 assignment
      let factorPositive := factorIH zeroFree.2 assignment
      exact (weightPositive.multiply factorPositive).transport
        (ProbabilityResult.symm (ProbabilityResult.weightedMultiply_agrees
          weightPositive.toSupported factorPositive.toSupported))
  | divide numerator denominator numeratorIH denominatorIH =>
      exact (numeratorIH zeroFree.1 assignment).divide
        (denominatorIH zeroFree.2 assignment)

end ProbabilityTerm

/-- Build every recursive support obligation from positivity and the
source-side syntactic invariant.  Transitivity obtains the intermediate
invariant from the first derivation; congruence reads invariants of the
actual source operands.  Every listed marginal substitution is supported.

The guarded factor branch is a function of positive weight, as required by
the ordinary support tree.  Here its body can be built everywhere because
global positivity is an explicit premise, not because the guard is removed. -/
noncomputable def LocalDerivationSupport.ofObservationallyPositive
    {G : ObservedGraph S}
    (model : ExactModel S) (positive : ObservationallyPositive model)
    {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right)
    (zeroFree : left.ZeroFree) (assignment : S.Assignment) :
    LocalDerivationSupport model assignment derivation := by
  let supported (term : ProbabilityTerm S) (fragment : term.ZeroFree)
      (reference : S.Assignment) :=
    (term.positiveSupportedValue_of_zeroFree model positive fragment reference).toSupported
  induction derivation generalizing assignment with
  | refl term => exact ⟨supported term zeroFree assignment, supported term zeroFree assignment, ()⟩
  | symm inner ih =>
      have innerZeroFree := inner.zeroFree_iff.mpr zeroFree
      let innerSupport := ih innerZeroFree assignment
      exact ⟨innerSupport.2.1, innerSupport.1, innerSupport⟩
  | trans first second firstIH secondIH =>
      let firstSupport := firstIH zeroFree assignment
      let secondSupport := secondIH (first.zeroFree_iff.mp zeroFree) assignment
      exact ⟨firstSupport.1, secondSupport.2.1, firstSupport, secondSupport⟩
  | doRule application =>
      exact ⟨supported _ zeroFree assignment,
        supported _ trivial assignment, ()⟩
  | marginalization => exact ⟨supported _ zeroFree assignment, supported _ trivial assignment, ()⟩
  | conditioning => exact ⟨supported _ zeroFree assignment, supported _ ⟨trivial, trivial⟩ assignment, ()⟩
  | chain => exact ⟨supported _ zeroFree assignment, supported _ ⟨trivial, trivial⟩ assignment, ()⟩
  | weightedChain => exact ⟨supported _ zeroFree assignment, supported _ ⟨trivial, trivial⟩ assignment, ()⟩
  | multiplyComm first second =>
      exact ⟨supported _ zeroFree assignment, supported _ ⟨zeroFree.2, zeroFree.1⟩ assignment, ()⟩
  | multiplyAssoc first second third =>
      exact ⟨supported _ zeroFree assignment,
        supported _ ⟨zeroFree.1.1, zeroFree.1.2, zeroFree.2⟩ assignment, ()⟩
  | marginalizeCongr nodes inner ih =>
      exact ⟨supported _ zeroFree assignment,
        supported _ (inner.zeroFree_iff.mp zeroFree) assignment,
        fun variant _member => ih zeroFree variant⟩
  | evaluateAtCongr fixed inner ih =>
      exact ⟨supported _ zeroFree assignment,
        supported _ (inner.zeroFree_iff.mp zeroFree) assignment, ih zeroFree fixed⟩
  | addCongr first second firstIH secondIH =>
      exact ⟨supported _ zeroFree assignment,
        supported _ ⟨first.zeroFree_iff.mp zeroFree.1, second.zeroFree_iff.mp zeroFree.2⟩ assignment,
        firstIH zeroFree.1 assignment, secondIH zeroFree.2 assignment⟩
  | multiplyCongr first second firstIH secondIH =>
      exact ⟨supported _ zeroFree assignment,
        supported _ ⟨first.zeroFree_iff.mp zeroFree.1, second.zeroFree_iff.mp zeroFree.2⟩ assignment,
        firstIH zeroFree.1 assignment, secondIH zeroFree.2 assignment⟩
  | weightedMultiplyCongr first second firstIH secondIH =>
      exact ⟨supported _ zeroFree assignment,
        supported _ ⟨first.zeroFree_iff.mp zeroFree.1, second.zeroFree_iff.mp zeroFree.2⟩ assignment,
        firstIH zeroFree.1 assignment, fun _positiveWeight => secondIH zeroFree.2 assignment⟩
  | divideCongr numerator denominator numeratorIH denominatorIH =>
      exact ⟨supported _ zeroFree assignment,
        supported _ ⟨numerator.zeroFree_iff.mp zeroFree.1, denominator.zeroFree_iff.mp zeroFree.2⟩ assignment,
        numeratorIH zeroFree.1 assignment, denominatorIH zeroFree.2 assignment⟩
  | eqCongr hleft hright inner ih =>
      have innerZeroFree := hleft ▸ zeroFree
      let innerSupport := ih innerZeroFree assignment
      exact ⟨supported _ zeroFree assignment,
        supported _ (by rw [hright]; exact inner.zeroFree_iff.mp innerZeroFree) assignment,
        innerSupport⟩

end Causality
end Thesis
