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
      exact ⟨innerSupport.endpoints.2, innerSupport.endpoints.1, innerSupport⟩
  | trans first second firstIH secondIH =>
      let firstSupport := firstIH zeroFree assignment
      let secondSupport := secondIH (first.zeroFree_iff.mp zeroFree) assignment
      exact ⟨firstSupport.endpoints.1, secondSupport.endpoints.2, firstSupport, secondSupport⟩
  | @doRule left right application =>
      exact ⟨supported (.kernel left) zeroFree assignment,
        supported (.kernel right) trivial assignment, ()⟩
  | marginalization x y z w _disjoint =>
      exact ⟨supported (.kernel ⟨y, x, w⟩) zeroFree assignment,
        supported (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) trivial assignment, ()⟩
  | conditioning x y z w _disjoint =>
      exact ⟨supported (.kernel ⟨y, x, NodeSet.union z w⟩) zeroFree assignment,
        supported (.divide (.kernel ⟨NodeSet.union y z, x, w⟩) (.kernel ⟨z, x, w⟩))
          ⟨trivial, trivial⟩ assignment, ()⟩
  | chain x y z w _disjoint =>
      exact ⟨supported (.kernel ⟨NodeSet.union y z, x, w⟩) zeroFree assignment,
        supported (.multiply (.kernel ⟨y, x, NodeSet.union z w⟩) (.kernel ⟨z, x, w⟩))
          ⟨trivial, trivial⟩ assignment, ()⟩
  | weightedChain x y z w _disjoint =>
      exact ⟨supported (.kernel ⟨NodeSet.union y z, x, w⟩) zeroFree assignment,
        supported (.weightedMultiply (.kernel ⟨z, x, w⟩) (.kernel ⟨y, x, NodeSet.union z w⟩))
          ⟨trivial, trivial⟩ assignment, ()⟩
  | multiplyComm first second =>
      exact ⟨supported (.multiply first second) zeroFree assignment,
        supported (.multiply second first) ⟨zeroFree.2, zeroFree.1⟩ assignment, ()⟩
  | multiplyAssoc first second third =>
      exact ⟨supported (.multiply (.multiply first second) third) zeroFree assignment,
        supported (.multiply first (.multiply second third))
          ⟨zeroFree.1.1, zeroFree.1.2, zeroFree.2⟩ assignment, ()⟩
  | @marginalizeCongr nodes left right inner ih =>
      exact ⟨supported (.marginalize nodes left) zeroFree assignment,
        supported (.marginalize nodes right) (inner.zeroFree_iff.mp zeroFree) assignment,
        fun variant _member => ih zeroFree variant⟩
  | @evaluateAtCongr fixed left right inner ih =>
      exact ⟨supported (.evaluateAt fixed left) zeroFree assignment,
        supported (.evaluateAt fixed right) (inner.zeroFree_iff.mp zeroFree) assignment, ih zeroFree fixed⟩
  | @addCongr left left' right right' first second firstIH secondIH =>
      exact ⟨supported (.add left right) zeroFree assignment,
        supported (.add left' right')
          ⟨first.zeroFree_iff.mp zeroFree.1, second.zeroFree_iff.mp zeroFree.2⟩ assignment,
        firstIH zeroFree.1 assignment, secondIH zeroFree.2 assignment⟩
  | @multiplyCongr left left' right right' first second firstIH secondIH =>
      exact ⟨supported (.multiply left right) zeroFree assignment,
        supported (.multiply left' right')
          ⟨first.zeroFree_iff.mp zeroFree.1, second.zeroFree_iff.mp zeroFree.2⟩ assignment,
        firstIH zeroFree.1 assignment, secondIH zeroFree.2 assignment⟩
  | @weightedMultiplyCongr weight weight' factor factor' first second firstIH secondIH =>
      exact ⟨supported (.weightedMultiply weight factor) zeroFree assignment,
        supported (.weightedMultiply weight' factor')
          ⟨first.zeroFree_iff.mp zeroFree.1, second.zeroFree_iff.mp zeroFree.2⟩ assignment,
        firstIH zeroFree.1 assignment, fun _positiveWeight => secondIH zeroFree.2 assignment⟩
  | @divideCongr left left' right right' numerator denominator numeratorIH denominatorIH =>
      exact ⟨supported (.divide left right) zeroFree assignment,
        supported (.divide left' right')
          ⟨numerator.zeroFree_iff.mp zeroFree.1, denominator.zeroFree_iff.mp zeroFree.2⟩ assignment,
        numeratorIH zeroFree.1 assignment, denominatorIH zeroFree.2 assignment⟩
  | @eqCongr left left' right right' hleft hright inner ih =>
      have innerZeroFree := hleft ▸ zeroFree
      let innerSupport := ih innerZeroFree assignment
      exact ⟨supported left zeroFree assignment,
        supported right (by rw [hright]; exact inner.zeroFree_iff.mp innerZeroFree) assignment,
        innerSupport⟩

end Causality
end Thesis
