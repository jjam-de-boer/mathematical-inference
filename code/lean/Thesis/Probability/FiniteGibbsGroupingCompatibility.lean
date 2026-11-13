import Thesis.Probability.FiniteGibbsDegeneracy

namespace Thesis.Probability.FiniteGibbsGrouping
open ConstructiveReal
open ConstructiveReal.FiniteFibers
open Distros.RationalLinear

/-- A previously defined microstate family has unit reference weights and
agrees in rational value with the supplied grouped observables. Unreduced
rational presentations are allowed. These are checked physical compatibility
conditions, not assumptions of partition or probability agreement. -/
structure Compatible (grouping : FiniteGibbsGrouping micro groups features)
    (original : FiniteGibbsFamily micro features) : Prop where
  reference : ∀ i, SignedRatio.Equiv (original.reference i).toSignedRatio SignedRatio.one
  response : ∀ k i, SignedRatio.Equiv (original.response k i) (grouping.response k (grouping.states.label i))

theorem Compatible.score {grouping : FiniteGibbsGrouping micro groups features} {original : FiniteGibbsFamily micro features}
    (compatible : grouping.Compatible original) (parameters : Fin features → ConstructiveReal) (i : Fin micro) :
    Equiv (original.score parameters i) (grouping.microFamily.score parameters i) :=
  equiv_trans (realRationalDot_pair features (fun k => original.response k i) parameters)
    (equiv_trans (FiniteLinear.pair_congr features _ _ parameters parameters
      (fun k => (ofSignedRatio_equiv_iff _ _).mpr (compatible.response k i)) (fun _ => equiv_refl _))
      (equiv_symm (realRationalDot_pair features _ parameters)))

theorem Compatible.logWeight {grouping : FiniteGibbsGrouping micro groups features} {original : FiniteGibbsFamily micro features}
    (compatible : grouping.Compatible original) (parameters : Fin features → ConstructiveReal) (i : Fin micro) :
    Equiv ((original.asTilt parameters).logWeight one i) ((grouping.microFamily.asTilt parameters).logWeight one i) := by
  have referenceZero : Equiv (original.logReference i) zero :=
    equiv_trans (positiveLn_congr ((ofSignedRatio_equiv_iff _ _).mpr (compatible.reference i))
      (original.reference i) PositiveRatio.one (le_refl _) (le_refl one))
      (positiveLn_one PositiveRatio.one (le_refl one))
  exact add_congr (mul_congr (equiv_refl _) (neg_congr (compatible.score parameters i)))
    (equiv_trans referenceZero (equiv_symm (positiveLn_one PositiveRatio.one (le_refl one))))

/-- Transfer to a preexisting family preserves the actual partition. -/
theorem Compatible.partition_eq {grouping : FiniteGibbsGrouping micro groups features} {original : FiniteGibbsFamily micro features}
    (compatible : grouping.Compatible original) (parameters : Fin features → ConstructiveReal) :
    Equiv (original.partition parameters) (grouping.macroFamily.partition parameters) :=
  equiv_trans (FiniteGibbsTilt.partition_congr (compatible.logWeight parameters)) (grouping.partition_eq parameters)

/-- The probability aggregation theorem applies to the original physical
family, after checking only its reference weights and observables. -/
theorem Compatible.mass_aggregated {grouping : FiniteGibbsGrouping micro groups features} {original : FiniteGibbsFamily micro features}
    (compatible : grouping.Compatible original) (parameters : Fin features → ConstructiveReal) (j : Fin groups) :
    Equiv (sumFiber grouping.states.label (original.mass parameters) j) (grouping.macroFamily.mass parameters j) :=
  equiv_trans (sumFiber_congr grouping.states.label j (original.mass parameters) (grouping.microFamily.mass parameters)
    (fun i _ => FiniteGibbsTilt.mass_congr (compatible.logWeight parameters) i)) (grouping.mass_aggregated parameters j)

/-- Corrected Shannon entropy of a preexisting microstate family agrees
with the counted macrostate description. The correction is in bits. -/
theorem Compatible.entropy_correction {grouping : FiniteGibbsGrouping micro groups features} {original : FiniteGibbsFamily micro features}
    (compatible : grouping.Compatible original) (parameters : Fin features → ConstructiveReal) :
    Equiv (original.entropy parameters)
      (add (grouping.macroFamily.entropy parameters) (grouping.macroFamily.expectation parameters grouping.logDegeneracy)) :=
  equiv_trans (FiniteGibbsTilt.entropy_congr (compatible.logWeight parameters)) (grouping.entropy_bits_correction parameters)

end Thesis.Probability.FiniteGibbsGrouping
