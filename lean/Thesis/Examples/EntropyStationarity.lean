import Thesis.Probability.ConstructiveRealEntropyStationarity

namespace Thesis.Examples.EntropyStationarity
open Probability Probability.Distros ConstructiveReal

/-- Fermat's conclusion is obtained from a genuine nonconstant local
maximum, even when the supplied derivative has an arbitrary slope value. -/
example (slope : ConstructiveReal)
    (derivative : HasDerivativeAt (fun x => neg (mul x x)) zero slope) : Equiv slope zero := by
  apply (derivative.restrict (fun _ => True) True.intro).slope_zero_of_local_maximum PositiveRatio.one
    (fun _ _ => True.intro)
  intro nearby _ _
  have upper := (neg_le_neg_iff zero (mul nearby nearby)).mpr (square_nonnegative nearby)
  exact (le_congr (equiv_refl _) (equiv_symm (neg_congr (mul_zero zero)))).mp upper

/-- A one-sided boundary maximum does have a nonzero derivative. This
prevents dropping the two-sided-neighborhood hypothesis from Fermat. -/
private def boundaryDerivative :
    HasDerivativeWithinAt (fun x => LE zero x) (fun x _ => neg x) zero (le_refl zero) (neg one) :=
  (HasDerivativeAt.identity zero).neg.restrict (fun x => LE zero x) (le_refl zero)

example (nearby : ConstructiveReal) (admitted : LE zero nearby) : LE (neg nearby) (neg zero) :=
  (neg_le_neg_iff zero nearby).mpr admitted

example : ¬ Equiv (neg one) zero := by
  intro same
  have rational := (ofSignedRatio_equiv_iff (SignedRatio.neg SignedRatio.one) SignedRatio.zero).mp
    (equiv_trans (ofSignedRatio_neg SignedRatio.one) same)
  exact (by decide +kernel : ¬ SignedRatio.Equiv (SignedRatio.neg SignedRatio.one) SignedRatio.zero) rational

private def half : ConstructiveReal := ofSignedRatio ⟨1, 2, by decide⟩
private def lower : PositiveRatio := ⟨1, 4, by decide, by decide⟩
private def direction (index : Fin 2) : ConstructiveReal := if index = 0 then one else neg one
private theorem half_inside : entropyPositiveDomain lower half :=
  ⟨(ofSignedRatio_le_iff _ _).mpr (by decide +kernel), (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)⟩

private theorem cancel_opposite (gradient : ConstructiveReal) :
    Equiv (add (mul one gradient) (add (mul (neg one) gradient) zero)) zero :=
  equiv_trans (add_congr (one_mul gradient)
    (equiv_trans (add_congr (equiv_trans (neg_mul one gradient) (neg_congr (one_mul gradient))) (equiv_refl _)) (add_zero _)))
    (add_neg gradient)

/-- Along the normalized two-state tangent (1,-1), the fair law has zero
first variation. The derivative still carries a computed error modulus. -/
example : HasDerivativeWithinAt (entropyLineDomain (fun _ : Fin 2 => half) direction (fun _ => lower))
    (entropyLine (fun _ : Fin 2 => half) direction (fun _ => lower)) zero
    (entropyLineDomain_zero _ _ _ (fun _ => half_inside)) zero := by
  apply (entropyLine_hasDerivativeWithinAt (fun _ : Fin 2 => half) direction (fun _ => lower) (fun _ => half_inside)).slope_congr
  change Equiv (add (mul one (entropyBitGradient half lower half_inside.1))
    (add (mul (neg one) (entropyBitGradient half lower half_inside.1)) zero)) zero
  exact cancel_opposite _

/-- Natural units give the same zero variation at the fair law. -/
example : HasDerivativeWithinAt (entropyLineDomain (fun _ : Fin 2 => half) direction (fun _ => lower))
    (fun parameter supplied => mul (entropyLine (fun _ : Fin 2 => half) direction (fun _ => lower) parameter supplied) lnTwo) zero
    (entropyLineDomain_zero _ _ _ (fun _ => half_inside)) zero := by
  apply (naturalEntropyLine_hasDerivativeWithinAt (fun _ : Fin 2 => half) direction (fun _ => lower) (fun _ => half_inside)).slope_congr
  change Equiv (add (mul one (entropyNaturalGradient half lower half_inside.1))
    (add (mul (neg one) (entropyNaturalGradient half lower half_inside.1)) zero)) zero
  exact cancel_opposite _

open RationalLinear
private def repeated : RationalConstraint 2 := ⟨fun _ => ⟨2, 6, by decide⟩, ⟨1, 3, by decide⟩⟩
private def problem : RationalEntropyProblem 2 := ⟨by decide, [repeated, repeated]⟩
private def signedDirection (index : Fin 2) : SignedRatio := if index = 0 then SignedRatio.one else SignedRatio.neg SignedRatio.one
private def rationalDirection (index : Fin 2) : ConstructiveReal := ofSignedRatio (signedDirection index)

private theorem rational_tangent : problem.ConstraintKernel rationalDirection := by
  refine ⟨equiv_trans (realDot_ofSignedRatio 2 (fun _ => 1) signedDirection)
    ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)), ?_⟩
  have rational : ∀ row ∈ problem.rows, SignedRatio.Equiv (dot 2 row.clear.coefficients signedDirection) SignedRatio.zero := by decide +kernel
  intro row member
  exact equiv_trans (realDot_ofSignedRatio 2 row.clear.coefficients signedDirection)
    ((ofSignedRatio_equiv_iff _ _).mpr (rational row member))

/-- Redundant unreduced rational rows do not obstruct the kernel theorem.
Positivity of the maximizing law is an explicit hypothesis here. -/
example (law : problem.RealLaw) (maximal : law.Maximal) (bounds : Fin 2 → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (bounds i).toSignedRatio) (law.mass i).value) :
    Equiv (listSum ((List.finRange 2).map (fun i =>
      mul (rationalDirection i) (entropyBitGradient (law.mass i).value (bounds i) (positive i))))) zero :=
  law.maximum_stationary maximal bounds positive rationalDirection rational_tangent

example (law : problem.RealLaw) (maximal : law.Maximal) (bounds : Fin 2 → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (bounds i).toSignedRatio) (law.mass i).value) :
    Equiv (listSum ((List.finRange 2).map (fun i =>
      mul (rationalDirection i) (entropyNaturalGradient (law.mass i).value (bounds i) (positive i))))) zero :=
  law.maximum_stationary_natural maximal bounds positive rationalDirection rational_tangent

/-- The constructed path satisfies the original rows and normalization at
any admitted positive or negative parameter, rather than only at zero. -/
example (law : problem.RealLaw) (bounds : Fin 2 → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (bounds i).toSignedRatio) (law.mass i).value)
    (parameter : ConstructiveReal)
    (close : Within (affinePositiveRadius (fun i => (law.mass i).value) rationalDirection bounds).toQProb zero parameter) :
    ∀ row ∈ problem.rows, row.RealHolds (fun i =>
      ((law.tangentLine rationalDirection rational_tangent bounds positive parameter close).mass i).value) :=
  (law.tangentLine rationalDirection rational_tangent bounds positive parameter close).valid

/-- A singleton normalized law sits at the upper endpoint p=1. Its zero
tangent still has a two-sided admitted neighborhood; no strict upper bound
is needed for the general simplex construction. -/
example (parameter : ConstructiveReal)
    (close : Within (affinePositiveRadius (fun _ : Fin 1 => one) (fun _ => zero) (fun _ => PositiveRatio.one)).toQProb zero parameter) :
    entropyLineDomain (fun _ : Fin 1 => one) (fun _ => zero) (fun _ => PositiveRatio.one.half) parameter := by
  apply affine_simplex_positive_near (fun _ : Fin 1 => one) (fun _ => zero) (fun _ => PositiveRatio.one) (fun _ => le_refl _) _ _ parameter close
  · exact equiv_trans (realDot_ofSignedRatio 1 (fun _ => 1) (fun _ => SignedRatio.one))
      ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))
  · exact equiv_trans (realDot_ofSignedRatio 1 (fun _ => 1) (fun _ => SignedRatio.zero))
      ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))

end Thesis.Examples.EntropyStationarity
