import Thesis.Probability.FiniteGrandThermodynamicIdentification

namespace Thesis.Examples.UniformEntropyPaths
open Probability ConstructiveReal

private def half : SignedRatio := ⟨1, 2, by decide⟩
private def quarter : SignedRatio := ⟨1, 4, by decide⟩
private def floor : PositiveRatio := ⟨1, 4, by decide, by decide⟩
private def masses (_ : Fin 2) : ConstructiveReal := ofSignedRatio half
private def directions (i : Fin 2) : ConstructiveReal :=
  if i = 0 then ofSignedRatio quarter else neg (ofSignedRatio quarter)
private def floors (_ : Fin 2) := floor
private theorem initial (i : Fin 2) : entropyPositiveDomain (floors i) (masses i) := by
  change entropyPositiveDomain floor (ofSignedRatio half)
  exact ⟨(ofSignedRatio_le_iff _ _).mpr (by decide +kernel), (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)⟩
private def atZero := entropyLineDomain_zero masses directions floors initial

/-- The same computed uniform certificate covers the symmetric affine
binary line, including the uniform midpoint. Its actual entropy derivative
there is zero because the signed velocities cancel. -/
example : HasDerivativeWithinAt (entropyLineDomain masses directions floors)
    (entropyLine masses directions floors) zero atZero zero := by
  let gradient := entropyBitGradient (ofSignedRatio half) floor (initial 0).1
  have same (i : Fin 2) : Equiv
      (entropyBitGradient (affineCoordinate (masses i) (directions i) zero) (floors i) (atZero i).1) gradient :=
    neg_congr (add_congr (positiveLog2_congr (affineCoordinate_zero _ _) _ _ (atZero i).1 (initial 0).1) (equiv_refl _))
  have collected : Equiv (listSum ((List.finRange 2).map (fun i => mul (directions i) gradient))) zero := by
    change Equiv (add (mul (ofSignedRatio quarter) gradient)
      (add (mul (neg (ofSignedRatio quarter)) gradient) zero)) zero
    exact equiv_trans (add_congr (equiv_refl _) (equiv_trans (add_zero _) (neg_mul _ _))) (add_neg _)
  exact ((entropyLine_uniformDerivative masses directions floors).atPoint zero atZero).slope_congr
    (equiv_trans (listSum_map_congr (List.finRange 2) _ _ (fun i _ => mul_congr (equiv_refl _) (same i))) collected)

private def two : ConstructiveReal := ofSignedRatio ⟨2, 1, by decide⟩
private def seven : ConstructiveReal := ofSignedRatio ⟨7, 1, by decide⟩
private def unitDomain (t : ConstructiveReal) : Prop := LE zero t ∧ LE t one
private theorem zero_le_one : LE zero one := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
private theorem unitWidth : LE (sub one zero) one :=
  (le_congr (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _)) (equiv_refl _)).mpr (le_refl one)

/-- Negative affine factors are admitted by the uniform chain certificate.
This checks a real composition, not a substituted formal derivative. -/
example : UniformDerivativeWithin unitDomain
    (fun t _ => mul (add (mul t (neg two)) one) (add (mul t (neg two)) one))
    (fun t _ => mul (neg two) (add (add (mul t (neg two)) one) (add (mul t (neg two)) one))) :=
  (square_uniformDerivative (fun _ => True)).affine_pullback (neg two) one (fun _ _ => True.intro)

/-- An independently supplied potential with derivative 2t and initial
value seven must take value eight at one. It is not defined to be t²+7;
the conclusion follows from the variation certificate and reference value. -/
example (potential : ∀ t, unitDomain t → ConstructiveReal)
    (derivative : UniformDerivativeWithin unitDomain potential (fun t _ => add t t))
    (reference : Equiv (potential zero ⟨le_refl zero, zero_le_one⟩) seven) :
    Equiv (potential one ⟨zero_le_one, le_refl one⟩) (ofSignedRatio ⟨8, 1, by decide⟩) := by
  have referenceValue : Equiv (add (mul zero zero) seven) seven :=
    equiv_trans (add_congr (zero_mul zero) (equiv_refl seven)) (zero_add seven)
  have agreement := derivative.agreement_of_reference (square_uniformDerivative unitDomain) (fun _ _ => equiv_refl _)
    zero one seven zero_le_one unitWidth (fun _ lower upper => ⟨lower, upper⟩)
    (equiv_trans reference (equiv_symm referenceValue))
  exact equiv_trans agreement (equiv_trans (add_congr (one_mul one) (equiv_refl seven))
    (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))


/-- The comparison also works across a parameter interval of length two;
the uniform certificate is transported to the unit interval rather than
assuming the old auxiliary width restriction. -/
example (potential : ∀ t : ConstructiveReal, True → ConstructiveReal)
    (derivative : UniformDerivativeWithin (fun _ => True) potential (fun t _ => add t t))
    (reference : Equiv (potential zero True.intro) seven) :
    Equiv (potential two True.intro) (ofSignedRatio ⟨11, 1, by decide⟩) := by
  have ordered : LE zero two := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  have referenceValue : Equiv (add (mul zero zero) seven) seven :=
    equiv_trans (add_congr (zero_mul zero) (equiv_refl seven)) (zero_add seven)
  have agreement := derivative.agreement_of_reference_on_interval
    (square_uniformDerivative (fun _ => True)) (fun _ _ => equiv_refl _)
    zero two seven ordered (fun _ _ _ => True.intro)
    (equiv_trans reference (equiv_symm referenceValue))
  exact equiv_trans agreement (equiv_trans (add_congr (ofSignedRatio_mul _ _) (equiv_refl seven))
    (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))

end Thesis.Examples.UniformEntropyPaths
