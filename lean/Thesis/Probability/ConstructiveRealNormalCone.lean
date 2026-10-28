import Thesis.Probability.ConstructiveRealDualDirections

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear
open IntegerLinearAlgebra

/-- The full variational normal-cone condition on a finite simplex with
fixed integral rows. Every feasible analytic competitor is included;
nonnegativity and normalization imply each coordinate is at most one. -/
def SimplexVariational (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (masses gradient : Fin columns → ConstructiveReal) : Prop :=
  ∀ values : Fin columns → ConstructiveReal,
    (∀ i, LE zero (values i)) →
    Equiv (realDot columns (fun _ => 1) values) one →
    (∀ r, LE (realDot columns (matrix r) values) (realInteger (bounds r))) →
    LE (FiniteLinear.pair columns (fun i => sub (values i) (masses i)) gradient) zero

/-- A canceled dual combination has nonnegative analytic bound at a
quantitatively positive variational maximum. The proof constructs a
positive rational step, keeps all original constraints exactly, and
cancels that step in the variational inequality. No active-row test,
rank hypothesis, Slater condition or separation oracle is supplied. -/
theorem signature_nonnegative_of_variational (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (masses gradient : Fin columns → ConstructiveReal)
    (lower : Fin columns → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (masses i))
    (normalized : Equiv (realDot columns (fun _ => 1) masses) one)
    (valid : ∀ r, LE (realDot columns (matrix r) masses) (realInteger (bounds r)))
    (variational : SimplexVariational matrix bounds masses gradient)
    (signature : DualSignature rows columns)
    (normalCancellation : dot signature.direction (fun _ => 1) + signature.total = 0)
    (rowCancellation : ∀ r, dot signature.direction (matrix r) + signature.total * bounds r = (signature.cone r : Int)) :
    LE zero (signature.row matrix bounds gradient (FiniteLinear.pair columns masses gradient)).bound := by
  let directions := signature.perturbation masses
  let derivative := HasDerivativeAt.affine zero (neg (realInteger signature.total)) one
  let radii := [affinePositiveRadius masses directions lower, derivative.positiveRadius PositiveRatio.one]
  let radius := finitePositiveRadius radii
  let parameter := ofSignedRatio radius.toSignedRatio
  let values := fun i => affineCoordinate (masses i) (directions i) parameter
  let rhs := (signature.row matrix bounds gradient (FiniteLinear.pair columns masses gradient)).bound
  have close : Within radius.toQProb zero parameter :=
    (within_congr (equiv_refl _) (zero_add parameter)).mp (within_positive_shift zero radius)
  have coordinateRadius := finitePositiveRadius_le radii (affinePositiveRadius masses directions lower)
    (List.mem_cons_self ..)
  have scalarRadius := finitePositiveRadius_le radii (derivative.positiveRadius PositiveRatio.one)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have positiveNear := affineCoordinate_positive_near masses directions lower positive parameter (within_mono close coordinateRadius)
  have valuesNonnegative (i : Fin columns) : LE zero (values i) :=
    le_trans ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr (lower i).half.signed_nonnegative))
      (positiveNear i)
  have scalarFloor := derivative.positive_near PositiveRatio.one
    ((le_congr (equiv_refl _) (affineCoordinate_zero one (neg (realInteger signature.total)))).mpr (le_refl one))
    parameter (within_mono close scalarRadius)
  have scalarSame : Equiv (affineCoordinate one (neg (realInteger signature.total)) parameter)
      (sub one (mul parameter (realInteger signature.total))) :=
    equiv_trans (add_congr (mul_neg _ _) (equiv_refl one)) (add_comm _ _)
  have scalarNonnegative : LE zero (sub one (mul parameter (realInteger signature.total))) :=
    (le_congr (equiv_refl _) scalarSame).mp (le_trans
      ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr PositiveRatio.one.half.signed_nonnegative)) scalarFloor)
  have parameterNonnegative : LE zero parameter :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr radius.signed_nonnegative)
  have directionsNormalized := signature.perturbation_normalized masses normalized normalCancellation
  have valuesNormalized : Equiv (realDot columns (fun _ => 1) values) one :=
    equiv_trans (realDot_affineCoordinate_fixed columns (fun _ => 1) masses directions directionsNormalized parameter) normalized
  have valuesValid (r : Fin rows) : LE (realDot columns (matrix r) values) (realInteger (bounds r)) := by
    have slackNonnegative := (zero_le_sub_iff _ _).mpr (valid r)
    have coneNonnegative : LE zero (realInteger (signature.cone r : Int)) :=
      (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr (Int.natCast_nonneg _))
    have sumNonnegative := (le_congr (zero_add zero) (equiv_refl _)).mp
      (add_le_add (mul_nonnegative scalarNonnegative slackNonnegative) (mul_nonnegative parameterNonnegative coneNonnegative))
    exact (zero_le_sub_iff _ _).mp ((le_congr (equiv_refl _)
      (equiv_symm (signature.perturbation_slack matrix bounds masses parameter rowCancellation r))).mp sumNonnegative)
  have compared := variational values valuesNonnegative valuesNormalized valuesValid
  have delta (i : Fin columns) : Equiv (sub (values i) (masses i)) (mul parameter (directions i)) :=
    equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg (masses i))) (add_zero _))
  have slope : Equiv (FiniteLinear.pair columns (fun i => sub (values i) (masses i)) gradient)
      (mul parameter (neg rhs)) :=
    equiv_trans (FiniteLinear.pair_congr columns _ _ gradient gradient delta (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.pair_scale_first columns parameter directions gradient)
        (mul_congr (equiv_refl _) (signature.perturbation_pair matrix bounds masses gradient)))
  have scaled := (le_congr slope (equiv_symm (mul_zero parameter))).mp compared
  have negative := (mul_le_mul_positive_iff parameter radius (le_refl _) (neg rhs) zero).mp scaled
  exact (le_congr (equiv_refl _) (zero_add rhs)).mp ((neg_le_iff_nonnegative_add rhs zero).mp negative)

/-- The variational inequality proves the actual Farkas condition for any
finite multiplier-row list rendered from signatures. All witnesses are
computed from finite data by the previously proved solver. -/
theorem farkas_of_variational (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (masses gradient : Fin columns → ConstructiveReal)
    (lower : Fin columns → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (masses i))
    (normalized : Equiv (realDot columns (fun _ => 1) masses) one)
    (valid : ∀ r, LE (realDot columns (matrix r) masses) (realInteger (bounds r)))
    (variational : SimplexVariational matrix bounds masses gradient)
    (signatures : List (DualSignature rows columns)) :
    FarkasCondition (dualRows matrix bounds gradient (FiniteLinear.pair columns masses gradient) signatures) :=
  farkas_of_signature_nonnegative matrix bounds gradient (FiniteLinear.pair columns masses gradient) signatures
    (signature_nonnegative_of_variational matrix bounds masses gradient lower positive normalized valid variational)

end Thesis.Probability.AnalyticLinear
