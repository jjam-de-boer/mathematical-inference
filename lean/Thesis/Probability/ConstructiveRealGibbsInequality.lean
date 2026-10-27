import Thesis.Probability.ConstructiveRealEntropySupporting
import Thesis.Probability.ConstructiveRealEntropyVectorConcavity
import Thesis.Probability.ConstructiveRealRelativeEntropy
import Thesis.Probability.ConstructiveRealFiniteLinear

namespace Thesis.Probability.ConstructiveReal

private theorem sum_map_neg (indices : List ι) (values : ι → ConstructiveReal) :
    Equiv (listSum (indices.map (fun i => neg (values i)))) (neg (listSum (indices.map values))) := by
  induction indices with
  | nil => exact ofSignedRatio_neg SignedRatio.zero
  | cons i rest ih => exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (neg_add _ _))

private theorem sum_map_sub (indices : List ι) (first second : ι → ConstructiveReal) :
    Equiv (listSum (indices.map (fun i => sub (first i) (second i))))
      (sub (listSum (indices.map first)) (listSum (indices.map second))) :=
  equiv_trans (listSum_map_add indices first (fun i => neg (second i))) (add_congr (equiv_refl _) (sum_map_neg indices second))

/-- Analytic cross entropy against a reference with supplied positive
coordinate floors. No observed-coordinate logarithm is required. -/
def realCrossEntropySum (observed reference : Fin variables → UnitIntervalValue) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) : ConstructiveReal :=
  listSum ((List.finRange variables).map (fun i => neg (mul (observed i).value ((reference i).value.positiveLog2 (lower i) (positive i)))))

def realRelativeEntropySum (observed reference : Fin variables → UnitIntervalValue) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) : ConstructiveReal :=
  listSum ((List.finRange variables).map (fun i => (observed i).value.realRelativeEntropyTerm
    (observed i).nonnegative (observed i).bounded (reference i).value (lower i) (positive i)))

theorem realRelativeEntropySum_decomposition (observed reference : Fin variables → UnitIntervalValue)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    Equiv (realRelativeEntropySum observed reference lower positive)
      (sub (realCrossEntropySum observed reference lower positive) (realEntropySum ((List.finRange variables).map observed))) := by
  simpa only [realRelativeEntropySum, realRelativeEntropyTerm, realCrossEntropySum, realEntropySum, UnitIntervalValue.entropy, List.map_map] using
    sum_map_sub (List.finRange variables)
      (fun i => neg (mul (observed i).value ((reference i).value.positiveLog2 (lower i) (positive i))))
      (fun i => (observed i).entropy)

private abbrev Expr := RationalPolynomial.Expression 4
private def x : Expr := .coordinate 0
private def y : Expr := .coordinate 1
private def logarithm : Expr := .coordinate 2
private def coefficient : Expr := .coordinate 3
private def negate (value : Expr) : Expr := .sub (.constant SignedRatio.zero) value
private def tangentExpr : Expr := .add (negate (.mul y logarithm)) (.mul (.sub x y) (negate (.add logarithm coefficient)))
private def crossExpr : Expr := .add (negate (.mul x logarithm)) (.mul coefficient (.sub y x))

private theorem cross_tangent_identity (xv yv logv cv : ConstructiveReal) :
    Equiv (add (neg (mul yv logv)) (mul (sub xv yv) (neg (add logv cv))))
      (add (neg (mul xv logv)) (mul cv (sub yv xv))) :=
  by
    have raw : Equiv (add (sub zero (mul yv logv)) (mul (sub xv yv) (sub zero (add logv cv))))
        (add (sub zero (mul xv logv)) (mul cv (sub yv xv))) :=
      RationalPolynomial.Expression.equalityCheck_sound_real tangentExpr crossExpr (by decide +kernel)
        (fun i => if i.val = 0 then xv else if i.val = 1 then yv else if i.val = 2 then logv else cv)
    exact equiv_trans (equiv_symm (add_congr (zero_add _) (mul_congr (equiv_refl _) (zero_add _))))
      (equiv_trans raw (add_congr (zero_add _) (equiv_refl _)))

/-- Exact scalar cross-entropy decomposition of the tangent expression. -/
theorem UnitIntervalValue.entropy_tangent_cross (observed reference : UnitIntervalValue) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) reference.value) :
    Equiv (add reference.entropy (mul (sub observed.value reference.value) (entropyBitGradient reference.value lower positive)))
      (add (neg (mul observed.value (reference.value.positiveLog2 lower positive)))
        (mul RationalLogSecant.limit (sub reference.value observed.value))) :=
  equiv_trans (add_congr (reference.value.realEntropyTerm_formula reference.nonnegative reference.bounded lower positive) (equiv_refl _))
    (cross_tangent_identity _ _ _ _)

/-- The scalar tangent inequality in cross-entropy form. The correction is
exactly the derivative coefficient times the difference in total mass. -/
theorem UnitIntervalValue.entropy_cross_supporting (observed reference : UnitIntervalValue) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) reference.value) :
    LE observed.entropy (add (neg (mul observed.value (reference.value.positiveLog2 lower positive)))
      (mul RationalLogSecant.limit (sub reference.value observed.value))) :=
  (le_congr (equiv_refl _) (observed.entropy_tangent_cross reference lower positive)).mp (observed.entropy_supporting reference lower positive)

/-- Summed entropy support, before normalization or moment constraints are
imposed. Zero observed coordinates remain admitted. -/
theorem realEntropySum_supporting (observed reference : Fin variables → UnitIntervalValue) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    LE (realEntropySum ((List.finRange variables).map observed))
      (add (realEntropySum ((List.finRange variables).map reference))
        (FiniteLinear.pair variables (fun i => sub (observed i).value (reference i).value)
          (fun i => entropyBitGradient (reference i).value (lower i) (positive i)))) := by
  have terms := listSum_map_mono (List.finRange variables) (fun i => (observed i).entropy)
    (fun i => add (reference i).entropy (mul (sub (observed i).value (reference i).value)
      (entropyBitGradient (reference i).value (lower i) (positive i))))
    (fun i _ => (observed i).entropy_supporting (reference i) (lower i) (positive i))
  simpa only [realEntropySum, List.map_map] using
    (le_congr (equiv_refl _) (listSum_map_add (List.finRange variables) (fun i => (reference i).entropy)
      (fun i => mul (sub (observed i).value (reference i).value) (entropyBitGradient (reference i).value (lower i) (positive i))))).mp terms

/-- Normalization written in the same finite-sum form as entropy and KL. -/
theorem normalized_mass_sum (masses : Fin variables → UnitIntervalValue)
    (normalized : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (masses i).value)) one) :
    Equiv (listSum ((List.finRange variables).map (fun i => (masses i).value))) one := by
  have evaluation := equiv_trans (FiniteLinear.realDot_pair variables (fun _ => 1) (fun i => (masses i).value))
    (listSum_map_congr (List.finRange variables) _ _ (fun i _ => one_mul (masses i).value))
  exact equiv_trans (equiv_symm evaluation) normalized

/-- On normalized laws the supporting tangent is exactly cross entropy.
This identity, including its zero-observation case, connects the local
multiplier equation with the global Gibbs inequality. -/
theorem realEntropy_tangent_eq_crossEntropy (observed reference : Fin variables → UnitIntervalValue)
    (normalizedObserved : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (observed i).value)) one)
    (normalizedReference : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (reference i).value)) one)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    Equiv (add (realEntropySum ((List.finRange variables).map reference))
      (FiniteLinear.pair variables (fun i => sub (observed i).value (reference i).value)
        (fun i => entropyBitGradient (reference i).value (lower i) (positive i))))
      (realCrossEntropySum observed reference lower positive) := by
  let slope := fun i => mul (sub (observed i).value (reference i).value) (entropyBitGradient (reference i).value (lower i) (positive i))
  let cross := fun i => neg (mul (observed i).value ((reference i).value.positiveLog2 (lower i) (positive i)))
  let correctionTerm := fun i => mul RationalLogSecant.limit (sub (reference i).value (observed i).value)
  have identity := listSum_map_congr (List.finRange variables)
    (fun i => add (reference i).entropy (slope i)) (fun i => add (cross i) (correctionTerm i))
    (fun i _ => (observed i).entropy_tangent_cross (reference i) (lower i) (positive i))
  have massDifference := equiv_trans (sum_map_sub (List.finRange variables) (fun i => (reference i).value) (fun i => (observed i).value))
    (equiv_trans (add_congr (normalized_mass_sum reference normalizedReference)
      (neg_congr (normalized_mass_sum observed normalizedObserved))) ((sub_equiv_zero_iff one one).mpr (equiv_refl one)))
  have distributed := mul_listSum RationalLogSecant.limit
    ((List.finRange variables).map (fun i => sub (reference i).value (observed i).value))
  simp only [List.map_map] at distributed
  have correction : Equiv
      (listSum ((List.finRange variables).map (fun i => mul RationalLogSecant.limit (sub (reference i).value (observed i).value)))) zero :=
    equiv_trans (equiv_symm distributed)
      (equiv_trans (mul_congr (equiv_refl _) massDifference) (mul_zero _))
  have left := listSum_map_add (List.finRange variables) (fun i => (reference i).entropy) slope
  have right := equiv_trans (listSum_map_add (List.finRange variables) cross correctionTerm)
    (equiv_trans (add_congr (equiv_refl _) correction) (add_zero _))
  simpa only [realEntropySum, List.map_map, realCrossEntropySum] using equiv_trans (equiv_symm left) (equiv_trans identity right)

/-- The global analytic Gibbs inequality for normalized finite laws. There
are no shared moment constraints and observed probabilities may vanish. -/
theorem realEntropySum_le_crossEntropy (observed reference : Fin variables → UnitIntervalValue)
    (normalizedObserved : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (observed i).value)) one)
    (normalizedReference : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (reference i).value)) one)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    LE (realEntropySum ((List.finRange variables).map observed)) (realCrossEntropySum observed reference lower positive) :=
  (le_congr (equiv_refl _) (realEntropy_tangent_eq_crossEntropy observed reference normalizedObserved normalizedReference lower positive)).mp
    (realEntropySum_supporting observed reference lower positive)

theorem realRelativeEntropySum_nonnegative (observed reference : Fin variables → UnitIntervalValue)
    (normalizedObserved : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (observed i).value)) one)
    (normalizedReference : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (reference i).value)) one)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    LE zero (realRelativeEntropySum observed reference lower positive) :=
  (le_congr (equiv_refl _) (realRelativeEntropySum_decomposition observed reference lower positive)).mpr
    ((zero_le_sub_iff _ _).mpr (realEntropySum_le_crossEntropy observed reference normalizedObserved normalizedReference lower positive))

/-- A positive reference attains its own cross entropy. Only reference
masses use logarithms, so the preceding global bound still admits zeros in
other laws. -/
theorem realCrossEntropySum_self (reference : Fin variables → UnitIntervalValue) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    Equiv (realCrossEntropySum reference reference lower positive) (realEntropySum ((List.finRange variables).map reference)) := by
  simp only [realCrossEntropySum, realEntropySum, List.map_map]
  exact listSum_map_congr _ _ _ (fun i _ => equiv_symm ((reference i).value.realEntropyTerm_formula
    (reference i).nonnegative (reference i).bounded (lower i) (positive i)))

/-- Natural KL retains the established zero-observation extension. -/
def naturalRelativeEntropySum (observed reference : Fin variables → UnitIntervalValue) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) : ConstructiveReal :=
  listSum ((List.finRange variables).map (fun i => (observed i).value.naturalRelativeEntropyTerm
    (observed i).nonnegative (observed i).bounded (reference i).value (lower i) (positive i)))

theorem naturalRelativeEntropySum_units (observed reference : Fin variables → UnitIntervalValue) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    Equiv (naturalRelativeEntropySum observed reference lower positive) (mul (realRelativeEntropySum observed reference lower positive) lnTwo) := by
  simpa only [naturalRelativeEntropySum, naturalRelativeEntropyTerm, realRelativeEntropySum, List.map_map] using
    equiv_symm (listSum_mul ((List.finRange variables).map (fun i => (observed i).value.realRelativeEntropyTerm
      (observed i).nonnegative (observed i).bounded (reference i).value (lower i) (positive i))) lnTwo)

theorem naturalRelativeEntropySum_nonnegative (observed reference : Fin variables → UnitIntervalValue)
    (normalizedObserved : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (observed i).value)) one)
    (normalizedReference : Equiv (Distros.RationalLinear.realDot variables (fun _ => 1) (fun i => (reference i).value)) one)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value) :
    LE zero (naturalRelativeEntropySum observed reference lower positive) := by
  have factor : LE zero lnTwo := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr RationalLogSecant.limit.positiveInverseLower.signed_nonnegative)) lnTwo_lower
  exact (le_congr (equiv_refl _) (naturalRelativeEntropySum_units observed reference lower positive)).mpr
    (mul_nonnegative (realRelativeEntropySum_nonnegative observed reference normalizedObserved normalizedReference lower positive) factor)

end Thesis.Probability.ConstructiveReal
