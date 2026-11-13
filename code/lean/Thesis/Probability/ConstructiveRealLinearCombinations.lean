import Thesis.Probability.ConstructiveRealLinearProjection

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear

/-- Explicit nonnegative integral combinations of original rows. Indices
are finite data and scalar coefficients are naturals; no row selection is
extracted from an existential proposition. -/
inductive Combination (rows : List (Inequality variables)) where
  | input (index : Fin rows.length)
  | addScaled (first second : Nat) (left right : Combination rows)

def Combination.coefficients {rows : List (Inequality variables)} : Combination rows → Fin variables → Int
  | .input index => (rows[index.val]).coefficients
  | .addScaled first second left right => fun column => (first : Int) * left.coefficients column + (second : Int) * right.coefficients column

def Combination.bound {rows : List (Inequality variables)} : Combination rows → ConstructiveReal
  | .input index => (rows[index.val]).bound
  | .addScaled first second left right => add (mul (realInteger (first : Int)) left.bound) (mul (realInteger (second : Int)) right.bound)

private theorem integer_nat_nonnegative (value : Nat) : LE zero (realInteger (value : Int)) :=
  (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr (Int.natCast_nonneg value))

/-- Nonnegative row combinations are sound for analytic assignments and
right-hand sides, independently of the elimination algorithm. -/
theorem Combination.holds_of_satisfies {rows : List (Inequality variables)} (combination : Combination rows)
    (values : Fin variables → ConstructiveReal) (satisfies : Satisfies rows values) :
    LE (realDot variables combination.coefficients values) combination.bound := by
  induction combination with
  | input index => exact satisfies _ (List.getElem_mem index.isLt)
  | addScaled first second left right ihLeft ihRight =>
      have evaluation := equiv_trans (realDot_add_coefficients variables _ _ values)
        (add_congr (realDot_scale_coefficients variables (first : Int) left.coefficients values)
          (realDot_scale_coefficients variables (second : Int) right.coefficients values))
      exact (le_congr evaluation (equiv_refl _)).mpr
        (add_le_add (mul_le_mul_nonnegative (integer_nat_nonnegative first) ihLeft)
          (mul_le_mul_nonnegative (integer_nat_nonnegative second) ihRight))

/-- The finite-dimensional Farkas condition, expressed with actual
nonnegative combination data. No alternative or feasibility decision on
analytic values is built into this proposition. -/
def FarkasCondition (rows : List (Inequality variables)) : Prop :=
  ∀ combination : Combination rows, (∀ column, combination.coefficients column = 0) → LE zero combination.bound

theorem farkas_of_satisfies (rows : List (Inequality variables)) (values : Fin variables → ConstructiveReal)
    (satisfies : Satisfies rows values) : FarkasCondition rows := by
  intro combination vanished
  have zeroCoefficients : combination.coefficients = (fun _ => 0) := funext vanished
  have bounded := combination.holds_of_satisfies values satisfies
  rw [zeroCoefficients] at bounded
  exact (le_congr (realDot_zero variables values) (equiv_refl _)).mp bounded

/-- Padding a projected row by zero records the coefficients of variables
already eliminated. Only natural-index comparisons occur in this lookup. -/
def coefficientAt (row : Inequality variables) (column : Nat) : Int :=
  if before : column < variables then row.coefficients ⟨column, before⟩ else 0

private theorem coefficientAt_trim (row : Inequality (variables + 1)) (zeroPivot : row.pivot = 0) (column : Nat) :
    coefficientAt row.trim column = coefficientAt row column := by
  by_cases before : column < variables
  · have beforeNext : column < variables + 1 := by omega
    simp only [coefficientAt, dif_pos before, dif_pos beforeNext, Inequality.trim]
    exact congrArg row.coefficients (Fin.ext rfl)
  · by_cases last : column = variables
    · subst column
      simp only [coefficientAt, dif_neg (Nat.lt_irrefl variables), dif_pos (Nat.lt_succ_self variables)]
      exact zeroPivot.symm
    · have after : ¬ column < variables + 1 := by omega
      simp only [coefficientAt, dif_neg before, dif_neg after]

private theorem coefficientAt_combine (upper lower : Inequality (variables + 1)) (column : Nat) :
    coefficientAt (combine upper lower) column =
      -lower.pivot * coefficientAt upper column + upper.pivot * coefficientAt lower column := by
  by_cases before : column < variables
  · have beforeNext : column < variables + 1 := by omega
    simp only [coefficientAt, dif_pos before, dif_pos beforeNext, combine]
    rw [show (⟨column, before⟩ : Fin variables).castSucc = ⟨column, beforeNext⟩ from Fin.ext rfl]
  · by_cases last : column = variables
    · subst column
      simp only [coefficientAt, dif_neg (Nat.lt_irrefl variables), dif_pos (Nat.lt_succ_self variables)]
      change 0 = -lower.pivot * upper.pivot + upper.pivot * lower.pivot
      rw [Int.neg_mul, Int.mul_comm lower.pivot upper.pivot]
      omega
    · have after : ¬ column < variables + 1 := by omega
      simp only [coefficientAt, dif_neg before, dif_neg after, Int.mul_zero, Int.add_zero]

/-- Each projected row carries an explicit nonnegative combination of the
original rows, including the vanished coefficients of eliminated columns. -/
structure Traced (rows : List (Inequality original)) (retained : Nat) where
  row : Inequality retained
  source : Combination rows
  coefficients_agree : ∀ column : Fin original, source.coefficients column = coefficientAt row column.val
  bound_agrees : Equiv row.bound source.bound

def Traced.input (rows : List (Inequality variables)) (index : Fin rows.length) : Traced rows variables where
  row := rows[index.val]
  source := .input index
  coefficients_agree column := by simp only [Combination.coefficients, coefficientAt, dif_pos column.isLt]
  bound_agrees := equiv_refl _

def Traced.trim {rows : List (Inequality original)} (traced : Traced rows (retained + 1)) (zeroPivot : traced.row.pivot = 0) : Traced rows retained where
  row := traced.row.trim
  source := traced.source
  coefficients_agree column := (traced.coefficients_agree column).trans (coefficientAt_trim traced.row zeroPivot column.val).symm
  bound_agrees := traced.bound_agrees

def Traced.combine {rows : List (Inequality original)} (upper lower : Traced rows (retained + 1))
    (positive : 0 < upper.row.pivot) (negative : lower.row.pivot < 0) : Traced rows retained := by
  have firstCast : ((-lower.row.pivot).toNat : Int) = -lower.row.pivot := Int.toNat_of_nonneg (by omega)
  have secondCast : (upper.row.pivot.toNat : Int) = upper.row.pivot := Int.toNat_of_nonneg (by omega)
  refine ⟨AnalyticLinear.combine upper.row lower.row,
    .addScaled (-lower.row.pivot).toNat upper.row.pivot.toNat upper.source lower.source, ?_, ?_⟩
  · intro column
    change ((-lower.row.pivot).toNat : Int) * upper.source.coefficients column +
      (upper.row.pivot.toNat : Int) * lower.source.coefficients column = _
    rw [firstCast, secondCast, upper.coefficients_agree column, lower.coefficients_agree column]
    exact (coefficientAt_combine upper.row lower.row column.val).symm
  · change Equiv (add (mul (realInteger (-lower.row.pivot)) upper.row.bound) (mul (realInteger upper.row.pivot) lower.row.bound))
      (add (mul (realInteger ((-lower.row.pivot).toNat : Int)) upper.source.bound) (mul (realInteger (upper.row.pivot.toNat : Int)) lower.source.bound))
    rw [firstCast, secondCast]
    exact add_congr (mul_congr (equiv_refl _) upper.bound_agrees) (mul_congr (equiv_refl _) lower.bound_agrees)

/-- At zero retained variables, the recorded source annihilates every
original column. Farkas therefore supplies the required constant sign. -/
theorem Traced.constant_nonnegative {rows : List (Inequality original)} (traced : Traced rows 0)
    (condition : FarkasCondition rows) : LE zero traced.row.bound :=
  (le_congr (equiv_refl _) (equiv_symm traced.bound_agrees)).mp
    (condition traced.source (fun column => by
      have recorded := traced.coefficients_agree column
      simpa only [coefficientAt, Nat.not_lt_zero, dif_neg] using recorded))

end Thesis.Probability.AnalyticLinear
