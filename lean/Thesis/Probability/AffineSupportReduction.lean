import Thesis.Probability.IntegerNullspace
import Thesis.Probability.FiniteRatioMinimum

namespace Thesis
namespace Probability
namespace AffineSupportReduction

open IntegerLinearAlgebra

/-!
# A maximal feasible support-reduction step

Append normalization to the supplied integer moment constraints and construct
an actual null direction.  Orient its explicit nonzero coordinate positively,
then minimize weight divided by positive direction coefficient over all finite
coordinates.  Nonpositive direction coordinates contribute the supplied
positive anchor instead; no positive coordinate is omitted from this search.

The update is fraction-free: `a_chosen * weight_i - weight_chosen * a_i`.
Every resulting weight is nonnegative, the chosen weight is zero, and every
moment, including total mass, is scaled by the same positive integer.  Thus
normalizing by the correspondingly scaled denominator preserves probabilities.
Negative integers describe only directions and intermediate differences;
the returned weights are natural numbers with a proved exact integer cast.

The internal step accepts strictly positive input weights.  General records
may contain zeros; a later compression wrapper must remove zero atoms before
calling this step and recurse on the number of remaining positive atoms.
This module does not assume that wrapper or a native-source replacement.
-/

def withNormalization {rows columns : Nat} (matrix : Matrix rows columns) : Matrix (rows + 1) columns :=
  fun row column => if original : row.val < rows then matrix ⟨row.val, original⟩ column else 1

theorem withNormalization_castSucc {rows columns : Nat} (matrix : Matrix rows columns) (row : Fin rows) :
    withNormalization matrix row.castSucc = matrix row := by
  funext column
  simp only [withNormalization, Fin.val_castSucc, dif_pos row.isLt]

theorem withNormalization_last {rows columns : Nat} (matrix : Matrix rows columns) :
    withNormalization matrix (Fin.last rows) = (fun _ => 1) := by
  funext column
  simp only [withNormalization, Fin.val_last, dif_neg (Nat.lt_irrefl rows)]

structure Direction {rows columns : Nat} (matrix : Matrix rows columns) where
  vector : Vector columns
  witness : Fin columns
  positive : 0 < vector witness
  mass_zero : dot (fun _ => 1) vector = 0
  moments_zero : Kernel matrix vector

/-- The affine direction is constructed, including an actual positive
coordinate.  No sign or normalization condition is supplied as an oracle. -/
def direction {rows columns : Nat} (matrix : Matrix rows columns) (larger : rows + 1 < columns) : Direction matrix := by
  let found := nonzeroKernel (rows + 1) columns (withNormalization matrix) larger
  let orientation : Int := if 0 < found.vector found.witness then 1 else -1
  let oriented : Vector columns := fun index => orientation * found.vector index
  refine ⟨oriented, found.witness, ?_, ?_, ?_⟩
  · by_cases positive : 0 < found.vector found.witness
    · simpa only [oriented, orientation, if_pos positive, Int.one_mul] using positive
    · have nonzero := found.nonzero
      simp only [oriented, orientation, if_neg positive, Int.neg_mul, Int.one_mul]
      omega
  · have normalized := found.vanishes (Fin.last rows)
    rw [withNormalization_last] at normalized
    change dot (fun _ => 1) (fun index => orientation * found.vector index) = 0
    rw [dot_scale_right, normalized, Int.mul_zero]
  · intro row
    have preserved := found.vanishes row.castSucc
    rw [withNormalization_castSucc] at preserved
    change dot (matrix row) (fun index => orientation * found.vector index) = 0
    rw [dot_scale_right, preserved, Int.mul_zero]

abbrev Weights (columns : Nat) := Fin columns → Nat

def positiveCandidates {rows columns : Nat} {matrix : Matrix rows columns} (movement : Direction matrix) :
    List {index : Fin columns // 0 < movement.vector index} :=
  (List.finRange columns).map (fun index =>
    if positive : 0 < movement.vector index then ⟨index, positive⟩ else ⟨movement.witness, movement.positive⟩)

theorem positiveCandidates_complete {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (index : Fin columns) (positive : 0 < movement.vector index) :
    (⟨index, positive⟩ : {index : Fin columns // 0 < movement.vector index}) ∈ positiveCandidates movement := by
  unfold positiveCandidates
  apply List.mem_map.mpr
  refine ⟨index, List.mem_finRange index, ?_⟩
  simp only [dif_pos positive]

def ratio {rows columns : Nat} {matrix : Matrix rows columns} (movement : Direction matrix)
    (weights : Weights columns) (candidate : {index : Fin columns // 0 < movement.vector index}) : QProb :=
  ⟨weights candidate.val, (movement.vector candidate.val).toNat, Int.pos_iff_toNat_pos.mp candidate.property⟩

/-- Every candidate carries its positive coefficient as data.  Mapping
nonpositive coordinates to the anchor permits a simple complete finite list,
without choosing an inhabitant of a filtered subtype. -/
def chosen {rows columns : Nat} {matrix : Matrix rows columns} (movement : Direction matrix) (weights : Weights columns) :
    {index : Fin columns // 0 < movement.vector index} :=
  FiniteRatioMinimum.select (ratio movement weights) ⟨movement.witness, movement.positive⟩ (positiveCandidates movement)

theorem chosen_minimal {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) (index : Fin columns) (positive : 0 < movement.vector index) :
    (weights (chosen movement weights).val : Int) * movement.vector index ≤
      (weights index : Int) * movement.vector (chosen movement weights).val := by
  have bound := (FiniteRatioMinimum.select_bounds (ratio movement weights)
    ⟨movement.witness, movement.positive⟩ (positiveCandidates movement)).2
    ⟨index, positive⟩ (positiveCandidates_complete movement index positive)
  have natural : weights (chosen movement weights).val * (movement.vector index).toNat ≤
      weights index * (movement.vector (chosen movement weights).val).toNat := bound
  have cast : ((weights (chosen movement weights).val * (movement.vector index).toNat : Nat) : Int) ≤
      ((weights index * (movement.vector (chosen movement weights).val).toNat : Nat) : Int) := by omega
  simp only [Int.natCast_mul, Int.toNat_of_nonneg (Int.le_of_lt positive),
    Int.toNat_of_nonneg (Int.le_of_lt (chosen movement weights).property)] at cast
  exact cast

def rawWeight {rows columns : Nat} {matrix : Matrix rows columns} (movement : Direction matrix)
    (weights : Weights columns) (index : Fin columns) : Int :=
  movement.vector (chosen movement weights).val * (weights index : Int) -
    (weights (chosen movement weights).val : Int) * movement.vector index

/-- Positive coordinates obey the minimum-ratio bound; nonpositive ones
can only gain mass.  No truncating subtraction is used in this proof. -/
theorem rawWeight_nonnegative {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) (index : Fin columns) :
    0 ≤ rawWeight movement weights index := by
  by_cases positive : 0 < movement.vector index
  · have feasible := chosen_minimal movement weights index positive
    unfold rawWeight
    rw [Int.mul_comm (movement.vector (chosen movement weights).val) (weights index : Int)]
    omega
  · have directionNonpositive : movement.vector index ≤ 0 := by omega
    have first := Int.mul_nonneg (Int.le_of_lt (chosen movement weights).property) (Int.natCast_nonneg (weights index))
    have second := Int.mul_nonpos_of_nonneg_of_nonpos
      (Int.natCast_nonneg (weights (chosen movement weights).val)) directionNonpositive
    unfold rawWeight
    omega

def updated {rows columns : Nat} {matrix : Matrix rows columns} (movement : Direction matrix)
    (weights : Weights columns) : Weights columns := fun index => (rawWeight movement weights index).toNat

theorem updated_cast {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) (index : Fin columns) :
    (updated movement weights index : Int) = rawWeight movement weights index :=
  Int.toNat_of_nonneg (rawWeight_nonnegative movement weights index)

theorem updated_chosen_zero {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) : updated movement weights (chosen movement weights).val = 0 := by
  have rawZero : rawWeight movement weights (chosen movement weights).val = 0 := by
    unfold rawWeight
    rw [Int.mul_comm (movement.vector (chosen movement weights).val) (weights (chosen movement weights).val : Int)]
    omega
  simp only [updated, rawZero, Int.toNat_zero]

theorem dot_sub_right {columns : Nat} (row first second : Vector columns) :
    dot row (fun index => first index - second index) = dot row first - dot row second := by
  rw [dot_comm row, dot_sub_left, dot_comm first row, dot_comm second row]

/-- Every annihilated moment scales by precisely the same positive
coefficient.  Normalization is one such moment, not an extra assumption. -/
theorem updated_dot {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) (row : Vector columns)
    (annihilated : dot row movement.vector = 0) :
    dot row (fun index => (updated movement weights index : Int)) =
      movement.vector (chosen movement weights).val * dot row (fun index => (weights index : Int)) := by
  have values : (fun index => (updated movement weights index : Int)) =
      (fun index => movement.vector (chosen movement weights).val * (weights index : Int) -
        (weights (chosen movement weights).val : Int) * movement.vector index) :=
    funext (updated_cast movement weights)
  rw [values, dot_sub_right, dot_scale_right, dot_scale_right, annihilated, Int.mul_zero, Int.sub_zero]

theorem updated_moments {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) (row : Fin rows) :
    dot (matrix row) (fun index => (updated movement weights index : Int)) =
      movement.vector (chosen movement weights).val * dot (matrix row) (fun index => (weights index : Int)) :=
  updated_dot movement weights (matrix row) (movement.moments_zero row)

theorem updated_mass {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) :
    dot (fun _ => 1) (fun index => (updated movement weights index : Int)) =
      movement.vector (chosen movement weights).val * dot (fun _ => 1) (fun index => (weights index : Int)) :=
  updated_dot movement weights (fun _ => 1) movement.mass_zero

def positiveCount {columns : Nat} (weights : Weights columns) : Nat :=
  ((List.finRange columns).filter (fun index => decide (0 < weights index))).length

private theorem filter_eq_of_all (values : List α) (predicate : α → Bool)
    (accepted : forall value, value ∈ values → predicate value = true) : values.filter predicate = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headAccepted := accepted head List.mem_cons_self
      have tailAccepted := fun value listed => accepted value (List.mem_cons_of_mem head listed)
      simp only [List.filter_cons, headAccepted, if_true, inductionHypothesis tailAccepted]

theorem positiveCount_eq_columns {columns : Nat} (weights : Weights columns)
    (positive : forall index, 0 < weights index) : positiveCount weights = columns := by
  have unchanged := filter_eq_of_all (List.finRange columns) (fun index => decide (0 < weights index))
    (fun index _ => decide_eq_true (positive index))
  simp only [positiveCount, unchanged, List.length_finRange]

private theorem filter_length_le (values : List α) (predicate : α → Bool) :
    (values.filter predicate).length ≤ values.length := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons head tail inductionHypothesis =>
      cases headValue : predicate head <;>
        simp only [List.filter_cons, headValue, Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

/-- A direct finite-list proof avoids classical empty-filter equivalences.
One rejected listed coordinate suffices for strict length decrease. -/
private theorem filter_length_lt_of_rejected (values : List α) (predicate : α → Bool) :
    forall rejected, rejected ∈ values → predicate rejected = false →
      (values.filter predicate).length < values.length := by
  induction values with
  | nil => intro rejected impossible _; cases impossible
  | cons head tail inductionHypothesis =>
      intro rejected listed rejectedValue
      cases headValue : predicate head with
      | false =>
          have bounded := filter_length_le tail predicate
          simp only [List.filter_cons, headValue, Bool.false_eq_true, if_false, List.length_cons]
          omega
      | true =>
          have later : rejected ∈ tail := by
            rcases List.mem_cons.mp listed with same | member
            · subst rejected
              rw [headValue] at rejectedValue
              cases rejectedValue
            · exact member
          have smaller := inductionHypothesis rejected later rejectedValue
          simp only [List.filter_cons, headValue, if_true, List.length_cons]
          omega

theorem updated_positiveCount_lt {rows columns : Nat} {matrix : Matrix rows columns}
    (movement : Direction matrix) (weights : Weights columns) :
    positiveCount (updated movement weights) < columns := by
  have rejected : decide (0 < updated movement weights (chosen movement weights).val) = false := by
    rw [updated_chosen_zero]
    rfl
  have smaller := filter_length_lt_of_rejected (List.finRange columns)
    (fun index => decide (0 < updated movement weights index))
    (chosen movement weights).val (List.mem_finRange _) rejected
  simpa only [positiveCount, List.length_finRange] using smaller

/-- Actual natural output weights, a positive common scaling factor, and
an old positive atom made zero.  With positive input weights the old support
has exactly `columns` atoms, so the displayed count is a strict progress
measure independent of how large the new denominator becomes. -/
structure Step {rows columns : Nat} (matrix : Matrix rows columns) (weights : Weights columns) where
  newWeights : Weights columns
  factor : Nat
  factor_positive : 0 < factor
  old_positive : forall index, 0 < weights index
  dropped : Fin columns
  dropped_old_positive : 0 < weights dropped
  dropped_zero : newWeights dropped = 0
  mass_scaled : dot (fun _ => 1) (fun index => (newWeights index : Int)) =
    (factor : Int) * dot (fun _ => 1) (fun index => (weights index : Int))
  moments_scaled : forall row, dot (matrix row) (fun index => (newWeights index : Int)) =
    (factor : Int) * dot (matrix row) (fun index => (weights index : Int))
  positive_count_decreases : positiveCount newWeights < positiveCount weights

/-- A complete single reduction step, not an assumed feasibility interface.
The matrix may include arbitrary signed integer moment coefficients.  Only
the actual probability weights, both before and after, are natural. -/
def step {rows columns : Nat} (matrix : Matrix rows columns) (weights : Weights columns)
    (positive : forall index, 0 < weights index) (larger : rows + 1 < columns) : Step matrix weights := by
  let movement := direction matrix larger
  let selected := chosen movement weights
  let factor := (movement.vector selected.val).toNat
  have factorPositive : 0 < factor := Int.pos_iff_toNat_pos.mp selected.property
  have factorCast : (factor : Int) = movement.vector selected.val := Int.toNat_of_nonneg (Int.le_of_lt selected.property)
  refine ⟨updated movement weights, factor, factorPositive, positive, selected.val, positive selected.val,
    updated_chosen_zero movement weights, ?_, ?_, ?_⟩
  · rw [factorCast]
    exact updated_mass movement weights
  · intro row
    rw [factorCast]
    exact updated_moments movement weights row
  · rw [positiveCount_eq_columns weights positive]
    exact updated_positiveCount_lt movement weights

end AffineSupportReduction
end Probability
end Thesis
