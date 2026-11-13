import Thesis.Probability.Combinatorics

namespace Thesis.Probability.FiniteAMGM

/-- An explicit natural product, including zero factors. -/
def product : List Nat → Nat
  | [] => 1
  | head :: rest => head * product rest

theorem product_append (xs ys : List Nat) : product (xs ++ ys) = product xs * product ys := by
  induction xs with
  | nil => simp only [List.nil_append, product, Nat.one_mul]
  | cons head rest ih => simp only [List.cons_append, product, ih, Nat.mul_assoc]

theorem sum_scale (xs : List Nat) (factor : Nat) : (xs.map (fun x => factor * x)).sum = factor * xs.sum := by
  induction xs with
  | nil => simp
  | cons head rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem product_scale (xs : List Nat) (factor : Nat) :
    product (xs.map (fun x => factor * x)) = factor ^ xs.length * product xs := by
  induction xs with
  | nil => simp only [List.map_nil, product, List.length_nil, Nat.pow_zero, Nat.mul_one]
  | cons head rest ih =>
      simp only [List.map_cons, product, ih, List.length_cons, Nat.pow_succ]
      ac_rfl

/-- Two-coordinate AM–GM, without a square root or division. -/
theorem four_mul_le_square (a b : Nat) : 4 * a * b ≤ (a + b) ^ 2 := by
  change (2 + 2) * a * b ≤ _
  rw [Nat.add_mul, Nat.add_mul]
  calc
    _ ≤ (a * a + b * b) + 2 * a * b :=
      Nat.add_le_add_right (Combinatorics.two_mul_le_sq_add a b) _
    _ = (a + b) ^ 2 := by
      simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.two_mul]
      ac_rfl

/-- The denominator-cleared AM–GM assertion at a fixed length. -/
def Bound (n : Nat) : Prop :=
  ∀ xs : List Nat, xs.length = n → n ^ n * product xs ≤ xs.sum ^ n

theorem bound_one : Bound 1 := by
  intro xs length
  cases xs with
  | nil => simp at length
  | cons head rest =>
      have restLength : rest.length = 0 := by simp only [List.length_cons] at length; omega
      have empty : rest = [] := List.eq_nil_of_length_eq_zero restLength
      subst rest
      simp only [product, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.mul_one, Nat.one_mul, Nat.pow_one]
      exact Nat.le_refl _

private theorem coefficient_double (n : Nat) : (2 * n) ^ (2 * n) = 4 ^ n * (n ^ n * n ^ n) := by
  rw [Nat.pow_mul (2 * n) 2 n, Nat.mul_pow 2 n 2]
  rw [show 2 ^ 2 = 4 from rfl, Nat.pow_two n, Nat.mul_pow, Nat.mul_pow]

private theorem append_bound (n : Nat) (bound : Bound n) (xs ys : List Nat)
    (leftLength : xs.length = n) (rightLength : ys.length = n) :
    (2 * n) ^ (2 * n) * product (xs ++ ys) ≤ (xs ++ ys).sum ^ (2 * n) := by
  rw [product_append, List.sum_append]
  calc
    _ = 4 ^ n * ((n ^ n * product xs) * (n ^ n * product ys)) := by rw [coefficient_double]; ac_rfl
    _ ≤ 4 ^ n * (xs.sum ^ n * ys.sum ^ n) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (bound xs leftLength) (bound ys rightLength))
    _ = (4 * (xs.sum * ys.sum)) ^ n := by rw [Nat.mul_pow, Nat.mul_pow]
    _ ≤ ((xs.sum + ys.sum) ^ 2) ^ n :=
      Nat.pow_le_pow_left (by simpa only [Nat.mul_assoc] using four_mul_le_square xs.sum ys.sum) n
    _ = (xs.sum + ys.sum) ^ (2 * n) := (Nat.pow_mul _ _ _).symm

theorem bound_double (n : Nat) (bound : Bound n) : Bound (2 * n) := by
  intro xs length
  have leftLength : (xs.take n).length = n := by rw [List.length_take, length]; omega
  have rightLength : (xs.drop n).length = n := by rw [List.length_drop, length]; omega
  have joined := append_bound n bound (xs.take n) (xs.drop n) leftLength rightLength
  simpa only [List.take_append_drop] using joined

private theorem product_zero_of_sum_zero (xs : List Nat) (nonempty : 0 < xs.length) (zero : xs.sum = 0) : product xs = 0 := by
  cases xs with
  | nil => simp at nonempty
  | cons head rest =>
      have headZero : head = 0 := by change head + rest.sum = 0 at zero; omega
      simp only [product, headZero, Nat.zero_mul]

/-- Cauchy's descending step pads scaled entries with their sum. It makes
no appeal to a real minimum or a choice of maximizer. -/
theorem bound_predecessor (n : Nat) (next : Bound (n + 1)) : Bound n := by
  intro xs length
  by_cases nZero : n = 0
  · have empty := List.eq_nil_of_length_eq_zero (length.trans nZero)
    subst xs
    rw [nZero]
    exact Nat.le_refl _
  · have nPositive : 0 < n := Nat.pos_of_ne_zero nZero
    by_cases sumZero : xs.sum = 0
    · have vanished := product_zero_of_sum_zero xs (by omega) sumZero
      rw [vanished, Nat.mul_zero]
      exact Nat.zero_le _
    · have sumPositive := Nat.pos_of_ne_zero sumZero
      let padded := xs.map (fun x => n * x) ++ [xs.sum]
      have paddedLength : padded.length = n + 1 := by simp only [padded, List.length_append, List.length_map, length, List.length_cons, List.length_nil]
      have paddedSum : padded.sum = (n + 1) * xs.sum := by
        simp only [padded, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, sum_scale, Nat.add_mul, Nat.one_mul]
      have paddedProduct : product padded = n ^ n * product xs * xs.sum := by
        simp only [padded, product_append, product_scale, length, product, Nat.mul_one]
      have estimate := next padded paddedLength
      rw [paddedProduct, paddedSum, Nat.mul_pow, Nat.pow_succ xs.sum n] at estimate
      have cancelled := (Nat.mul_le_mul_left_iff (Nat.pow_pos (Nat.zero_lt_succ n))).mp estimate
      exact (Nat.mul_le_mul_right_iff sumPositive).mp cancelled

theorem bound_two_pow (power : Nat) : Bound (2 ^ power) := by
  induction power with
  | zero => exact bound_one
  | succ power ih =>
      simpa only [Nat.pow_succ, Nat.mul_comm] using bound_double (2 ^ power) ih

/-- Finite AM–GM, cleared of roots and rational denominators. The proof
ascends through powers of two and descends a bounded number of steps. -/
theorem bound (n : Nat) : Bound n := by
  have descend : ∀ gap, Bound (n + gap) → Bound n := by
    intro gap
    induction gap with
    | zero => intro same; exact same
    | succ gap ih =>
        intro above
        exact ih (bound_predecessor (n + gap) above)
  have within : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  apply descend (2 ^ n - n)
  rw [Nat.add_sub_of_le within]
  exact bound_two_pow n

theorem inequality (xs : List Nat) : xs.length ^ xs.length * product xs ≤ xs.sum ^ xs.length :=
  bound xs.length xs rfl

/-- Expand natural multiplicities for the proof only; zero weights contribute
no factors, even if their recorded value is zero. -/
def expand (items : List (Nat × Nat)) : List Nat :=
  items.flatMap (fun item => List.replicate item.2 item.1)

def weightedProduct : List (Nat × Nat) → Nat
  | [] => 1
  | (value, weight) :: rest => value ^ weight * weightedProduct rest

private theorem sum_replicate (count value : Nat) : (List.replicate count value).sum = count * value := by
  induction count with
  | zero => simp only [List.replicate_zero, List.sum_nil, Nat.zero_mul]
  | succ count ih => simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

private theorem product_replicate (count value : Nat) : product (List.replicate count value) = value ^ count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [List.replicate_succ, product, ih, Nat.pow_succ, Nat.mul_comm]

theorem expand_length (items : List (Nat × Nat)) : (expand items).length = Combinatorics.weightTotal items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [expand, List.flatMap_cons, List.length_append, List.length_replicate, Combinatorics.weightTotal] at ih ⊢; rw [ih]

theorem expand_sum (items : List (Nat × Nat)) : (expand items).sum = Combinatorics.weightedSum items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [expand, List.flatMap_cons, List.sum_append, sum_replicate, Combinatorics.weightedSum] at ih ⊢; rw [ih]

theorem expand_product (items : List (Nat × Nat)) : product (expand items) = weightedProduct items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [expand, List.flatMap_cons, product_append, product_replicate, weightedProduct] at ih ⊢; rw [ih]

/-- Weighted finite AM–GM includes zero values, zero multiplicities and the
empty family, with the same explicit `0^0 = 1` power convention. -/
theorem weighted_inequality (items : List (Nat × Nat)) :
    Combinatorics.weightTotal items ^ Combinatorics.weightTotal items * weightedProduct items ≤
      Combinatorics.weightedSum items ^ Combinatorics.weightTotal items := by
  have result := inequality (expand items)
  simpa only [expand_length, expand_sum, expand_product] using result

/-- If the weighted arithmetic mean is at most a common denominator, the
weighted product of the cleared numerators is at most its total-weight power.
This is the rational multiplicative form needed by the Gibbs inequality. -/
theorem weighted_product_le_pow (items : List (Nat × Nat)) (denominator : Nat)
    (positive : 0 < Combinatorics.weightTotal items)
    (bounded : Combinatorics.weightedSum items ≤ Combinatorics.weightTotal items * denominator) :
    weightedProduct items ≤ denominator ^ Combinatorics.weightTotal items := by
  have estimate := Nat.le_trans (weighted_inequality items)
    (Nat.pow_le_pow_left bounded (Combinatorics.weightTotal items))
  rw [Nat.mul_pow] at estimate
  exact (Nat.mul_le_mul_left_iff (Nat.pow_pos positive)).mp estimate

/-- A strict arithmetic-mean bound gives a strict product bound, without
requiring positivity of individual recorded values or multiplicities. -/
theorem weighted_product_lt_pow (items : List (Nat × Nat)) (denominator : Nat)
    (positive : 0 < Combinatorics.weightTotal items)
    (bounded : Combinatorics.weightedSum items < Combinatorics.weightTotal items * denominator) :
    weightedProduct items < denominator ^ Combinatorics.weightTotal items := by
  have estimate := Nat.lt_of_le_of_lt (weighted_inequality items)
    (Nat.pow_lt_pow_left bounded (Nat.ne_of_gt positive))
  rw [Nat.mul_pow] at estimate
  by_cases desired : weightedProduct items < denominator ^ Combinatorics.weightTotal items
  · exact desired
  · have reverse := Nat.mul_le_mul_left (Combinatorics.weightTotal items ^ Combinatorics.weightTotal items)
      (Nat.le_of_not_gt desired)
    exact False.elim (Nat.not_le_of_gt estimate reverse)

end Thesis.Probability.FiniteAMGM
