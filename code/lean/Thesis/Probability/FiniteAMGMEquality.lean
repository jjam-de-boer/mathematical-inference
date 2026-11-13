import Thesis.Probability.FiniteAMGM

namespace Thesis.Probability.FiniteAMGM
open Combinatorics

/-- Change only the values of a finite family of natural multiplicities. -/
def mapped (items : List (Nat × Nat)) (f : Nat → Nat) : List (Nat × Nat) :=
  items.map (fun item => (f item.1, item.2))

theorem mapped_weight (items : List (Nat × Nat)) (f : Nat → Nat) : weightTotal (mapped items f) = weightTotal items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [mapped, List.map_cons, weightTotal] at ih ⊢; rw [ih]

def mappedProduct (items : List (Nat × Nat)) (f : Nat → Nat) : Nat := weightedProduct (mapped items f)

theorem mappedProduct_pos (items : List (Nat × Nat)) (f : Nat → Nat)
    (positive : ∀ item ∈ items, 0 < f item.1) : 0 < mappedProduct items f := by
  induction items with
  | nil => exact Nat.zero_lt_one
  | cons item rest ih =>
      exact Nat.mul_pos (Nat.pow_pos (positive item (List.mem_cons_self ..)))
        (ih (fun other member => positive other (List.mem_cons_of_mem _ member)))

theorem mappedProduct_mono (items : List (Nat × Nat)) (f g : Nat → Nat)
    (compared : ∀ item ∈ items, f item.1 ≤ g item.1) : mappedProduct items f ≤ mappedProduct items g := by
  induction items with
  | nil => exact Nat.le_refl _
  | cons item rest ih =>
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (compared item (List.mem_cons_self ..)) item.2)
        (ih (fun other member => compared other (List.mem_cons_of_mem _ member)))

/-- Equality in a product of positive coordinatewise inequalities forces
equality at each coordinate of positive multiplicity. -/
theorem mappedProduct_eq_of_bounds (items : List (Nat × Nat)) (f g : Nat → Nat)
    (positive : ∀ item ∈ items, 0 < f item.1)
    (compared : ∀ item ∈ items, f item.1 ≤ g item.1)
    (equal : mappedProduct items f = mappedProduct items g) :
    ∀ item ∈ items, 0 < item.2 → f item.1 = g item.1 := by
  induction items with
  | nil => intro item member; exact False.elim (List.not_mem_nil member)
  | cons head rest ih =>
      have tailPositive := mappedProduct_pos rest f (fun other member => positive other (List.mem_cons_of_mem _ member))
      have tailBound := mappedProduct_mono rest f g (fun other member => compared other (List.mem_cons_of_mem _ member))
      have headBound := Nat.pow_le_pow_left (compared head (List.mem_cons_self ..)) head.2
      change f head.1 ^ head.2 * mappedProduct rest f = g head.1 ^ head.2 * mappedProduct rest g at equal
      have reversed : g head.1 ^ head.2 * mappedProduct rest f ≤ f head.1 ^ head.2 * mappedProduct rest f := by
        calc
          _ ≤ g head.1 ^ head.2 * mappedProduct rest g := Nat.mul_le_mul_left _ tailBound
          _ = _ := equal.symm
      have headEqual := Nat.le_antisymm headBound ((Nat.mul_le_mul_right_iff tailPositive).mp reversed)
      have tailEqual : mappedProduct rest f = mappedProduct rest g := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (positive head (List.mem_cons_self ..)))
        calc
          _ = g head.1 ^ head.2 * mappedProduct rest g := equal
          _ = _ := by rw [headEqual]
      intro item member weight
      rcases List.mem_cons.mp member with here | later
      · subst item
        exact (Nat.pow_left_inj (Nat.ne_of_gt weight)).mp headEqual
      · exact ih (fun other member => positive other (List.mem_cons_of_mem _ member))
          (fun other member => compared other (List.mem_cons_of_mem _ member)) tailEqual item later weight

private theorem pair_square (a d : Nat) : (a + (a + d)) ^ 2 = 4 * a * (a + d) + d * d := by
  change (a + (a + d)) ^ 2 = ((1 + 1) + (1 + 1)) * a * (a + d) + d * d
  simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul]
  ac_rfl

private theorem eq_of_four_mul_eq_square_of_le (a b : Nat) (order : a ≤ b)
    (equal : 4 * a * b = (a + b) ^ 2) : a = b := by
  have presentation : b = a + (b - a) := (Nat.add_sub_of_le order).symm
  have expansion : (a + b) ^ 2 = 4 * a * b + (b - a) * (b - a) := by
    simpa only [← presentation] using pair_square a (b - a)
  have squareZero : (b - a) * (b - a) = 0 := by omega
  have difference : b - a = 0 := (Nat.mul_eq_zero.mp squareZero).elim id id
  rw [difference, Nat.add_zero] at presentation
  exact presentation.symm

theorem eq_of_four_mul_eq_square (a b : Nat) (equal : 4 * a * b = (a + b) ^ 2) : a = b := by
  rcases Nat.le_total a b with order | order
  · exact eq_of_four_mul_eq_square_of_le a b order equal
  · apply (eq_of_four_mul_eq_square_of_le b a order ?_).symm
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm] using equal

theorem mapped_sum_add (items : List (Nat × Nat)) (constant : Nat) :
    Combinatorics.weightedSum (mapped items (fun value => value + constant)) =
      Combinatorics.weightedSum items + weightTotal items * constant := by
  induction items with
  | nil => simp only [mapped, List.map_nil, Combinatorics.weightedSum, weightTotal, Nat.zero_mul]
  | cons item rest ih =>
      simp only [mapped, List.map_cons, Combinatorics.weightedSum, weightTotal, Nat.mul_add, Nat.add_mul] at ih ⊢
      rw [ih]
      ac_rfl

theorem mappedProduct_pow (items : List (Nat × Nat)) (f : Nat → Nat) (power : Nat) :
    mappedProduct items (fun value => f value ^ power) = mappedProduct items f ^ power := by
  induction items with
  | nil => simp only [mappedProduct, mapped, List.map_nil, weightedProduct, Nat.one_pow]
  | cons item rest ih =>
      change (f item.1 ^ power) ^ item.2 * mappedProduct rest (fun value => f value ^ power) =
        (f item.1 ^ item.2 * mappedProduct rest f) ^ power
      rw [ih, Nat.mul_pow, Nat.pow_right_comm]

theorem mappedProduct_quadratic (items : List (Nat × Nat)) (constant : Nat) :
    mappedProduct items (fun value => 4 * value * constant) =
      4 ^ weightTotal items * weightedProduct items * constant ^ weightTotal items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change (4 * item.1 * constant) ^ item.2 * mappedProduct rest (fun value => 4 * value * constant) =
        4 ^ (item.2 + weightTotal rest) * (item.1 ^ item.2 * weightedProduct rest) * constant ^ (item.2 + weightTotal rest)
      rw [ih]
      simp only [Nat.mul_pow, Nat.pow_add]
      ac_rfl

/-- Equality in the arithmetic-mean product bound forces every positive-weight
entry to equal the denominator. The proof compares each entry with its
midpoint with the denominator, using only the finite AM–GM inequality. -/
theorem eq_den_of_weightedProduct_eq_pow (items : List (Nat × Nat)) (den : Nat)
    (denPositive : 0 < den) (weightPositive : 0 < weightTotal items)
    (positive : ∀ item ∈ items, 0 < item.1)
    (bounded : Combinatorics.weightedSum items ≤ weightTotal items * den)
    (equal : weightedProduct items = den ^ weightTotal items) :
    ∀ item ∈ items, 0 < item.2 → item.1 = den := by
  have midpointBound : Combinatorics.weightedSum (mapped items (fun value => value + den)) ≤ weightTotal items * (2 * den) := by
    rw [mapped_sum_add]
    calc
      _ ≤ weightTotal items * den + weightTotal items * den := Nat.add_le_add_right bounded _
      _ = _ := by rw [Nat.two_mul, Nat.mul_add]
  have midpointProduct : mappedProduct items (fun value => value + den) ≤ (2 * den) ^ weightTotal items := by
    have result := weighted_product_le_pow (mapped items (fun value => value + den)) (2 * den)
      (by simpa only [mapped_weight] using weightPositive)
      (by simpa only [mapped_weight] using midpointBound)
    simpa only [mappedProduct, mapped_weight] using result
  have upper : mappedProduct items (fun value => (value + den) ^ 2) ≤ mappedProduct items (fun value => 4 * value * den) := by
    rw [mappedProduct_pow]
    calc
      _ ≤ ((2 * den) ^ weightTotal items) ^ 2 := Nat.pow_le_pow_left midpointProduct 2
      _ = 4 ^ weightTotal items * (den ^ weightTotal items * den ^ weightTotal items) := by
        rw [show (4 : Nat) = 2 * 2 from rfl]
        simp only [Nat.mul_pow, Nat.pow_two]
        ac_rfl
      _ = _ := by rw [mappedProduct_quadratic, equal]; ac_rfl
  have lower := mappedProduct_mono items (fun value => 4 * value * den) (fun value => (value + den) ^ 2)
    (fun item _ => four_mul_le_square item.1 den)
  have coordinate := mappedProduct_eq_of_bounds items (fun value => 4 * value * den) (fun value => (value + den) ^ 2)
    (fun item member => Nat.mul_pos (Nat.mul_pos (by decide) (positive item member)) denPositive)
    (fun item _ => four_mul_le_square item.1 den) (Nat.le_antisymm lower upper)
  intro item member weight
  exact eq_of_four_mul_eq_square _ _ (coordinate item member weight)

end Thesis.Probability.FiniteAMGM
