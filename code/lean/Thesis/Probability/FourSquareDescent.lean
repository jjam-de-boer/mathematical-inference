import Thesis.Probability.FourSquareNorm

namespace Thesis.Probability.FourSquareNorm

/-!
# Descent on a represented multiple of an odd prime

Even multipliers can be halved by grouping two same-parity pairs. For an
odd multiplier take centered residues. Their norm is a strictly smaller
multiple of that multiplier. Multiplying the two quadruples by Euler's
identity and dividing every coordinate gives a representation of the
smaller multiple of the original prime. Every residue and division in
this argument is computed over integers.
-/

namespace Quad

private theorem square_mod_two (x : Int) : (x * x) % 2 = x % 2 := by
  rw [Int.mul_emod]
  have alternatives : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases alternatives with h | h <;> rw [h] <;> decide

private theorem norm_even_iff (a : Quad) : a.norm % 2 = 0 ↔
    (a.first % 2 + a.second % 2 + a.third % 2 + a.fourth % 2) % 2 = 0 := by
  unfold norm
  rw [Int.add_emod, Int.add_emod (a.first * a.first + a.second * a.second),
    Int.add_emod (a.first * a.first), square_mod_two, square_mod_two, square_mod_two, square_mod_two]
  constructor <;> intro even <;> omega

private theorem halve_pairs (a : Quad) (firstPair : a.first % 2 = a.second % 2)
    (lastPair : a.third % 2 = a.fourth % 2) : ∃ b : Quad, 2 * b.norm = a.norm := by
  let b : Quad := ⟨(a.first + a.second) / 2, (a.first - a.second) / 2,
    (a.third + a.fourth) / 2, (a.third - a.fourth) / 2⟩
  have h₁ : 2 * b.first = a.first + a.second := by dsimp [b]; omega
  have h₂ : 2 * b.second = a.first - a.second := by dsimp [b]; omega
  have h₃ : 2 * b.third = a.third + a.fourth := by dsimp [b]; omega
  have h₄ : 2 * b.fourth = a.third - a.fourth := by dsimp [b]; omega
  refine ⟨b, ?_⟩
  have pair₁ := congrArg (fun x : Int => x * x) h₁
  have pair₂ := congrArg (fun x : Int => x * x) h₂
  have pair₃ := congrArg (fun x : Int => x * x) h₃
  have pair₄ := congrArg (fun x : Int => x * x) h₄
  unfold norm
  simp only [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg,
    Int.neg_neg, Int.mul_comm, Int.mul_left_comm] at *
  omega

/-- Halving an even norm. The three possible pairings account for parity
without assuming that the supplied quadruple is already ordered. -/
theorem halve (a : Quad) (even : a.norm % 2 = 0) : ∃ b : Quad, 2 * b.norm = a.norm := by
  have parity := (norm_even_iff a).mp even
  by_cases first : a.first % 2 = a.second % 2
  · exact halve_pairs a first (by omega)
  · by_cases next : a.first % 2 = a.third % 2
    · let reordered : Quad := ⟨a.first, a.third, a.second, a.fourth⟩
      have normSame : reordered.norm = a.norm := by dsimp [reordered, norm]; ac_rfl
      have pairing : reordered.third % 2 = reordered.fourth % 2 := by dsimp [reordered]; omega
      rcases halve_pairs reordered next pairing with ⟨b, half⟩
      exact ⟨b, half.trans normSame⟩
    · let reordered : Quad := ⟨a.first, a.fourth, a.second, a.third⟩
      have normSame : reordered.norm = a.norm := by dsimp [reordered, norm]; ac_rfl
      have pairing : reordered.first % 2 = reordered.second % 2 := by dsimp [reordered]; omega
      have remaining : reordered.third % 2 = reordered.fourth % 2 := by dsimp [reordered]; omega
      rcases halve_pairs reordered pairing remaining with ⟨b, half⟩
      exact ⟨b, half.trans normSame⟩

private def centered (value modulus : Int) : Int :=
  let residue := value % modulus
  if modulus < 2 * residue then residue - modulus else residue

private theorem centered_congruent (value modulus : Int) : modulus ∣ value - centered value modulus := by
  have near := Int.dvd_self_sub_emod (x := value) (m := modulus)
  dsimp [centered]
  split
  · rcases near with ⟨witness, same⟩
    exact ⟨witness + 1, by rw [Int.mul_add, Int.mul_one]; omega⟩
  · exact near

private theorem centered_bounds (value modulus : Int) (positive : 0 < modulus) (odd : modulus % 2 = 1) :
    -modulus < 2 * centered value modulus ∧ 2 * centered value modulus < modulus := by
  have lo := Int.emod_nonneg value (show modulus ≠ 0 by omega)
  have hi := Int.emod_lt_of_pos value positive
  dsimp [centered]
  split <;> constructor <;> omega

private def center (a : Quad) (modulus : Int) : Quad :=
  ⟨centered a.first modulus, centered a.second modulus,
    centered a.third modulus, centered a.fourth modulus⟩

private theorem center_congruent (a : Quad) (modulus : Int) : a.Congruent (a.center modulus) modulus :=
  ⟨centered_congruent _ _, centered_congruent _ _, centered_congruent _ _, centered_congruent _ _⟩

private theorem centered_square_lt (value modulus : Int) (positive : 0 < modulus) (odd : modulus % 2 = 1) :
    4 * (centered value modulus * centered value modulus) < modulus * modulus := by
  obtain ⟨lo, hi⟩ := centered_bounds value modulus positive odd
  have difference := Int.mul_pos (show 0 < modulus - 2 * centered value modulus by omega)
    (show 0 < modulus + 2 * centered value modulus by omega)
  simp only [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg, Int.mul_comm, Int.mul_left_comm] at *
  omega

private theorem center_norm_lt (a : Quad) (modulus : Int) (positive : 0 < modulus) (odd : modulus % 2 = 1) :
    (a.center modulus).norm < modulus * modulus := by
  have h₁ := centered_square_lt a.first modulus positive odd
  have h₂ := centered_square_lt a.second modulus positive odd
  have h₃ := centered_square_lt a.third modulus positive odd
  have h₄ := centered_square_lt a.fourth modulus positive odd
  simp only [center, norm]
  omega

private theorem square_nonnegative (x : Int) : 0 ≤ x * x := by
  simpa [Int.pow_succ] using Int.sq_nonneg x

private theorem norm_nonnegative (a : Quad) : 0 ≤ a.norm := by
  unfold norm
  exact Int.add_nonneg (Int.add_nonneg (Int.add_nonneg (square_nonnegative _) (square_nonnegative _))
    (square_nonnegative _)) (square_nonnegative _)

private theorem norm_zero_coordinates (a : Quad) (zero : a.norm = 0) : a = ⟨0, 0, 0, 0⟩ := by
  cases a with
  | mk first second third fourth =>
    change first * first + second * second + third * third + fourth * fourth = 0 at zero
    have p₁ := square_nonnegative first
    have p₂ := square_nonnegative second
    have p₃ := square_nonnegative third
    have p₄ := square_nonnegative fourth
    have coordinates : first = 0 ∧ second = 0 ∧ third = 0 ∧ fourth = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        apply Or.elim (Int.mul_eq_zero.mp (by omega)) id id
    obtain ⟨rfl, rfl, rfl, rfl⟩ := coordinates
    rfl

private theorem divisible_norm_difference (a b : Quad) (modulus : Int)
    (same : a.Congruent b modulus) : modulus ∣ a.norm - b.norm := by
  rcases same with ⟨⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩, ⟨u, hu⟩⟩
  refine ⟨r * (a.first + b.first) + s * (a.second + b.second) +
    t * (a.third + b.third) + u * (a.fourth + b.fourth), ?_⟩
  have h₁ := congrArg (fun x : Int => x * (a.first + b.first)) hr
  have h₂ := congrArg (fun x : Int => x * (a.second + b.second)) hs
  have h₃ := congrArg (fun x : Int => x * (a.third + b.third)) ht
  have h₄ := congrArg (fun x : Int => x * (a.fourth + b.fourth)) hu
  unfold norm
  simp only [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg, Int.mul_comm, Int.mul_left_comm] at *
  omega

/-- Shrink any represented multiple m·p with 1 < m that does not divide p.
This is the arithmetic descent. The prime case uses it by recursion on m. -/
theorem descend (a : Quad) (m p : Int) (greater : 1 < m) (noDivisor : ¬ m ∣ p)
    (represents : a.norm = m * p) : ∃ k : Int, 0 < k ∧ k < m ∧ ∃ next : Quad, next.norm = k * p := by
  by_cases even : m % 2 = 0
  · have split : 2 * (m / 2) = m := by omega
    obtain ⟨half, halfNorm⟩ := a.halve (by rw [represents, Int.mul_emod, even]; simp)
    refine ⟨m / 2, by omega, by omega, half, ?_⟩
    apply Int.eq_of_mul_eq_mul_left (a := 2) (by decide)
    calc
      2 * half.norm = a.norm := halfNorm
      _ = m * p := represents
      _ = 2 * (m / 2 * p) := by rw [← Int.mul_assoc, split]
  · have odd : m % 2 = 1 := by omega
    let b := a.center m
    have related : a.Congruent b m := center_congruent a m
    have bDivides : m ∣ b.norm := by
      obtain ⟨difference, difference_eq⟩ := divisible_norm_difference a b m related
      refine ⟨p - difference, ?_⟩
      rw [Int.mul_sub, ← represents, ← difference_eq]
      omega
    have bPositive : 0 < b.norm := by
      have nonnegative := norm_nonnegative b
      by_cases vanished : b.norm = 0
      · exfalso
        apply noDivisor
        have bZero := norm_zero_coordinates b vanished
        rw [bZero] at related
        rcases related with ⟨⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩, ⟨u, hu⟩⟩
        let roots : Quad := ⟨r, s, t, u⟩
        have scaled : roots.scale m = a := by
          cases a
          simpa [roots, scale, Quad.mk.injEq] using And.intro hr.symm (And.intro hs.symm (And.intro ht.symm hu.symm))
        have normEq := congrArg norm scaled
        rw [norm_scale, represents, Int.mul_assoc] at normEq
        exact ⟨roots.norm, (Int.eq_of_mul_eq_mul_left (by omega) normEq).symm⟩
      · omega
    obtain ⟨k, bNorm⟩ := bDivides
    have kPositive : 0 < k := by
      refine Int.lt_of_mul_lt_mul_left (a := m) ?_ (by omega)
      rw [Int.mul_zero, ← bNorm]
      exact bPositive
    have kSmaller : k < m := by
      refine Int.lt_of_mul_lt_mul_left (a := m) ?_ (by omega)
      rw [← bNorm]
      exact center_norm_lt a m (by omega) odd
    obtain ⟨next, scaled⟩ := product_dvd_of_congruent a b m related ⟨k, bNorm⟩
    have norms := congrArg norm scaled
    rw [norm_scale, norm_product, represents, bNorm] at norms
    refine ⟨k, kPositive, kSmaller, next, ?_⟩
    apply Int.eq_of_mul_eq_mul_left (a := m * m) (by exact Int.ne_of_gt (Int.mul_pos (by omega) (by omega)))
    calc
      _ = (m * p) * (m * k) := norms
      _ = _ := by ac_rfl

end Quad
end Thesis.Probability.FourSquareNorm
