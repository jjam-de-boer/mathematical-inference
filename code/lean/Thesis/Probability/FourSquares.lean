import Thesis.Probability.FourSquarePrime

namespace Thesis.Probability.FourSquareNorm

/-!
# Constructive four-square existence

Bounded divisibility searches split a natural number into smaller factors
or certify that it has only prime divisors. Euler's product identity combines
representations of the factors. For an odd prime, the finite residue search
provides an initial small positive multiplier and descent removes it.
Taking absolute values gives natural witnesses. This stays in the explicit
finite arithmetic used by the rational-bound encoding.
-/

private theorem prime_norm (p : Nat) (greater : 1 < p) (prime : HasOnlyPrimeDivisors p) :
    ∃ quadruple : Quad, quadruple.norm = (p : Int) := by
  by_cases even : p % 2 = 0
  · rcases prime 2 (Nat.dvd_iff_mod_eq_zero.mpr even) with excluded | pIsTwo
    · exact False.elim (by omega)
    · subst p
      exact ⟨⟨1, 1, 0, 0⟩, by decide⟩
  · have odd : p % 2 = 1 := by omega
    obtain ⟨m, mPos, mBound, quad, represented⟩ := odd_prime_multiple p greater odd prime
    have reduce (m : Nat) : 0 < m → m < p → (∃ q : Quad, q.norm = (m : Int) * p) →
        ∃ q : Quad, q.norm = (p : Int) := by
      induction m using Nat.strongRecOn with
      | ind m ih =>
        rintro positive bound ⟨q, multiple⟩
        by_cases one : m = 1
        · subst m
          exact ⟨q, by simpa only [Int.natCast_one, Int.one_mul] using multiple⟩
        · have notDvd : ¬ (m : Int) ∣ (p : Int) := by
            intro divides
            rcases prime m (Int.ofNat_dvd.mp divides) with otherOne | full
            · exact one otherOne
            · omega
          obtain ⟨k, kPositive, smaller, next, nextEq⟩ := q.descend m p (by omega) notDvd multiple
          have kNat : (k.toNat : Int) = k := Int.toNat_of_nonneg (by omega)
          have kBound : k.toNat < m := by omega
          exact ih k.toNat kBound (by omega) (by omega) ⟨next, by rw [kNat]; exact nextEq⟩
    exact reduce m mPos mBound ⟨quad, represented⟩

private theorem natural_norm (n : Nat) : ∃ quadruple : Quad, quadruple.norm = (n : Int) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n < 2
    · exact ⟨⟨n, 0, 0, 0⟩, by have choices : n = 0 ∨ n = 1 := by omega
                              rcases choices with rfl | rfl <;> decide⟩
    · if proper : ∃ d : Fin n, 1 < d.val ∧ d.val ∣ n then
        obtain ⟨factor, nontrivial, cofactor, prod⟩ := proper
        have factorBound := factor.isLt
        have positive : 0 < cofactor := by
          cases cofactor with
          | zero => simp only [Nat.mul_zero] at prod; omega
          | succ _ => omega
        have cofactorBound : cofactor < n := by
          have doubled : 2 * cofactor ≤ factor.val * cofactor := Nat.mul_le_mul_right _ (by omega)
          omega
        obtain ⟨a, normA⟩ := ih factor.val factorBound
        obtain ⟨b, normB⟩ := ih cofactor cofactorBound
        refine ⟨a.product b, ?_⟩
        rw [Quad.norm_product, normA, normB, ← Int.natCast_mul, ← prod]
      else
        have prime : HasOnlyPrimeDivisors n := by
          intro d divides
          have bound := Nat.le_of_dvd (show 0 < n by omega) divides
          have positive : 0 < d := by
            cases d with
            | zero => obtain ⟨_, impossible⟩ := divides; simp only [Nat.zero_mul] at impossible; omega
            | succ _ => omega
          by_cases one : d = 1
          · exact .inl one
          · by_cases full : d = n
            · exact .inr full
            · exact (proper ⟨⟨d, by omega⟩, (show 1 < d by omega), divides⟩).elim
        exact prime_norm n (by omega) prime

/-- Every natural number is a sum of four natural squares. The certificate
is propositional and comes from bounded searches and integer descent. -/
theorem exists_natural_squares (n : Nat) : ∃ a b c d : Nat, a*a + b*b + c*c + d*d = n := by
  obtain ⟨q, normEq⟩ := natural_norm n
  refine ⟨q.first.natAbs, q.second.natAbs, q.third.natAbs, q.fourth.natAbs, ?_⟩
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_add, Int.natAbs_mul_self]
  exact normEq

end Thesis.Probability.FourSquareNorm
