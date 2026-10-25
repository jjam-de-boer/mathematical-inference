import Thesis.Probability.ConstructiveRealRationalScaling
import Thesis.Probability.ConstructiveRealReciprocal

namespace Thesis.Probability.ConstructiveReal

/-- A map that respects real-value equivalence and finite addition. No
continuity is postulated, so linearity is initially proved only on rationals. -/
structure AdditiveMap where
  value : ConstructiveReal → ConstructiveReal
  map_equiv : ∀ {x y}, Equiv x y → Equiv (value x) (value y)
  map_add : ∀ x y, Equiv (value (add x y)) (add (value x) (value y))

namespace AdditiveMap

theorem map_zero (f : AdditiveMap) : Equiv (f.value zero) zero := by
  let a := f.value zero
  have sum : Equiv (add a a) a :=
    equiv_trans (equiv_symm (f.map_add zero zero)) (f.map_equiv (add_zero zero))
  have canceled : Equiv (add a a) (add zero a) := equiv_trans sum (equiv_symm (zero_add a))
  exact ⟨(add_le_add_right_iff a zero a).mp canceled.1, (add_le_add_right_iff zero a a).mp canceled.2⟩

theorem map_neg (f : AdditiveMap) (x : ConstructiveReal) : Equiv (f.value (neg x)) (neg (f.value x)) :=
  neg_unique (f.value x) (f.value (neg x))
    (equiv_trans (equiv_symm (f.map_add x (neg x))) (equiv_trans (f.map_equiv (add_neg x)) f.map_zero))

theorem map_scaleNat (f : AdditiveMap) (x : ConstructiveReal) (n : Nat) :
    Equiv (f.value (scaleNat n x)) (scaleNat n (f.value x)) := by
  induction n with
  | zero => exact f.map_zero
  | succ n ih => exact equiv_trans (f.map_add (scaleNat n x) x) (add_congr ih (equiv_refl (f.value x)))

theorem map_natural (f : AdditiveMap) (n : Nat) :
    Equiv (f.value (ofSignedRatio (QProb.ofNat n).toSignedRatio))
      (mul (ofSignedRatio (QProb.ofNat n).toSignedRatio) (f.value one)) := by
  have input : Equiv (scaleNat n one) (ofSignedRatio (QProb.ofNat n).toSignedRatio) :=
    equiv_trans (scaleNat_mul n one) (mul_one _)
  exact equiv_trans (f.map_equiv (equiv_symm input)) (equiv_trans (f.map_scaleNat one n) (scaleNat_mul n (f.value one)))

theorem map_integer (f : AdditiveMap) (z : Int) :
    Equiv (f.value (ofSignedRatio ⟨z, 1, by decide⟩)) (mul (ofSignedRatio ⟨z, 1, by decide⟩) (f.value one)) := by
  cases z with
  | ofNat n => exact f.map_natural n
  | negSucc n =>
      let positive := ofSignedRatio (QProb.ofNat (n + 1)).toSignedRatio
      let negative := ofSignedRatio (⟨Int.negSucc n, 1, by decide⟩ : SignedRatio)
      have input : Equiv negative (neg positive) := equiv_symm (ofSignedRatio_neg (QProb.ofNat (n + 1)).toSignedRatio)
      have output : Equiv (neg (mul positive (f.value one))) (mul negative (f.value one)) :=
        equiv_trans (equiv_symm (neg_mul positive (f.value one))) (mul_congr (equiv_symm input) (equiv_refl (f.value one)))
      exact equiv_trans (f.map_equiv input) (equiv_trans (f.map_neg positive)
        (equiv_trans (neg_congr (f.map_natural (n + 1))) output))

/-- Additivity determines the value at every signed rational, including
unreduced fractions and zero numerators. Denominator cancellation uses its
supplied positive natural value, without choosing a real representative. -/
theorem map_rational (f : AdditiveMap) (q : SignedRatio) :
    Equiv (f.value (ofSignedRatio q)) (mul (ofSignedRatio q) (f.value one)) := by
  let denominator := ofSignedRatio (QProb.ofNat q.den).toSignedRatio
  have input : Equiv (scaleNat q.den (ofSignedRatio q)) (ofSignedRatio ⟨q.num, 1, by decide⟩) :=
    equiv_trans (scaleNat_mul q.den (ofSignedRatio q)) (equiv_trans (ofSignedRatio_mul _ _)
      ((ofSignedRatio_equiv_iff _ _).mpr (by
        simp only [SignedRatio.Equiv, SignedRatio.mul, QProb.toSignedRatio, QProb.ofNat,
          Int.natCast_one, Nat.one_mul, Int.mul_one]
        ac_rfl)))
  have numerator : Equiv (ofSignedRatio ⟨q.num, 1, by decide⟩) (mul denominator (ofSignedRatio q)) :=
    equiv_trans (equiv_symm input) (scaleNat_mul q.den (ofSignedRatio q))
  have compared : Equiv (mul denominator (f.value (ofSignedRatio q)))
      (mul denominator (mul (ofSignedRatio q) (f.value one))) :=
    equiv_trans (equiv_symm (scaleNat_mul q.den (f.value (ofSignedRatio q))))
      (equiv_trans (equiv_symm (f.map_scaleNat (ofSignedRatio q) q.den))
        (equiv_trans (f.map_equiv input) (equiv_trans (f.map_integer q.num)
          (equiv_trans (mul_congr numerator (equiv_refl (f.value one))) (mul_assoc denominator (ofSignedRatio q) (f.value one))))))
  let lower := PositiveRatio.ofNat q.den q.den_pos
  exact ⟨(mul_le_mul_positive_iff denominator lower (le_refl _) _ _).mp compared.1,
    (mul_le_mul_positive_iff denominator lower (le_refl _) _ _).mp compared.2⟩

end AdditiveMap
end Thesis.Probability.ConstructiveReal
