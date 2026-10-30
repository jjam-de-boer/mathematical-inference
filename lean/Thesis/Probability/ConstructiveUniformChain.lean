import Thesis.Probability.ConstructiveUniformDerivative
import Thesis.Probability.ConstructiveRealUniformBounds

namespace Thesis.Probability.ConstructiveReal.UniformDerivativeWithin
open ConstructiveReal

private def commonRadius (first second : PositiveRatio) : PositiveRatio :=
  if PositiveRatio.LE first second then first else second
private theorem commonRadius_bounds (first second : PositiveRatio) :
    PositiveRatio.LE (commonRadius first second) first ∧ PositiveRatio.LE (commonRadius first second) second := by
  by_cases ordered : PositiveRatio.LE first second
  · simp only [commonRadius, if_pos ordered]; exact ⟨PositiveRatio.le_refl _, ordered⟩
  · simp only [commonRadius, if_neg ordered]
    exact ⟨(PositiveRatio.le_total first second).resolve_left ordered, PositiveRatio.le_refl _⟩

/-- The uniform derivative and a uniform signed slope bound give one local
Lipschitz constant over the whole explicit domain. This is derived from the
remainder certificate rather than assumed as separate path behavior. -/
theorem local_within_uniform {domain : ConstructiveReal → Prop} {f slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f slope) (count : Nat)
    (bounded : ∀ x hx precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE ((slope x hx).rationalApproximation.value precision).magnitude (QProb.ofNat count))
    (radius : PositiveRatio) (small : PositiveRatio.LE radius (derivative.modulus PositiveRatio.one))
    (x : ConstructiveReal) (hx : domain x) (y : ConstructiveReal) (hy : domain y) (close : Within radius.toQProb x y) :
    Within (QProb.mul radius.toQProb (QProb.ofNat (count + 1))) (f y hy) (f x hx) := by
  have product := (within_congr (equiv_refl _) (zero_mul (slope x hx))).mp
    (within_mul_right_uniform count (within_increment close) (bounded x hx))
  have translated := (within_congr (equiv_refl _) (add_zero (f x hx))).mp
    ((within_add_left_iff _ (f x hx) _ _).mpr product)
  have estimate := within_triangle (derivative.remainder PositiveRatio.one radius small x hx y hy close) translated
  have collected : QProb.Equiv
      (QProb.add (QProb.mul PositiveRatio.one.toQProb radius.toQProb) (QProb.mul radius.toQProb (QProb.ofNat count)))
      (QProb.mul radius.toQProb (QProb.ofNat (count + 1))) := by
    simp only [QProb.Equiv, QProb.mul, QProb.add, QProb.ofNat, PositiveRatio.one, PositiveRatio.toQProb,
      Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul]
    ac_rfl
  exact within_mono estimate (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

/-- General effective uniform composition on explicit domains. Slope bounds
are quantitative data, not an inferred compactness principle or decidable
real-order test. Signed and zero slopes are admitted on both sides. -/
def chainWithin {source target : ConstructiveReal → Prop}
    {f sf : ∀ x, source x → ConstructiveReal} {g sg : ∀ x, target x → ConstructiveReal}
    (first : UniformDerivativeWithin source f sf) (second : UniformDerivativeWithin target g sg)
    (admitted : ∀ x hx, target (f x hx)) (innerSize outerSize : Nat)
    (innerBounded : ∀ x hx precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE ((sf x hx).rationalApproximation.value precision).magnitude (QProb.ofNat innerSize))
    (outerBounded : ∀ x hx precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE ((sg x hx).rationalApproximation.value precision).magnitude (QProb.ofNat outerSize)) :
    UniformDerivativeWithin source (fun x hx => g (f x hx) (admitted x hx))
      (fun x hx => mul (sf x hx) (sg (f x hx) (admitted x hx))) where
  congr x y hx hy same := second.congr _ _ _ _ (first.congr x y hx hy same)
  modulus epsilon :=
    let l := innerSize + 1
    let m := outerSize + 1
    let inner := epsilon.half.divideNat m (Nat.zero_lt_succ _)
    let outer := epsilon.half.divideNat l (Nat.zero_lt_succ _)
    commonRadius (first.modulus PositiveRatio.one)
      (commonRadius (first.modulus inner) ((second.modulus outer).divideNat l (Nat.zero_lt_succ _)))
  remainder epsilon radius small x hx y hy close := by
    let l := innerSize + 1
    let m := outerSize + 1
    let inner := epsilon.half.divideNat m (Nat.zero_lt_succ _)
    let outer := epsilon.half.divideNat l (Nat.zero_lt_succ _)
    let rho := PositiveRatio.mul radius (PositiveRatio.ofNat l (Nat.zero_lt_succ _))
    have firstBounds := commonRadius_bounds (first.modulus PositiveRatio.one)
      (commonRadius (first.modulus inner) ((second.modulus outer).divideNat l (Nat.zero_lt_succ _)))
    have secondBounds := commonRadius_bounds (first.modulus inner) ((second.modulus outer).divideNat l (Nat.zero_lt_succ _))
    have threshold := PositiveRatio.le_trans small firstBounds.2
    have inputChange := first.local_within_uniform innerSize innerBounded radius
      (PositiveRatio.le_trans small firstBounds.1) x hx y hy close
    have imageSmall : PositiveRatio.LE rho (second.modulus outer) :=
      QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.divide_mul (second.modulus outer) l (Nat.zero_lt_succ _))
        (QProb.mul_le_mul (PositiveRatio.le_trans threshold secondBounds.2) (QProb.le_refl (QProb.ofNat l)))
    have outerRemainder := second.remainder outer rho imageSmall _ (admitted x hx) _ (admitted y hy) (within_symm inputChange)
    have innerRemainder := first.remainder inner radius (PositiveRatio.le_trans threshold secondBounds.1) x hx y hy close
    have increment := (within_congr (equiv_refl _) (add_sub_cancel (f x hx) (mul (sub y x) (sf x hx)))).mp
      ((within_sub_right_iff _ (f x hx) _ _).mpr innerRemainder)
    have enlargedBound (precision : PositiveRatio) (fine : PositiveRatio.LE precision PositiveRatio.one) :
        QProb.LE ((sg (f x hx) (admitted x hx)).rationalApproximation.value precision).magnitude (QProb.ofNat m) :=
      QProb.le_trans (outerBounded _ _ precision fine) (by
        change outerSize * 1 ≤ (outerSize + 1) * 1
        omega)
    have scaled := within_mul_right_uniform m increment enlargedBound
    have translated := (within_add_left_iff _ (g (f x hx) (admitted x hx)) _ _).mpr scaled
    have linear : Equiv (ConstructiveReal.add (g (f x hx) (admitted x hx))
        (mul (mul (sub y x) (sf x hx)) (sg (f x hx) (admitted x hx))))
      (ConstructiveReal.add (g (f x hx) (admitted x hx)) (mul (sub y x) (mul (sf x hx) (sg (f x hx) (admitted x hx))))) :=
      add_congr (equiv_refl _) (mul_assoc _ _ _)
    have estimate := within_triangle outerRemainder ((within_congr (equiv_refl _) linear).mp translated)
    have innerError : QProb.Equiv (QProb.mul (QProb.mul inner.toQProb radius.toQProb) (QProb.ofNat m))
        (QProb.mul epsilon.half.toQProb radius.toQProb) := by
      simp only [inner, PositiveRatio.divideNat, PositiveRatio.toQProb, QProb.Equiv, QProb.mul, QProb.ofNat, Nat.mul_one]
      ac_rfl
    have outerError : QProb.Equiv (QProb.mul outer.toQProb rho.toQProb) (QProb.mul epsilon.half.toQProb radius.toQProb) := by
      simp only [outer, rho, PositiveRatio.mul, PositiveRatio.ofNat, PositiveRatio.divideNat, PositiveRatio.toQProb, QProb.Equiv, QProb.mul, Nat.mul_one]
      ac_rfl
    have collected := QProb.equiv_trans (QProb.add_congr outerError innerError)
      (QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _)) (QProb.mul_congr epsilon.half_sum (QProb.equiv_refl _)))
    exact within_mono estimate (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal.UniformDerivativeWithin
