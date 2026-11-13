import Thesis.Probability.RationalExponentialContinuity
import Thesis.Probability.RationalPolynomialExpression

namespace Thesis.Probability.RationalTaylorExponential
open SignedRatio RationalGeometricSeries

private theorem block_mul (terms : Nat → SignedRatio) (factor : SignedRatio) (start count : Nat) :
    Equiv (block (fun n => mul factor (terms n)) start count) (mul factor (block terms start count)) := by
  induction count generalizing start with
  | zero => exact equiv_symm (mul_zero _)
  | succ count ih => exact equiv_trans (add_congr (equiv_refl _) (ih (start + 1))) (equiv_symm (mul_add _ _ _))

/-- First-order remainder of one Taylor coefficient, before taking limits. -/
def firstRemainder (a b : SignedRatio) (n : Nat) : SignedRatio :=
  sub (sub (term b (n + 1)) (term a (n + 1))) (mul (sub b a) (term a n))

private theorem term_first (x : SignedRatio) : Equiv (term x 1) x := by
  simp only [term, Equiv, mul, one, divideNat, Nat.mul_one, Int.mul_one, Nat.zero_add]

theorem firstRemainder_zero (a b : SignedRatio) : Equiv (firstRemainder a b 0) zero := by
  apply equiv_trans (add_congr (add_congr (term_first b) (neg_congr (term_first a))) (neg_congr (mul_one (sub b a))))
  exact (sub_equiv_zero_iff _ _).mpr (equiv_refl _)

private abbrev Expr := RationalPolynomial.Expression 6
private def aVar : Expr := .coordinate 0
private def bVar : Expr := .coordinate 1
private def uVar : Expr := .coordinate 2
private def vVar : Expr := .coordinate 3
private def wVar : Expr := .coordinate 4
private def zVar : Expr := .coordinate 5
private def hVar : Expr := .sub bVar aVar
private def numeratorLeft : Expr :=
  .sub (.sub (.mul bVar uVar) (.mul aVar vVar))
    (.mul (.add zVar (.constant one)) (.mul hVar vVar))
private def numeratorRight : Expr :=
  .add (.add (.mul bVar (.sub (.sub uVar vVar) (.mul hVar wVar))) (.mul (.mul hVar hVar) wVar))
    (.mul hVar (.sub (.mul aVar wVar) (.mul zVar vVar)))

/-- A finite universal polynomial check; its variables remain arbitrary signed
rationals. This avoids expanding the denominators of complete Taylor terms. -/
private theorem numerator_identity (a b u v w z : SignedRatio) :
    Equiv (sub (sub (mul b u) (mul a v)) (mul (add z one) (mul (sub b a) v)))
      (add (add (mul b (sub (sub u v) (mul (sub b a) w))) (mul (mul (sub b a) (sub b a)) w))
        (mul (sub b a) (sub (mul a w) (mul z v)))) := by
  let values : Fin 6 → SignedRatio := fun index => match index.val with
    | 0 => a | 1 => b | 2 => u | 3 => v | 4 => w | _ => z
  exact RationalPolynomial.Expression.equalityCheck_sound numeratorLeft numeratorRight (by decide +kernel) values

private def natValue (n : Nat) : SignedRatio := (QProb.ofNat n).toSignedRatio

private theorem natValue_add_one (n : Nat) : Equiv (natValue (n + 1)) (add (natValue n) one) := by
  simp only [natValue, QProb.ofNat, QProb.toSignedRatio, Equiv, add, one, Nat.mul_one, Int.mul_one, Int.natCast_add, Int.natCast_one]

private theorem scale_as_product (value : SignedRatio) (n : Nat) : Equiv (scaleNat n value) (mul (natValue n) value) := by
  simp only [Equiv, scaleNat, mul, natValue, QProb.ofNat, QProb.toSignedRatio, Nat.one_mul]

private theorem divide_scaled (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    Equiv (divideNat (scaleNat n value) n positive) value := by
  simp only [Equiv, scaleNat, divideNat, Int.natCast_mul]
  ac_rfl

private theorem scaled_divide (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    Equiv (scaleNat n (divideNat value n positive)) value := by
  simp only [Equiv, scaleNat, divideNat, Int.natCast_mul]
  ac_rfl

private theorem divide_sub (first second : SignedRatio) (n : Nat) (positive : 0 < n) :
    Equiv (sub (divideNat first n positive) second) (divideNat (sub first (scaleNat n second)) n positive) :=
  equiv_trans (add_congr (equiv_refl _) (neg_congr (equiv_symm (divide_scaled second n positive))))
    (equiv_symm (divideNat_add _ _ _ _))

/-- Exact finite recurrence for the first-order Taylor remainder. -/
theorem firstRemainder_step (a b : SignedRatio) (n : Nat) :
    Equiv (firstRemainder a b (n + 1))
      (divideNat (add (mul b (firstRemainder a b n)) (mul (mul (sub b a) (sub b a)) (term a n)))
        (n + 2) (Nat.zero_lt_succ _)) := by
  let u := term b (n + 1)
  let v := term a (n + 1)
  let w := term a n
  let h := sub b a
  let z := natValue (n + 1)
  have combined : Equiv (firstRemainder a b (n + 1))
      (divideNat (sub (sub (mul b u) (mul a v)) (scaleNat (n + 2) (mul h v))) (n + 2) (Nat.zero_lt_succ _)) :=
    equiv_trans (add_congr (equiv_symm (divideNat_add _ _ _ _)) (equiv_refl _)) (divide_sub _ _ _ _)
  have scalar : Equiv (scaleNat (n + 2) (mul h v)) (mul (add z one) (mul h v)) :=
    equiv_trans (scale_as_product _ _) (mul_congr (natValue_add_one (n + 1)) (equiv_refl _))
  have recurrence : Equiv (mul z v) (mul a w) :=
    equiv_trans (equiv_symm (scale_as_product v (n + 1))) (scaled_divide (mul a w) (n + 1) (Nat.zero_lt_succ _))
  have vanished : Equiv (mul h (sub (mul a w) (mul z v))) zero :=
    equiv_trans (mul_congr (equiv_refl _) ((sub_equiv_zero_iff _ _).mpr (equiv_symm recurrence))) (mul_zero h)
  have numerator := equiv_trans (add_congr (equiv_refl _) (neg_congr scalar))
    (equiv_trans (numerator_identity a b u v w z) (equiv_trans (add_congr (equiv_refl _) vanished) (add_zero _)))
  exact equiv_trans combined (divideNat_congr numerator _ _)

/-- The exact quadratic factor `|b-a|²/2` in a first-order remainder. -/
def quadraticError (a b : SignedRatio) : QProb :=
  QProb.mul (QProb.mul (sub b a).magnitude (sub b a).magnitude) ⟨1, 2, by decide⟩

private theorem swap_factors (a b c : QProb) : QProb.Equiv (QProb.mul a (QProb.mul b c)) (QProb.mul b (QProb.mul a c)) :=
  QProb.equiv_trans (QProb.equiv_symm (QProb.mul_assoc _ _ _))
    (QProb.equiv_trans (QProb.mul_congr (QProb.mul_comm _ _) (QProb.equiv_refl _)) (QProb.mul_assoc _ _ _))

private theorem coefficient_absorb (bound n : Nat) :
    QProb.Equiv (QProb.mul (QProb.ofNat bound) (coefficient bound n))
      (QProb.mul (QProb.ofNat (n + 1)) (coefficient bound (n + 1))) := by
  simp only [QProb.Equiv, QProb.mul, QProb.ofNat, coefficient, factorial, Nat.pow_succ, Nat.one_mul]
  ac_rfl

private theorem scalar_collect (n : Nat) :
    QProb.Equiv (QProb.mul (QProb.add (QProb.mul (⟨1, 2, by decide⟩ : QProb) (QProb.ofNat (n + 1))) QProb.one)
      ⟨1, n + 3, Nat.zero_lt_succ _⟩) (⟨1, 2, by decide⟩ : QProb) := by
  simp only [QProb.Equiv, QProb.mul, QProb.add, QProb.ofNat, QProb.one, Nat.mul_one, Nat.one_mul, Nat.mul_two]
  omega

private theorem half_coefficient_collect (bound n : Nat) :
    QProb.Equiv
      (QProb.mul (QProb.add (QProb.mul (QProb.ofNat bound) (QProb.mul ⟨1, 2, by decide⟩ (coefficient bound n)))
        (coefficient bound (n + 1))) ⟨1, n + 3, Nat.zero_lt_succ _⟩)
      (QProb.mul ⟨1, 2, by decide⟩ (coefficient bound (n + 1))) := by
  have first : QProb.Equiv (QProb.mul (QProb.ofNat bound) (QProb.mul ⟨1, 2, by decide⟩ (coefficient bound n)))
      (QProb.mul (QProb.mul ⟨1, 2, by decide⟩ (QProb.ofNat (n + 1))) (coefficient bound (n + 1))) :=
    QProb.equiv_trans (swap_factors _ _ _)
      (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) (coefficient_absorb bound n)) (QProb.equiv_symm (QProb.mul_assoc _ _ _)))
  have factored := QProb.equiv_trans (QProb.add_congr first (QProb.equiv_symm (QProb.one_mul _)))
    (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
  exact QProb.equiv_trans (QProb.mul_congr factored (QProb.equiv_refl _))
    (QProb.equiv_trans (QProb.mul_assoc _ _ _)
      (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) (QProb.mul_comm _ _))
        (QProb.equiv_trans (QProb.equiv_symm (QProb.mul_assoc _ _ _)) (QProb.mul_congr (scalar_collect n) (QProb.equiv_refl _)))))

private theorem quadratic_collect (error : QProb) (bound n : Nat) :
    QProb.Equiv
      (QProb.mul
        (QProb.add (QProb.mul (QProb.ofNat bound) (QProb.mul (QProb.mul error ⟨1, 2, by decide⟩) (coefficient bound n)))
          (QProb.mul error (coefficient bound (n + 1))))
        ⟨1, n + 3, Nat.zero_lt_succ _⟩)
      (QProb.mul (QProb.mul error ⟨1, 2, by decide⟩) (coefficient bound (n + 1))) := by
  have first : QProb.Equiv
      (QProb.mul (QProb.ofNat bound) (QProb.mul (QProb.mul error ⟨1, 2, by decide⟩) (coefficient bound n)))
      (QProb.mul error (QProb.mul (QProb.ofNat bound) (QProb.mul ⟨1, 2, by decide⟩ (coefficient bound n)))) :=
    QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) (QProb.mul_assoc _ _ _)) (swap_factors _ _ _)
  have factored : QProb.Equiv
      (QProb.add (QProb.mul (QProb.ofNat bound) (QProb.mul (QProb.mul error ⟨1, 2, by decide⟩) (coefficient bound n)))
        (QProb.mul error (coefficient bound (n + 1))))
      (QProb.mul error (QProb.add (QProb.mul (QProb.ofNat bound) (QProb.mul ⟨1, 2, by decide⟩ (coefficient bound n)))
        (coefficient bound (n + 1)))) :=
    QProb.equiv_trans (QProb.add_congr first (QProb.equiv_refl _)) (QProb.equiv_symm (QProb.mul_add_distrib _ _ _))
  exact QProb.equiv_trans (QProb.mul_congr factored (QProb.equiv_refl _))
    (QProb.equiv_trans (QProb.mul_assoc _ _ _) (QProb.equiv_trans
      (QProb.mul_congr (QProb.equiv_refl _) (half_coefficient_collect bound n)) (QProb.equiv_symm (QProb.mul_assoc _ _ _))))

/-- Every finite Taylor coefficient has a quadratic first-order remainder
bound on a bounded rational interval, derived before any analytic derivative
or exponential addition law is assumed. -/
theorem firstRemainder_bound (a b : SignedRatio) (bound : Nat)
    (boundedA : QProb.LE a.magnitude (QProb.ofNat bound)) (boundedB : QProb.LE b.magnitude (QProb.ofNat bound)) (n : Nat) :
    QProb.LE (firstRemainder a b (n + 1)).magnitude (QProb.mul (quadraticError a b) (coefficient bound n)) := by
  induction n with
  | zero =>
      have same : Equiv (firstRemainder a b 1) (divideNat (mul (sub b a) (sub b a)) 2 (by decide)) :=
        equiv_trans (firstRemainder_step a b 0)
          (divideNat_congr (equiv_trans
            (add_congr (equiv_trans (mul_congr (equiv_refl _) (firstRemainder_zero a b)) (mul_zero b)) (mul_one _))
            (zero_add _)) _ _)
      have size : QProb.Equiv (firstRemainder a b 1).magnitude (quadraticError a b) :=
        QProb.equiv_trans (magnitude_congr same)
          (QProb.equiv_trans (magnitude_divideNat _ _ _) (QProb.mul_congr (magnitude_mul _ _) (QProb.equiv_refl _)))
      exact QProb.le_congr (QProb.equiv_symm size) (QProb.equiv_symm (QProb.mul_one _)) (QProb.le_refl _)
  | succ n ih =>
      have first := QProb.le_congr (QProb.equiv_symm (magnitude_mul b (firstRemainder a b (n + 1)))) (QProb.equiv_refl _)
        (QProb.mul_le_mul boundedB ih)
      have second := QProb.le_congr (QProb.equiv_symm (QProb.equiv_trans (magnitude_mul _ _)
        (QProb.mul_congr (magnitude_mul _ _) (QProb.equiv_refl _)))) (QProb.equiv_refl _)
        (QProb.mul_le_mul (QProb.le_refl (QProb.mul (sub b a).magnitude (sub b a).magnitude))
          (term_coefficient_bound a bound boundedA (n + 1)))
      have estimate := QProb.mul_le_mul (QProb.le_trans (magnitude_add _ _) (QProb.add_le_add first second))
        (QProb.le_refl (⟨1, n + 3, Nat.zero_lt_succ _⟩ : QProb))
      have same := QProb.equiv_trans (magnitude_congr (firstRemainder_step a b (n + 1))) (magnitude_divideNat _ _ _)
      exact QProb.le_congr (QProb.equiv_symm same) (quadratic_collect _ bound n) estimate

/-- The derivative polynomial has one fewer term than the Taylor polynomial.
This finite convention avoids assigning a value to a negative truncation. -/
def partialRemainder (a b : SignedRatio) (count : Nat) : SignedRatio :=
  sub (sub (RationalGeometricSeries.partialSum (term b) (count + 1)) (RationalGeometricSeries.partialSum (term a) (count + 1)))
    (mul (sub b a) (RationalGeometricSeries.partialSum (term a) count))

open RationalGeometricSeries

theorem partialRemainder_terms (a b : SignedRatio) (count : Nat) :
    Equiv (partialRemainder a b count) (block (firstRemainder a b) 0 count) := by
  have shifted := block_shift (fun n => sub (term b n) (term a n)) 1 0 count
  simp only [Nat.add_comm 1] at shifted
  have difference : Equiv (sub (partialSum (term b) (count + 1)) (partialSum (term a) (count + 1)))
      (block (fun n => sub (term b (n + 1)) (term a (n + 1))) 0 count) :=
    equiv_trans (block_sub (term b) (term a) 0 (count + 1))
      (equiv_trans (add_congr ((sub_equiv_zero_iff one one).mpr (equiv_refl _)) (equiv_symm shifted)) (zero_add _))
  exact equiv_trans (add_congr difference (neg_congr (equiv_symm (block_mul (term a) (sub b a) 0 count))))
    (block_sub _ _ 0 count)

/-- Every Taylor polynomial has a quadratic first-order remainder with one
common explicit bound over the rational interval. This is a finite theorem;
the derivative of the completed real exponential requires passage to limits. -/
theorem partialRemainder_bound (a b : SignedRatio) (bound : Nat)
    (boundedA : QProb.LE a.magnitude (QProb.ofNat bound)) (boundedB : QProb.LE b.magnitude (QProb.ofNat bound)) (count : Nat) :
    QProb.LE (partialRemainder a b count).magnitude (QProb.mul (quadraticError a b) (QProb.ofNat (uniformSumBound bound))) := by
  cases count with
  | zero =>
      exact QProb.le_congr (QProb.equiv_symm (magnitude_congr (partialRemainder_terms a b 0))) (QProb.equiv_refl _) (QProb.zero_le _)
  | succ count =>
      have shifted := block_shift (firstRemainder a b) 1 0 count
      simp only [Nat.add_comm 1] at shifted
      have same : Equiv (partialRemainder a b (count + 1)) (block (fun n => firstRemainder a b (n + 1)) 0 count) :=
        equiv_trans (partialRemainder_terms a b (count + 1))
          (equiv_trans (add_congr (firstRemainder_zero a b) (equiv_symm shifted)) (zero_add _))
      have estimate := block_magnitude (fun n => firstRemainder a b (n + 1))
        (fun n => QProb.mul (quadraticError a b) (coefficient bound n)) (firstRemainder_bound a b bound boundedA boundedB) 0 count
      have collected := QProb.le_congr (QProb.equiv_refl _) (normSum_mul (coefficient bound) (quadraticError a b) 0 count) estimate
      exact QProb.le_congr (QProb.equiv_symm (magnitude_congr same)) (QProb.equiv_refl _)
        (QProb.le_trans collected (QProb.mul_le_mul (QProb.le_refl _) (coefficient_sum_bound bound count)))

end Thesis.Probability.RationalTaylorExponential
