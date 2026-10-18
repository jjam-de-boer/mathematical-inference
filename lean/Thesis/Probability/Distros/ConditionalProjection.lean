import Thesis.Probability.Distros.ConditionalAlgebra

namespace Thesis.Probability.SignedRatio

theorem sub_zero (a : SignedRatio) : Equiv (sub a zero) a := add_zero a

theorem sub_split (a b c : SignedRatio) : Equiv (sub a c) (add (sub a b) (sub b c)) := by
  apply equiv_symm
  simp only [Equiv, sub, add, neg, Int.natCast_mul, Int.mul_add, Int.mul_neg,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

theorem add_sub_cancel_left (a b : SignedRatio) : Equiv (sub (add a b) a) b := by
  simp only [Equiv, sub, add, neg, Int.natCast_mul, Int.add_mul, Int.mul_add, Int.neg_mul,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

theorem le_add_of_nonnegative (a b : SignedRatio) (positive : Nonnegative b) : LE a (add a b) :=
  (nonnegative_congr (add_sub_cancel_left a b)).mpr positive

theorem square_add (a b : SignedRatio) :
    Equiv (mul (add a b) (add a b))
      (add (add (mul a a) (mul b b)) (add (mul a b) (mul a b))) := by
  refine equiv_trans (add_mul a b (add a b)) ?_
  refine equiv_trans (add_congr (mul_add a a b) (mul_add b a b)) ?_
  refine equiv_trans (add_congr (equiv_refl _) (add_congr (mul_comm b a) (equiv_refl _))) ?_
  refine equiv_trans (add_congr (equiv_refl _) (add_comm _ _)) ?_
  exact add_interchange _ _ _ _

theorem square_sub_split (a b c : SignedRatio) :
    Equiv (mul (sub a c) (sub a c))
      (add (add (mul (sub a b) (sub a b)) (mul (sub b c) (sub b c)))
        (add (mul (sub a b) (sub b c)) (mul (sub a b) (sub b c)))) :=
  equiv_trans (mul_congr (sub_split a b c) (sub_split a b c)) (square_add _ _)

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.Distros

/-- Nonnegative responses have nonnegative rational integrals. Arbitrary
response values at zero-weight occurrences remain immaterial. -/
theorem rationalAtomSum_nonnegative (atoms : List (Ω × Nat)) (f : Ω → SignedRatio)
    (positive : ∀ atom ∈ atoms, 0 < atom.2 → SignedRatio.Nonnegative (f atom.1)) :
    SignedRatio.Nonnegative (FiniteProbRecord.rationalAtomSum atoms f) := by
  induction atoms with
  | nil => exact SignedRatio.nonnegative_zero
  | cons atom atoms ih =>
      change SignedRatio.Nonnegative (SignedRatio.add (SignedRatio.scaleNat atom.2 (f atom.1))
        (FiniteProbRecord.rationalAtomSum atoms f))
      apply SignedRatio.nonnegative_add
      · change 0 ≤ (atom.2 : Int) * (f atom.1).num
        by_cases zero : atom.2 = 0
        · simpa only [zero, Int.natCast_zero, Int.zero_mul] using (Int.le_refl 0)
        · exact Int.mul_nonneg (Int.natCast_nonneg _) (positive atom (List.mem_cons_self ..) (Nat.pos_of_ne_zero zero))
      · exact ih (fun other member => positive other (List.mem_cons_of_mem _ member))

theorem Distro.rationalExpectation_nonnegative (μ : Distro Ω) (f : Ω → SignedRatio)
    (positive : μ.AlmostSurely (fun x => SignedRatio.Nonnegative (f x))) :
    SignedRatio.Nonnegative (μ.rationalExpectation f) :=
  rationalAtomSum_nonnegative μ.record.atoms f positive

/-- Mean square loss between two rational response observables. -/
def Distro.rationalSquaredError (μ : Distro Ω) (f g : Ω → SignedRatio) : SignedRatio :=
  μ.rationalExpectation (fun x => SignedRatio.mul (SignedRatio.sub (f x) (g x)) (SignedRatio.sub (f x) (g x)))

theorem Distro.rationalSquaredError_nonnegative (μ : Distro Ω) (f g : Ω → SignedRatio) :
    SignedRatio.Nonnegative (μ.rationalSquaredError f g) :=
  μ.rationalExpectation_nonnegative _ (fun _ _ _ => SignedRatio.nonnegative_square _)

theorem Distro.rationalSquaredError_zero (μ : Distro Ω) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f (fun _ => SignedRatio.zero))
      (μ.rationalExpectation (fun x => SignedRatio.mul (f x) (f x))) :=
  μ.rationalExpectation_congr _ _ (fun x => SignedRatio.mul_congr (SignedRatio.sub_zero (f x)) (SignedRatio.sub_zero (f x)))

/-- Pythagorean decomposition of mean square error for every predictor
which depends only on the supplied finite evidence label. -/
theorem Distro.conditionalExpectation_squaredError (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (h : Fin colours → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f (fun x => h (key x)))
      (SignedRatio.add (μ.rationalSquaredError f (μ.conditionalExpectation key f))
        (μ.rationalSquaredError (μ.conditionalExpectation key f) (fun x => h (key x)))) := by
  let center := μ.conditionalExpectation key f
  let residual := fun x => SignedRatio.sub (f x) (center x)
  let bias := fun x => SignedRatio.sub (center x) (h (key x))
  let cross := fun x => SignedRatio.mul (residual x) (bias x)
  let gap := fun label => SignedRatio.sub
    (conditionalBlockMean (μ.record.atoms.filter (fun atom => decide (key atom.1 = label))) f) (h label)
  have vanished : SignedRatio.Equiv (μ.rationalExpectation cross) SignedRatio.zero :=
    SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _ (fun x => SignedRatio.mul_comm (residual x) (bias x)))
      (μ.conditionalExpectation_orthogonal key f gap)
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _
    (fun x => SignedRatio.square_sub_split (f x) (center x) (h (key x)))) ?_
  refine SignedRatio.equiv_trans (μ.rationalExpectation_add
    (fun x => SignedRatio.add (SignedRatio.mul (residual x) (residual x)) (SignedRatio.mul (bias x) (bias x)))
    (fun x => SignedRatio.add (cross x) (cross x))) ?_
  refine SignedRatio.equiv_trans (SignedRatio.add_congr
    (μ.rationalExpectation_add (fun x => SignedRatio.mul (residual x) (residual x)) (fun x => SignedRatio.mul (bias x) (bias x)))
    (SignedRatio.equiv_trans (μ.rationalExpectation_add cross cross) (SignedRatio.add_congr vanished vanished))) ?_
  exact SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.add_zero _)) (SignedRatio.add_zero _)

/-- The conditional mean minimizes squared error among all rational
predictors determined by the finite label. No support assumption on a label
is imposed and the original sample record is unchanged. -/
theorem Distro.conditionalExpectation_least_squares (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (h : Fin colours → SignedRatio) :
    SignedRatio.LE (μ.rationalSquaredError f (μ.conditionalExpectation key f))
      (μ.rationalSquaredError f (fun x => h (key x))) :=
  (SignedRatio.le_congr (SignedRatio.equiv_refl _) (μ.conditionalExpectation_squaredError key f h)).mpr
    (SignedRatio.le_add_of_nonnegative _ _ (μ.rationalSquaredError_nonnegative _ _))

/-- Conditional expectation contracts the squared rational norm. -/
theorem Distro.conditionalExpectation_square_contraction (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) :
    SignedRatio.LE (μ.rationalExpectation (fun x => SignedRatio.mul
      (μ.conditionalExpectation key f x) (μ.conditionalExpectation key f x)))
      (μ.rationalExpectation (fun x => SignedRatio.mul (f x) (f x))) := by
  have split := SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.rationalSquaredError_zero f))
    (SignedRatio.equiv_trans (μ.conditionalExpectation_squaredError key f (fun _ => SignedRatio.zero))
      (SignedRatio.add_congr (SignedRatio.equiv_refl _) (μ.rationalSquaredError_zero (μ.conditionalExpectation key f))))
  apply (SignedRatio.le_congr (SignedRatio.equiv_refl _) split).mpr
  apply (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _)).mpr
  exact SignedRatio.le_add_of_nonnegative _ _ (μ.rationalSquaredError_nonnegative _ _)

end Thesis.Probability.Distros
