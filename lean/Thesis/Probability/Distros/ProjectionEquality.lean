import Thesis.Probability.Distros.ConditionalProjection
import Thesis.Probability.Distros.RationalChebyshev
import Thesis.Probability.Distros.PositiveSupport

namespace Thesis.Probability.SignedRatio

/-- Equality after adding a term characterizes that term's rational zero value. -/
theorem add_equiv_left_iff (a b : SignedRatio) : Equiv (add a b) a ↔ Equiv b zero := by
  constructor
  · intro same
    exact equiv_trans (equiv_symm (add_sub_cancel_left a b)) ((sub_equiv_zero_iff _ _).mpr same)
  · intro zero
    exact (sub_equiv_zero_iff _ _).mp (equiv_trans (add_sub_cancel_left a b) zero)

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.Distros

private theorem qprob_add_num_zero_iff (a b : QProb) :
    (QProb.add a b).num = 0 ↔ a.num = 0 ∧ b.num = 0 := by
  change a.num * b.den + b.num * a.den = 0 ↔ _
  constructor
  · intro zero
    have first : a.num * b.den = 0 := by omega
    have second : b.num * a.den = 0 := by omega
    constructor
    · rcases Nat.mul_eq_zero.mp first with vanished | impossible
      · exact vanished
      · have positive := b.den_pos; omega
    · rcases Nat.mul_eq_zero.mp second with vanished | impossible
      · exact vanished
      · have positive := a.den_pos; omega
  · rintro ⟨first, second⟩
    rw [first, second, Nat.zero_mul, Nat.zero_mul, Nat.zero_add]

/-- A nonnegative rational integral vanishes precisely on positive-weight atoms. -/
theorem rationalIntegral_num_zero_iff (atoms : List (Ω × Nat)) (f : Ω → QProb) :
    (rationalIntegral atoms f).num = 0 ↔ ∀ atom ∈ atoms, 0 < atom.2 → (f atom.1).num = 0 := by
  induction atoms with
  | nil =>
      constructor
      · intro _ atom member
        exact False.elim (List.not_mem_nil member)
      · intro _
        rfl
  | cons atom atoms ih =>
      constructor
      · intro zero
        have parts := (qprob_add_num_zero_iff (QProb.scale atom.2 (f atom.1)) (rationalIntegral atoms f)).mp zero
        intro other member weight
        rcases List.mem_cons.mp member with same | member
        · subst other
          have head := parts.1
          change atom.2 * (f atom.1).num = 0 at head
          rcases Nat.mul_eq_zero.mp head with impossible | vanished
          · omega
          · exact vanished
        · exact ih.mp parts.2 other member weight
      · intro zero
        apply (qprob_add_num_zero_iff _ _).mpr
        constructor
        · change atom.2 * (f atom.1).num = 0
          by_cases weight : atom.2 = 0
          · rw [weight, Nat.zero_mul]
          · rw [zero atom (List.mem_cons_self ..) (Nat.pos_of_ne_zero weight), Nat.mul_zero]
        · exact ih.mpr (fun other member => zero other (List.mem_cons_of_mem _ member))

theorem Distro.expectation_num_zero_iff (μ : Distro Ω) (f : Ω → QProb) :
    (μ.expectation f).num = 0 ↔ μ.AlmostSurely (fun x => (f x).num = 0) := by
  simpa only [Distro.expectation, QProb.div, QProb.ofNat, Nat.mul_one] using
    rationalIntegral_num_zero_iff μ.record.atoms f

/-- A mean square vanishes exactly when its signed rational base vanishes
almost surely. No reduced fraction or globally bounded denominator is required. -/
theorem Distro.rationalSquareExpectation_zero_iff (μ : Distro Ω) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.mul (f x) (f x))) SignedRatio.zero ↔
      μ.AlmostSurely (fun x => SignedRatio.Equiv (f x) SignedRatio.zero) := by
  have embedding := SignedRatio.equiv_trans
    (μ.rationalExpectation_congr _ _ (fun x => SignedRatio.equiv_symm (squaredRatio_spec (f x))))
    (μ.rationalExpectation_toSignedRatio (fun x => squaredRatio (f x)))
  constructor
  · intro vanished
    have integerZero := (SignedRatio.equiv_num_zero_iff embedding).mp ((SignedRatio.equiv_zero_iff _).mp vanished)
    have naturalZero : (μ.expectation (fun x => squaredRatio (f x))).num = 0 := Int.ofNat_inj.mp integerZero
    have supported := (μ.expectation_num_zero_iff _).mp naturalZero
    intro atom member weight
    have squareZero := supported atom member weight
    change (f atom.1).num.natAbs * (f atom.1).num.natAbs = 0 at squareZero
    have absoluteZero : (f atom.1).num.natAbs = 0 := by
      rcases Nat.mul_eq_zero.mp squareZero with first | second
      · exact first
      · exact second
    exact (SignedRatio.equiv_zero_iff _).mpr (Int.natAbs_eq_zero.mp absoluteZero)
  · intro supported
    refine SignedRatio.equiv_trans (μ.rationalExpectation_congr_positive _ (fun _ => SignedRatio.zero) ?_)
      (μ.rationalExpectation_constant SignedRatio.zero)
    intro atom member weight
    exact SignedRatio.equiv_trans (SignedRatio.mul_congr (supported atom member weight) (supported atom member weight))
      (SignedRatio.mul_zero _)

/-- Zero squared error means rational equivalence at every positive-weight
occurrence; arbitrary values on null atoms remain part of the record. -/
theorem Distro.rationalSquaredError_zero_iff (μ : Distro Ω) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f g) SignedRatio.zero ↔
      μ.AlmostSurely (fun x => SignedRatio.Equiv (f x) (g x)) := by
  constructor
  · intro vanished
    have supported := (μ.rationalSquareExpectation_zero_iff (fun x => SignedRatio.sub (f x) (g x))).mp vanished
    exact fun atom member weight => (SignedRatio.sub_equiv_zero_iff _ _).mp (supported atom member weight)
  · intro supported
    apply (μ.rationalSquareExpectation_zero_iff (fun x => SignedRatio.sub (f x) (g x))).mpr
    exact fun atom member weight => (SignedRatio.sub_equiv_zero_iff _ _).mpr (supported atom member weight)

theorem Distro.rationalSquaredError_congr_positive (μ : Distro Ω) (f f' g g' : Ω → SignedRatio)
    (first : μ.AlmostSurely (fun x => SignedRatio.Equiv (f x) (f' x)))
    (second : μ.AlmostSurely (fun x => SignedRatio.Equiv (g x) (g' x))) :
    SignedRatio.Equiv (μ.rationalSquaredError f g) (μ.rationalSquaredError f' g') :=
  μ.rationalExpectation_congr_positive _ _ (fun atom member weight =>
    SignedRatio.mul_congr (ratio_sub_congr (first atom member weight) (second atom member weight))
      (ratio_sub_congr (first atom member weight) (second atom member weight)))

/-- Exactly the predictors agreeing almost surely with the conditional mean
attain its minimum squared error. Unsupported labels need not agree pointwise. -/
theorem Distro.conditionalExpectation_optimal_iff (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (h : Fin colours → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f (fun x => h (key x)))
      (μ.rationalSquaredError f (μ.conditionalExpectation key f)) ↔
    μ.AlmostSurely (fun x => SignedRatio.Equiv (μ.conditionalExpectation key f x) (h (key x))) := by
  have split := μ.conditionalExpectation_squaredError key f h
  constructor
  · intro optimal
    exact (μ.rationalSquaredError_zero_iff _ _).mp
      ((SignedRatio.add_equiv_left_iff _ _).mp (SignedRatio.equiv_trans (SignedRatio.equiv_symm split) optimal))
  · intro supported
    exact SignedRatio.equiv_trans split ((SignedRatio.add_equiv_left_iff _ _).mpr
      ((μ.rationalSquaredError_zero_iff _ _).mpr supported))

/-- Conditional expectation is nonexpansive for mean squared distances. -/
theorem Distro.conditionalExpectation_squaredError_contraction (μ : Distro Ω) (key : Ω → Fin colours)
    (f g : Ω → SignedRatio) :
    SignedRatio.LE (μ.rationalSquaredError (μ.conditionalExpectation key f) (μ.conditionalExpectation key g))
      (μ.rationalSquaredError f g) := by
  have same := μ.rationalExpectation_congr
    (fun x => SignedRatio.mul (SignedRatio.sub (μ.conditionalExpectation key f x) (μ.conditionalExpectation key g x))
      (SignedRatio.sub (μ.conditionalExpectation key f x) (μ.conditionalExpectation key g x)))
    (fun x => SignedRatio.mul (μ.conditionalExpectation key (fun y => SignedRatio.sub (f y) (g y)) x)
      (μ.conditionalExpectation key (fun y => SignedRatio.sub (f y) (g y)) x))
    (fun x => SignedRatio.mul_congr (SignedRatio.equiv_symm (μ.conditionalExpectation_sub key f g x))
      (SignedRatio.equiv_symm (μ.conditionalExpectation_sub key f g x)))
  exact (SignedRatio.le_congr same (SignedRatio.equiv_refl _)).mpr
    (μ.conditionalExpectation_square_contraction key (fun x => SignedRatio.sub (f x) (g x)))

/-- More informative labels cannot increase optimal prediction error.
Even the refinement relation itself is required only almost surely. -/
theorem Distro.conditionalExpectation_error_refinement_almostSurely (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (merge : Fin n → Fin m)
    (agrees : μ.AlmostSurely (fun x => coarse x = merge (fine x))) (f : Ω → SignedRatio) :
    SignedRatio.LE (μ.rationalSquaredError f (μ.conditionalExpectation fine f))
      (μ.rationalSquaredError f (μ.conditionalExpectation coarse f)) := by
  let h := fun label => conditionalBlockMean
    (μ.record.atoms.filter (fun atom => decide (coarse atom.1 = merge label))) f
  have same : μ.AlmostSurely (fun x => SignedRatio.Equiv (h (fine x)) (μ.conditionalExpectation coarse f x)) := by
    intro atom member weight
    change SignedRatio.Equiv
      (conditionalBlockMean (μ.record.atoms.filter (fun other => decide (coarse other.1 = merge (fine atom.1)))) f)
      (conditionalBlockMean (μ.record.atoms.filter (fun other => decide (coarse other.1 = coarse atom.1))) f)
    rw [agrees atom member weight]
    exact SignedRatio.equiv_refl _
  have losses := μ.rationalSquaredError_congr_positive f f (fun x => h (fine x)) (μ.conditionalExpectation coarse f)
    (fun _ _ _ => SignedRatio.equiv_refl _) same
  exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) losses).mp (μ.conditionalExpectation_least_squares fine f h)

theorem Distro.conditionalExpectation_error_refinement (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (refinement : ObservableRefinement fine coarse) (f : Ω → SignedRatio) :
    SignedRatio.LE (μ.rationalSquaredError f (μ.conditionalExpectation fine f))
      (μ.rationalSquaredError f (μ.conditionalExpectation coarse f)) :=
  μ.conditionalExpectation_error_refinement_almostSurely fine coarse refinement.merge
    (fun atom _ _ => refinement.agrees atom.1) f

end Thesis.Probability.Distros
