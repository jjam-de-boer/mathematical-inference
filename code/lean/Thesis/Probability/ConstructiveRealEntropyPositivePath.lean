import Thesis.Probability.ConstructiveRealCrossEntropyBounds
import Thesis.Probability.ConstructiveRealEqualityConstraints

namespace Thesis.Probability.ConstructiveReal

private theorem rational_half (lower : PositiveRatio) :
    Equiv (mul (ofSignedRatio lower.toSignedRatio) (ofSignedRatio ⟨1, 2, by decide⟩)) (ofSignedRatio lower.half.toSignedRatio) :=
  equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by
    simp only [PositiveRatio.half, PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio,
      SignedRatio.Equiv, SignedRatio.mul, Int.natCast_mul, Int.mul_one]))

/-- The target's positive floor survives each midpoint, scaled by the known
dyadic coefficient. The reference endpoint may have zero coordinates. -/
theorem UnitIntervalValue.towards_target_positive (reference target : UnitIntervalValue) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) target.value) (n : Nat) :
    LE (ofSignedRatio (lower.mul (dyadicPrecision n)).toSignedRatio) (reference.towards target n).value := by
  induction n with
  | zero => simpa only [dyadicPrecision, PositiveRatio.mul_one] using positive
  | succ n ih =>
      have halfPositive : LE zero (ofSignedRatio (⟨1, 2, by decide⟩ : SignedRatio)) := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
      have combined := mul_le_mul_nonnegative_right halfPositive (add_le_add reference.nonnegative ih)
      have represented := equiv_trans (mul_congr (zero_add _) (equiv_refl _)) (rational_half (lower.mul (dyadicPrecision n)))
      have same : (lower.mul (dyadicPrecision n)).half = lower.mul (dyadicPrecision (n + 1)) := by
        apply PositiveRatio.ext <;> simp only [PositiveRatio.mul, PositiveRatio.half, dyadicPrecision, Nat.mul_assoc]
      exact (le_congr (by simpa only [same] using represented) (equiv_refl _)).mp combined

theorem dyadicPrecision_le_one (n : Nat) : LE (ofSignedRatio (dyadicPrecision n).toSignedRatio) one := by
  apply (ofSignedRatio_le_iff _ _).mpr
  apply (SignedRatio.toSignedRatio_le_iff (dyadicPrecision n).toQProb QProb.one).mpr
  change (dyadicPrecision n).num * 1 ≤ 1 * (dyadicPrecision n).den
  rw [dyadicPrecision_num]
  simpa only [Nat.one_mul, Nat.mul_one] using (dyadicPrecision n).den_pos

private theorem sub_add_left (x increment : ConstructiveReal) : Equiv (sub x (add x increment)) (neg increment) :=
  equiv_trans (add_congr (equiv_refl _) (neg_add _ _))
    (equiv_trans (equiv_symm (add_assoc _ _ _))
      (equiv_trans (add_congr (add_neg x) (equiv_refl _)) (zero_add _)))

/-- Reversing the displacement from a dyadic sample to its reference. -/
theorem UnitIntervalValue.towards_backward (reference target : UnitIntervalValue) (n : Nat) :
    Equiv (sub reference.value (reference.towards target n).value)
      (neg (mul (ofSignedRatio (dyadicPrecision n).toSignedRatio) (sub target.value reference.value))) :=
  equiv_trans (add_congr (equiv_refl _) (neg_congr (reference.towards_affine target n))) (sub_add_left _ _)

private abbrev Expr := RationalPolynomial.Expression 3
private theorem displacement_split (target reference sample : ConstructiveReal) :
    Equiv (sub target sample) (add (sub target reference) (sub reference sample)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real
    (.sub (.coordinate 0) (.coordinate 2) : Expr)
    (.add (.sub (.coordinate 0) (.coordinate 1)) (.sub (.coordinate 1) (.coordinate 2))) (by decide +kernel)
    (fun i => if i.val = 0 then target else if i.val = 1 then reference else sample)

/-- The corresponding displacement from the sample to its target. -/
theorem UnitIntervalValue.towards_forward (reference target : UnitIntervalValue) (n : Nat) :
    Equiv (sub target.value (reference.towards target n).value)
      (mul (sub one (ofSignedRatio (dyadicPrecision n).toSignedRatio)) (sub target.value reference.value)) :=
  equiv_trans (displacement_split _ _ _)
    (equiv_trans (add_congr (equiv_refl _) (reference.towards_backward target n))
      (equiv_symm (equiv_trans (sub_mul _ _ _) (add_congr (one_mul _) (equiv_refl _)))))

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal
open RationalLinear

/-- Actual original-row feasible midpoint, including all closed inequalities,
normalization, redundant rows and forced zero coordinates. -/
def RealLaw.midpoint {problem : RationalEntropyProblem variables} (first second : problem.RealLaw) : problem.RealLaw where
  mass i := (first.mass i).midpoint (second.mass i)
  normalized := equiv_trans (realDot_midpoint variables (fun _ => 1) _ _)
    (equiv_trans (mul_congr (add_congr first.normalized second.normalized) (equiv_refl _)) (midpoint_self one))
  valid row member := by
    have halfPositive : LE zero (ofSignedRatio (⟨1, 2, by decide⟩ : SignedRatio)) := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
    have cleared := mul_le_mul_nonnegative_right halfPositive
      (add_le_add ((row.clear_real_iff _).mpr (first.valid row member)) ((row.clear_real_iff _).mpr (second.valid row member)))
    exact (row.clear_real_iff _).mp ((le_congr (equiv_symm (realDot_midpoint variables row.clear.coefficients _ _))
      (midpoint_self (ofSignedRatio row.clear.bound))).mp cleared)

/-- A sequence of exactly feasible dyadic mixtures approaching the reference.
No coordinate rounding or real feasibility decision is used. -/
def RealLaw.towards {problem : RationalEntropyProblem variables} (reference target : problem.RealLaw) : Nat → problem.RealLaw
  | 0 => target
  | n + 1 => reference.midpoint (reference.towards target n)

theorem RealLaw.towards_mass {problem : RationalEntropyProblem variables} (reference target : problem.RealLaw) (n : Nat) (i : Fin variables) :
    (reference.towards target n).mass i = (reference.mass i).towards (target.mass i) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun value => (reference.mass i).midpoint value) ih

/-- Global maximality bounds cross entropy of a positive feasible target
against every positive dyadic sample. The bound is uniform in the sample
index and will give positive floors at the unknown optimizer itself. -/
theorem RealLaw.maximum_towards_crossEntropy {problem : RationalEntropyProblem variables} (reference target : problem.RealLaw)
    (maximal : reference.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (target.mass i).value) (n : Nat) :
    let sample := reference.towards target n
    let floors := fun i => (lower i).mul (dyadicPrecision n)
    let admitted : ∀ i, LE (ofSignedRatio (floors i).toSignedRatio) (sample.mass i).value := fun i => by
      rw [reference.towards_mass target n i]
      exact (reference.mass i).towards_target_positive (target.mass i) (lower i) (positive i) n
    LE (realCrossEntropySum target.mass sample.mass floors admitted) (entropySizeBound variables) := by
  intro sample floors admitted
  let gradient := fun i => entropyBitGradient (sample.mass i).value (floors i) (admitted i)
  let direction := fun i => sub (target.mass i).value (reference.mass i).value
  let slope := FiniteLinear.pair variables direction gradient
  let coefficient := ofSignedRatio (dyadicPrecision n).toSignedRatio
  have backward : Equiv (FiniteLinear.pair variables (fun i => sub (reference.mass i).value (sample.mass i).value) gradient)
      (neg (mul coefficient slope)) :=
    equiv_trans (FiniteLinear.pair_congr variables _ _ gradient gradient
      (fun i => by rw [reference.towards_mass target n i]; exact (reference.mass i).towards_backward (target.mass i) n) (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.pair_neg_first variables _ gradient)
        (neg_congr (FiniteLinear.pair_scale_first variables coefficient direction gradient)))
  have supporting := realEntropySum_supporting reference.mass sample.mass floors admitted
  have slopePositive : LE zero (FiniteLinear.pair variables (fun i => sub (reference.mass i).value (sample.mass i).value) gradient) := by
    have compared := le_trans (maximal sample) supporting
    exact (add_le_add_right_iff _ _ sample.entropy).mp
      ((le_congr (equiv_symm (zero_add sample.entropy)) (add_comm _ _)).mp compared)
  have negative : LE (mul coefficient slope) zero :=
    (neg_le_neg_iff _ _).mp ((le_congr (ofSignedRatio_neg SignedRatio.zero) backward).mp slopePositive)
  have slopeNonpositive : LE slope zero :=
    (mul_le_mul_positive_iff coefficient (dyadicPrecision n) (le_refl _) slope zero).mp
      ((le_congr (equiv_refl _) (equiv_symm (mul_zero coefficient))).mp negative)
  have forward : Equiv (FiniteLinear.pair variables (fun i => sub (target.mass i).value (sample.mass i).value) gradient)
      (mul (sub one coefficient) slope) :=
    equiv_trans (FiniteLinear.pair_congr variables _ _ gradient gradient
      (fun i => by rw [reference.towards_mass target n i]; exact (reference.mass i).towards_forward (target.mass i) n) (fun _ => equiv_refl _))
      (FiniteLinear.pair_scale_first variables (sub one coefficient) direction gradient)
  have forwardNonpositive : LE (FiniteLinear.pair variables (fun i => sub (target.mass i).value (sample.mass i).value) gradient) zero :=
    (le_congr (equiv_symm forward) (mul_zero (sub one coefficient))).mp
      (mul_le_mul_nonnegative ((zero_le_sub_iff _ _).mpr (dyadicPrecision_le_one n)) slopeNonpositive)
  have crossIdentity := realEntropy_tangent_eq_crossEntropy target.mass sample.mass target.normalized sample.normalized floors admitted
  have crossBound : LE (realCrossEntropySum target.mass sample.mass floors admitted) sample.entropy :=
    (le_congr crossIdentity (add_zero sample.entropy)).mp (add_le_add (le_refl sample.entropy) forwardNonpositive)
  exact le_trans crossBound (realEntropySum_le_sizeBound sample.mass)

end Thesis.Probability.Distros.RationalEntropyProblem
