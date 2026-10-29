import Thesis.Examples.EntropyMeanHalfGibbs
import Thesis.Probability.RationalThirteenSquareObstruction

/-!
# The irrational ideal behind the rational mean-half certificate

The original rational problem fixes the mean of {0,1,2} to one half and
retains redundant rows. Its constructive ideal optimizer is attained and
unique. The preceding multiplier regression proves its geometric relation;
here the exact constraint equations yield a discriminant of thirteen.
Finite arithmetic descent then excludes every exact rational maximizing law.
The existing rational certificates continue to bound this same ideal entropy
and return exactly feasible approximations. No irrational atom is added to
`Distro`, and no exact rational maximizer is asserted.
-/

namespace Thesis.Examples.EntropyMeanHalfDiscriminant
open Probability Probability.Distros ConstructiveReal

private abbrev problem := EntropyMeanHalf.problem
private abbrev ideal := EntropyMeanHalfGibbs.ideal
private def mass (i : Fin 3) : ConstructiveReal := (ideal.mass i).value
private abbrev Expression := RationalPolynomial.Expression 3
private def first : Expression := .coordinate 0
private def middle : Expression := .coordinate 1
private def last : Expression := .coordinate 2
private def c (value : Int) : Expression := .constant ⟨value, 1, by decide⟩
private def normExpr : Expression := .add (.mul (c 1) last) (.add (.mul (c 1) middle) (.add (.mul (c 1) first) (c 0)))
private def meanExpr : Expression := .add (.mul (c 2) last) (.add (.mul (c 1) middle) (.add (.mul (c 0) first) (c 0)))
private def differenceExpr : Expression := .sub first (.add middle (.mul (c 3) last))
private def half : SignedRatio := ⟨1, 2, by decide⟩
private def meanRow : MomentInterval Nat := .exact (fun value => (value : Int)) half

private theorem normalized : Equiv (normExpr.evaluateReal mass) one := ideal.normalized
private theorem mean_exact : Equiv (meanExpr.evaluateReal mass) (ofSignedRatio half) := by
  have member : meanRow ∈ problem.intervals := List.mem_cons_self ..
  have bounds := ConstructiveEntropyOptimizer.meanHalfIdeal.moment_bounds meanRow member
  exact ⟨bounds.2, bounds.1⟩

/-- Normalization and mean one half imply p0=p1+3p2, independently of any
stationarity or rationality assumption on the ideal coordinates. -/
theorem linear_relation : Equiv (mass 0) (add (mass 1) (mul (ofSignedRatio ⟨3, 1, by decide⟩) (mass 2))) := by
  have polynomial := RationalPolynomial.Expression.equalityCheck_sound_real differenceExpr
    (.sub normExpr (.mul (c 2) meanExpr)) (by decide +kernel) mass
  have twiceMean : Equiv (mul (ofSignedRatio ⟨2, 1, by decide⟩) (meanExpr.evaluateReal mass)) one :=
    equiv_trans (mul_congr (equiv_refl _) mean_exact)
      (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))
  apply (sub_equiv_zero_iff _ _).mp
  exact equiv_trans polynomial (equiv_trans (add_congr normalized (neg_congr twiceMean)) (add_neg one))

private def discriminantLeft : Expression := .mul (.add first (.mul (c 6) middle)) (.add first (.mul (c 6) middle))
private def discriminantRight : Expression := .mul (c 13) (.mul first first)
private def remainderExpr : Expression := .mul (c 12)
  (.add (.mul first (.sub (.add middle (.mul (c 3) last)) first))
    (.mul (c 3) (.sub (.mul middle middle) (.mul first last))))

/-- The actual ideal law has discriminant thirteen. This exact identity
will exclude rational probability vectors without choosing a square root. -/
theorem discriminant : Equiv (discriminantLeft.evaluateReal mass) (discriminantRight.evaluateReal mass) := by
  have polynomial := RationalPolynomial.Expression.equalityCheck_sound_real
    (.sub discriminantLeft discriminantRight) remainderExpr (by decide +kernel) mass
  have firstZero := (sub_equiv_zero_iff _ _).mpr (equiv_symm linear_relation)
  have secondZero := (sub_equiv_zero_iff _ _).mpr (equiv_symm EntropyMeanHalfGibbs.geometric)
  have reduced : Equiv (remainderExpr.evaluateReal mass) zero :=
    equiv_trans (mul_congr (equiv_refl _) (add_congr
      (equiv_trans (mul_congr (equiv_refl _) firstZero) (mul_zero _))
      (equiv_trans (mul_congr (equiv_refl _) secondZero) (mul_zero _))))
      (equiv_trans (mul_congr (equiv_refl _) (zero_add zero)) (mul_zero _))
  exact (sub_equiv_zero_iff _ _).mp (equiv_trans polynomial reduced)

private theorem common_product (a b factor : ConstructiveReal) :
    Equiv (mul (mul a factor) (mul b factor)) (mul (mul a b) (mul factor factor)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real
    (.mul (.mul first last) (.mul middle last)) (.mul (.mul first middle) (.mul last last))
    (by decide +kernel) (fun i => if i = 0 then a else if i = 1 then b else factor)

/-- At least one of the first two ideal masses is irrational. The argument
works with arbitrary unreduced rational presentations and does not assume
that an algebraic square root or a rational maximizer is available. -/
theorem not_rational_pair (q0 q1 : QProb)
    (firstRational : Equiv (mass 0) (ofSignedRatio q0.toSignedRatio))
    (secondRational : Equiv (mass 1) (ofSignedRatio q1.toSignedRatio)) : False := by
  let floor := EntropyMeanHalfGibbs.lower (0 : Fin 3)
  have lowerBound : LE (ofSignedRatio floor.toSignedRatio) (ofSignedRatio q0.toSignedRatio) :=
    (le_congr (equiv_refl _) firstRational).mp (EntropyMeanHalfGibbs.positive (0 : Fin 3))
  have rationalLower := (SignedRatio.toSignedRatio_le_iff floor.toQProb q0).mp ((ofSignedRatio_le_iff _ _).mp lowerBound)
  have q0Positive : 0 < q0.num := by
    apply Nat.pos_of_ne_zero
    intro vanished
    change floor.num * q0.den ≤ q0.num * floor.den at rationalLower
    rw [vanished, Nat.zero_mul] at rationalLower
    have productPositive := Nat.mul_pos floor.num_pos q0.den_pos
    omega
  let positiveFirst : PositiveRatio := ⟨q0.num, q0.den, q0Positive, q0.den_pos⟩
  let inverse := ofSignedRatio positiveFirst.inv.toSignedRatio
  have unit : Equiv (mul (mass 0) inverse) one :=
    equiv_trans (mul_congr firstRational (equiv_refl _))
      (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (PositiveRatio.signed_mul_inv positiveFirst)))
  let numerator := QProb.add q0 (QProb.mul (QProb.ofNat 6) q1)
  let root := QProb.div numerator q0 q0Positive
  let sum := add (mass 0) (mul (ofSignedRatio ⟨6, 1, by decide⟩) (mass 1))
  have numeratorValue : Equiv (ofSignedRatio numerator.toSignedRatio) sum := by
    change Equiv (ofSignedRatio (QProb.add q0 (QProb.mul (QProb.ofNat 6) q1)).toSignedRatio) _
    rw [QProb.toSignedRatio_add, QProb.toSignedRatio_mul]
    exact equiv_trans (equiv_symm (ofSignedRatio_add _ _))
      (add_congr (equiv_symm firstRational) (equiv_trans (equiv_symm (ofSignedRatio_mul _ _))
        (mul_congr (equiv_refl _) (equiv_symm secondRational))))
  have rootValue : Equiv (ofSignedRatio root.toSignedRatio) (mul sum inverse) := by
    change Equiv (ofSignedRatio (QProb.mul numerator positiveFirst.inv.toQProb).toSignedRatio) _
    rw [QProb.toSignedRatio_mul]
    exact equiv_trans (equiv_symm (ofSignedRatio_mul _ _)) (mul_congr numeratorValue (equiv_refl _))
  have rootSquare : Equiv (mul (ofSignedRatio root.toSignedRatio) (ofSignedRatio root.toSignedRatio))
      (ofSignedRatio (QProb.ofNat 13).toSignedRatio) :=
    equiv_trans (mul_congr rootValue rootValue) (equiv_trans (common_product sum sum inverse)
      (equiv_trans (mul_congr discriminant (equiv_refl _)) (equiv_trans (mul_assoc _ _ _)
        (equiv_trans (mul_congr (equiv_refl _) (equiv_symm (common_product (mass 0) (mass 0) inverse)))
          (equiv_trans (mul_congr (equiv_refl _) (equiv_trans (mul_congr unit unit) (one_mul one))) (mul_one _))))))
  have rationalSquare : QProb.Equiv (QProb.mul root root) (QProb.ofNat 13) := by
    apply (QProb.toSignedRatio_equiv_iff _ _).mp
    apply (ofSignedRatio_equiv_iff _ _).mp
    rw [QProb.toSignedRatio_mul]
    exact equiv_trans (equiv_symm (ofSignedRatio_mul _ _)) rootSquare
  exact QProb.square_ne_thirteen root rationalSquare

/-- Every actual rational compatible law fails to attain the ideal entropy
maximum in this example. Uniqueness transfers any hypothetical rational
maximum to the constructed ideal, contradicting the discriminant proof. -/
theorem rational_not_maximal (law : problem.CompatibleLaw) : ¬ law.toReal.Maximal := by
  intro maximal
  have same := law.toReal.maximal_unique ConstructiveEntropyOptimizer.meanHalfIdeal maximal
    (problem.idealEntropyLaw_maximal EntropyMeanHalf.anchor)
  exact not_rational_pair (law.distro.pmf 0) (law.distro.pmf 1)
    (equiv_symm (same (0 : Fin 3))) (equiv_symm (same (1 : Fin 3)))

/-- The existing exactly feasible rational law cannot be the ideal law,
even though its entropy is certified within 1/1000 bit of the optimum. -/
example : ¬ (∀ i : Fin 3, Equiv (ideal.mass i).value (EntropyMeanHalf.anchor.toReal.mass i).value) := by
  intro rational
  exact not_rational_pair
    (EntropyMeanHalf.anchor.distro.pmf 0) (EntropyMeanHalf.anchor.distro.pmf 1) (rational 0) (rational 1)

end Thesis.Examples.EntropyMeanHalfDiscriminant
