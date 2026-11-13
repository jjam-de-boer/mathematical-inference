import Thesis.Probability.Distros.JointMomentTable

namespace Thesis.Probability.Distros

/-- Convert a candidate signed mass to a nonnegative rational presentation.
The realization constructor below always supplies its nonnegativity proof. -/
def jointTableProbability (moments : List Nat → QProb) (bounds value : List Nat) : QProb :=
  ⟨(inverseJointFactorialTable moments bounds value).num.toNat,
    (inverseJointFactorialTable moments bounds value).den, (inverseJointFactorialTable moments bounds value).den_pos⟩

theorem jointTableProbability_spec (moments : List Nat → QProb) (bounds value : List Nat)
    (positive : SignedRatio.Nonnegative (inverseJointFactorialTable moments bounds value)) :
    SignedRatio.Equiv (jointTableProbability moments bounds value).toSignedRatio
      (inverseJointFactorialTable moments bounds value) := by
  change ((inverseJointFactorialTable moments bounds value).num.toNat : Int) *
      (inverseJointFactorialTable moments bounds value).den =
    (inverseJointFactorialTable moments bounds value).num * (inverseJointFactorialTable moments bounds value).den
  rw [Int.toNat_of_nonneg positive]

private theorem joint_probability_sum_embedding (values : List QProb) :
    (QProb.listSum values).toSignedRatio = SignedRatio.listSum (values.map QProb.toSignedRatio) := by
  induction values with
  | nil => rfl
  | cons value values ih => rw [QProb.listSum, QProb.toSignedRatio_add, List.map_cons, SignedRatio.listSum, ih]

theorem jointTableProbability_normalized (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) :
    QProb.Equiv (QProb.listSum ((factorialRectangle bounds).map (jointTableProbability moments bounds))) QProb.one := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  rw [joint_probability_sum_embedding, List.map_map]
  exact SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem (factorialRectangle bounds) _
    (inverseJointFactorialTable moments bounds) (fun value member =>
      jointTableProbability_spec moments bounds value (valid.1 value (factorialRectangle_mem bounds value member)))) valid.2

/-- Canonical realization on the coordinate-specific rectangle. Every grid
cell is retained, including zero masses, zero-width axes and the empty vector. -/
def realizedJointFactorialDistro (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) : Distro (List Nat) :=
  probabilityList (factorialRectangle bounds) [] (jointTableProbability moments bounds)
    (factorialRectangle_positive bounds) (jointTableProbability_normalized moments bounds valid)

theorem realizedJointFactorialDistro_bounded (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) :
    (realizedJointFactorialDistro moments bounds valid).AlmostSurely (fun counts => CoordinateBounds counts bounds) := by
  intro atom member weight
  exact factorialRectangle_mem bounds atom.1 (probabilityList_supported (factorialRectangle bounds) []
    (jointTableProbability moments bounds) (factorialRectangle_positive bounds)
    (jointTableProbability_normalized moments bounds valid) atom member weight)

theorem realizedJointFactorialDistro_retains (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) (value : List Nat) (within : CoordinateBounds value bounds) :
    ∃ weight, (value, weight) ∈ (realizedJointFactorialDistro moments bounds valid).record.atoms :=
  probabilityList_retains (factorialRectangle bounds) [] (jointTableProbability moments bounds) (factorialRectangle_positive bounds)
    (jointTableProbability_normalized moments bounds valid) value (factorialRectangle_complete bounds value within)

theorem realizedJointFactorialDistro_coefficient (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) (orders : List Nat) (within : CoordinateBounds orders bounds) :
    SignedRatio.Equiv (multivariateFactorialCoefficient (realizedJointFactorialDistro moments bounds valid) orders).toSignedRatio
      (jointFactorialTableCoefficient moments orders) := by
  let μ := realizedJointFactorialDistro moments bounds valid
  have integral := probabilityList_expectation (factorialRectangle bounds) [] (jointTableProbability moments bounds)
    (factorialRectangle_positive bounds) (jointTableProbability_normalized moments bounds valid)
    (fun counts => (QProb.ofNat (jointChoose orders counts)).toSignedRatio)
  have masses := SignedRatio.listSum_map_congr_on_mem (factorialRectangle bounds)
    (fun counts => SignedRatio.mul (jointTableProbability moments bounds counts).toSignedRatio (QProb.ofNat (jointChoose orders counts)).toSignedRatio)
    (fun counts => SignedRatio.mul (inverseJointFactorialTable moments bounds counts) (QProb.ofNat (jointChoose orders counts)).toSignedRatio)
    (fun counts member => SignedRatio.mul_congr
      (jointTableProbability_spec moments bounds counts (valid.1 counts (factorialRectangle_mem bounds counts member)))
      (SignedRatio.equiv_refl _))
  exact SignedRatio.equiv_trans (QProb.toSignedRatio_congr (multivariateFactorialCoefficient_choose μ orders))
    (SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.rationalExpectation_ofNat (jointChoose orders)))
      (SignedRatio.equiv_trans integral (SignedRatio.equiv_trans masses (inverseJointFactorialTable_choose moments bounds orders within))))

/-- Recover exactly the supplied finite table of mixed factorial moments. -/
theorem realizedJointFactorialDistro_moments (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) (orders : List Nat) (within : CoordinateBounds orders bounds) :
    QProb.Equiv (jointFactorialMoment (realizedJointFactorialDistro moments bounds valid) orders) (moments orders) := by
  have same := (QProb.toSignedRatio_equiv_iff _ _).mp (realizedJointFactorialDistro_coefficient moments bounds valid orders within)
  apply Nat.eq_of_mul_eq_mul_right (orderFactorial_pos orders)
  change (jointFactorialMoment (realizedJointFactorialDistro moments bounds valid) orders).num * (moments orders).den * orderFactorial orders =
    (moments orders).num * (jointFactorialMoment (realizedJointFactorialDistro moments bounds valid) orders).den * orderFactorial orders
  simpa only [multivariateFactorialCoefficient, jointFactorialTableCoefficient, QProb.Equiv, QProb.div,
    QProb.ofNat, Nat.mul_one, Nat.mul_assoc] using same

/-- Nonnegative normalized tensor-inverse masses characterize realizability
of a bounded joint rational moment table, before any joint law is given. -/
theorem jointFactorialMomentTable_realizable_iff (moments : List Nat → QProb) (bounds : List Nat) :
    JointFactorialMomentTableValid moments bounds ↔ ∃ μ : Distro (List Nat),
      μ.AlmostSurely (fun counts => CoordinateBounds counts bounds) ∧
      ∀ orders, CoordinateBounds orders bounds → QProb.Equiv (jointFactorialMoment μ orders) (moments orders) := by
  constructor
  · intro valid
    exact ⟨realizedJointFactorialDistro moments bounds valid, realizedJointFactorialDistro_bounded moments bounds valid,
      realizedJointFactorialDistro_moments moments bounds valid⟩
  · rintro ⟨μ, support, momentsAgree⟩
    exact jointFactorialMomentTable_valid_of_moments μ moments bounds support momentsAgree

/-- Uniqueness is full event-law equality, even for alternative presentations
with duplicated or rescaled atoms and arbitrary zero-weight outliers. -/
theorem realizedJointFactorialDistro_unique (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) (μ : Distro (List Nat))
    (support : μ.AlmostSurely (fun counts => CoordinateBounds counts bounds))
    (momentsAgree : ∀ orders, CoordinateBounds orders bounds → QProb.Equiv (jointFactorialMoment μ orders) (moments orders)) :
    μ.SameLaw (realizedJointFactorialDistro moments bounds valid) :=
  μ.sameLaw_of_rectangleFactorialMoments _ bounds support (realizedJointFactorialDistro_bounded moments bounds valid)
    (fun orders within => QProb.equiv_trans (momentsAgree orders within)
      (QProb.equiv_symm (realizedJointFactorialDistro_moments moments bounds valid orders within)))

theorem realizedJointFactorialDistro_pmf (moments : List Nat → QProb) (bounds : List Nat)
    (valid : JointFactorialMomentTableValid moments bounds) (value : List Nat) (dimension : value.length = bounds.length) :
    SignedRatio.Equiv ((realizedJointFactorialDistro moments bounds valid).pmf value).toSignedRatio
      (inverseJointFactorialTable moments bounds value) :=
  inverseJointFactorialTable_of_moments _ moments bounds value dimension
    (realizedJointFactorialDistro_bounded moments bounds valid) (realizedJointFactorialDistro_moments moments bounds valid)

end Thesis.Probability.Distros
