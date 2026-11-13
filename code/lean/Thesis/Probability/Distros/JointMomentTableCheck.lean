import Thesis.Probability.Distros.JointMomentRealization
import Thesis.Probability.Distros.MomentTableCheck

namespace Thesis.Probability.Distros

inductive JointFactorialTableObstruction (moments : List Nat → QProb) (bounds : List Nat) where
  | negative (value : List Nat) (within : CoordinateBounds value bounds)
      (proof : (inverseJointFactorialTable moments bounds value).num < 0)
  | unnormalized (proof : ¬ SignedRatio.Equiv
      (SignedRatio.listSum ((factorialRectangle bounds).map (inverseJointFactorialTable moments bounds))) SignedRatio.one)

theorem JointFactorialTableObstruction.not_valid {moments : List Nat → QProb} {bounds : List Nat}
    (obstruction : JointFactorialTableObstruction moments bounds) : ¬ JointFactorialMomentTableValid moments bounds := by
  intro valid
  cases obstruction with
  | negative value within negative => have nonnegative := valid.1 value within; change 0 ≤ _ at nonnegative; omega
  | unnormalized proof => exact proof valid.2

theorem JointFactorialTableObstruction.not_realizable {moments : List Nat → QProb} {bounds : List Nat}
    (obstruction : JointFactorialTableObstruction moments bounds) :
    ¬ ∃ μ : Distro (List Nat), μ.AlmostSurely (fun counts => CoordinateBounds counts bounds) ∧
      ∀ orders, CoordinateBounds orders bounds → QProb.Equiv (jointFactorialMoment μ orders) (moments orders) :=
  fun law => obstruction.not_valid ((jointFactorialMomentTable_realizable_iff moments bounds).mpr law)

structure JointFactorialTableRealization (moments : List Nat → QProb) (bounds : List Nat) where
  distro : Distro (List Nat)
  bounded : distro.AlmostSurely (fun counts => CoordinateBounds counts bounds)
  momentsAgree : ∀ orders, CoordinateBounds orders bounds → QProb.Equiv (jointFactorialMoment distro orders) (moments orders)
  retains : ∀ value, CoordinateBounds value bounds → ∃ weight, (value, weight) ∈ distro.record.atoms

/-- Complete finite checking on the actual rectangle. Success returns a
joint law with its moment, bound and zero-cell-retention certificates. Failure
returns a negative bounded cell or an explicit normalization obstruction. -/
def checkJointFactorialMomentTable (moments : List Nat → QProb) (bounds : List Nat) :
    Sum (JointFactorialTableRealization moments bounds) (JointFactorialTableObstruction moments bounds) :=
  match checkFiniteMasses (factorialRectangle bounds) (inverseJointFactorialTable moments bounds) with
  | .negative value member proof => .inr (.negative value (factorialRectangle_mem bounds value member) proof)
  | .nonnegative proof =>
    if normalized : SignedRatio.Equiv
        (SignedRatio.listSum ((factorialRectangle bounds).map (inverseJointFactorialTable moments bounds))) SignedRatio.one then
      let valid : JointFactorialMomentTableValid moments bounds :=
        ⟨fun value within => proof value (factorialRectangle_complete bounds value within), normalized⟩
      .inl ⟨realizedJointFactorialDistro moments bounds valid,
        realizedJointFactorialDistro_bounded moments bounds valid, realizedJointFactorialDistro_moments moments bounds valid,
        realizedJointFactorialDistro_retains moments bounds valid⟩
    else .inr (.unnormalized normalized)

theorem checkJointFactorialMomentTable_success_iff (moments : List Nat → QProb) (bounds : List Nat) :
    (match checkJointFactorialMomentTable moments bounds with | .inl _ => True | .inr _ => False) ↔
      JointFactorialMomentTableValid moments bounds := by
  cases result : checkJointFactorialMomentTable moments bounds with
  | inl law =>
      constructor
      · intro _
        exact jointFactorialMomentTable_valid_of_moments law.distro moments bounds law.bounded law.momentsAgree
      · intro _; trivial
  | inr obstruction =>
      constructor
      · intro impossible; exact False.elim impossible
      · intro valid; exact False.elim (obstruction.not_valid valid)

end Thesis.Probability.Distros
