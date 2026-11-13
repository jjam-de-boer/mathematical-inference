import Thesis.Probability.Distros.JointMomentTableAlgebra
import Thesis.Probability.Distros.ProbabilityList

namespace Thesis.Probability.Distros
open Combinatorics

/-- Supplied mixed factorial moments divided by the coordinate factorials. -/
def jointFactorialTableCoefficient (moments : List Nat → QProb) (orders : List Nat) : SignedRatio :=
  (QProb.div (moments orders) (QProb.ofNat (orderFactorial orders)) (orderFactorial_pos orders)).toSignedRatio

/-- Tensor inversion of a candidate table, independent of an existing law. -/
def inverseJointFactorialTable (moments : List Nat → QProb) (bounds target : List Nat) : SignedRatio :=
  SignedRatio.listSum ((factorialRectangle bounds).map (fun orders =>
    SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩ (jointFactorialTableCoefficient moments orders)))

def JointFactorialMomentTableValid (moments : List Nat → QProb) (bounds : List Nat) : Prop :=
  (∀ value, CoordinateBounds value bounds → SignedRatio.Nonnegative (inverseJointFactorialTable moments bounds value)) ∧
  SignedRatio.Equiv (SignedRatio.listSum ((factorialRectangle bounds).map (inverseJointFactorialTable moments bounds))) SignedRatio.one

/-- Inversion followed by mixed binomial moments recovers the supplied
coefficient at every order in the rectangle, without positivity assumptions. -/
theorem inverseJointFactorialTable_choose (moments : List Nat → QProb) (bounds order : List Nat) (within : CoordinateBounds order bounds) :
    SignedRatio.Equiv (SignedRatio.listSum ((factorialRectangle bounds).map (fun value =>
      SignedRatio.mul (inverseJointFactorialTable moments bounds value) (QProb.ofNat (jointChoose order value)).toSignedRatio)))
      (jointFactorialTableCoefficient moments order) := by
  let values := factorialRectangle bounds
  let kernel := fun value r => SignedRatio.mul (jointFactorialTableCoefficient moments r)
    (SignedRatio.mul ⟨jointInverseBinomial r value, 1, Nat.zero_lt_one⟩ (QProb.ofNat (jointChoose order value)).toSignedRatio)
  have rows (value : List Nat) : SignedRatio.Equiv
      (SignedRatio.mul (inverseJointFactorialTable moments bounds value) (QProb.ofNat (jointChoose order value)).toSignedRatio)
      (SignedRatio.listSum (values.map (kernel value))) := by
    refine SignedRatio.equiv_trans (SignedRatio.listSum_mul
      (values.map (fun r => SignedRatio.mul ⟨jointInverseBinomial r value, 1, Nat.zero_lt_one⟩ (jointFactorialTableCoefficient moments r)))
      (QProb.ofNat (jointChoose order value)).toSignedRatio) ?_
    simpa only [List.map_map, Function.comp_def, kernel] using
      (SignedRatio.listSum_map_congr values _ _ (fun r => by
        simp only [SignedRatio.Equiv, SignedRatio.mul, Int.natCast_mul]
        ac_rfl))
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr values _ _ rows) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_swap values values kernel) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem values _
    (fun r => if r = order then jointFactorialTableCoefficient moments order else SignedRatio.zero) ?_) ?_
  · intro r member
    have rWithin := factorialRectangle_mem bounds r member
    refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
      simpa only [List.map_map, Function.comp_def, kernel] using
        (SignedRatio.mul_listSum (jointFactorialTableCoefficient moments r)
          (values.map (fun value => SignedRatio.mul ⟨jointInverseBinomial r value, 1, Nat.zero_lt_one⟩
            (QProb.ofNat (jointChoose order value)).toSignedRatio))))) ?_
    refine SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
      (jointInverseBinomial_reverse_rectangle_kernel r order bounds ((coordinateBounds_length _ _ within).trans (coordinateBounds_length _ _ rWithin).symm) rWithin)) ?_
    by_cases same : r = order
    · subst r
      simp only [if_true]
      exact SignedRatio.mul_one _
    · simp only [if_neg same]
      exact SignedRatio.mul_zero _
  · exact factorialRectangle_select bounds order (jointFactorialTableCoefficient moments) within

theorem inverseJointFactorialTable_of_moments (μ : Distro (List Nat)) (moments : List Nat → QProb) (bounds target : List Nat)
    (dimension : target.length = bounds.length) (support : μ.AlmostSurely (fun counts => CoordinateBounds counts bounds))
    (momentsAgree : ∀ orders, CoordinateBounds orders bounds → QProb.Equiv (jointFactorialMoment μ orders) (moments orders)) :
    SignedRatio.Equiv (μ.pmf target).toSignedRatio (inverseJointFactorialTable moments bounds target) := by
  refine SignedRatio.equiv_trans (μ.pmf_rectangleFactorial_inversion bounds target dimension support) ?_
  apply SignedRatio.listSum_map_congr_on_mem
  intro orders member
  exact SignedRatio.mul_congr (SignedRatio.equiv_refl _)
    (QProb.toSignedRatio_congr (QProb.div_congr (momentsAgree orders (factorialRectangle_mem bounds orders member))
      (QProb.equiv_refl _) _ _))

/-- Every actual bounded joint law satisfies exactly the signed inverse
probability constraints. Null atoms need not have the rectangle's shape. -/
theorem jointFactorialMomentTable_valid_of_moments (μ : Distro (List Nat)) (moments : List Nat → QProb) (bounds : List Nat)
    (support : μ.AlmostSurely (fun counts => CoordinateBounds counts bounds))
    (momentsAgree : ∀ orders, CoordinateBounds orders bounds → QProb.Equiv (jointFactorialMoment μ orders) (moments orders)) :
    JointFactorialMomentTableValid moments bounds := by
  constructor
  · intro value within
    have same := inverseJointFactorialTable_of_moments μ moments bounds value (coordinateBounds_length _ _ within) support momentsAgree
    exact (SignedRatio.nonnegative_congr same).mp (QProb.toSignedRatio_nonnegative _)
  · let zeroOrders := List.replicate bounds.length 0
    have zeroBounded : CoordinateBounds zeroOrders bounds := coordinateBounds_zero bounds
    have terms := SignedRatio.listSum_map_congr_on_mem (factorialRectangle bounds)
      (fun counts => SignedRatio.mul (inverseJointFactorialTable moments bounds counts)
        (QProb.ofNat (jointChoose zeroOrders counts)).toSignedRatio)
      (inverseJointFactorialTable moments bounds) (by
        intro counts member
        have dimension := coordinateBounds_length counts bounds (factorialRectangle_mem bounds counts member)
        have choose : jointChoose zeroOrders counts = 1 := by
          change jointChoose (List.replicate bounds.length 0) counts = 1
          rw [← dimension]
          exact jointChoose_zeroOrders counts
        change SignedRatio.Equiv (SignedRatio.mul (inverseJointFactorialTable moments bounds counts)
          (QProb.ofNat (jointChoose zeroOrders counts)).toSignedRatio) (inverseJointFactorialTable moments bounds counts)
        rw [choose]
        exact SignedRatio.mul_one _)
    have actual := μ.expectNat_congr_positive (jointChoose zeroOrders) (fun _ => 1) (by
      intro atom member weight
      have dimension := coordinateBounds_length atom.1 bounds (support atom member weight)
      change jointChoose (List.replicate bounds.length 0) atom.1 = 1
      rw [← dimension]
      exact jointChoose_zeroOrders atom.1)
    have one : QProb.Equiv (multivariateFactorialCoefficient μ zeroOrders) QProb.one := by
      refine QProb.equiv_trans (multivariateFactorialCoefficient_choose μ zeroOrders) ?_
      rw [actual]
      exact μ.expectNat_constant 1
    have supplied : SignedRatio.Equiv (multivariateFactorialCoefficient μ zeroOrders).toSignedRatio
        (jointFactorialTableCoefficient moments zeroOrders) :=
      QProb.toSignedRatio_congr (QProb.div_congr (momentsAgree zeroOrders zeroBounded)
        (QProb.equiv_refl (QProb.ofNat (orderFactorial zeroOrders))) (orderFactorial_pos zeroOrders) (orderFactorial_pos zeroOrders))
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm terms)
      (SignedRatio.equiv_trans (inverseJointFactorialTable_choose moments bounds zeroOrders zeroBounded)
        (SignedRatio.equiv_trans (SignedRatio.equiv_symm supplied) (QProb.toSignedRatio_congr one)))

end Thesis.Probability.Distros
