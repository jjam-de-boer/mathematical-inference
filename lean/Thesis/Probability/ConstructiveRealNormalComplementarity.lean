import Thesis.Probability.ConstructiveRealNormalMultipliers
import Thesis.Probability.ConstructiveRealEntropyVectorConcavity

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear
open IntegerLinearAlgebra

private theorem constant_pair (size : Nat) (constant : ConstructiveReal) (values : Fin size → ConstructiveReal) :
    Equiv (FiniteLinear.pair size (fun _ => constant) values) (mul constant (realDot size (fun _ => 1) values)) :=
  equiv_trans (FiniteLinear.pair_congr size _ (fun _ => mul constant one) values values
    (fun _ => equiv_symm (mul_one constant)) (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_scale_first size constant (fun _ => one) values)
      (mul_congr (equiv_refl _) (equiv_symm (FiniteLinear.realDot_pair size (fun _ => 1) values))))

/-- Pairing the computed stationarity equation with a normalized primal law
uses finite bilinear Fubini and retains every original row. -/
theorem NormalMultipliers.pairing_normalized {matrix : Matrix rows columns} {bounds : Fin rows → Int}
    {gradient : Fin columns → ConstructiveReal} {target : ConstructiveReal}
    (certificate : NormalMultipliers matrix bounds gradient target)
    (masses : Fin columns → ConstructiveReal)
    (normalized : Equiv (realDot columns (fun _ => 1) masses) one) :
    Equiv (FiniteLinear.pair columns gradient masses)
      (add certificate.offset (FiniteLinear.pair rows certificate.coefficient
        (fun r => realDot columns (matrix r) masses))) := by
  have scorePair : Equiv (FiniteLinear.pair columns
      (fun i => realDot rows (fun r => matrix r i) certificate.coefficient) masses)
      (FiniteLinear.pair rows certificate.coefficient (fun r => realDot columns (matrix r) masses)) :=
    equiv_trans (FiniteLinear.pair_congr columns _ _ masses masses (fun i =>
      equiv_trans (FiniteLinear.realDot_pair rows (fun r => matrix r i) certificate.coefficient)
        (FiniteLinear.pair_comm rows _ _)) (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.combination_pair rows columns (fun r i => realInteger (matrix r i)) certificate.coefficient masses)
        (FiniteLinear.pair_congr rows certificate.coefficient certificate.coefficient _ _ (fun _ => equiv_refl _)
          (fun r => equiv_symm (FiniteLinear.realDot_pair columns (matrix r) masses))))
  have constantPair := equiv_trans (constant_pair columns certificate.offset masses)
    (equiv_trans (mul_congr (equiv_refl _) normalized) (mul_one certificate.offset))
  exact equiv_trans (FiniteLinear.pair_congr columns _ _ masses masses certificate.represents (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_add_first columns _ _ masses) (add_congr constantPair scorePair))

/-- Equality of attained primal and dual values forces the sum of weighted
slacks to vanish. This uses the actual returned coefficients. -/
theorem NormalMultipliers.weighted_slack_zero {matrix : Matrix rows columns} {bounds : Fin rows → Int}
    {gradient masses : Fin columns → ConstructiveReal}
    (certificate : NormalMultipliers matrix bounds gradient (FiniteLinear.pair columns masses gradient))
    (normalized : Equiv (realDot columns (fun _ => 1) masses) one) :
    Equiv (FiniteLinear.pair rows certificate.coefficient
      (fun r => sub (realInteger (bounds r)) (realDot columns (matrix r) masses))) zero := by
  let left := realDot rows bounds certificate.coefficient
  let right := FiniteLinear.pair rows certificate.coefficient (fun r => realDot columns (matrix r) masses)
  have affineSame : Equiv (add certificate.offset left) (add certificate.offset right) :=
    equiv_trans certificate.attained (equiv_trans (FiniteLinear.pair_comm columns masses gradient)
      (certificate.pairing_normalized masses normalized))
  have swapped : Equiv (add left certificate.offset) (add right certificate.offset) :=
    equiv_trans (add_comm _ _) (equiv_trans affineSame (add_comm _ _))
  have canceled : Equiv left right :=
    ⟨(add_le_add_right_iff left right certificate.offset).mp swapped.1,
      (add_le_add_right_iff right left certificate.offset).mp swapped.2⟩
  have bridge : Equiv left (FiniteLinear.pair rows certificate.coefficient (fun r => realInteger (bounds r))) :=
    equiv_trans (FiniteLinear.realDot_pair rows bounds certificate.coefficient) (FiniteLinear.pair_comm rows _ _)
  exact equiv_trans (FiniteLinear.pair_sub_second rows certificate.coefficient _ _)
    ((sub_equiv_zero_iff _ _).mpr (equiv_trans (equiv_symm bridge) canceled))

/-- Each complementary product vanishes separately: all are nonnegative
and their finite sum is zero. Neither zero/nonzero slack classification nor
an independent active set is needed. -/
theorem NormalMultipliers.complementary {matrix : Matrix rows columns} {bounds : Fin rows → Int}
    {gradient masses : Fin columns → ConstructiveReal}
    (certificate : NormalMultipliers matrix bounds gradient (FiniteLinear.pair columns masses gradient))
    (normalized : Equiv (realDot columns (fun _ => 1) masses) one)
    (valid : ∀ r, LE (realDot columns (matrix r) masses) (realInteger (bounds r))) (r : Fin rows) :
    Equiv (mul (certificate.coefficient r) (sub (realInteger (bounds r)) (realDot columns (matrix r) masses))) zero := by
  let term := fun s => mul (certificate.coefficient s) (sub (realInteger (bounds s)) (realDot columns (matrix s) masses))
  let terms := (List.finRange rows).map term
  have nonnegative (s : Fin rows) : LE zero (term s) :=
    mul_nonnegative (certificate.nonnegative s) ((zero_le_sub_iff _ _).mpr (valid s))
  have bounded := le_listSum_of_mem terms (fun value member => by
    obtain ⟨s, _, same⟩ := List.mem_map.mp member
    cases same
    exact nonnegative s) (term r) (List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩)
  exact ⟨le_trans bounded (certificate.weighted_slack_zero normalized).1, nonnegative r⟩

end Thesis.Probability.AnalyticLinear
