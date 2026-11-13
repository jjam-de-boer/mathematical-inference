import Thesis.Probability.ConstructiveRealEntropyMultipliers
import Thesis.Probability.ConstructiveRealLogInverse

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

namespace LagrangeCoefficients

/-- The affine score uses the original rational response coefficients. -/
def score {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (column : Fin variables) : ConstructiveReal :=
  RationalLinear.realRationalDot problem.rows.length (fun row => (problem.rows[row.val]).coefficients column) certificate.coefficient

def partition {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) : ConstructiveReal :=
  listSum ((List.finRange variables).map (fun i => (neg (certificate.score i)).exp))

/-- Nonemptiness gives an explicit positive summand. No positive lower bound
for a finite sum is chosen from an existential proposition. -/
def partitionLower {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) : PositiveRatio :=
  (neg (certificate.score ⟨0, problem.nonempty⟩)).expLower

theorem partition_positive {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) :
    LE (ofSignedRatio certificate.partitionLower.toSignedRatio) certificate.partition := by
  apply le_trans (exp_lower (neg (certificate.score ⟨0, problem.nonempty⟩)))
  apply le_listSum_of_mem
  · intro value member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    exact exp_nonnegative _
  · exact List.mem_map.mpr ⟨⟨0, problem.nonempty⟩, List.mem_finRange _, rfl⟩

def partitionInverse {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) : ConstructiveReal :=
  certificate.partition.positiveInverse certificate.partitionLower certificate.partition_positive

end LagrangeCoefficients

private theorem subtract_one (value : ConstructiveReal) : Equiv (sub (add value one) one) value :=
  equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg one)) (add_zero value))

private theorem logarithm_score (value offset score : ConstructiveReal)
    (same : Equiv (neg (add value one)) (add offset score)) :
    Equiv value (add (neg (add one offset)) (neg score)) := by
  have restored := equiv_trans (equiv_symm (neg_neg (add value one))) (neg_congr same)
  have shifted := add_congr restored (equiv_refl (neg one))
  have arranged : Equiv (sub (neg (add offset score)) one) (add (neg (add one offset)) (neg score)) :=
    equiv_trans (equiv_symm (neg_add (add offset score) one))
      (equiv_trans (neg_congr (equiv_trans (add_comm _ _) (equiv_symm (add_assoc one offset score))))
        (neg_add _ _))
  exact equiv_trans (equiv_symm (subtract_one value)) (equiv_trans shifted arranged)

private theorem RealLaw.mass_sum {problem : RationalEntropyProblem variables} (law : problem.RealLaw) :
    Equiv (listSum ((List.finRange variables).map (fun i => (law.mass i).value))) one := by
  have evaluation := equiv_trans (FiniteLinear.realDot_pair variables (fun _ => 1) (fun i => (law.mass i).value))
    (listSum_map_congr (List.finRange variables) _ _ (fun i _ => one_mul (law.mass i).value))
  exact equiv_trans (equiv_symm evaluation) law.normalized

private def prefactor {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) : ConstructiveReal :=
  (neg (add one certificate.offset)).exp

private theorem exponential_coordinate {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)))
    (column : Fin variables) :
    Equiv (law.mass column).value (mul (prefactor certificate) (neg (certificate.score column)).exp) :=
  equiv_trans (equiv_symm (exp_positiveLn _ (lower column) (positive column)))
    (equiv_trans (exp_congr (logarithm_score _ _ _ (certificate.represents column))) (exp_add _ _))

private theorem prefactor_partition {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i))) :
    Equiv (mul (prefactor certificate) certificate.partition) one := by
  have represented := listSum_map_congr (List.finRange variables) _ _ (fun i _ => exponential_coordinate law lower positive certificate i)
  have distributed : Equiv (mul (prefactor certificate) certificate.partition)
      (listSum ((List.finRange variables).map (fun i => mul (prefactor certificate) (neg (certificate.score i)).exp))) := by
    simpa only [List.map_map] using mul_listSum (prefactor certificate)
      ((List.finRange variables).map (fun i => (neg (certificate.score i)).exp))
  exact equiv_trans distributed (equiv_trans (equiv_symm represented) law.mass_sum)

/-- Natural-unit multiplier equations imply the normalized exponential
family. The partition inverse and its positive domain certificate are
constructed. These are auxiliary analytic probabilities, without a claim
that a general exponential law has exactly representable rational weights. -/
theorem gibbsForm_of_coefficients {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)))
    (column : Fin variables) :
    Equiv (law.mass column).value (mul (neg (certificate.score column)).exp certificate.partitionInverse) := by
  have inverse : Equiv (prefactor certificate) certificate.partitionInverse :=
    inverse_unique certificate.partition _ _
      (equiv_trans (mul_comm _ _) (prefactor_partition law lower positive certificate))
      (certificate.partition.mul_positiveInverse certificate.partitionLower certificate.partition_positive)
  exact equiv_trans (exponential_coordinate law lower positive certificate column)
    (equiv_trans (mul_comm _ _) (mul_congr (equiv_refl _) inverse))

/-- The necessary coefficients are produced from the positive maximum;
this conclusion does not assume a multiplier solution supplied by a caller.
Interval KKT signs and reasoning on forced-zero faces remain separate. -/
theorem RealLaw.maximum_gibbsForm {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value) (column : Fin variables) :
    let certificate := law.naturalLagrangeMultipliers maximal lower positive
    Equiv (law.mass column).value (mul (neg (certificate.score column)).exp certificate.partitionInverse) :=
  gibbsForm_of_coefficients law lower positive _ column

/-- The normalization coefficient is log(Z)-1 in natural units. This
identity is derived from normalization rather than taken as a definition. -/
theorem partition_log_offset {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i))) :
    Equiv (certificate.partition.positiveLn certificate.partitionLower certificate.partition_positive) (add one certificate.offset) := by
  have normalized := prefactor_partition law lower positive certificate
  have opposite : Equiv (mul (prefactor certificate) (add one certificate.offset).exp) one :=
    equiv_trans (mul_comm _ _) (exp_mul_exp_neg _)
  have partitionValue : Equiv certificate.partition (add one certificate.offset).exp :=
    inverse_unique (prefactor certificate) _ _ normalized opposite
  exact equiv_trans (positiveLn_congr partitionValue _ _ certificate.partition_positive (add one certificate.offset).exp_lower) (positiveLn_exp _)

end Thesis.Probability.Distros.RationalEntropyProblem
