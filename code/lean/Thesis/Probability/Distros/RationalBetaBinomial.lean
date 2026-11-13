import Thesis.Probability.Distros.RationalAggregation

namespace Thesis.Probability.Distros

/-- The two-colour rational Pólya count, including either zero parameter
when the total parameter is positive. -/
def rationalBetaBinomialNatDistro (n : Nat) (alpha beta : QProb)
    (positive : 0 < (QProb.listSum [alpha, beta]).num) : NatDistro (List Nat) :=
  ⟨rationalDirichletMultinomialDistro n [alpha, beta] positive, fun counts => counts.getD 0 0⟩

/-- The sum of all other colour parameters in the common encoded units.
No subtraction of an unproved nonnegative rational is used. -/
def rationalParameterComplement (alphas : List QProb) (index : Nat) : QProb :=
  ⟨(rationalUrnWeights alphas).sum - (rationalUrnWeights alphas).getD index 0,
    (QProb.listSum alphas).den, (QProb.listSum alphas).den_pos⟩

theorem rationalParameterComplement_balance (alphas : List QProb) (index : Nat) :
    QProb.Equiv (QProb.add (alphas.getD index QProb.zero) (rationalParameterComplement alphas index))
      (QProb.listSum alphas) := by
  refine QProb.equiv_trans (QProb.add_congr
    (QProb.equiv_symm (rationalUrnWeights_parameter alphas index)) (QProb.equiv_refl _)) ?_
  refine QProb.equiv_trans (QProb.add_mk_same_den _ _ _ _) ?_
  have total := Nat.add_sub_of_le (list_getD_le_sum (rationalUrnWeights alphas) index)
  change ((rationalUrnWeights alphas).getD index 0 +
      ((rationalUrnWeights alphas).sum - (rationalUrnWeights alphas).getD index 0)) *
      (QProb.listSum alphas).den = (QProb.listSum alphas).num * (QProb.listSum alphas).den
  rw [total, rationalUrnWeights_sum]

theorem aggregateRationalParameters_coordinate (alphas : List QProb) (index : Nat) (within : index < alphas.length) :
    RationalParametersEquiv (aggregateRationalParameters 2 (coordinateArguments 0 alphas.length index) alphas)
      [alphas.getD index QProb.zero, rationalParameterComplement alphas index] := by
  have encoded := (aggregateRationalParameters_encoding 2 (coordinateArguments 0 alphas.length index) alphas).symm
  have identity : aggregateCounts 2 (coordinateArguments 0 alphas.length index) (rationalUrnWeights alphas) =
      [(rationalUrnWeights alphas).getD index 0,
        (rationalUrnWeights alphas).sum - (rationalUrnWeights alphas).getD index 0] := by
    rw [← rationalUrnWeights_length alphas]
    exact aggregateCounts_coordinate _ index (by rw [rationalUrnWeights_length]; exact within)
  rw [identity] at encoded
  exact encoded.trans (.cons (rationalUrnWeights_parameter alphas index) (.cons (QProb.equiv_refl _) (.refl [])))

theorem rationalCoordinate_parameters_positive (alphas : List QProb) (positive : 0 < (QProb.listSum alphas).num)
    (index : Nat) (within : index < alphas.length) :
    0 < (QProb.listSum [alphas.getD index QProb.zero, rationalParameterComplement alphas index]).num :=
  (aggregateRationalParameters_coordinate alphas index within).positive
    (aggregateRationalParameters_positive 2 _ alphas positive (coordinateArguments_length _ _ _) (coordinateLabels_within _ _))

/-- Every coordinate has its rational beta-binomial marginal. Both the
selected parameter and its complement may vanish separately. -/
theorem rationalDirichletMultinomial_coordinate_betaBinomial (n : Nat) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num) (index : Nat) (within : index < alphas.length) :
    (⟨rationalDirichletMultinomialDistro n alphas positive, fun counts => counts.getD index 0⟩ : NatDistro (List Nat)).SameLaw
      (rationalBetaBinomialNatDistro n (alphas.getD index QProb.zero) (rationalParameterComplement alphas index)
        (rationalCoordinate_parameters_positive alphas positive index within)) := by
  let labels := coordinateArguments 0 alphas.length index
  let μ := rationalDirichletMultinomialDistro n alphas positive
  have grouped := rationalDirichletMultinomial_aggregation n 2 alphas labels positive
    (coordinateArguments_length _ _ _) (coordinateLabels_within _ _)
  have beta := rationalDirichletMultinomial_sameLaw_parameters n _ _
    (aggregateRationalParameters_positive 2 labels alphas positive (coordinateArguments_length _ _ _) (coordinateLabels_within _ _))
    (rationalCoordinate_parameters_positive alphas positive index within)
    (aggregateRationalParameters_coordinate alphas index within)
  apply (NatDistro.sameLaw_iff_events _ _).mpr
  intro event
  refine QProb.equiv_trans (μ.probVal_congr_on_support _
    (fun counts => event ((aggregateCounts 2 labels counts).getD 0 0)) ?_) ?_
  · intro atom member
    have support := reinforcedCount_support n (rationalUrnWeights alphas) (QProb.listSum alphas).den atom member
    simp only [rationalUrnWeights_length] at support
    change event (atom.1.getD index 0) = event ((aggregateCounts 2 labels atom.1).getD 0 0)
    have identity : aggregateCounts 2 labels atom.1 = [atom.1.getD index 0, atom.1.sum - atom.1.getD index 0] := by
      change aggregateCounts 2 (coordinateArguments 0 alphas.length index) atom.1 = _
      rw [← support.1, aggregateCounts_coordinate atom.1 index (by omega)]
    rw [identity]
    rfl
  · exact QProb.equiv_trans (QProb.equiv_symm (μ.map_probVal (aggregateCounts 2 labels)
      (fun counts => event (counts.getD 0 0))))
      (QProb.equiv_trans (grouped (fun counts => event (counts.getD 0 0)))
        (beta (fun counts => event (counts.getD 0 0))))

/-- Integral rational parameters recover the existing beta-binomial law. -/
theorem rationalBetaBinomial_ofNat (n a b : Nat) (positive : 0 < a + b) :
    (rationalBetaBinomialNatDistro n (QProb.ofNat a) (QProb.ofNat b)
      (by simpa only [QProb.listSum, QProb.add, QProb.ofNat, QProb.zero, Nat.mul_one,
        Nat.mul_zero, Nat.add_zero] using positive)).SameLaw
      (betaBinomialNatDistroOfTotal n a b positive) := by
  have ordinary := rationalDirichletMultinomial_ofNat n [a, b] (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive)
  have same : (rationalDirichletMultinomialDistro n ([a, b].map QProb.ofNat)
      (by rw [← rationalUrnWeights_sum, (rationalUrnWeights_ofNat [a, b]).2];
          simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive)).SameLaw
      (dirichletMultinomialDistro n [a, b] (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive)) := by
    rw [ordinary]
    exact Distro.SameLaw.refl _
  have numeric := NatDistro.sameLaw_of_distro same (fun counts => counts.getD 0 0)
  exact numeric.trans (dirichletMultinomial_two_coordinate n a b positive)

end Thesis.Probability.Distros
