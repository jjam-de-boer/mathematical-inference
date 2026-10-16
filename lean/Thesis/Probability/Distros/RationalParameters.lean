import Thesis.Probability.Distros.RationalPolya

namespace Thesis.Probability.Distros

/-- Parameters in the original urn's units, divided by its positive
reinforcement. These may exceed one; `QProb` represents nonnegative rationals. -/
def urnRatioParameters (weights : List Nat) (increment : Nat) (positive : 0 < increment) : List QProb :=
  weights.map (fun weight => ⟨weight, increment, positive⟩)

theorem urnRatioParameters_getD (weights : List Nat) (increment : Nat) (positive : 0 < increment) (index : Nat) :
    QProb.Equiv ((urnRatioParameters weights increment positive).getD index QProb.zero)
      ⟨weights.getD index 0, increment, positive⟩ := by
  induction weights generalizing index with
  | nil => simp only [urnRatioParameters, List.map_nil, List.getD_nil, QProb.Equiv, QProb.zero, Nat.zero_mul]
  | cons weight weights ih => cases index with
      | zero => exact QProb.equiv_refl _
      | succ index => exact ih index

theorem urnRatioParameters_positive (weights : List Nat) (increment : Nat)
    (positive : 0 < increment) (nonempty : 0 < weights.sum) :
    0 < (QProb.listSum (urnRatioParameters weights increment positive)).num := by
  exact (QProb.equiv_num_pos_iff (QProb.listSum_mk_same_den increment positive weights)).mpr nonempty

/-- Every integer urn with positive reinforcement is a unit-reinforcement
rational urn with parameters `weights / increment`. The identity concerns the
entire ordered path law, including arbitrary zero initial colour weights. -/
theorem reinforcedUrn_rationalParameters (n : Nat) (weights : List Nat) (increment : Nat)
    (positive : 0 < weights.sum) (reinforcement : 0 < increment) :
    (reinforcedUrnDistro n weights increment positive).SameLaw
      (rationalPolyaDistro n (urnRatioParameters weights increment reinforcement)
        (urnRatioParameters_positive weights increment reinforcement positive)) := by
  let parameters := urnRatioParameters weights increment reinforcement
  let denominator := (QProb.listSum parameters).den
  have cross : weights.map (fun a => denominator * a) =
      (rationalUrnWeights parameters).map (fun a => increment * a) := by
    apply scaledLists_eq_of_cross
    · simp only [rationalUrnWeights_length, parameters, urnRatioParameters, List.length_map]
    · intro i
      have h := QProb.equiv_trans (rationalUrnWeights_parameter parameters i)
        (urnRatioParameters_getD weights increment reinforcement i)
      change (rationalUrnWeights parameters).getD i 0 * increment = weights.getD i 0 * denominator at h
      calc
        _ = weights.getD i 0 * denominator := Nat.mul_comm _ _
        _ = _ := by rw [← h, Nat.mul_comm]
  have left := reinforcedUrn_scale_sameLaw n weights increment denominator positive (QProb.listSum parameters).den_pos
  have right := reinforcedUrn_scale_sameLaw n (rationalUrnWeights parameters) denominator increment
    (by rw [rationalUrnWeights_sum]; exact urnRatioParameters_positive weights increment reinforcement positive) reinforcement
  simp only [cross, Nat.mul_comm denominator increment] at left
  exact left.symm.trans right

/-- The same parameter identification for the complete count-vector law. -/
theorem reinforcedCount_rationalParameters (n : Nat) (weights : List Nat) (increment : Nat)
    (positive : 0 < weights.sum) (reinforcement : 0 < increment) :
    (reinforcedCountDistro n weights increment positive).SameLaw
      (rationalDirichletMultinomialDistro n (urnRatioParameters weights increment reinforcement)
        (urnRatioParameters_positive weights increment reinforcement positive)) := by
  have paths := (reinforcedUrn_rationalParameters n weights increment positive reinforcement).map (colourCounts weights.length)
  have left := reinforcedUrn_count_correspondence n weights increment positive
  have right := rationalPolya_count_correspondence n (urnRatioParameters weights increment reinforcement)
    (urnRatioParameters_positive weights increment reinforcement positive)
  simp only [urnRatioParameters, List.length_map] at right
  exact left.symm.trans (paths.trans right)

/-- An encoding returned to rational parameter units recovers every original
parameter, independently of the chosen fraction presentations. -/
theorem rationalParameters_encoding (alphas : List QProb) :
    RationalParametersEquiv
      (urnRatioParameters (rationalUrnWeights alphas) (QProb.listSum alphas).den (QProb.listSum alphas).den_pos) alphas := by
  constructor
  · simp only [urnRatioParameters, List.length_map, rationalUrnWeights_length]
  · intro i
    exact QProb.equiv_trans (urnRatioParameters_getD _ _ _ i) (rationalUrnWeights_parameter alphas i)

namespace RationalParametersEquiv

theorem refl (alphas : List QProb) : RationalParametersEquiv alphas alphas :=
  ⟨rfl, fun _ => QProb.equiv_refl _⟩

theorem symm {alphas betas : List QProb} (same : RationalParametersEquiv alphas betas) :
    RationalParametersEquiv betas alphas := ⟨same.1.symm, fun i => QProb.equiv_symm (same.2 i)⟩

theorem trans {alphas betas gammas : List QProb} (same : RationalParametersEquiv alphas betas)
    (next : RationalParametersEquiv betas gammas) : RationalParametersEquiv alphas gammas :=
  ⟨same.1.trans next.1, fun i => QProb.equiv_trans (same.2 i) (next.2 i)⟩

theorem cons {alpha beta : QProb} {alphas betas : List QProb} (head : QProb.Equiv alpha beta)
    (tail : RationalParametersEquiv alphas betas) : RationalParametersEquiv (alpha :: alphas) (beta :: betas) := by
  refine ⟨congrArg Nat.succ tail.1, fun i => ?_⟩
  cases i with
  | zero => exact head
  | succ i => exact tail.2 i

theorem listSum {alphas betas : List QProb} (same : RationalParametersEquiv alphas betas) :
    QProb.Equiv (QProb.listSum alphas) (QProb.listSum betas) := by
  induction alphas generalizing betas with
  | nil => cases betas with
      | nil => exact QProb.equiv_refl _
      | cons beta betas => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; omega
  | cons alpha alphas ih => cases betas with
      | nil => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; omega
      | cons beta betas =>
          exact QProb.add_congr (same.2 0)
            (ih ⟨Nat.succ.inj same.1, fun i => same.2 (i + 1)⟩)

theorem positive {alphas betas : List QProb} (same : RationalParametersEquiv alphas betas)
    (positive : 0 < (QProb.listSum alphas).num) : 0 < (QProb.listSum betas).num :=
  (QProb.equiv_num_pos_iff same.listSum).mp positive

end RationalParametersEquiv
end Thesis.Probability.Distros
