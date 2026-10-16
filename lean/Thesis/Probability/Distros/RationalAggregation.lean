import Thesis.Probability.Distros.RationalParameters
import Thesis.Probability.Distros.ReinforcedAggregation

namespace Thesis.Probability.Distros

namespace RationalParametersEquiv

theorem modify_add {alphas betas : List QProb} (same : RationalParametersEquiv alphas betas)
    {a b : QProb} (amount : QProb.Equiv a b) (index : Nat) :
    RationalParametersEquiv (alphas.modify index (fun old => QProb.add old a))
      (betas.modify index (fun old => QProb.add old b)) := by
  induction alphas generalizing betas index with
  | nil => cases betas with
      | nil => exact refl []
      | cons beta betas => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; omega
  | cons alpha alphas ih => cases betas with
      | nil => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; omega
      | cons beta betas =>
          have tail : RationalParametersEquiv alphas betas := ⟨Nat.succ.inj same.1, fun i => same.2 (i + 1)⟩
          cases index with
          | zero => exact cons (QProb.add_congr (same.2 0) amount) tail
          | succ index => exact cons (same.2 0) (ih tail index)

end RationalParametersEquiv

/-- Sum rational colour parameters according to their destination labels.
Empty destination categories retain parameter zero. -/
def aggregateRationalParameters (groups : Nat) : List Nat → List QProb → List QProb
  | label :: labels, alpha :: alphas =>
      (aggregateRationalParameters groups labels alphas).modify label (fun old => QProb.add old alpha)
  | _, _ => List.replicate groups QProb.zero

theorem aggregateRationalParameters_length (groups : Nat) (labels : List Nat) (alphas : List QProb) :
    (aggregateRationalParameters groups labels alphas).length = groups := by
  induction labels generalizing alphas with
  | nil => exact List.length_replicate
  | cons label labels ih => cases alphas <;>
      simp only [aggregateRationalParameters, List.length_modify, List.length_replicate, ih]

theorem aggregateRationalParameters_congr (groups : Nat) (labels : List Nat) {alphas betas : List QProb}
    (same : RationalParametersEquiv alphas betas) :
    RationalParametersEquiv (aggregateRationalParameters groups labels alphas)
      (aggregateRationalParameters groups labels betas) := by
  induction labels generalizing alphas betas with
  | nil => exact .refl _
  | cons label labels ih => cases alphas with
      | nil => cases betas with
          | nil => exact .refl _
          | cons beta betas => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; omega
      | cons alpha alphas => cases betas with
          | nil => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; omega
          | cons beta betas =>
              exact (ih ⟨Nat.succ.inj same.1, fun i => same.2 (i + 1)⟩).modify_add (same.2 0) label

theorem urnRatioParameters_zero (groups denominator : Nat) (positive : 0 < denominator) :
    RationalParametersEquiv (urnRatioParameters (List.replicate groups 0) denominator positive)
      (List.replicate groups QProb.zero) := by
  induction groups with
  | zero => exact .refl []
  | succ groups ih =>
      exact .cons (by change 0 * 1 = 0 * denominator; simp only [Nat.zero_mul]) ih

theorem urnRatioParameters_modify_add (weights : List Nat) (denominator : Nat) (positive : 0 < denominator)
    (index amount : Nat) :
    RationalParametersEquiv (urnRatioParameters (weights.modify index (fun old => old + amount)) denominator positive)
      ((urnRatioParameters weights denominator positive).modify index
        (fun old => QProb.add old ⟨amount, denominator, positive⟩)) := by
  induction weights generalizing index with
  | nil => exact .refl []
  | cons weight weights ih => cases index with
      | zero => exact .cons (QProb.equiv_symm (QProb.add_mk_same_den denominator positive weight amount)) (.refl _)
      | succ index => exact .cons (QProb.equiv_refl _) (ih index)

theorem aggregateRationalParameters_ratios (groups : Nat) (labels weights : List Nat)
    (denominator : Nat) (positive : 0 < denominator) :
    RationalParametersEquiv
      (urnRatioParameters (aggregateCounts groups labels weights) denominator positive)
      (aggregateRationalParameters groups labels (urnRatioParameters weights denominator positive)) := by
  induction labels generalizing weights with
  | nil => exact urnRatioParameters_zero groups denominator positive
  | cons label labels ih => cases weights with
      | nil => exact urnRatioParameters_zero groups denominator positive
      | cons weight weights =>
          exact (urnRatioParameters_modify_add _ denominator positive label weight).trans
            ((ih weights).modify_add (QProb.equiv_refl _) label)

theorem aggregateRationalParameters_encoding (groups : Nat) (labels : List Nat) (alphas : List QProb) :
    RationalParametersEquiv
      (urnRatioParameters (aggregateCounts groups labels (rationalUrnWeights alphas))
        (QProb.listSum alphas).den (QProb.listSum alphas).den_pos)
      (aggregateRationalParameters groups labels alphas) :=
  (aggregateRationalParameters_ratios groups labels _ _ _).trans
    (aggregateRationalParameters_congr groups labels (rationalParameters_encoding alphas))

theorem aggregateRationalParameters_positive (groups : Nat) (labels : List Nat) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num) (dimension : labels.length = alphas.length)
    (within : ∀ label ∈ labels, label < groups) :
    0 < (QProb.listSum (aggregateRationalParameters groups labels alphas)).num := by
  apply (aggregateRationalParameters_encoding groups labels alphas).positive
  apply urnRatioParameters_positive
  rw [aggregateCounts_sum groups labels _ (by rw [rationalUrnWeights_length]; exact dimension) within,
    rationalUrnWeights_sum]
  exact positive

/-- Rational Pólya paths coarsen by summing their actual rational parameters,
with no restriction on fraction presentations or zero destination weights. -/
theorem rationalPolya_aggregation (n groups : Nat) (alphas : List QProb) (labels : List Nat)
    (positive : 0 < (QProb.listSum alphas).num) (dimension : labels.length = alphas.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((rationalPolyaDistro n alphas positive).map (fun word => word.map (fun i => labels.getD i 0))).SameLaw
      (rationalPolyaDistro n (aggregateRationalParameters groups labels alphas)
        (aggregateRationalParameters_positive groups labels alphas positive dimension within)) := by
  have weightsPositive : 0 < (rationalUrnWeights alphas).sum := by rw [rationalUrnWeights_sum]; exact positive
  have groupedPositive : 0 < (aggregateCounts groups labels (rationalUrnWeights alphas)).sum := by
    rw [aggregateCounts_sum groups labels _ (by rw [rationalUrnWeights_length]; exact dimension) within]
    exact weightsPositive
  have aggregated := reinforcedUrn_aggregation n groups (rationalUrnWeights alphas) labels (QProb.listSum alphas).den
    weightsPositive (by rw [rationalUrnWeights_length]; exact dimension) within
  exact aggregated.trans ((reinforcedUrn_rationalParameters n _ _ groupedPositive (QProb.listSum alphas).den_pos).trans
    (rationalPolya_sameLaw_parameters n _ _ _ _ (aggregateRationalParameters_encoding groups labels alphas)))

/-- The complete rational Dirichlet-multinomial count law respects every
category partition, including categories receiving no original colours. -/
theorem rationalDirichletMultinomial_aggregation (n groups : Nat) (alphas : List QProb) (labels : List Nat)
    (positive : 0 < (QProb.listSum alphas).num) (dimension : labels.length = alphas.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((rationalDirichletMultinomialDistro n alphas positive).map (aggregateCounts groups labels)).SameLaw
      (rationalDirichletMultinomialDistro n (aggregateRationalParameters groups labels alphas)
        (aggregateRationalParameters_positive groups labels alphas positive dimension within)) := by
  have weightsPositive : 0 < (rationalUrnWeights alphas).sum := by rw [rationalUrnWeights_sum]; exact positive
  have groupedPositive : 0 < (aggregateCounts groups labels (rationalUrnWeights alphas)).sum := by
    rw [aggregateCounts_sum groups labels _ (by rw [rationalUrnWeights_length]; exact dimension) within]
    exact weightsPositive
  have aggregated := reinforcedCount_aggregation n groups (rationalUrnWeights alphas) labels (QProb.listSum alphas).den
    weightsPositive (by rw [rationalUrnWeights_length]; exact dimension) within
  exact aggregated.trans ((reinforcedCount_rationalParameters n _ _ groupedPositive (QProb.listSum alphas).den_pos).trans
    (rationalDirichletMultinomial_sameLaw_parameters n _ _ _ _ (aggregateRationalParameters_encoding groups labels alphas)))

end Thesis.Probability.Distros
