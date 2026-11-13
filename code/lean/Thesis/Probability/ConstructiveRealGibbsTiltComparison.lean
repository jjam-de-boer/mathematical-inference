import Thesis.Probability.ConstructiveRealGibbsTiltEntropy

namespace Thesis.Probability.FiniteGibbsTilt
open ConstructiveReal

/-- Equivalent coordinate log weights give the same analytic law, including
when the two presentations use different affine parameter paths. -/
theorem partition_congr {first second : FiniteGibbsTilt states} {left right : ConstructiveReal}
    (same : ∀ i, Equiv (first.logWeight left i) (second.logWeight right i)) :
    Equiv (first.partition left) (second.partition right) :=
  listSum_map_congr (List.finRange states) _ _ (fun i _ => exp_congr (same i))

theorem inverse_congr {first second : FiniteGibbsTilt states} {left right : ConstructiveReal}
    (same : ∀ i, Equiv (first.logWeight left i) (second.logWeight right i)) :
    Equiv (first.partitionInverse left) (second.partitionInverse right) :=
  positiveInverse_congr (partition_congr same) _ _ (first.partition_positive left) (second.partition_positive right)

theorem mass_congr {first second : FiniteGibbsTilt states} {left right : ConstructiveReal}
    (same : ∀ i, Equiv (first.logWeight left i) (second.logWeight right i)) (i : Fin states) :
    Equiv (first.mass left i) (second.mass right i) := mul_congr (exp_congr (same i)) (inverse_congr same)

theorem expectation_compare {first second : FiniteGibbsTilt states} {left right : ConstructiveReal}
    (same : ∀ i, Equiv (first.logWeight left i) (second.logWeight right i)) (observable : Fin states → ConstructiveReal) :
    Equiv (first.expectation left observable) (second.expectation right observable) :=
  FiniteLinear.pair_congr states observable observable _ _ (fun _ => equiv_refl _) (mass_congr same)

theorem covariance_compare {first second : FiniteGibbsTilt states} {left right : ConstructiveReal}
    (same : ∀ i, Equiv (first.logWeight left i) (second.logWeight right i))
    (a b : Fin states → ConstructiveReal) : Equiv (first.covariance left a b) (second.covariance right a b) :=
  add_congr (expectation_compare same _) (neg_congr (mul_congr (expectation_compare same a) (expectation_compare same b)))

theorem entropy_congr {first second : FiniteGibbsTilt states} {left right : ConstructiveReal}
    (same : ∀ i, Equiv (first.logWeight left i) (second.logWeight right i)) :
    Equiv (first.entropy left) (second.entropy right) := by
  unfold entropy realEntropySum
  simp only [List.map_map, Function.comp_def]
  exact listSum_map_congr (List.finRange states) _ _ (fun i _ => realEntropyTerm_congr (mass_congr same i)
    (first.probability left i).nonnegative (second.probability right i).nonnegative
    (first.probability left i).bounded (second.probability right i).bounded)

theorem logPartition_congr {first second : FiniteGibbsTilt states} {left right : ConstructiveReal}
    (same : ∀ i, Equiv (first.logWeight left i) (second.logWeight right i)) :
    Equiv (first.logPartition left) (second.logPartition right) :=
  positiveLn_congr (partition_congr same) _ _ (first.partition_positive left) (second.partition_positive right)

end Thesis.Probability.FiniteGibbsTilt
