import Thesis.Probability.ConstructiveRealFiniteFibers
import Thesis.Probability.ConstructiveRealGibbsFamilyDerivative

namespace Thesis.Probability
open ConstructiveReal

/-- A physical grouping of distinct microstate indices with observables
constant on each retained macrostate fiber. The microstate family has unit
reference weights; the macrostate reference weights are the computed fiber
cardinalities. This is not aggregation of repeated distribution-record atoms. -/
structure FiniteGibbsGrouping (micro groups features : Nat) where
  nonempty : 0 < micro
  states : FiniteStateGrouping micro groups
  response : Fin features → Fin groups → SignedRatio

namespace FiniteGibbsGrouping
open Distros.RationalLinear
open ConstructiveReal.FiniteFibers

def microFamily (grouping : FiniteGibbsGrouping micro groups features) : FiniteGibbsFamily micro features :=
  ⟨grouping.nonempty, (fun _ => PositiveRatio.one), (fun k i => grouping.response k (grouping.states.label i))⟩

def macroFamily (grouping : FiniteGibbsGrouping micro groups features) : FiniteGibbsFamily groups features :=
  ⟨grouping.states.macro_positive grouping.nonempty, grouping.states.reference, grouping.response⟩

def baseWeight (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) (j : Fin groups) : ConstructiveReal :=
  (neg (grouping.macroFamily.score parameters j)).exp

/-- Every actual microstate in a fiber has this unnormalized Gibbs weight. -/
theorem micro_weight (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) (i : Fin micro) :
    Equiv ((grouping.microFamily.asTilt parameters).weight one i) (grouping.baseWeight parameters (grouping.states.label i)) :=
  exp_congr (equiv_trans (add_congr (one_mul _) (positiveLn_one PositiveRatio.one (le_refl one))) (add_zero _))

/-- Macrostate weight is the actual degeneracy times one microstate weight.
The multiplicity has been counted from the finite labeling data. -/
theorem macro_weight (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) (j : Fin groups) :
    Equiv ((grouping.macroFamily.asTilt parameters).weight one j)
      (mul (realInteger (grouping.states.degeneracy j : Int)) (grouping.baseWeight parameters j)) :=
  equiv_trans (exp_congr (add_congr (one_mul _) (equiv_refl _)))
    (equiv_trans (exp_add _ _) (equiv_trans (mul_congr (equiv_refl _)
      (exp_positiveLn _ (grouping.states.reference j) (le_refl _))) (mul_comm _ _)))

/-- Summing the actual microstate weights in one fiber produces exactly
the macrostate weight, rather than merely a proposed expression for it. -/
theorem fiber_weight (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) (j : Fin groups) :
    Equiv (sumFiber grouping.states.label ((grouping.microFamily.asTilt parameters).weight one) j)
      ((grouping.macroFamily.asTilt parameters).weight one j) := by
  have counted := sumFiber_constant grouping.states.label j ((grouping.microFamily.asTilt parameters).weight one)
    (grouping.baseWeight parameters j) (fun i same => equiv_trans (grouping.micro_weight parameters i) (by
      rw [← same]
      exact equiv_refl _))
  exact equiv_trans counted (equiv_symm (grouping.macro_weight parameters j))

/-- The macrostate and microstate partition functions agree by proved finite
fiber Fubini, including fibers containing several equal-observable states. -/
theorem partition_eq (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) :
    Equiv (grouping.microFamily.partition parameters) (grouping.macroFamily.partition parameters) :=
  equiv_trans (grouped_sum grouping.states.label ((grouping.microFamily.asTilt parameters).weight one))
    (listSum_map_congr (List.finRange groups) _ _ (fun j _ => grouping.fiber_weight parameters j))

theorem inverse_eq (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) :
    Equiv ((grouping.microFamily.asTilt parameters).partitionInverse one) ((grouping.macroFamily.asTilt parameters).partitionInverse one) :=
  positiveInverse_congr (grouping.partition_eq parameters) _ _
    ((grouping.microFamily.asTilt parameters).partition_positive one) ((grouping.macroFamily.asTilt parameters).partition_positive one)

/-- The normalized macrostate probability is the sum of the normalized
microstate probabilities in its fiber. Rational representability of these
analytic probabilities is not assumed. -/
theorem mass_aggregated (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) (j : Fin groups) :
    Equiv (sumFiber grouping.states.label (grouping.microFamily.mass parameters) j) (grouping.macroFamily.mass parameters j) :=
  equiv_trans (sumFiber_mul_right grouping.states.label ((grouping.microFamily.asTilt parameters).weight one)
    ((grouping.microFamily.asTilt parameters).partitionInverse one) j)
    (mul_congr (grouping.fiber_weight parameters j) (grouping.inverse_eq parameters))

/-- Equal observable labels do not collapse physical states: each retains
the same individual probability, while the preceding theorem sums them. -/
theorem mass_same_fiber (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal)
    (i k : Fin micro) (same : grouping.states.label i = grouping.states.label k) :
    Equiv (grouping.microFamily.mass parameters i) (grouping.microFamily.mass parameters k) := by
  have weights := equiv_trans (grouping.micro_weight parameters i) (equiv_trans
    (by rw [same]; exact equiv_refl _) (equiv_symm (grouping.micro_weight parameters k)))
  exact mul_congr weights (equiv_refl _)

/-- Every macrostate observable has exactly the same expectation before and
after actual probability aggregation. In particular all constraint features
and their products are preserved. -/
theorem observable_mean (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal)
    (observable : Fin groups → ConstructiveReal) :
    Equiv (grouping.microFamily.expectation parameters (fun i => observable (grouping.states.label i)))
      (grouping.macroFamily.expectation parameters observable) :=
  equiv_trans (grouped_pair grouping.states.label (grouping.microFamily.mass parameters) observable)
    (FiniteLinear.pair_congr groups observable observable _ _ (fun _ => equiv_refl _) (grouping.mass_aggregated parameters))

theorem feature_mean (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) (k : Fin features) :
    Equiv (grouping.microFamily.expectation parameters (grouping.microFamily.feature k))
      (grouping.macroFamily.expectation parameters (grouping.macroFamily.feature k)) :=
  grouping.observable_mean parameters (grouping.macroFamily.feature k)

theorem logPartition_eq (grouping : FiniteGibbsGrouping micro groups features) (parameters : Fin features → ConstructiveReal) :
    Equiv (grouping.microFamily.logPartition parameters) (grouping.macroFamily.logPartition parameters) :=
  positiveLn_congr (grouping.partition_eq parameters) _ _
    ((grouping.microFamily.asTilt parameters).partition_positive one) ((grouping.macroFamily.asTilt parameters).partition_positive one)

end FiniteGibbsGrouping
end Thesis.Probability
