import Thesis.CausalTransport.ConditionalColliderCounterexample
import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalColliderRegression

open Probability

/-!
# Regression checks for conditional collider countermodels

The probability checks use unequal context masses and repeated source labels;
their conditioning denominators really differ.  Bias retains the posterior
gap, whereas fair noise erases it.  Full posterior support is checked
separately from separation.

The structural fixture is `U -> R <- A` with `A <-> R`.  The original query
`P(U | do(A), R)` genuinely fails conditional ID and has no exchangeable
conditioner.  Its hedge root is `R`, which belongs to the conditioner rather
than the queried outcome.  The collider construction supplies a complete
positive counterexample for that query on three-valued observed alphabets,
without evaluating a giant augmented latent table or supplying a kernel gap.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Exact channel checks with genuinely unequal conditioning masses -/

/-- The first source repeats its false/context atom and includes a zero
atom.  Those representational details must not alter the posterior law. -/
def leftSource : FiniteProbRecord (Bool × Bool) where
  atoms := [((false, true), 1), ((false, true), 1), ((true, true), 1),
    ((true, false), 3), ((false, false), 0)]
  den := 6
  den_pos := by decide
  total_mass := rfl

def rightSource : FiniteProbRecord (Bool × Bool) where
  atoms := [((false, true), 1), ((true, true), 1), ((false, false), 8)]
  den := 10
  den_pos := by decide
  total_mass := rfl

def privateNoise : FiniteProbRecord Bool := FiniteProbRecord.biasedFlip 1 1 (by decide)

theorem left_context_positive : leftSource.EventPositive (fun sample => sample.2) := by decide +kernel
theorem right_context_positive : rightSource.EventPositive (fun sample => sample.2) := by decide +kernel

def leftPosterior (value : Bool) := ColliderChannel.posterior leftSource (fun sample => sample.1)
  (fun sample => sample.2) left_context_positive privateNoise value

def rightPosterior (value : Bool) := ColliderChannel.posterior rightSource (fun sample => sample.1)
  (fun sample => sample.2) right_context_positive privateNoise value

theorem conditioning_denominators_differ (value : Bool) :
    (leftPosterior value).den = 9 ∧ (rightPosterior value).den = 6 := by
  constructor
  · exact ColliderChannel.posterior_den leftSource (fun sample => sample.1) (fun sample => sample.2)
      left_context_positive privateNoise value
  · exact ColliderChannel.posterior_den rightSource (fun sample => sample.1) (fun sample => sample.2)
      right_context_positive privateNoise value

theorem left_false_collider_value : QProb.Equiv ((leftPosterior false).probVal id)
    ⟨4, 9, by decide⟩ := by decide +kernel

theorem left_true_collider_value : QProb.Equiv ((leftPosterior true).probVal id)
    ⟨5, 9, by decide⟩ := by decide +kernel

theorem right_collider_value (value : Bool) : QProb.Equiv ((rightPosterior value).probVal id)
    ⟨1, 2, by decide⟩ := by cases value <;> decide +kernel

/-- The support claim and the signal gap are independent checks.  Neither
posterior loses its false bit merely because only its true mass was compared. -/
theorem both_posteriors_positive (value bit : Bool) :
    (leftPosterior value).EventPositive (FiniteProbRecord.singletonEvent bit) ∧
      (rightPosterior value).EventPositive (FiniteProbRecord.singletonEvent bit) := by
  have noisePositive : forall bit, privateNoise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
    intro bit
    cases bit <;> decide +kernel
  exact ⟨ColliderChannel.posterior_positive leftSource (fun sample => sample.1) (fun sample => sample.2)
      left_context_positive privateNoise noisePositive value bit,
    ColliderChannel.posterior_positive rightSource (fun sample => sample.1) (fun sample => sample.2)
      right_context_positive privateNoise noisePositive value bit⟩

/-- Apply the general injectivity theorem to the unequal-denominator pair.
The literal numbers above are independent regression checks, not hypotheses
used to manufacture the general channel theorem. -/
theorem biased_posterior_gap (value : Bool) :
    Not (QProb.Equiv ((leftPosterior value).probVal id) ((rightPosterior value).probVal id)) := by
  intro equal
  have sourceEqual := (ColliderChannel.posterior_probVal_equiv_iff_of_bias leftSource
    (fun sample => sample.1) (fun sample => sample.2) left_context_positive rightSource
    (fun sample => sample.1) (fun sample => sample.2) right_context_positive
    privateNoise value 1 (by decide) (by decide +kernel)).mp equal
  have different : Not (QProb.Equiv
      ((leftSource.conditionOn (fun sample => sample.2) left_context_positive).probVal
        (fun sample => Bool.xor sample.1 value))
      ((rightSource.conditionOn (fun sample => sample.2) right_context_positive).probVal
        (fun sample => Bool.xor sample.1 value))) := by
    cases value <;> decide +kernel
  exact different sourceEqual

/-- Fair private noise really destroys the distinction, despite retaining
both output bits.  Full support alone is not a countermodel construction. -/
theorem balanced_noise_erases_gap (value : Bool) :
    QProb.Equiv
      ((ColliderChannel.posterior leftSource (fun sample => sample.1) (fun sample => sample.2)
        left_context_positive ColliderChannel.fairMask value).probVal id)
      ((ColliderChannel.posterior rightSource (fun sample => sample.1) (fun sample => sample.2)
        right_context_positive ColliderChannel.fairMask value).probVal id) :=
  ColliderChannel.posterior_probVal_equiv_of_balanced leftSource (fun sample => sample.1)
    (fun sample => sample.2) left_context_positive rightSource (fun sample => sample.1)
    (fun sample => sample.2) right_context_positive ColliderChannel.fairMask value (by decide +kernel)

/-! ## A real irreducible conditional failure on three-valued observed nodes -/

/-- The topological order is `U,A,R`; only the two arrows into `R` are
declared.  The third label remains in the actual positive model class. -/
def signature : ObservedSignature where
  count := 3
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val < 2 ∧ child.val = 2)
  directed_earlier := by intro parent child edge; have selected := of_decide_eq_true edge; omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right ∧ 1 ≤ left.val ∧ 1 ≤ right.val)
  bidirected_symmetric := by
    intro left right edge
    have selected := of_decide_eq_true edge
    exact decide_eq_true ⟨Ne.symm selected.1, selected.2.2, selected.2.1⟩
  bidirected_irreflexive := by intro node; simp only [ne_eq, not_true_eq_false, false_and, decide_false]

def parent : Fin signature.count := ⟨0, by decide⟩
def actionNode : Fin signature.count := ⟨1, by decide⟩
def collider : Fin signature.count := ⟨2, by decide⟩

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton parent
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton collider
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def large : NodeSet signature := fun node => decide (1 ≤ node.val)
def small : NodeSet signature := NodeSet.singleton collider
def child : ForestChild signature := fun node => if node = actionNode then some collider else none
def selection : HedgeSelection signature := ⟨large, small, child⟩

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

theorem roots_are_collider : witness.roots = NodeSet.singleton collider :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

theorem parent_outside : witness.large parent = false := by decide +kernel
theorem root_not_in_outcome : witness.roots collider = true ∧ query.outcome collider = false := by decide +kernel

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining large && NodeSet.equal fail.free small
  | _ => false

private theorem failureOfTest (result : IdentificationOutcome signature) (checked : failureTest result = true) :
    result = .failed ⟨large, small⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have parts := Bool.and_eq_true_iff.mp checked
      have largeEq := (NodeSet.equal_eq_true_iff _ _).mp parts.1
      have smallEq := (NodeSet.equal_eq_true_iff _ _).mp parts.2
      cases fail with
      | mk remaining free => cases largeEq; cases smallEq; rfl

theorem no_exchange : conditionalExchangeStep? graph query = none := by decide +kernel

theorem original_query_failed : identifyConditionalKernel graph query = .failed ⟨large, small⟩ :=
  failureOfTest _ (by decide +kernel)

/-- The earlier path extraction finds the real incoming-parent step used by
the semantic construction; it is not an unrelated identifiable path fixture. -/
def backdoor : ConditionalBackdoorPath graph query collider :=
  .ofNoExchange graph query no_exchange collider (by decide +kernel)

theorem backdoor_path_codes : backdoor.path.nodes.map SeparationNode.code = [2, 0] := by
  decide +kernel

/-- All counterexample fields are supplied by the general singleton-root
constructor.  In particular, no numerical probability gap or equality of
the modified observed distributions is passed in as an assumption. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfSingletonRootCollider rich parent collider (by decide +kernel)
    rfl rfl roots_are_collider parent_outside

theorem left_positive : ObservationallyPositive counterexample.left := counterexample.left_mem.2
theorem right_positive : ObservationallyPositive counterexample.right := counterexample.right_mem.2

theorem full_observational_equality : ObservationallyEquivalent counterexample.left counterexample.right :=
  counterexample.observationally_equal

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

end ConditionalColliderRegression
end Examples
end Causality
end Thesis
