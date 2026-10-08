import Thesis.CausalTransport.HedgeChannelLikelihood
import Thesis.Examples.HedgeChannelConstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelTable

open Probability

/-!
# Actual positive channel-table checks on a two-node bow

The table centres read both a declared directed parent and the appropriate
channel coordinate of an incident pair-root source.  Positivity and exact
graph compatibility are obtained from the general actual-CPT construction,
not by evaluating its much larger private response-function prior.

The numerical regressions check a hard intervention at the action node.
The local check evaluates two integrated private row factors at one shared
assignment.  The whole-model checks integrate only four shared assignments
and use the semantic likelihood theorem; they never reduce the private
response-function prior.  A conflicting forced sample has probability zero,
but its common denominator remains positive.  Complementing both local
channel centres preserves the entire observed law by complete integration,
not by equating the pointwise row signals.  This symmetry test does not
assert a countermodel gap for the illustrative table pair.
-/

private def graph := HedgeChannelConstruction.graph
private def signature := HedgeChannelConstruction.signature

private def table : BooleanChannelTable (Fin 2) :=
  BooleanChannelTable.ofCapacity (List.finRange 2) (fun channel => channel.val + 1) 5 (by decide +kernel)

private def tables (_child : Fin signature.count) : BooleanChannelTable (Fin 2) := table

private def signals : Causality.HedgeChannelTable.Signals graph 2 :=
  fun child parents inputs channel => Bool.xor
    (PairRootChannels.inputIncidence graph.binary 2 NodeSet.full child inputs channel)
    (if edge : signature.directed HedgeChannelConstruction.actionNode child = true then
      parents HedgeChannelConstruction.actionNode edge else false)

/-- The genuine functionalized model is canonically semi-Markovian and
projects to exactly the bow graph; channel vectors add no global source. -/
theorem actual_model_compatible :
    Compatible (Causality.HedgeChannelTable.model graph 2 tables signals) graph.binary :=
  Causality.HedgeChannelTable.model_compatible graph 2 tables signals

/-- Full observed support is a theorem of the actual model semantics,
including the parent-responsive row, without invoking soundness. -/
theorem actual_model_positive : ObservationallyPositive (Causality.HedgeChannelTable.model graph 2 tables signals) :=
  Causality.HedgeChannelTable.model_positive graph 2 tables signals

private def shared : (PairRootChannels.extension graph.binary 2).Assignment := fun _ _ => false
private def sample : signature.binary.Assignment := fun node => decide (node.val = 0)
private def target : Fin signature.count -> Option Bool := fun node => if node.val = 0 then some true else none

/-- The matching forced action contributes exactly one.  The actual free
child reads the forced true parent and has numerator two at the false sample.
Only these row cells, not any SCM private response enumeration, are reduced. -/
theorem forced_private_product :
    ((FiniteProduct.qProduct signature.count (fun child => (Causality.HedgeChannelTable.cpt graph 2 tables signals).sliceFactors
      target shared sample ((Causality.HedgeChannelTable.cpt graph 2 tables signals).privateRoot child))).num : Int) = 2 := by
  have expanded := Causality.HedgeChannelTable.privateProduct_num_expansion graph 2 tables signals target shared sample
  exact expanded.trans (by decide +kernel)

/-- Four shared channel vectors yield total row numerator twenty.  The
forced action has denominator one and the free child denominator ten;
the actual shared prior retains denominator four. -/
theorem forced_likelihood_terms :
    Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals target sample = 20 ∧
    Causality.HedgeChannelTable.likelihoodDenominator graph 2 tables target = 40 := by
  constructor <;> decide +kernel

/-- The actual SCM probability is one half after the intervention.  Only
the small integrated numerator is computed; the much larger SCM execution
and response-function source space are handled by the general theorem. -/
theorem forced_actual_probability :
    QProb.Equiv ((Causality.HedgeChannelTable.model graph 2 tables signals).interventionalValue target
      (FiniteProbRecord.singletonEvent sample)) ⟨1, 2, by decide⟩ := by
  refine QProb.equiv_trans
    (Causality.HedgeChannelTable.model_interventional_singleton graph 2 tables signals target sample) ?_
  change Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals target sample * 2 =
    1 * Causality.HedgeChannelTable.likelihoodDenominator graph 2 tables target
  rw [forced_likelihood_terms.1, forced_likelihood_terms.2]

private def conflictingTarget : Fin signature.count -> Option Bool :=
  fun node => if node.val = 0 then some false else none

/-- An incompatible forced sample stays zero through whole-prior
integration.  No proof divides by its zero numerator or by a row cell. -/
theorem conflicting_actual_probability :
    QProb.Equiv ((Causality.HedgeChannelTable.model graph 2 tables signals).interventionalValue conflictingTarget
      (FiniteProbRecord.singletonEvent sample)) QProb.zero := by
  refine QProb.equiv_trans
    (Causality.HedgeChannelTable.model_interventional_singleton graph 2 tables signals conflictingTarget sample) ?_
  have numerator : Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals conflictingTarget sample = 0 := by
    decide +kernel
  change Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals conflictingTarget sample * 1 =
    0 * Causality.HedgeChannelTable.likelihoodDenominator graph 2 tables conflictingTarget
  rw [numerator, Nat.zero_mul, Nat.zero_mul]

/-- Term-by-term integration of the complete expansion gives the same
natural numerator used by the actual hard-intervention probability. -/
theorem forced_actual_expansion :
    Causality.HedgeChannelTable.expandedIntegral graph 2 tables signals target sample = 20 := by
  exact (Causality.HedgeChannelTable.integratedNumerator_expansion graph 2 tables signals target sample).symm.trans
    (congrArg (fun value : Nat => (value : Int)) forced_likelihood_terms.1)

/-- The uncut factual likelihood retains both nonuniform row factors and
their interaction.  Its numerator is not the product of separately averaged
row numerators; the shared assignments must be integrated jointly. -/
theorem factual_likelihood_terms :
    Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals
      (FiniteLatentSCM.noIntervention signature.binary) sample = 120 ∧
    Causality.HedgeChannelTable.likelihoodDenominator graph 2 tables
      (FiniteLatentSCM.noIntervention signature.binary) = 400 := by
  constructor <;> decide +kernel

/-- The actual factual singleton has probability three tenths.  Unlike
the forced check, both integrated private factors contribute interactions. -/
theorem factual_actual_probability :
    QProb.Equiv ((Causality.HedgeChannelTable.model graph 2 tables signals).observationalValue
      (FiniteProbRecord.singletonEvent sample)) ⟨3, 10, by decide⟩ := by
  refine QProb.equiv_trans
    (Causality.HedgeChannelTable.model_observational_singleton graph 2 tables signals sample) ?_
  change Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals
    (FiniteLatentSCM.noIntervention signature.binary) sample * 10 =
      3 * Causality.HedgeChannelTable.likelihoodDenominator graph 2 tables
        (FiniteLatentSCM.noIntervention signature.binary)
  rw [factual_likelihood_terms.1, factual_likelihood_terms.2]

private def complementedSignals : Causality.HedgeChannelTable.Signals graph 2 :=
  fun child parents inputs channel => !(signals child parents inputs channel)

private theorem binary_assignment_presentation (value : signature.binary.Assignment) :
    value = (fun node => if node.val = 0 then value (0 : Fin 2) else value (1 : Fin 2)) := by
  funext node
  by_cases first : node.val = 0
  · have equal : node = (0 : Fin 2) := Fin.ext first
    subst node
    rfl
  · have equal : node = (1 : Fin 2) := Fin.ext (by
      change node.val = 1
      have bound := node.isLt
      change node.val < 2 at bound
      omega)
    subst node
    rfl

/-- Different pointwise centre families have the same complete factual
expansions after integrating all four actual shared vectors.  The four
observed Boolean assignments are checked, not just the displayed sample. -/
theorem complemented_expansions (value : signature.binary.Assignment) :
    Causality.HedgeChannelTable.expandedIntegral graph 2 tables signals
      (FiniteLatentSCM.noIntervention signature.binary) value =
    Causality.HedgeChannelTable.expandedIntegral graph 2 tables complementedSignals
      (FiniteLatentSCM.noIntervention signature.binary) value := by
  refine (Causality.HedgeChannelTable.integratedNumerator_expansion graph 2 tables signals
    (FiniteLatentSCM.noIntervention signature.binary) value).symm.trans ?_
  refine Eq.trans ?_ (Causality.HedgeChannelTable.integratedNumerator_expansion graph 2 tables complementedSignals
    (FiniteLatentSCM.noIntervention signature.binary) value)
  apply congrArg (fun numerator : Nat => (numerator : Int))
  have presentation := binary_assignment_presentation value
  cases first : value (0 : Fin 2) <;> cases second : value (1 : Fin 2) <;>
    rw [first, second] at presentation <;> rw [presentation] <;> decide +kernel

/-- Complete expansion matching implies equality of every observed event
in the two actual SCMs.  This tests the semantic comparison theorem without
reducing either private response prior or assuming row-wise equality. -/
theorem complemented_actual_observed_law :
    ObservationallyEquivalent (Causality.HedgeChannelTable.model graph 2 tables signals)
      (Causality.HedgeChannelTable.model graph 2 tables complementedSignals) :=
  Causality.HedgeChannelTable.model_observationallyEquivalent_of_expansion graph 2 tables tables
    signals complementedSignals (fun _ => rfl) complemented_expansions

private def outcomeEvent (value : signature.binary.Assignment) : Bool := !(value (1 : Fin 2))
private def constantSignals : Causality.HedgeChannelTable.Signals graph 2 := fun _ _ _ _ => false

/-- Projection to the queried child still has numerator twenty; the other
action value contributes zero because of the intervention.  A projected
event, not just a full-assignment discrepancy, is what a query gap requires. -/
theorem forced_event_numerators :
    Causality.HedgeChannelTable.eventNumerator graph 2 tables signals target outcomeEvent = 20 ∧
    Causality.HedgeChannelTable.eventNumerator graph 2 tables constantSignals target outcomeEvent = 32 := by
  constructor <;> decide +kernel

/-- The projected event has the actual probability one half.  The semantic
event theorem integrates both selected observed assignments and every real
shared vector, without evaluating the SCM response-function prior. -/
theorem forced_actual_event_probability :
    QProb.Equiv ((Causality.HedgeChannelTable.model graph 2 tables signals).interventionalValue target outcomeEvent)
      ⟨1, 2, by decide⟩ := by
  refine QProb.equiv_trans
    (Causality.HedgeChannelTable.model_interventional_event graph 2 tables signals target outcomeEvent) ?_
  change Causality.HedgeChannelTable.eventNumerator graph 2 tables signals target outcomeEvent * 2 =
    1 * Causality.HedgeChannelTable.likelihoodDenominator graph 2 tables target
  rw [forced_event_numerators.1, forced_likelihood_terms.2]

/-- The explicit projected numerator gap separates these two actual
interventional event probabilities.  The constant-centre comparison model
is only a gap regression: no observational equivalence with it is claimed. -/
theorem forced_actual_event_gap :
    ¬ QProb.Equiv ((Causality.HedgeChannelTable.model graph 2 tables signals).interventionalValue target outcomeEvent)
      ((Causality.HedgeChannelTable.model graph 2 tables constantSignals).interventionalValue target outcomeEvent) := by
  apply Causality.HedgeChannelTable.model_interventional_event_not_equiv graph 2 tables tables
    signals constantSignals (fun _ => rfl) target outcomeEvent
  rw [forced_event_numerators.1, forced_event_numerators.2]
  decide

/-- Proper selection of one connected channel cancels the full character
against the actual pair-root prior.  The second selection remains arbitrary. -/
theorem actual_prior_cancels (secondSelection : NodeSet signature) (phases : Fin 2 -> Bool) :
    (PairRootChannels.prior graph 2).signedMass (fun assignment => FiniteProduct.iProduct 2
      (fun channel => FiniteProbRecord.characterSign (Bool.xor (phases channel)
        (hedgeChannelIncidenceParity graph NodeSet.full
          (if channel.val = 0 then NodeSet.singleton HedgeChannelConstruction.actionNode else secondSelection)
          (fun root => assignment root channel))))) = 0 :=
  PairRootChannels.prior_character_signedMass_zero graph 2 (fun _ => NodeSet.full)
    (fun channel => if channel.val = 0 then NodeSet.singleton HedgeChannelConstruction.actionNode else secondSelection)
    phases 0 HedgeChannelConstruction.witness.large_forest.component (by intro node _selected; rfl)
    HedgeChannelConstruction.outcomeNode (by decide +kernel)
    (by change NodeSet.singleton HedgeChannelConstruction.actionNode HedgeChannelConstruction.outcomeNode = false; decide +kernel)
    HedgeChannelConstruction.actionNode
    (by change NodeSet.singleton HedgeChannelConstruction.actionNode HedgeChannelConstruction.actionNode = true; decide +kernel)

end HedgeChannelTable
end Examples
end Causality
end Thesis
