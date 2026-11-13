import Thesis.CausalTransport.HedgeChannelCoefficients
import Thesis.Examples.HedgeChannelConstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelCoefficients

open Probability

/-!
# Positive coefficient-matched actual channel models on a bow

The power construction is instantiated with four source channels and degree
bound one, giving ordinary amplitude six and common capacity thirty-six.
The first model activates two large channels, one for each outer mask.  The
second activates the singleton small channel.  Both retain the same ordinary
background channel at the action vertex.  Unused channels have empty supports
and do not occur in local row lists; no source is removed or globally shared.

This is an actual graph-compatible positive SCM pair, not a pair of assumed
likelihood polynomials.  Complete root-major integration checks all four
observed assignments.  The semantic bridge then gives equality of every
observed event and an actual intervened outcome-event gap.  Only sixteen
shared bit vectors and two already integrated row factors are computed;
the potentially much larger private response-function space is never reduced.

A separate two-outer-vertex mask check exercises the nontrivial power identity
beyond the bow.  These regressions validate the general coefficient family,
but do not replace the general installation and observed-law proof in the
later channel modules.  The original-outcome flow argument and universal
conditional countermodel theorem remain separate completeness obligations.
-/

private def signature := HedgeChannelConstruction.signature
private def graph := HedgeChannelConstruction.graph
private def action := HedgeChannelConstruction.actionNode
private def outcome := HedgeChannelConstruction.outcomeNode

private def leftNodes (channel : Fin 4) : NodeSet signature :=
  if channel.val < 2 then NodeSet.full
  else if channel.val = 3 then NodeSet.singleton action else NodeSet.empty
private def rightNodes (channel : Fin 4) : NodeSet signature :=
  if channel.val = 2 then NodeSet.singleton outcome
  else if channel.val = 3 then NodeSet.singleton action else NodeSet.empty

private def leftAnchors (channel : Fin 4) : Option (Fin signature.count) := if channel.val < 2 then some action else none
private def rightAnchors (channel : Fin 4) : Option (Fin signature.count) := if channel.val = 2 then some outcome else none
private def leftDeficits (channel : Fin 4) : Nat := if channel.val = 1 then 1 else 0
private def rightDeficits (channel : Fin 4) : Nat := if channel.val = 2 then 1 else 0

private def leftParentSignal (child : Fin signature.count) (parents : signature.binary.ParentValues child) (channel : Fin 4) : Bool :=
  if channel.val = 0 then
    if edge : signature.directed action child = true then parents action edge else false
  else false
private def rightParentSignal (_child : Fin signature.count) (_parents : signature.binary.ParentValues _child) (_channel : Fin 4) : Bool := false

private def leftTables := Causality.HedgeChannelCoefficients.tables 4 1 leftNodes leftAnchors leftDeficits
private def rightTables := Causality.HedgeChannelCoefficients.tables 4 1 rightNodes rightAnchors rightDeficits
private def leftSignals := Causality.HedgeChannelTable.incidenceSignals graph 4 leftNodes leftParentSignal
private def rightSignals := Causality.HedgeChannelTable.incidenceSignals graph 4 rightNodes rightParentSignal
private def leftModel := Causality.HedgeChannelCoefficients.model graph 4 1 leftNodes leftAnchors leftDeficits leftParentSignal
private def rightModel := Causality.HedgeChannelCoefficients.model graph 4 1 rightNodes rightAnchors rightDeficits rightParentSignal

/-- Both actual power-table models preserve canonical pair incidence and
the entire original projected bow graph, including inactive channel slots. -/
theorem actual_models_compatible : Compatible leftModel graph.binary ∧ Compatible rightModel graph.binary :=
  ⟨Causality.HedgeChannelCoefficients.model_compatible graph 4 1 leftNodes leftAnchors leftDeficits leftParentSignal,
    Causality.HedgeChannelCoefficients.model_compatible graph 4 1 rightNodes rightAnchors rightDeficits rightParentSignal⟩

/-- Both models have full Boolean observed support from the automatically
proved baseline bounds, not from an added positivity assumption. -/
theorem actual_models_positive : ObservationallyPositive leftModel ∧ ObservationallyPositive rightModel :=
  ⟨Causality.HedgeChannelCoefficients.model_positive graph 4 1 leftNodes leftAnchors leftDeficits leftParentSignal,
    Causality.HedgeChannelCoefficients.model_positive graph 4 1 rightNodes rightAnchors rightDeficits rightParentSignal⟩

private theorem assignment_presentation (sample : signature.binary.Assignment) :
    sample = (fun child => if child.val = 0 then sample (0 : Fin 2) else sample (1 : Fin 2)) := by
  funext child
  by_cases first : child.val = 0
  · have equal : child = (0 : Fin 2) := Fin.ext first
    subst child
    rfl
  · have equal : child = (1 : Fin 2) := Fin.ext (by
      change child.val = 1
      have bound := child.isLt
      change child.val < 2 at bound
      omega)
    subst child
    rfl

/-- Full actual integration agrees at every observed assignment, including
all large-channel interactions and the common biased outer background. -/
theorem actual_integrated_numerators_equal (sample : signature.binary.Assignment) :
    Causality.HedgeChannelTable.integratedNumerator graph 4 leftTables leftSignals
      (FiniteLatentSCM.noIntervention signature.binary) sample =
    Causality.HedgeChannelTable.integratedNumerator graph 4 rightTables rightSignals
      (FiniteLatentSCM.noIntervention signature.binary) sample := by
  have presentation := assignment_presentation sample
  cases first : sample (0 : Fin 2) <;> cases second : sample (1 : Fin 2) <;>
    rw [first, second] at presentation <;> rw [presentation] <;> decide +kernel

/-- Equality of the full expansions, not only observed coordinate means.
The natural integration check is transported through the proved exact bridge. -/
theorem actual_expansions_equal (sample : signature.binary.Assignment) :
    Causality.HedgeChannelTable.expandedIntegral graph 4 leftTables leftSignals
      (FiniteLatentSCM.noIntervention signature.binary) sample =
    Causality.HedgeChannelTable.expandedIntegral graph 4 rightTables rightSignals
      (FiniteLatentSCM.noIntervention signature.binary) sample :=
  (Causality.HedgeChannelTable.integratedNumerator_expansion graph 4 leftTables leftSignals
    (FiniteLatentSCM.noIntervention signature.binary) sample).symm.trans
      ((congrArg (fun numerator : Nat => (numerator : Int)) (actual_integrated_numerators_equal sample)).trans
        (Causality.HedgeChannelTable.integratedNumerator_expansion graph 4 rightTables rightSignals
          (FiniteLatentSCM.noIntervention signature.binary) sample))

/-- The two actual SCMs agree on every observed event.  Common capacities
are derived from the power construction even though active supports differ. -/
theorem actual_observational_equivalence : ObservationallyEquivalent leftModel rightModel :=
  Causality.HedgeChannelTable.model_observationallyEquivalent_of_expansion graph 4 leftTables rightTables
    leftSignals rightSignals (Causality.HedgeChannelCoefficients.tables_capacities_equal 4 1
      leftNodes rightNodes leftAnchors rightAnchors leftDeficits rightDeficits) actual_expansions_equal

private def target (child : Fin signature.count) : Option Bool := if child.val = 0 then some true else none
private def outcomeEvent (sample : signature.binary.Assignment) : Bool := !(sample (1 : Fin 2))

/-- Under the original action intervention the large channels disappear,
whereas the small singleton bias remains.  The projected outcome event has
different literal numerators on the same actual shared prior. -/
theorem intervened_outcome_numerators :
    Causality.HedgeChannelTable.eventNumerator graph 4 leftTables leftSignals target outcomeEvent = 576 ∧
    Causality.HedgeChannelTable.eventNumerator graph 4 rightTables rightSignals target outcomeEvent = 592 := by
  constructor <;> decide +kernel

/-- The genuine outcome-event gap follows from actual probability semantics.
Together with positivity and complete observed equality, this validates the
coefficient-matched prototype without evaluating either SCM response prior. -/
theorem actual_interventional_gap :
    ¬ QProb.Equiv (leftModel.interventionalValue target outcomeEvent) (rightModel.interventionalValue target outcomeEvent) := by
  apply Causality.HedgeChannelTable.model_interventional_event_not_equiv graph 4 leftTables rightTables leftSignals rightSignals
    (Causality.HedgeChannelCoefficients.tables_capacities_equal 4 1 leftNodes rightNodes leftAnchors rightAnchors leftDeficits rightDeficits)
    target outcomeEvent
  rw [intervened_outcome_numerators.1, intervened_outcome_numerators.2]
  decide

private def twoOuterBits (index : Fin 2) : Bool := decide (index.val = 1)

/-- Two outer vertices exercise empty, single and double masks.  Their
complete signed mask sum is 45360, matching the positive background product
`(216+36)*(216-36)` rather than omitting the double interaction. -/
theorem two_outer_mask_sum : Causality.HedgeChannelCoefficients.largeMaskSum 4 2 0 2 twoOuterBits = 45360 :=
  (Causality.HedgeChannelCoefficients.largeMaskSum_eq_background_product 4 2 0 2 (Nat.le_refl 2) twoOuterBits).trans
    (by decide +kernel)

end HedgeChannelCoefficients
end Examples
end Causality
end Thesis
