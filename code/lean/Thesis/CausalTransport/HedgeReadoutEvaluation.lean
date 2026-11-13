import Thesis.CausalTransport.HedgeReadoutSequence

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Exact mechanism evaluation through finite private readout plans

An installed readout transforms a mechanism at its current parent inputs.
It does not transform the old observed assignment coordinate independently
of responding descendants.  These lemmas expose that distinction for every
finite plan, before imposing a particular hedge routing construction.

Fresh input bits and the original latent unit are explicit data.  Their
successive encodings inhabit the actual folded SCM's dependent latent space.
The mechanism theorem tracks each readout at its own row; other rows retain
their original typed inputs.  A pivot-distinct plan therefore installs each
stated local response exactly once, regardless of the installation order.
The later compensated-flow construction uses these equations under arbitrary
interventions, not a sink-based observable coordinate substitution.

The bit map indexes pivots.  It represents independent coordinates for a
pivot-distinct plan.  On repeated pivots it deliberately assigns the same
supplied bit to each encoding; the general mechanism equation is still true,
but no claim of independent repeated factors is inferred from that map.
-/

/-- One mechanism-row response at arbitrary current parents.  The dependent
equality branch transports the old full value only to the matching pivot. -/
def HedgeReadoutStep.responseAt (step : HedgeReadoutStep S) (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (parents : S.ParentValues child) (bit : Bool) (old : S.Value child) : S.Value child :=
  if same : child = step.pivot then by
    subst child
    exact hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents old bit
  else old

namespace HedgeReadoutEvaluation

/-- Compose only the responses installed at `child`.  All of them receive
the same current parents; updates at other rows do not rewrite this equation. -/
def response (rich : ObservedSignature.ValueRich S) (bits : Fin S.count -> Bool)
    (child : Fin S.count) (parents : S.ParentValues child) :
    List (HedgeReadoutStep S) -> S.Value child -> S.Value child
  | [], old => old
  | step :: rest, old => response rich bits child parents rest
      (step.responseAt rich child parents (bits step.pivot) old)

private theorem response_off (rich : ObservedSignature.ValueRich S) (bits : Fin S.count -> Bool)
    (child : Fin S.count) (parents : S.ParentValues child) (steps : List (HedgeReadoutStep S))
    (different : forall step, step ∈ steps -> child ≠ step.pivot) (old : S.Value child) :
    response rich bits child parents steps old = old := by
  induction steps generalizing old with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      rw [response, inductionHypothesis
        (fun next listed => different next (List.mem_cons_of_mem _ listed))]
      simp only [HedgeReadoutStep.responseAt, dif_neg (different step List.mem_cons_self)]

private theorem response_of_mem (rich : ObservedSignature.ValueRich S) (bits : Fin S.count -> Bool)
    (steps : List (HedgeReadoutStep S))
    (distinct : steps.Pairwise (fun first second => first.pivot ≠ second.pivot))
    (step : HedgeReadoutStep S) (listed : step ∈ steps)
    (parents : S.ParentValues step.pivot) (old : S.Value step.pivot) :
    response rich bits step.pivot parents steps old =
      hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents old (bits step.pivot) := by
  induction steps generalizing old with
  | nil => cases listed
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp listed with same | inRest
      · subst step
        rw [response, response_off rich bits head.pivot parents rest
          ((List.pairwise_cons.mp distinct).1)]
        simp only [HedgeReadoutStep.responseAt, dite_true]
      · have different : step.pivot ≠ head.pivot :=
          Ne.symm ((List.pairwise_cons.mp distinct).1 step inRest)
        rw [response]
        simp only [HedgeReadoutStep.responseAt, dif_neg different]
        exact inductionHypothesis (List.pairwise_cons.mp distinct).2 inRest old

end HedgeReadoutEvaluation

/-- Encode the supplied fresh input at every actual independent extension.
This constructs a latent unit of the final SCM, not an auxiliary signal. -/
def FiniteLatentSCM.hedgeReadoutAssignment (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (bits : Fin S.count -> Bool) : (steps : List (HedgeReadoutStep S)) ->
    base.latent.Assignment -> (base.withHedgeReadouts rich steps).latent.Assignment
  | [], unit => unit
  | step :: rest, unit => (step.apply rich base).hedgeReadoutAssignment rich bits rest
      (PrivateBooleanNoise.assignment base.latent (bits step.pivot) unit)

private theorem HedgeReadoutStep.apply_mechanism_assignment (step : HedgeReadoutStep S)
    (rich : ObservedSignature.ValueRich S) (base : ExactModel S)
    (child : Fin S.count) (parents : S.ParentValues child)
    (bit : Bool) (unit : base.latent.Assignment) :
    (step.apply rich base).mechanism child parents
        (fun root _incident => PrivateBooleanNoise.assignment base.latent bit unit root) =
      step.responseAt rich child parents bit (base.mechanism child parents (fun root _incident => unit root)) := by
  by_cases same : child = step.pivot
  · subst child
    dsimp only [HedgeReadoutStep.apply, FiniteLatentSCM.withHedgeReadout, FiniteLatentSCM.withPrivateReadout]
    rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_pivot]
    have newBit := PrivateBooleanNoise.bit_assignment base.latent step.pivot bit unit
    refine (congrArg (fun actualBit => hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal
      parents (base.mechanism step.pivot parents (PrivateBooleanNoise.oldInputs base.latent step.pivot
        step.pivot (fun root _incident => PrivateBooleanNoise.assignment base.latent bit unit root))) actualBit)
      newBit).trans ?_
    have oldInputs := PrivateBooleanNoise.oldInputs_assignment base.latent step.pivot step.pivot bit unit
    refine (congrArg (fun value => hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal
      parents value bit) (congrArg (base.mechanism step.pivot parents) oldInputs)).trans ?_
    simp only [HedgeReadoutStep.responseAt, dite_true]
  · dsimp only [HedgeReadoutStep.apply, FiniteLatentSCM.withHedgeReadout, FiniteLatentSCM.withPrivateReadout]
    rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne _ _ _ _ _ same]
    have oldInputs := PrivateBooleanNoise.oldInputs_assignment base.latent step.pivot child bit unit
    simpa only [HedgeReadoutStep.responseAt, dif_neg same] using
      congrArg (base.mechanism child parents) oldInputs

/-- Exact mechanism-row composition for any finite plan and represented
latent inputs.  Repeated pivots are composed, not silently overwritten;
parent inputs are arbitrary and need not be factual observations. -/
theorem FiniteLatentSCM.withHedgeReadouts_mechanism_eq_response
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) (bits : Fin S.count -> Bool)
    (unit : base.latent.Assignment) (child : Fin S.count) (parents : S.ParentValues child) :
    (base.withHedgeReadouts rich steps).mechanism child parents
        (fun root _incident => base.hedgeReadoutAssignment rich bits steps unit root) =
      HedgeReadoutEvaluation.response rich bits child parents steps
        (base.mechanism child parents (fun root _incident => unit root)) := by
  induction steps generalizing base with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      change ((step.apply rich base).withHedgeReadouts rich rest).mechanism child parents
          (fun root _incident => (step.apply rich base).hedgeReadoutAssignment rich bits rest
            (PrivateBooleanNoise.assignment base.latent (bits step.pivot) unit) root) =
        HedgeReadoutEvaluation.response rich bits child parents rest
          (step.responseAt rich child parents (bits step.pivot)
            (base.mechanism child parents (fun root _incident => unit root)))
      exact (inductionHypothesis (step.apply rich base) _).trans
        (congrArg (HedgeReadoutEvaluation.response rich bits child parents rest)
          (step.apply_mechanism_assignment rich base child parents (bits step.pivot) unit))

/-- In a pivot-distinct plan, a listed instruction supplies exactly its
local response at the final SCM's current parents.  No topological ordering
or non-influence premise is needed for this mechanism-level statement. -/
theorem FiniteLatentSCM.withHedgeReadouts_mechanism_of_mem
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (distinct : steps.Pairwise (fun first second => first.pivot ≠ second.pivot))
    (step : HedgeReadoutStep S) (listed : step ∈ steps) (bits : Fin S.count -> Bool)
    (unit : base.latent.Assignment) (parents : S.ParentValues step.pivot) :
    (base.withHedgeReadouts rich steps).mechanism step.pivot parents
        (fun root _incident => base.hedgeReadoutAssignment rich bits steps unit root) =
      hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents
        (base.mechanism step.pivot parents (fun root _incident => unit root)) (bits step.pivot) := by
  rw [base.withHedgeReadouts_mechanism_eq_response]
  exact HedgeReadoutEvaluation.response_of_mem rich bits steps distinct step listed parents _

/-- Rows absent from the plan keep their exact old equation and typed
latent inputs, even when they respond to updated parent values. -/
theorem FiniteLatentSCM.withHedgeReadouts_mechanism_of_off
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) (bits : Fin S.count -> Bool)
    (unit : base.latent.Assignment) (child : Fin S.count) (parents : S.ParentValues child)
    (different : forall step, step ∈ steps -> child ≠ step.pivot) :
    (base.withHedgeReadouts rich steps).mechanism child parents
        (fun root _incident => base.hedgeReadoutAssignment rich bits steps unit root) =
      base.mechanism child parents (fun root _incident => unit root) := by
  rw [base.withHedgeReadouts_mechanism_eq_response]
  exact HedgeReadoutEvaluation.response_off rich bits child parents steps different _

end Causality
end Thesis
