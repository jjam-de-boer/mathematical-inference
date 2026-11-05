import Thesis.Causality.PetriPredecessors
import Thesis.Causality.CoordinateBoxes

namespace Thesis.Causality.PetriNet

open CoordinateBoxes

/-!
# Stored coverability witnesses and supplied saturation certificates

A backward basis point carries an actual transition word and its actual
endpoint, together with proofs of execution and target coverage. Extending
such a record by a predecessor first computes the enabled firing, then
lifts the stored suffix to that firing's possibly larger result. Surplus
tokens are retained throughout; coverability does not require exact arrival.

For a supplied finite basis, saturation means that every one-step covering
predecessor of every basis point already lies above some basis point. This
property is backward closure of the entire upward closure, not merely of
the listed points. Induction over any finite execution then proves that
every source covering the target belongs to that upward closure, provided
the target itself belongs to it. Stored witnesses give the converse.

The target-coverage premise is essential: an empty basis is saturated but
does not even recognize the target's empty execution. A certificate below
keeps that premise explicit. Its entries need not form a minimal basis or
an antichain; no equality decision on marking functions is required.

Only supplied data and closure proofs are handled here. This module does
not scan candidates, construct a saturated basis, decide coverability, or
add a search cutoff. Token counts and execution lengths remain unbounded.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions} {target : Marking places}

/-- Executable witness data, rather than a marking or word chosen from
a propositional existence assertion. All endpoints are literal results. -/
structure CoverabilityWitness (net : Thesis.Causality.PetriNet places transitions)
    (target : Marking places) where
  source : Marking places
  word : List (Fin transitions)
  endpoint : Marking places
  execution : net.Execution source word endpoint
  covers : Below target endpoint

def CoverabilityWitness.initial (net : Thesis.Causality.PetriNet places transitions)
    (target : Marking places) : CoverabilityWitness net target where
  source := target
  word := []
  endpoint := target
  execution := .nil _
  covers := Below.refl _

/-- Reuse the same stored word from a larger source, with the computed
surplus at its endpoint. This operation needs no new execution search. -/
def CoverabilityWitness.lift (witness : CoverabilityWitness net target)
    (larger : Marking places) (enough : Below witness.source larger) :
    CoverabilityWitness net target :=
  let lifted := witness.execution.lift larger enough
  { source := larger
    word := witness.word
    endpoint := lifted.val
    execution := lifted.property.1
    covers := witness.covers.trans lifted.property.2 }

/-- Prefix one real firing from the least covering predecessor. Its
successor can overshoot the old source, so the suffix must be lifted
before the two execution proofs can be composed. -/
def CoverabilityWitness.prepend (witness : CoverabilityWitness net target)
    (transition : Fin transitions) : CoverabilityWitness net target :=
  let before := net.predecessor transition witness.source
  let fired := net.fireFromPredecessor transition witness.source before (Below.refl _)
  let suffix := witness.lift fired.val fired.property.2
  { source := before
    word := transition :: witness.word
    endpoint := suffix.endpoint
    execution := .cons fired.property.1 suffix.execution
    covers := suffix.covers }

theorem CoverabilityWitness.coverable (witness : CoverabilityWitness net target) :
    net.Coverable witness.source target :=
  ⟨witness.endpoint, ⟨witness.word, witness.execution⟩, witness.covers⟩

/-- Finite closure obligation for a supplied basis. This is a proposition,
not an algorithm computing the basis or checking that obligation. -/
def Saturated (net : Thesis.Causality.PetriNet places transitions)
    (basis : List (Marking places)) : Prop :=
  ∀ point ∈ basis, ∀ transition, Covered basis (net.predecessor transition point)

theorem covered_mono {basis : List (Marking places)} {smaller larger : Marking places}
    (covered : Covered basis smaller) (enough : Below smaller larger) : Covered basis larger := by
  rcases covered with ⟨point, listed, below⟩
  exact ⟨point, listed, below.trans enough⟩

/-- Closure on the finite basis extends to arbitrary sources of actual
firings. The least-predecessor theorem supplies the needed lower bound. -/
theorem Saturated.covered_before {basis : List (Marking places)} (closed : Saturated net basis)
    {before after : Marking places} {transition : Fin transitions}
    (fired : net.Fires before transition after) (covered : Covered basis after) : Covered basis before := by
  rcases covered with ⟨point, listed, below⟩
  exact covered_mono (closed point listed transition) (predecessor_le_of_fires fired below)

/-- The word is arbitrary and has no prescribed length bound. All
existential eliminations in this closure proof remain in propositions. -/
theorem Saturated.covered_of_execution {basis : List (Marking places)} (closed : Saturated net basis)
    {before after : Marking places} {word : List (Fin transitions)}
    (execution : net.Execution before word after) : Covered basis after → Covered basis before := by
  induction execution with
  | nil => exact id
  | cons fired remaining ih =>
      intro covered
      exact closed.covered_before fired (ih covered)

theorem Saturated.covered_of_coverable {basis : List (Marking places)} (closed : Saturated net basis)
    (targetCovered : Covered basis target) {before : Marking places}
    (coverable : net.Coverable before target) : Covered basis before := by
  rcases coverable with ⟨after, ⟨word, execution⟩, enough⟩
  exact closed.covered_of_execution execution (covered_mono targetCovered enough)

/-- Soundness needs no saturation. A supplied entry below the requested
source lifts its actual stored word; this theorem does not select runtime
data from the existential assertion of basis coverage. -/
theorem coverable_of_witness_covered (entries : List (CoverabilityWitness net target))
    {before : Marking places} (covered : Covered (entries.map (fun entry => entry.source)) before) :
    net.Coverable before target := by
  rcases covered with ⟨point, listed, enough⟩
  obtain ⟨entry, _, equal⟩ := List.mem_map.mp listed
  subst point
  exact (entry.lift before enough).coverable

/-- A supplied saturated witnessed basis. This data certifies a complete
upward-closure description of coverability for this target, but no
construction or decision procedure for obtaining it is claimed. -/
structure CoverabilityCertificate (net : Thesis.Causality.PetriNet places transitions)
    (target : Marking places) where
  entries : List (CoverabilityWitness net target)
  targetCovered : Covered (entries.map (fun entry => entry.source)) target
  saturated : Saturated net (entries.map (fun entry => entry.source))

theorem CoverabilityCertificate.coverable_iff_covered (certificate : CoverabilityCertificate net target)
    (before : Marking places) :
    net.Coverable before target ↔ Covered (certificate.entries.map (fun entry => entry.source)) before :=
  ⟨certificate.saturated.covered_of_coverable certificate.targetCovered,
    coverable_of_witness_covered certificate.entries⟩

/-- A negative answer excludes every finite execution, not merely every
word below some tested cutoff. The supplied certificate carries both the
initial-target and saturation obligations needed for this conclusion. -/
theorem CoverabilityCertificate.not_coverable (certificate : CoverabilityCertificate net target)
    (before : Marking places)
    (missing : ¬ Covered (certificate.entries.map (fun entry => entry.source)) before) :
    ¬ net.Coverable before target :=
  fun coverable => missing ((certificate.coverable_iff_covered before).mp coverable)

end Thesis.Causality.PetriNet
