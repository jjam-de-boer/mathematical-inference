import Thesis.Causality.CoordinateBoxScan
import Thesis.Causality.PetriCoverabilityScan

namespace Thesis.Causality.PetriNet

open CoordinateBoxes

/-!
# Constructive backward saturation and witnessed coverability

The state retains a finite list of real covering executions, initial target
coverage, and boxes covering every point outside the current basis's upward
closure. The boxes are a termination measure, not a filter on candidates.
Every current basis entry and transition participates in the fresh scan.
An overlapping box with no current candidate is never discarded.

A fresh predecessor carries its actual execution data. Finite box lookup
locates a containing occurrence; the coverage invariant excludes failure.
Inserting the witness and splitting that occurrence preserves both state
invariants and strictly decreases the proved work-list relation. Neither
list length nor a sum of ranks is used as a scalar measure.

Ordinary well-founded recursion produces a saturated witnessed certificate.
There is no supplied fuel, token bound, word bound, antichain oracle, or
choice from a propositional existence assertion. The final classifier
returns an actual covering execution or a proof excluding all finite
executions. Overshoot is permitted: this decides coverability, not exact
reachability. No runtime or memory bound follows from the termination proof.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions} {target : Marking places}

/-- Every entry is sound by its stored execution. The two additional
invariants provide the initial target and a decreasing geometric cover. -/
structure SaturationState (net : Thesis.Causality.PetriNet places transitions)
    (target : Marking places) where
  entries : List (CoverabilityWitness net target)
  boxes : List (Box places)
  targetCovered : Covered (entries.map (fun entry => entry.source)) target
  coverage : CoversUncovered boxes (entries.map (fun entry => entry.source))

def SaturationState.initial (net : Thesis.Causality.PetriNet places transitions)
    (target : Marking places) : SaturationState net target where
  entries := [CoverabilityWitness.initial net target]
  boxes := [fun _ => none]
  targetCovered := ⟨target, List.mem_cons_self, Below.refl _⟩
  coverage := unbounded_covers _

/-- Inspect the computed finite option to obtain actual location data.
Only the impossible branch eliminates a contradiction from the invariant. -/
private def SaturationState.locateFresh (state : SaturationState net target)
    (hit : FreshPredecessor state.entries) : BoxLocation state.boxes hit.witness.source :=
  match checked : locateBox state.boxes hit.witness.source with
  | some location => location
  | none => False.elim (((locateBox_none_iff _ _).mp checked)
      (state.coverage hit.witness.source hit.uncovered))

/-- One certified update. The basis grows by one actual witness; one box
occurrence is replaced by its smaller children. Other boxes and all older
entries remain available. The subtype supplies the decrease to the caller. -/
def SaturationState.advance (state : SaturationState net target) (hit : FreshPredecessor state.entries) :
    {next : SaturationState net target // WorkStep places next.boxes state.boxes} := by
  let location := state.locateFresh hit
  refine ⟨{
    entries := hit.witness :: state.entries
    boxes := location.before ++ split location.box hit.witness.source ++ location.after
    targetCovered := ?_
    coverage := ?_ }, ?_⟩
  · rcases state.targetCovered with ⟨point, listed, below⟩
    exact ⟨point, List.mem_cons_of_mem hit.witness.source listed, below⟩
  · apply coversUncovered_after_replace location.before location.after location.box hit.witness.source
      (state.entries.map (fun entry => entry.source)) location.inside
    exact Eq.mp
      (congrArg (fun old => CoversUncovered old (state.entries.map (fun entry => entry.source)))
        location.reconstruct) state.coverage
  · exact Eq.mpr (congrArg
      (fun old => WorkStep places (location.before ++ split location.box hit.witness.source ++ location.after) old)
      location.reconstruct)
      (split_in_context location.before location.after location.box hit.witness.source location.inside)

/-- Every recursive call has the certified box-list decrease. Stopping
uses the exact global predecessor scan, not exhaustion of boxes or a
bounded failure to find a word. The executable recursion uses the standard
accessibility wrapper for the existing well-founded work-list relation. -/
def saturateFrom (state : SaturationState net target) : CoverabilityCertificate net target :=
  match checked : scanFreshPredecessor state.entries with
  | none => {
      entries := state.entries
      targetCovered := state.targetCovered
      saturated := (scanFreshPredecessor_none_iff _).mp checked }
  | some hit => saturateFrom (state.advance hit).val
termination_by workStep_wellFounded.wrap state.boxes
decreasing_by exact (state.advance hit).property

/-- A controlled one-step equation for proofs and small regressions.
Using the observed finite scan avoids normalizing accessibility proofs. -/
theorem saturateFrom_advance (state : SaturationState net target) (hit : FreshPredecessor state.entries)
    (checked : scanFreshPredecessor state.entries = some hit) :
    saturateFrom state = saturateFrom (state.advance hit).val := by
  rw [saturateFrom.eq_def]
  split
  · next stopped =>
      have impossible := stopped.symm.trans checked
      cases impossible
  · next actual selected =>
      have equal : actual = hit := Option.some.inj (selected.symm.trans checked)
      subst actual
      rfl

theorem saturateFrom_stopped_entries (state : SaturationState net target)
    (checked : scanFreshPredecessor state.entries = none) :
    (saturateFrom state).entries = state.entries := by
  rw [saturateFrom.eq_def]
  split
  · rfl
  · next actual selected =>
      have impossible := selected.symm.trans checked
      cases impossible

/-- Compute a finite witnessed basis for all sources covering this target.
The initial target's empty word is retained even if no transition exists. -/
def saturate (net : Thesis.Causality.PetriNet places transitions) (target : Marking places) :
    CoverabilityCertificate net target :=
  saturateFrom (SaturationState.initial net target)

theorem saturate_exact (net : Thesis.Causality.PetriNet places transitions)
    (target before : Marking places) :
    net.Coverable before target ↔ Covered ((net.saturate target).entries.map (fun entry => entry.source)) before :=
  (net.saturate target).coverable_iff_covered before

/-- A positive answer retains a real execution at the requested source.
A negative answer is a proof about every finite execution. The source
equality is supplied constructively, not decided for marking functions. -/
inductive CoverabilityResult (net : Thesis.Causality.PetriNet places transitions)
    (before target : Marking places) where
  | positive (witness : CoverabilityWitness net target) (source : witness.source = before)
  | negative (refuted : ¬ net.Coverable before target)

def CoverabilityResult.isPositive {before : Marking places} : CoverabilityResult net before target → Bool
  | .positive _ _ => true
  | .negative _ => false

theorem CoverabilityResult.positive_exact {before : Marking places}
    (result : CoverabilityResult net before target) : result.isPositive = true ↔ net.Coverable before target := by
  cases result with
  | positive witness source =>
      constructor
      · intro _
        simpa only [source] using witness.coverable
      · intro _
        rfl
  | negative refuted =>
      constructor
      · intro impossible
        cases impossible
      · intro coverable
        exact False.elim (refuted coverable)

/-- Saturate once for this target, then inspect the finite basis. A hit
computes its lifted word and endpoint; a miss invokes the proved complete
certificate. This is not a search for an execution of exact target size. -/
def classifyCoverability (net : Thesis.Causality.PetriNet places transitions)
    (before target : Marking places) : CoverabilityResult net before target :=
  let certificate := net.saturate target
  match checked : scanCoverage certificate.entries before with
  | some hit => .positive hit.witness rfl
  | none => .negative (certificate.not_coverable before ((scanCoverage_none_iff _ _).mp checked))

theorem classifyCoverability_exact (net : Thesis.Causality.PetriNet places transitions)
    (before target : Marking places) :
    (net.classifyCoverability before target).isPositive = true ↔ net.Coverable before target :=
  (net.classifyCoverability before target).positive_exact

theorem classifyCoverability_negative_iff (net : Thesis.Causality.PetriNet places transitions)
    (before target : Marking places) :
    (net.classifyCoverability before target).isPositive = false ↔ ¬ net.Coverable before target := by
  cases computed : net.classifyCoverability before target with
  | positive witness source =>
      constructor
      · intro impossible
        cases impossible
      · intro refuted
        have coverable : net.Coverable before target := by
          simpa only [source] using witness.coverable
        exact False.elim (refuted coverable)
  | negative refuted =>
      exact ⟨fun _ => refuted, fun _ => rfl⟩

end Thesis.Causality.PetriNet
