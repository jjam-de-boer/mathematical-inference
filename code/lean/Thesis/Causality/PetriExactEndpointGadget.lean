import Thesis.Causality.PetriControl
import Thesis.Causality.PetriWordCompletion

namespace Thesis.Causality.PetriExactEndpoints

open PetriNet

/-!
# Finite-control compiler for partial exact endpoints

The setup state can add tokens at unspecified source places. Entering the
original system locks in the completed source. Leaving it is possible only
at the requested final state. The cleanup state can drain unspecified
target places, so the final exact marking uses zero there. Prescribed
places are untouched by the corresponding setup or cleanup adjustments.

Each original edge retains its index in a disjoint block of the new
alphabet. The two phase switches have zero counter effect. Adjustments at
prescribed places also have zero effect, allowing the finite alphabet to
be indexed without enumerating a subtype of places.
-/

variable {places states transitions : Nat}

structure Query (places states transitions : Nat) where
  system : ControlledPetriNet places states transitions
  start : Fin states
  finish : Fin states
  source : PartialMarking places
  target : PartialMarking places

inductive Edge (places transitions : Nat) where
  | original (edge : Fin transitions)
  | enter
  | leave
  | fill (place : Fin places)
  | drain (place : Fin places)

abbrev edgeCount (places transitions : Nat) := transitions + 2 + places + places

namespace Edge

def encode : Edge places transitions → Fin (edgeCount places transitions)
  | .original edge => ((edge.castAdd 2).castAdd places).castAdd places
  | .enter => (((0 : Fin 2).natAdd transitions).castAdd places).castAdd places
  | .leave => (((1 : Fin 2).natAdd transitions).castAdd places).castAdd places
  | .fill place => (place.natAdd (transitions + 2)).castAdd places
  | .drain place => place.natAdd (transitions + 2 + places)

def decode : Fin (edgeCount places transitions) → Edge places transitions :=
  Fin.addCases (Fin.addCases (Fin.addCases .original (fun phase =>
    if phase = 0 then .enter else .leave)) .fill) .drain

@[simp] theorem decode_encode (edge : Edge places transitions) : decode edge.encode = edge := by
  cases edge <;> simp only [encode, decode, Fin.addCases_left, Fin.addCases_right]
  · rfl
  · rfl

end Edge

/-- Erase the auxiliary edges and restore the literal original indices. -/
def originalWord : List (Fin (edgeCount places transitions)) → List (Fin transitions)
  | [] => []
  | edge :: rest => match Edge.decode edge with
    | .original index => index :: originalWord rest
    | _ => originalWord rest

theorem originalWord_append (first second : List (Fin (edgeCount places transitions))) :
    originalWord (first ++ second) = originalWord first ++ originalWord second := by
  induction first with
  | nil => rfl
  | cons edge rest ih =>
      simp only [List.cons_append, originalWord]
      cases Edge.decode edge <;> simp only [ih, List.cons_append]

/-- The extra states form a separate suffix of the state space. -/
def running (state : Fin states) : Fin (states + 2) := state.castAdd 2

def setup : Fin (states + 2) := (0 : Fin 2).natAdd states

def cleanup : Fin (states + 2) := (1 : Fin 2).natAdd states

@[simp] theorem running_inj {first second : Fin states} : running first = running second ↔ first = second := by
  constructor
  · intro equal
    have values := congrArg Fin.val equal
    exact Fin.ext values
  · exact congrArg running

@[simp] theorem setup_ne_cleanup : (setup : Fin (states + 2)) ≠ cleanup := by
  intro equal
  have values := congrArg Fin.val equal
  change states + 0 = states + 1 at values
  omega

@[simp] theorem cleanup_ne_setup : (cleanup : Fin (states + 2)) ≠ setup :=
  Ne.symm setup_ne_cleanup

@[simp] theorem running_ne_setup (state : Fin states) : running state ≠ setup := by
  intro equal
  have values := congrArg Fin.val equal
  change state.val = states + 0 at values
  have bound := state.isLt
  omega

@[simp] theorem setup_ne_running (state : Fin states) : setup ≠ running state :=
  Ne.symm (running_ne_setup state)

@[simp] theorem running_ne_cleanup (state : Fin states) : running state ≠ cleanup := by
  intro equal
  have values := congrArg Fin.val equal
  change state.val = states + 1 at values
  have bound := state.isLt
  omega

@[simp] theorem cleanup_ne_running (state : Fin states) : cleanup ≠ running state :=
  Ne.symm (running_ne_cleanup state)

/-- One unit at the chosen place, provided that coordinate is unspecified. -/
def freeUnit (specified : PartialMarking places) (place : Fin places) : Marking places :=
  fun other => if other = place then (if (specified other).isNone then 1 else 0) else 0

theorem freeUnit_fixed (specified : PartialMarking places) (place other : Fin places)
    {value : Nat} (fixed : specified other = some value) : freeUnit specified place other = 0 := by
  simp only [freeUnit, fixed, Option.isNone_some, Bool.false_eq_true, if_false, ite_self]

/-- The exact endpoints start and finish with zero on unspecified places. -/
def fixedValues (specified : PartialMarking places) : Marking places :=
  fun place => (specified place).getD 0

theorem fixedValues_matches (specified : PartialMarking places) :
    specified.Matches (fixedValues specified) := by
  intro place
  cases fixed : specified place <;> simp only [fixedValues, fixed, Option.getD_some]

namespace Query

variable (query : Query places states transitions)

def edgeSource : Edge places transitions → Fin (states + 2)
  | .original edge => running (query.system.source edge)
  | .enter | .fill _ => setup
  | .leave => running query.finish
  | .drain _ => cleanup

def edgeTarget : Edge places transitions → Fin (states + 2)
  | .original edge => running (query.system.target edge)
  | .enter => running query.start
  | .fill _ => setup
  | .leave | .drain _ => cleanup

def consume : Edge places transitions → Marking places
  | .original edge => query.system.net.consume edge
  | .drain place => freeUnit query.target place
  | _ => fun _ => 0

def produce : Edge places transitions → Marking places
  | .original edge => query.system.net.produce edge
  | .fill place => freeUnit query.source place
  | _ => fun _ => 0

def phased : ControlledPetriNet places (states + 2) (edgeCount places transitions) where
  net := { consume := fun edge => query.consume (Edge.decode edge)
           produce := fun edge => query.produce (Edge.decode edge) }
  source := fun edge => query.edgeSource (Edge.decode edge)
  target := fun edge => query.edgeTarget (Edge.decode edge)

@[simp] theorem phased_source_encode (edge : Edge places transitions) :
    query.phased.source edge.encode = query.edgeSource edge := by
  simp only [phased, Edge.decode_encode]

@[simp] theorem phased_target_encode (edge : Edge places transitions) :
    query.phased.target edge.encode = query.edgeTarget edge := by
  simp only [phased, Edge.decode_encode]

@[simp] theorem phased_consume_encode (edge : Edge places transitions) :
    query.phased.net.consume edge.encode = query.consume edge := by
  simp only [phased, Edge.decode_encode]

@[simp] theorem phased_produce_encode (edge : Edge places transitions) :
    query.phased.net.produce edge.encode = query.produce edge := by
  simp only [phased, Edge.decode_encode]

/-- Interface to ordinary exact Petri-net reachability. -/
def compiled := query.phased.compiled

def initial : Marking (places + (states + 2)) :=
  ControlledPetriNet.encode setup (fixedValues query.source)

def final : Marking (places + (states + 2)) :=
  ControlledPetriNet.encode cleanup (fixedValues query.target)

end Query

/-- Expose both steps of a controlled execution on a nonempty word. The
counter firing and the control transition stay tied to the same edge. -/
theorem execution_cons_iff {system : ControlledPetriNet places states transitions}
    {state next : Fin states} {before after : Marking places} {edge : Fin transitions}
    {rest : List (Fin transitions)} :
    system.Execution state before (edge :: rest) next after ↔
      state = system.source edge ∧
        ∃ middle, system.net.Fires before edge middle ∧
          system.Execution (system.target edge) middle rest next after := by
  constructor
  · rintro ⟨control, counters⟩
    obtain ⟨source, tail⟩ := (ControlledPetriNet.controlRun_cons_iff system _ _ _ _).mp control
    cases counters with
    | cons fired remaining => exact ⟨source, _, fired, tail, remaining⟩
  · rintro ⟨source, _, fired, control, counters⟩
    exact ⟨(ControlledPetriNet.controlRun_cons_iff system _ _ _ _).mpr ⟨source, control⟩,
      .cons fired counters⟩

end Thesis.Causality.PetriExactEndpoints
