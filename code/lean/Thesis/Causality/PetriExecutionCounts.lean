import Thesis.Causality.IntegerEquationRows
import Thesis.Causality.PetriControl

namespace Thesis.Causality.PetriExecutionCounts

open PetriNet IntegerEquations Probability.IntegerLinearAlgebra

/-!
# Balance identities for enabled Petri words

An enabled word supplies actual occurrence counts. Its signed token
changes telescope along the firing sequence. The same word supplies
control flow: for each state, arrivals minus departures equal the
change of its single control token. These are necessary identities and
do not assert that an arbitrary vector of counts can be scheduled.
-/

variable {places states transitions : Nat}

def occurrences (word : List (Fin transitions)) (edge : Fin transitions) : Nat :=
  word.countP (fun actual => decide (actual = edge))

private theorem occurrences_cons (edge : Fin transitions) (rest : List (Fin transitions)) :
    occurrences (edge :: rest) = fun other => occurrences rest other + if other = edge then 1 else 0 := by
  funext other
  simp only [occurrences, List.countP_cons, decide_eq_true_eq]
  by_cases same : other = edge
  · subst other
    rfl
  · simp only [if_neg same, if_neg (Ne.symm same)]

theorem occurrences_zero_of_not_mem (word : List (Fin transitions)) (edge : Fin transitions)
    (absent : edge ∉ word) : occurrences word edge = 0 := by
  induction word with
  | nil => rfl
  | cons head rest ih =>
      have different : edge ≠ head := fun same => absent (List.mem_cons.mpr (Or.inl same))
      have never : edge ∉ rest := fun member => absent (List.mem_cons.mpr (Or.inr member))
      simp only [occurrences_cons, ih never, if_neg different, Nat.add_zero]

private theorem weighted_nil (weights : Fin transitions → Int) :
    rowValue weights (occurrences []) = 0 := by
  unfold rowValue
  rw [← sum_map_zero (List.finRange transitions)]
  congr 1
  apply List.map_congr_left
  intro edge _
  change weights edge * (0 : Int) = 0
  exact Int.mul_zero _

private theorem weighted_cons (weights : Fin transitions → Int) (edge : Fin transitions)
    (rest : List (Fin transitions)) :
    rowValue weights (occurrences (edge :: rest)) =
      rowValue weights (occurrences rest) + weights edge := by
  rw [occurrences_cons, rowValue_add]
  have one : rowValue weights (fun other => if other = edge then 1 else 0) = weights edge := by
    unfold rowValue
    rw [← IntegerEquations.sum_fin_single edge weights]
    congr 1
    apply List.map_congr_left
    intro other _
    by_cases same : other = edge
    · simp only [if_pos same, Int.natCast_one, Int.mul_one]
    · simp only [if_neg same, Int.natCast_zero, Int.mul_zero]
  rw [one]

def tokenChange (net : Thesis.Causality.PetriNet places transitions) (place : Fin places)
    (edge : Fin transitions) : Int :=
  (net.produce edge place : Int) - (net.consume edge place : Int)

theorem tokenBalance (net : Thesis.Causality.PetriNet places transitions)
    {before after : Marking places} {word : List (Fin transitions)}
    (execution : net.Execution before word after) (place : Fin places) :
    rowValue (tokenChange net place) (occurrences word) =
      (after place : Int) - (before place : Int) := by
  induction execution with
  | nil => rw [weighted_nil, Int.sub_self]
  | @cons before middle after edge rest fired remaining ih =>
      rw [weighted_cons, ih]
      have enough := fired.1 place
      have actual := congrFun fired.2 place
      change net.consume edge place ≤ before place at enough
      change middle place = before place - net.consume edge place + net.produce edge place at actual
      unfold tokenChange
      omega

def indicator (state atState : Fin states) : Int := if state = atState then 1 else 0

def controlChange (net : ControlledPetriNet places states transitions) (state : Fin states)
    (edge : Fin transitions) : Int :=
  indicator state (net.target edge) - indicator state (net.source edge)

theorem controlBalance (net : ControlledPetriNet places states transitions)
    {entry exit : Fin states} {word : List (Fin transitions)}
    (path : net.controlRun entry word = some exit) (state : Fin states) :
    rowValue (controlChange net state) (occurrences word) =
      indicator state exit - indicator state entry := by
  induction word generalizing entry with
  | nil =>
      have same : entry = exit := Option.some.inj path
      rw [same, weighted_nil, Int.sub_self]
  | cons edge rest ih =>
      obtain ⟨atSource, tail⟩ := (net.controlRun_cons_iff entry edge rest exit).mp path
      rw [weighted_cons, ih tail, atSource]
      unfold controlChange
      omega

end Thesis.Causality.PetriExecutionCounts
