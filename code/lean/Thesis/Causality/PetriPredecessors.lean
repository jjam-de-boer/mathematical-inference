import Thesis.Causality.PetriNet

namespace Thesis.Causality.PetriNet

/-!
# Execution monotonicity and exact one-step coverability predecessors

A successful supplied execution remains executable when extra natural
tokens are added to its source. The same word reaches its old endpoint
plus those extra tokens. This is a one-sided preservation statement:
adding tokens may also enable a word that previously failed.

For transition t and target b, the least source that can cover b after
one enabled firing is, coordinatewise,

  consume(t) + (b - produce(t)).

The subtraction is natural subtraction. In particular, a zero target or
large production never removes the transition's consumption requirement.
The proofs below characterize every source above this predecessor and
compute its actual successor. No marking or execution is selected from
a propositional existence assertion.

These facts support a later backward coverability search: stored words
can be lifted to larger sources, and each target has an exact predecessor
for each transition. This module supplies neither a saturation algorithm
nor its termination proof, a pumping test, or exact reachability search.
Token counts, supplied-word lengths and net dimensions have no fixed cap.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions}

theorem Below.refl (marking : Marking places) : Below marking marking :=
  fun _ => Nat.le_refl _

theorem Below.trans {first middle last : Marking places}
    (left : Below first middle) (right : Below middle last) : Below first last :=
  fun place => Nat.le_trans (left place) (right place)

/-- Explicit pointwise addition avoids placing global algebraic instances
on marking functions. Every extra coordinate is nonnegative by its type. -/
def addMarking (left right : Marking places) : Marking places :=
  fun place => left place + right place

theorem Enabled.mono {before larger : Marking places} {transition : Fin transitions}
    (ready : net.Enabled before transition) (dominates : Below before larger) :
    net.Enabled larger transition :=
  ready.trans dominates

/-- Enabling is retained before using the natural-subtraction identity.
The resulting marking is exactly the old result plus the same extra tokens. -/
theorem Fires.add_marking {before after : Marking places} {transition : Fin transitions}
    (fired : net.Fires before transition after) (extra : Marking places) :
    net.Fires (addMarking before extra) transition (addMarking after extra) := by
  constructor
  · intro place
    have ready := fired.1 place
    change net.consume transition place ≤ before place + extra place
    omega
  · funext place
    have ready := fired.1 place
    have result := congrFun fired.2 place
    change after place + extra place =
      (before place + extra place) - net.consume transition place + net.produce transition place
    change after place = before place - net.consume transition place + net.produce transition place at result
    omega

/-- Preserve the complete supplied word and every enabled intermediate
firing, including the unchanged word in the empty-execution case. -/
theorem Execution.add_marking {before after : Marking places} {word : List (Fin transitions)}
    (execution : net.Execution before word after) (extra : Marking places) :
    net.Execution (addMarking before extra) word (addMarking after extra) := by
  induction execution with
  | nil => exact .nil _
  | cons fired remaining ih => exact .cons (fired.add_marking extra) ih

/-- A larger source computes an endpoint for the very same word. Its
surplus is the pointwise source difference; no execution witness is chosen. -/
def Execution.lift {before after : Marking places} {word : List (Fin transitions)}
    (execution : net.Execution before word after) (larger : Marking places)
    (dominates : Below before larger) :
    {result : Marking places // net.Execution larger word result ∧ Below after result} := by
  let extra := fun place => larger place - before place
  have source : addMarking before extra = larger := by
    funext place
    have enough := dominates place
    change before place + (larger place - before place) = larger place
    omega
  refine ⟨addMarking after extra, ?_, ?_⟩
  · simpa only [source] using execution.add_marking extra
  · intro place
    change after place ≤ after place + extra place
    omega

theorem Coverable.mono {before larger target : Marking places}
    (coverable : net.Coverable before target) (dominates : Below before larger) :
    net.Coverable larger target := by
  obtain ⟨after, ⟨word, execution⟩, covers⟩ := coverable
  let lifted := execution.lift larger dominates
  exact ⟨lifted.val, ⟨word, lifted.property.1⟩, covers.trans lifted.property.2⟩

/-- Least initial token requirements for covering this target in one
firing. Production can offset target demand, but never consumption itself. -/
def predecessor (net : Thesis.Causality.PetriNet places transitions)
    (transition : Fin transitions) (target : Marking places) : Marking places :=
  fun place => net.consume transition place + (target place - net.produce transition place)

/-- Compute the actual successor of any source above the predecessor.
The returned proofs certify both enabling and coverage of the target. -/
def fireFromPredecessor (net : Thesis.Causality.PetriNet places transitions)
    (transition : Fin transitions) (target before : Marking places)
    (enough : Below (net.predecessor transition target) before) :
    {after : Marking places // net.Fires before transition after ∧ Below target after} := by
  refine ⟨fun place => before place - net.consume transition place + net.produce transition place,
    ⟨?_, rfl⟩, ?_⟩
  · intro place
    have bound := enough place
    change net.consume transition place + (target place - net.produce transition place) ≤ before place at bound
    omega
  · intro place
    have bound := enough place
    change net.consume transition place + (target place - net.produce transition place) ≤ before place at bound
    change target place ≤ before place - net.consume transition place + net.produce transition place
    omega

/-- Necessity supplies actual pointwise minimality, rather than just a
sufficient starting marking that might exclude some valid predecessors. -/
theorem predecessor_le_of_fires {before after target : Marking places} {transition : Fin transitions}
    (fired : net.Fires before transition after) (covers : Below target after) :
    Below (net.predecessor transition target) before := by
  intro place
  have ready := fired.1 place
  have result := congrFun fired.2 place
  have bound := covers place
  change after place = before place - net.consume transition place + net.produce transition place at result
  change net.consume transition place + (target place - net.produce transition place) ≤ before place
  omega

/-- Exact agreement with relational firing semantics for every initial
marking; target coverage permits overshoot and does not assert exact arrival. -/
theorem predecessor_exact (net : Thesis.Causality.PetriNet places transitions)
    (transition : Fin transitions) (target before : Marking places) :
    Below (net.predecessor transition target) before ↔
      ∃ after, net.Fires before transition after ∧ Below target after := by
  constructor
  · intro enough
    let result := net.fireFromPredecessor transition target before enough
    exact ⟨result.val, result.property⟩
  · rintro ⟨after, fired, covers⟩
    exact predecessor_le_of_fires fired covers

end Thesis.Causality.PetriNet
