import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Causality.HiddenDAGObservedIndex
import Thesis.Probability.FiniteFunctionTables

namespace Thesis.Causality
open Probability

/-!
# Recorded and unrecorded urns: an operational causal game

The primitive instruction is a nonempty finite urn for **each** tuple of
declared influencing values. No SCM, probability prior, do-calculus rule or
Markov property is a field of the game. `P` supplies only the finite wiring,
its acyclic rank and its checked projection to the recorded coordinates.
Unrecorded urns are ordinary vertices of that full wiring, not omitted causes.

Execution below reads independent tables of cell choices. A table has a cell
for every possible input tuple, including observationally impossible tuples.
Only one entry of each node's table is used in a run. Sampling these tables
beforehand is a coupling across experiments; it does not assert that local
stochastic recipes determine a unique counterfactual coupling. Its product
law, uniform row marginals and the causal representation are proved separately.
-/

/-- A recipe for a finite acyclic urn game. The recorded signature and full
wiring are fixed across experiments. A default value merely witnesses a
nonempty value alphabet; it is never a fallback for a missing recipe. Every
parent tuple has an actual nonempty urn, by the type of `contents`. -/
structure CausalUrnGame.{u} (S : ObservedSignature.{u})
    (P : FiniteLatentProjection S) where
  Value : Fin P.hiddenDAG.count → Type u
  values : (node : Fin P.hiddenDAG.count) → List (Value node)
  complete : ∀ node value, value ∈ values node
  valueEq : (node : Fin P.hiddenDAG.count) → DecidableEq (Value node)
  defaultValue : (node : Fin P.hiddenDAG.count) → Value node
  recordedValue : (i : Fin S.count) →
    ValueEquivalence (Value (P.hiddenDAG.observedNode i)) (S.Value i)
  contents : (child : Fin P.hiddenDAG.count) →
    P.hiddenDAG.ParentValues Value child → UrnProb (Value child)

namespace CausalUrnGame
universe u
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

instance (game : CausalUrnGame S P) (node : Fin P.hiddenDAG.count) :
    DecidableEq (game.Value node) := game.valueEq node

/-- The typed tuple of precisely the declared influences, including hidden
parents. Earlier unrelated draws are not available to a recipe. -/
abbrev Parents (game : CausalUrnGame S P) (child : Fin P.hiddenDAG.count) :=
  P.hiddenDAG.ParentValues game.Value child

def parentSlots (game : CausalUrnGame S P) (child parent : Fin P.hiddenDAG.count) :
    List (P.hiddenDAG.edge parent child = true → game.Value parent) :=
  ProofFunction.enumeration (P.hiddenDAG.edge parent child = true) (game.values parent)

def parentTuples (game : CausalUrnGame S P) (child : Fin P.hiddenDAG.count) : List (game.Parents child) :=
  FiniteProduct.enumeration P.hiddenDAG.count _ (game.parentSlots child)

theorem parentTuples_complete (game : CausalUrnGame S P) (child) (parents : game.Parents child) :
    parents ∈ game.parentTuples child :=
  FiniteProduct.enumeration_complete _ _ _
    (fun parent => ProofFunction.enumeration_complete _ _ (game.complete parent)) parents

instance (game : CausalUrnGame S P) (child) : DecidableEq (game.Parents child) :=
  FiniteProduct.assignmentDecidableEq _ _
    (fun parent => ProofFunction.decidableEq (P.hiddenDAG.edge parent child = true))

/-- Explicit finite row codes, with an actual inverse. Deduplication removes
repeated alphabet presentations, never repeated cells of an urn. -/
def parentWitness (game : CausalUrnGame S P) (child) : FiniteWitness (game.Parents child) :=
  FiniteWitness.ofList (deduplicate (game.parentTuples child))
    (fun parents => (mem_deduplicate _ _).mpr (game.parentTuples_complete child parents))
    (deduplicate_nodup _)

/-- Cell types depend on the parent row: a two-cell urn and a three-cell
urn therefore retain exactly their own uniform cell choices. -/
abbrev Cell (game : CausalUrnGame S P) (child) (row : Fin (game.parentWitness child).card) :=
  ULift.{u} (Fin (game.contents child ((game.parentWitness child).decode row)).n)

abbrev Seed (game : CausalUrnGame S P) (child) :=
  (row : Fin (game.parentWitness child).card) → game.Cell child row

abbrev Ticket (game : CausalUrnGame S P) :=
  (child : Fin P.hiddenDAG.count) → game.Seed child

/-- Read the chosen cell of the actual recipe. `decode_encode` makes this
well typed even when different parent rows have different cell counts. -/
def draw (game : CausalUrnGame S P) (child) (parents : game.Parents child)
    (seed : game.Seed child) : game.Value child :=
  let witness := game.parentWitness child
  let cell := seed (witness.encode parents)
  (game.contents child parents).draw
    (cast (congrArg (fun input => Fin (game.contents child input).n)
      (witness.decode_encode parents)) cell.down)

/-- A public setting is fixed before the run and targets recorded urns only.
The graph's explicit lookup proves that hidden urns are always drawn. -/
def forcedAt (game : CausalUrnGame S P) (setting : HardIntervention S)
    (node : Fin P.hiddenDAG.count) : Option (game.Value node) :=
  match found : P.hiddenDAG.observedIndex node with
  | none => none
  | some i => match setting.value i with
    | none => none
    | some value => some
      (P.hiddenDAG.observedIndex_sound node i found ▸ (game.recordedValue i).backward value)

theorem forcedAt_hidden (game : CausalUrnGame S P) (setting) (node)
    (hidden : P.hiddenDAG.hidden node = true) : game.forcedAt setting node = none := by
  unfold forcedAt
  split
  · rfl
  · rename_i i found
    rw [P.hiddenDAG.observedIndex_hidden node hidden] at found
    cases found

/-- Assign a value once, after all its declared parents. A setting skips only
this draw; the recursion for every unforced child still uses the same recipe
and reads the newly obtained parent values. The strict graph rank supplies
termination, independently of whether a node is recorded. -/
def read (game : CausalUrnGame S P) (setting : HardIntervention S)
    (ticket : game.Ticket) (node : Fin P.hiddenDAG.count) : game.Value node :=
  match game.forcedAt setting node with
  | some value => value
  | none => game.draw node (fun parent _edge => game.read setting ticket parent) (ticket node)
termination_by P.hiddenDAG.rank node
decreasing_by exact P.hiddenDAG.edge_rank_lt _edge

/-- Only the record projection hides urns. Their readings have already
participated in the same recursive execution as recorded readings. -/
def record (game : CausalUrnGame S P) (setting : HardIntervention S)
    (ticket : game.Ticket) : S.Assignment :=
  fun i => (game.recordedValue i).forward (game.read setting ticket (P.hiddenDAG.observedNode i))

/-- Any execution satisfying the local instructions gives this same result.
In particular, any compatible evaluation order gives the same assignment:
the rank used to justify recursion is not an extra causal influence. -/
theorem read_eq_of_solution (game : CausalUrnGame S P) (setting) (ticket)
    (candidate : (node : Fin P.hiddenDAG.count) → game.Value node)
    (solution : ∀ node, candidate node = match game.forcedAt setting node with
      | some value => value
      | none => game.draw node (fun parent _ => candidate parent) (ticket node)) (node) :
    game.read setting ticket node = candidate node := by
  rw [read, solution node]
  cases game.forcedAt setting node with
  | some => rfl
  | none =>
    apply congrArg (fun parents => game.draw node parents (ticket node))
    funext parent edge
    exact game.read_eq_of_solution setting ticket candidate solution parent
termination_by P.hiddenDAG.rank node
decreasing_by exact P.hiddenDAG.edge_rank_lt edge

/-- A completed run assigns one value to each urn. There is no overwrite
operation in this interface. The local equation says that the value is either
its declared setting or its one prescribed draw on the same source ticket. -/
structure Run (game : CausalUrnGame S P) (setting : HardIntervention S) (ticket : game.Ticket) where
  value : (node : Fin P.hiddenDAG.count) → game.Value node
  follows : ∀ node, value node = match game.forcedAt setting node with
    | some forced => forced
    | none => game.draw node (fun parent _ => value parent) (ticket node)

/-- Existence is an explicit interpreter, not a selection of a solution. -/
def execute (game : CausalUrnGame S P) (setting) (ticket) : game.Run setting ticket where
  value := game.read setting ticket
  follows := by intro node; rw [read]

/-- Every compatible sequential schedule that produces a completed run has
this same value assignment. The result depends on declared influences and
instructions, rather than a chosen scheduling rank. -/
theorem run_unique (game : CausalUrnGame S P) (setting) (ticket) (run : game.Run setting ticket) :
    run.value = (game.execute setting ticket).value := by
  funext node
  exact (game.read_eq_of_solution setting ticket run.value run.follows node).symm

end CausalUrnGame
end Thesis.Causality
