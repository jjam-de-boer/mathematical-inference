import Thesis.Causality.CausalUrnTickets
import Thesis.Probability.FiniteProductSplicing

namespace Thesis.Causality.CausalUrnGame
open Probability
universe u
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Fresh sampling when the selected recipe depends on earlier draws

A fixed-row marginal alone is not the whole argument: the parent row used in
a run is itself random. Acyclic locality proves that all parent readings are
functions of earlier nodes' tickets. Product splicing then proves that those
readings and this node's entire response table are independent. Finally the
uniform-row theorem identifies its draw law, even on a parent row whose mass
is zero. We use a cross-product identity and never divide by that mass.
-/

/-- Changes to tickets at or after a bound do not affect readings strictly
before that bound. This is a deterministic causality statement, proved by
recursing through declared parents, before using probability independence. -/
theorem read_agrees_below (game : CausalUrnGame S P) (setting)
    (first second : game.Ticket) (bound : Nat)
    (agree : ∀ node, P.hiddenDAG.rank node < bound → first node = second node)
    (node) (earlier : P.hiddenDAG.rank node < bound) :
    game.read setting first node = game.read setting second node := by
  rw [read, read]
  cases game.forcedAt setting node with
  | some => rfl
  | none =>
    rw [agree node earlier]
    apply congrArg (fun parents => game.draw node parents (second node))
    funext parent edge
    exact game.read_agrees_below setting first second bound agree parent
      (Nat.lt_trans (P.hiddenDAG.edge_rank_lt edge) earlier)
termination_by P.hiddenDAG.rank node
decreasing_by exact P.hiddenDAG.edge_rank_lt edge

def readParents (game : CausalUrnGame S P) (setting : HardIntervention S)
    (ticket : game.Ticket) (child) : game.Parents child :=
  fun parent _ => game.read setting ticket parent

/-- The actual parent tuple and the current node's independent response
table have the full product law, for arbitrary joint tests of both. Shared
unrecorded values may correlate different parent coordinates; no independence
between those values is assumed or concluded. -/
theorem parents_seed_product (game : CausalUrnGame S P) (setting) (child)
    (event : Event (game.Parents child × game.Seed child)) :
    QProb.Equiv (game.ticketLaw.probVal (fun ticket => event (game.readParents setting ticket child, ticket child)))
      (((game.ticketLaw.map (fun ticket => game.readParents setting ticket child)).product
        (game.ticketLaw.map (fun ticket => ticket child))).probVal event) := by
  let allocation := fun node => decide (P.hiddenDAG.rank node < P.hiddenDAG.rank child)
  apply FiniteProduct.readouts_product_probVal game.ticketLaw game.seedFactor game.ticketLaw_product
    game.seedValues game.seedValues_complete (fun _ => inferInstance) allocation
    (fun ticket => game.readParents setting ticket child) (fun ticket => ticket child)
  · intro first second
    funext parent edge
    apply game.read_agrees_below setting _ first (P.hiddenDAG.rank child)
    · intro node before
      simp only [FiniteProduct.splice, allocation, decide_eq_true before, if_true]
    · exact P.hiddenDAG.edge_rank_lt edge
  · intro first second
    simp only [FiniteProduct.splice, allocation, Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false]

/-- Fresh drawing in the operational game, conditional on any parent tuple,
as a denominator-free identity. A null parent tuple has zero joint mass on
both sides, rather than a fabricated conditional row obtained by division.
The recipe at that tuple still exists and is used if setting makes it occur. -/
theorem fresh_draw_joint (game : CausalUrnGame S P) (setting) (child)
    (unforced : game.forcedAt setting child = none) (parents : game.Parents child)
    (event : Event (game.Value child)) :
    QProb.Equiv
      (game.ticketLaw.probVal (fun ticket =>
        decide (game.readParents setting ticket child = parents) && event (game.read setting ticket child)))
      (QProb.mul
        (game.ticketLaw.probVal (fun ticket => decide (game.readParents setting ticket child = parents)))
        ((game.contents child parents).probVal event)) := by
  let joint : Event (game.Parents child × game.Seed child) :=
    fun pair => decide (pair.1 = parents) && event (game.draw child parents pair.2)
  have sameEvent : ∀ ticket,
      (decide (game.readParents setting ticket child = parents) && event (game.read setting ticket child)) =
      joint (game.readParents setting ticket child, ticket child) := by
    intro ticket
    by_cases same : game.readParents setting ticket child = parents
    · rw [read, unforced]
      change (decide (game.readParents setting ticket child = parents) &&
        event (game.draw child (game.readParents setting ticket child) (ticket child))) = _
      rw [same]
    · simp only [joint, same, decide_false, Bool.false_and]
  refine QProb.equiv_trans (game.ticketLaw.probVal_congr _ _ sameEvent) ?_
  refine QProb.equiv_trans (game.parents_seed_product setting child joint) ?_
  refine QProb.equiv_trans (FiniteProbRecord.product_probVal _ _
    (fun actual => decide (actual = parents)) (fun seed => event (game.draw child parents seed))) ?_
  apply QProb.mul_congr
  · exact game.ticketLaw.map_probVal _ _
  · exact QProb.equiv_trans (game.ticketLaw.map_probVal _ _)
      (QProb.equiv_trans (FiniteProduct.record_coordinate_probVal_dependent _ game.Seed game.seedFactor child
        (fun seed => event (game.draw child parents seed)))
        (game.draw_uniform child parents event))

end Thesis.Causality.CausalUrnGame
