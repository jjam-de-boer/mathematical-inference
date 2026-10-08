import Thesis.Causality.Identification

namespace Thesis
namespace Causality

/-!
# Retaining a hedge while changing a root-containing outcome

A conditional collider may first separate an auxiliary parent, even when
that parent is not in the original queried outcome.  Its auxiliary numerator
still contains every conditioned common root.  The original hedge can be
indexed by that numerator without changing either forest or the action.

The root-reaching obligation is then reflexive: each common root is itself
an outcome of the auxiliary joint query.  The displayed `rootSeed` is actual
data, such as the already selected separated root.  It supplies the required
outcome coordinate without eliminating a propositional existence claim into
a chosen vertex.  No assertion of countermodels or completeness occurs here.
-/

/-- Change only the query index of a hedge, retaining both forests, their
kept-child map, all common roots, and the original action seed.  The new
outcome contains every root and its action agrees with the old one. -/
def HedgeWitness.withOutcomeContainingRoots
    {S : ObservedSignature} {graph : ObservedGraph S} {query : JointKernelQuery S}
    (w : HedgeWitness graph query) (target : JointKernelQuery S)
    (action : query.action = target.action)
    (containsRoots : NodeSet.Subset w.roots target.outcome)
    (rootSeed : Fin S.count) (rootSeedSelected : w.roots rootSeed = true) :
    HedgeWitness graph target where
  large := w.large
  small := w.small
  roots := w.roots
  child := w.child
  large_forest := w.large_forest
  small_forest := w.small_forest
  small_subset_large := w.small_subset_large
  large_meets_intervention := by rw [← action]; exact w.large_meets_intervention
  small_avoids_intervention := by rw [← action]; exact w.small_avoids_intervention
  roots_reach_outcome := fun root selected => ⟨root, containsRoots root selected, .refl root⟩
  actionSeed := w.actionSeed
  actionSeed_in_large := w.actionSeed_in_large
  actionSeed_in_action := by rw [← action]; exact w.actionSeed_in_action
  outcomeSeed := rootSeed
  outcomeSeed_in_outcome := containsRoots rootSeed rootSeedSelected

/-- Every common root belongs to the large forest, so an outside coordinate
cannot be a root.  When a caller's conditioner equals the common roots, this
also supplies conditioner avoidance without an extra semantic premise. -/
theorem HedgeWitness.roots_false_of_large_false
    {S : ObservedSignature} {graph : ObservedGraph S} {query : JointKernelQuery S}
    (w : HedgeWitness graph query)
    (node : Fin S.count) (outside : w.large node = false) : w.roots node = false := by
  cases selected : w.roots node with
  | false => rfl
  | true =>
      have inside := ((w.large_forest.roots_exact node).mp selected).1
      rw [outside] at inside
      cases inside

end Causality
end Thesis
