import Thesis.CausalTransport.BinaryBowAttainable

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryBowBounds

open Probability BinaryBow

/-!
# Native bow regressions: interiors, exclusions, and a degenerate interval

The original graph has a hidden root `U` and arrows `U -> X`, `U -> Y`,
`X -> Y`.  Its projection is computed by the actual finite path/common-cause
searches.  A uniform observed law has interval `[1/4,3/4]`: the exact middle
value is attained and probability one is excluded.  A law concentrated on
`X=true` has a degenerate interval for that action, yet leaves the opposite
action completely free between zero and one.

Attainability and identification are obtained from the universal native
theorems.  Finite numerical checks concern only the displayed observed
records and rational endpoint inequalities, not substitute axioms about a
model or an optimizer's output.  The concentrated record has observed zeros;
there is no hidden positivity assumption in its fixed-law classification.
-/

def fullGraph : FiniteHiddenDAG signature where
  count := 3
  observedNode := fun node => if node.val = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  observedNode_injective := by unfold Function.Injective; decide +kernel
  hidden := fun node => decide (node.val = 0)
  observed_not_hidden := by decide +kernel
  node_classified := by decide +kernel
  edge := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨ (parent.val = 0 ∧ child.val = 2) ∨
      (parent.val = 1 ∧ child.val = 2))
  rank := Fin.val
  edge_rank_lt := by decide +kernel

private theorem directed_search_matches : forall first second : Fin signature.count,
    signature.directed first second =
      (fullGraph.hiddenInternalPath? (fullGraph.observedNode first) (fullGraph.observedNode second)).isSome := by
  decide +kernel

private theorem directed_matches : fullGraph.DirectedProjectionMatches := by
  intro first second
  change signature.directed first second = true ↔
    fullGraph.HiddenInternalPath (fullGraph.observedNode first) (fullGraph.observedNode second)
  rw [directed_search_matches first second]
  exact fullGraph.hiddenInternalPath?_iff _ _

def projection : FiniteLatentProjection signature := fullGraph.computedLatentProjection directed_matches

theorem projected_bow_edge : projection.observedGraph.bidirected x y = true := by decide +kernel

def assignment (action outcome : Bool) : signature.Assignment :=
  fun node => if node.val = 0 then action else outcome

def uniformLaw : FiniteProbRecord signature.Assignment where
  atoms := [(assignment false false, 1), (assignment false true, 1),
    (assignment true false, 1), (assignment true true, 1)]
  den := 4
  den_pos := by decide
  total_mass := rfl

def half : QProb := ⟨1, 2, by decide⟩
def quarter : QProb := ⟨1, 4, by decide⟩
def threeQuarters : QProb := ⟨3, 4, by decide⟩

theorem uniform_endpoints : QProb.Equiv (lower uniformLaw true) quarter ∧
    QProb.Equiv (upper uniformLaw true) threeQuarters := by decide +kernel

/-- The middle value is realized by a constructed rational shared-root
switch, and the resulting model lives on this actual original hidden DAG. -/
theorem uniform_middle_attainable : AttainableAt projection uniformLaw true half := by
  apply (attainable_iff_bounds projection projected_bow_edge uniformLaw true half).mpr
  unfold QProb.LE
  decide +kernel

theorem uniform_one_not_attainable : ¬ AttainableAt projection uniformLaw true QProb.one := by
  intro purported
  have upperBound := ((attainable_iff_bounds projection projected_bow_edge uniformLaw true QProb.one).mp purported).2
  have excluded : ¬ QProb.LE QProb.one (upper uniformLaw true) := by
    unfold QProb.LE
    decide +kernel
  exact excluded upperBound

theorem uniform_not_identified (action : Bool) : ¬ IdentifiedAt projection uniformLaw action := by
  intro purported
  have full := (identified_iff_action_one projection projected_bow_edge uniformLaw action).mp purported
  have excluded : ¬ QProb.Equiv (uniformLaw.probVal (actionEvent action)) QProb.one := by
    cases action <;> decide +kernel
  exact excluded full

def concentratedLaw : FiniteProbRecord signature.Assignment where
  atoms := [(assignment true false, 1), (assignment true true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- Fixed-law identification is genuinely broader than graph-level ID,
but only at the action already factual with probability one. -/
theorem concentrated_true_identified : IdentifiedAt projection concentratedLaw true := by
  apply (identified_iff_action_one projection projected_bow_edge concentratedLaw true).mpr
  decide +kernel

theorem concentrated_degenerate_attainable : AttainableAt projection concentratedLaw true half := by
  apply (attainable_iff_bounds projection projected_bow_edge concentratedLaw true half).mpr
  unfold QProb.LE
  decide +kernel

/-- The null observational treatment value is not assigned a conditional.
Instead two actual compatible SCMs attain opposite intervention probabilities. -/
theorem concentrated_opposite_endpoints : AttainableAt projection concentratedLaw false QProb.zero ∧
    AttainableAt projection concentratedLaw false QProb.one := by
  constructor
  · apply (attainable_iff_bounds projection projected_bow_edge concentratedLaw false QProb.zero).mpr
    unfold QProb.LE
    decide +kernel
  · apply (attainable_iff_bounds projection projected_bow_edge concentratedLaw false QProb.one).mpr
    unfold QProb.LE
    decide +kernel

end BinaryBowBounds
end Examples
end Causality
end Thesis
