import Thesis.CausalTransport.ActivePathNormalization

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentActivePathNormalization

open PathSpecification

/-!
# Regression checks for the two collider-normalization objectives

Two open endpoints `U,V` share the conditioned colliders `C(2),D(3)`.
The ordinary first-success search chooses `U -> C <- V`; the normal-form
search must choose `U -> D <- V`, because both have one collider and `D`
has greater topological rank.  This tests the secondary objective on actual
search data, not just an arithmetic inequality about abstract scores.

A second graph adds the genuine private pair `U <-> V`.  Its expanded latent
path has no collider, and must beat both observed collider paths regardless
of their later ranks.  Thus the primary objective really has priority.

The graph is deliberately small.  These kernel-checked computations do not
exercise the exhaustive normal-form search on a large graph or evaluate any
SCM probability table.  All path equality checks compare finite vertex codes.
-/

def signature : ObservedSignature where
  count := 4
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val < 2 ∧ 2 ≤ child.val)
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def leftEndpoint : Fin signature.count := ⟨0, by decide⟩
def rightEndpoint : Fin signature.count := ⟨1, by decide⟩
def earlierCollider : Fin signature.count := ⟨2, by decide⟩
def laterCollider : Fin signature.count := ⟨3, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := fun _ => rfl

def conditioned : NodeSet signature := fun node => decide (2 ≤ node.val)

/-- The old first-success API remains unchanged; its search order is not
mistaken for the rank-maximizing objective needed by a rerouting argument. -/
theorem first_success_uses_earlier_collider :
    (activePath? graph (GraphMutilation.none signature) conditioned
      (.observed leftEndpoint) (.observed rightEndpoint)).map
      (fun path => path.nodes.map SeparationNode.code) = some [0, 2, 1] := by
  decide +kernel

/-- Equal collider counts are resolved by greatest collider-rank sum.
The least-score search returns the actual later-collider vertex list. -/
theorem least_score_uses_later_collider :
    (leastScoreActivePath? graph (GraphMutilation.none signature) conditioned
      (.observed leftEndpoint) (.observed rightEndpoint)
      (colliderNormalizationScore graph (GraphMutilation.none signature))).map
      (fun path => path.nodes.map SeparationNode.code) = some [0, 3, 1] := by
  decide +kernel

/-- The two candidates have the same primary objective.  Their rank sums
differ, so minimizing count alone could not distinguish these witnesses. -/
theorem equal_count_distinct_ranks :
    colliderCount graph (GraphMutilation.none signature)
      [.observed leftEndpoint, .observed earlierCollider, .observed rightEndpoint] = 1 ∧
    colliderCount graph (GraphMutilation.none signature)
      [.observed leftEndpoint, .observed laterCollider, .observed rightEndpoint] = 1 ∧
    colliderRankSum graph (GraphMutilation.none signature)
      [.observed leftEndpoint, .observed earlierCollider, .observed rightEndpoint] = 2 ∧
    colliderRankSum graph (GraphMutilation.none signature)
      [.observed leftEndpoint, .observed laterCollider, .observed rightEndpoint] = 3 := by
  decide +kernel

def pairGraph : ObservedGraph signature where
  bidirected := fun left right => decide (left.val < 2 ∧ right.val < 2 ∧ left ≠ right)
  bidirected_symmetric := by
    intro left right edge
    have parts := of_decide_eq_true edge
    exact decide_eq_true ⟨parts.2.1, parts.1, Ne.symm parts.2.2⟩
  bidirected_irreflexive := by intro node; simp

/-- Zero colliders beat a later observed collider.  The winning path uses
the genuine pair's expanded latent vertex, not a globally shared hidden input. -/
theorem collider_count_has_priority :
    (leastScoreActivePath? pairGraph (GraphMutilation.none signature) conditioned
      (.observed leftEndpoint) (.observed rightEndpoint)
      (colliderNormalizationScore pairGraph (GraphMutilation.none signature))).map
      (fun path => path.nodes.map SeparationNode.code) =
        some [0, (SeparationNode.latentPair leftEndpoint rightEndpoint).code, 1] := by
  decide +kernel

/-- Closed endpoints do not acquire a witness through score optimization.
The candidate decoder still enforces the exact original endpoint openness. -/
theorem closed_endpoint_has_no_normal_path :
    leastScoreActivePath? graph (GraphMutilation.none signature) NodeSet.full
      (.observed leftEndpoint) (.observed rightEndpoint)
      (colliderNormalizationScore graph (GraphMutilation.none signature)) = none := by
  decide +kernel

end CurrentActivePathNormalization
end Examples
end Causality
end Thesis
