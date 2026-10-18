import Thesis.Causality.LatentRootDAG

namespace Thesis.Causality

/-!
# The full-DAG projection belonging to an arbitrary latent-root extension

Use the existing root-before-observed graph for the supplied incidence table.
The root values, their probabilities and the observed mechanisms do not enter
this projection. Its classifiers are proved equal to the extension's own
classifiers, with no canonical two-child condition. Native root realizations
can therefore retain one shared cause with any finite number of children.
-/

namespace LatentExtension

variable {S : ObservedSignature} (latent : LatentExtension S)

def rootHiddenDAG : FiniteHiddenDAG S := LatentRootDAG.graph S latent.count latent.incident

theorem rootHiddenDAG_projectedBidirected (left right : Fin S.count) :
    latent.rootHiddenDAG.projectedBidirected left right ↔ latent.projectedBidirected left right = true := by
  rw [rootHiddenDAG, LatentRootDAG.projectedBidirected_iff]
  constructor
  · rintro ⟨different, root, leftIncident, rightIncident⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, (finAny_eq_true_iff _).mpr ⟨root, Bool.and_eq_true_iff.mpr ⟨leftIncident, rightIncident⟩⟩⟩
    cases tested : Nat.beq left.val right.val with
    | false => rfl
    | true => exact False.elim (different (Fin.ext (Nat.eq_of_beq_eq_true tested)))
  · intro shared
    have parts := Bool.and_eq_true_iff.mp shared
    rcases (finAny_eq_true_iff _).mp parts.2 with ⟨root, incident⟩
    refine ⟨?_, root, (Bool.and_eq_true_iff.mp incident).1, (Bool.and_eq_true_iff.mp incident).2⟩
    intro same
    subst right
    rw [natBeq_refl] at parts
    cases parts.1

def rootProjection : FiniteLatentProjection S where
  hiddenDAG := latent.rootHiddenDAG
  directed_matches := fun left right =>
    (LatentRootDAG.projectedDirected_iff S latent.count latent.incident left right).symm
  bidirected := latent.projectedBidirected
  bidirected_matches := fun left right => (latent.rootHiddenDAG_projectedBidirected left right).symm

end LatentExtension

namespace FiniteLatentProjection

/-- The graph and Boolean classifier are the projection's only data fields.
Different proofs of their projection properties carry no additional choice. -/
theorem eq_of_graph_data {S : ObservedSignature} {left right : FiniteLatentProjection S}
    (hidden : left.hiddenDAG = right.hiddenDAG) (bidirected : left.bidirected = right.bidirected) : left = right := by
  cases left
  cases right
  cases hidden
  cases bidirected
  rfl

end FiniteLatentProjection
end Thesis.Causality
