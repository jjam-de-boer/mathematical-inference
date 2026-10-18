import Thesis.Causality.CliqueRootGraph
import Thesis.Probability.FiniteProductGrouping

namespace Thesis.Causality

open Probability

/-!
# Group arbitrary latent roots into the fixed clique-root incidence slots

For an input model with the stated observed projection, every root's actual
child mask is a bidirected clique. Compute that mask's index in the graph's
fixed list, then group exactly the old coordinates with that index. The
probability adapter constructs complete independent block factors; it does
not replace a multi-child cause by independent pair causes or identify the
different coordinates which happen to share a block.

The new mechanism recovers each old input from its one owned block, which
is an allowed input at every original child. Structural recursion proves
evaluation preservation for every block assignment and hard intervention.
The full decoded prior law then gives every interventional event probability,
including zero cells, without observational positivity or a canonical-root
premise. Empty/private masks remain available as in the graph construction.

This produces a latent-root SCM with a graph-fixed number of roots. Realizing
it as a `FiniteHiddenDAGSCM` on `cliqueRootProjection` is proved separately in
the downstream `CliqueRootNative` adapter. `ProjectionTemplateRepresentation`
then applies bounded native-template coverage to that actual realization.
-/

universe u v
variable {S : ObservedSignature.{u}}

namespace FiniteLatentSCM

variable (model : FiniteLatentSCM.{u, v} S) (graph : ObservedGraph S)
variable (projected : ∀ left right, model.latent.projectedBidirected left right = graph.bidirected left right)

include projected in
theorem rootChildMask_isClique (root : Fin model.latent.count) : graph.IsClique (model.latent.incident root) := by
  intro left right leftIncident rightIncident different
  rw [← projected left right]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, (finAny_eq_true_iff _).mpr ⟨root, Bool.and_eq_true_iff.mpr ⟨leftIncident, rightIncident⟩⟩⟩
  cases tested : Nat.beq left.val right.val with
  | false => rfl
  | true => exact False.elim (different (Fin.ext (Nat.eq_of_beq_eq_true tested)))

/-- The old child mask is data, so its exact finite-list index is computed.
No root, mask, source value or group is extracted from a bare existence proof. -/
def cliqueGroupOwner (root : Fin model.latent.count) : Fin graph.cliqueRootCount :=
  graph.cliqueRootOf (model.latent.incident root) (model.rootChildMask_isClique graph projected root)

theorem cliqueGroupOwner_mask (root : Fin model.latent.count) :
    graph.cliqueRootMask (model.cliqueGroupOwner graph projected root) = model.latent.incident root :=
  graph.cliqueRootMask_of _ (model.rootChildMask_isClique graph projected root)

def cliqueGroupedLatent : LatentExtension.{u, v} S where
  count := graph.cliqueRootCount
  Value := FiniteProductGrouping.Block model.latent.Value (model.cliqueGroupOwner graph projected)
  valueEnumeration := FiniteProductGrouping.blockEnumeration (model.cliqueGroupOwner graph projected) model.latent.valueEnumeration
  value_complete := FiniteProductGrouping.blockEnumeration_complete (model.cliqueGroupOwner graph projected)
    model.latent.valueEnumeration model.latent.value_complete
  valueDecidableEq := FiniteProductGrouping.blockDecidableEq (model.cliqueGroupOwner graph projected) model.latent.valueDecidableEq
  incident := graph.cliqueRootMask

/-- A child reads an old source only from that source's owned block. The
mask identity proves that this whole block is incident at that child. -/
def cliqueGroupedInputs (child : Fin S.count)
    (inputs : (model.cliqueGroupedLatent graph projected).Inputs child) : model.latent.Inputs child :=
  fun root incident =>
    (inputs (model.cliqueGroupOwner graph projected root) (by
      change graph.cliqueRootMask (model.cliqueGroupOwner graph projected root) child = true
      rw [model.cliqueGroupOwner_mask graph projected root]
      exact incident)) root rfl

/-- Actual independent block factors and their actual product prior are
installed. The original joint law is a proved comparison, not an input field. -/
def cliqueGroupedModel : FiniteLatentSCM.{u, v} S where
  latent := model.cliqueGroupedLatent graph projected
  factor := FiniteProductGrouping.factor (model.cliqueGroupOwner graph projected) model.factor
  prior := FiniteProductGrouping.prior (model.cliqueGroupOwner graph projected) model.factor
  product_law := FiniteProductGrouping.product_law (model.cliqueGroupOwner graph projected) model.factor
  mechanism := fun child parents inputs => model.mechanism child parents (model.cliqueGroupedInputs graph projected child inputs)

theorem cliqueGroupedModel_projectedGraph (left right : Fin S.count) :
    (model.cliqueGroupedModel graph projected).latent.projectedBidirected left right = graph.bidirected left right :=
  graph.cliqueRootIncident_projected left right

def decodeCliqueGroups (blocks : (model.cliqueGroupedLatent graph projected).Assignment) : model.latent.Assignment :=
  FiniteProductGrouping.decode (model.cliqueGroupOwner graph projected) blocks

/-- Pointwise simulation uses the observed topological order, with exactly
the same public intervention values and no factual-equation substitution. -/
theorem cliqueGroupedModel_evalNodeUnder (target : (child : Fin S.count) → Option (S.Value child))
    (blocks : (model.cliqueGroupedLatent graph projected).Assignment) (child : Fin S.count) :
    (model.cliqueGroupedModel graph projected).evalNodeUnder target blocks child =
      model.evalNodeUnder target (model.decodeCliqueGroups graph projected blocks) child := by
  rw [evalNodeUnder, evalNodeUnder]
  unfold equationUnder
  cases selected : target child with
  | some value => rfl
  | none =>
      change model.mechanism child
          (fun parent _ => (model.cliqueGroupedModel graph projected).evalNodeUnder target blocks parent)
          (fun root _ => blocks (model.cliqueGroupOwner graph projected root) root rfl) =
        model.mechanism child
          (fun parent _ => model.evalNodeUnder target (model.decodeCliqueGroups graph projected blocks) parent)
          (fun root _ => blocks (model.cliqueGroupOwner graph projected root) root rfl)
      have parentsAgree :
          (fun parent (_ : S.directed parent child = true) =>
            (model.cliqueGroupedModel graph projected).evalNodeUnder target blocks parent) =
          (fun parent (_ : S.directed parent child = true) =>
            model.evalNodeUnder target (model.decodeCliqueGroups graph projected blocks) parent) := by
        funext parent edge
        exact cliqueGroupedModel_evalNodeUnder target blocks parent
      rw [parentsAgree]
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem cliqueGroupedModel_evalUnder (target : (child : Fin S.count) → Option (S.Value child))
    (blocks : (model.cliqueGroupedLatent graph projected).Assignment) :
    (model.cliqueGroupedModel graph projected).evalUnder target blocks =
      model.evalUnder target (model.decodeCliqueGroups graph projected blocks) := by
  funext child
  exact model.cliqueGroupedModel_evalNodeUnder graph projected target blocks child

/-- Preserve all causal event probabilities, not only factual cells or a
preselected target list. The finite source alphabets are not yet compressed. -/
theorem cliqueGroupedModel_interventionalValue (target : (child : Fin S.count) → Option (S.Value child))
    (event : Event S.Assignment) :
    QProb.Equiv ((model.cliqueGroupedModel graph projected).interventionalValue target event)
      (model.interventionalValue target event) := by
  have units := (model.cliqueGroupedModel graph projected).prior.probVal_congr _ _
    (fun blocks => congrArg event (model.cliqueGroupedModel_evalUnder graph projected target blocks))
  have law := FiniteProductGrouping.decoded_probVal (model.cliqueGroupOwner graph projected) model.factor
    model.prior model.product_law model.latent.valueEnumeration model.latent.value_complete model.latent.valueDecidableEq
    (fun roots => event (model.evalUnder target roots))
  exact QProb.equiv_trans ((model.cliqueGroupedModel graph projected).interventionalValue_eq target event)
    (QProb.equiv_trans units (QProb.equiv_trans law (QProb.equiv_symm (model.interventionalValue_eq target event))))

theorem cliqueGroupedModel_observationalValue (event : Event S.Assignment) :
    QProb.Equiv ((model.cliqueGroupedModel graph projected).observationalValue event) (model.observationalValue event) :=
  model.cliqueGroupedModel_interventionalValue graph projected (noIntervention S) event

theorem cliqueGroupedModel_eventPositive_iff (target : (child : Fin S.count) → Option (S.Value child))
    (evidence : Event S.Assignment) :
    ((model.cliqueGroupedModel graph projected).interventionalDist target).EventPositive evidence ↔
      (model.interventionalDist target).EventPositive evidence :=
  QProb.equiv_num_pos_iff (model.cliqueGroupedModel_interventionalValue graph projected target evidence)

end FiniteLatentSCM
end Thesis.Causality
