import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Causality.HiddenPathSearch

namespace Thesis
namespace Causality

open Probability

universe u

variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Intervention-preserving collapse of finite hidden DAGs

A full hidden DAG need not already have hidden roots.  This module eliminates
its internal hidden vertices from the observed mechanisms, while retaining
one independent root for *each original private-noise coordinate*.  A hidden
coordinate feeds every observed child reached by a hidden-internal path; an
observed coordinate remains private to that observed vertex.

Hidden ancestors are evaluated recursively from their actual mechanisms.
At an observed ancestor the recursion stops and reads a declared projected
parent input.  In particular, it never substitutes that ancestor's factual
equation for its intervened value.  The typed path proves that every accessed
root and every observed parent is a permitted input of the new mechanism.

The noise domains, marginal records, joint prior and product-law proof are
reused, not re-encoded or selected by choice.  Unit-level evaluation agrees
under every hard intervention, and therefore the complete observational and
interventional finite records agree, including their zero cells.

The resulting roots may have more than two observed children.  This is an
exact model collapse, *not* a conversion to independent pairwise hidden causes
and not an assertion of canonical semi-Markovian compatibility.  Countermodel
lifting back into the original hidden DAG, and the final identification and
completeness bridge, are separate remaining obligations.
-/

namespace FiniteHiddenDAG

/-- The noise of an observed node is private to that node.  A hidden node's
noise is exposed precisely to its hidden-internal observed descendants.  The
finite path search supplies the Boolean incidence without an existential
choice of relay or an artificial bound on the number of children. -/
def collapseIncident (H : FiniteHiddenDAG S)
    (source : Fin H.count) (child : Fin S.count) : Bool :=
  if H.hidden source then
    (H.hiddenInternalPath? source (H.observedNode child)).isSome
  else decide (source = H.observedNode child)

/-- An observed mechanism always retains its own private-noise input. -/
theorem collapseIncident_observed (H : FiniteHiddenDAG S) (child : Fin S.count) :
    H.collapseIncident (H.observedNode child) child = true := by
  simp only [collapseIncident, H.observed_not_hidden, Bool.false_eq_true, if_false]
  exact decide_eq_true rfl

/-- A typed hidden relay justifies access to its private-noise coordinate. -/
theorem collapseIncident_of_hidden_path (H : FiniteHiddenDAG S)
    {source : Fin H.count} {child : Fin S.count}
    (hidden : H.hidden source = true)
    (path : H.HiddenInternalPathData source (H.observedNode child)) :
    H.collapseIncident source child = true := by
  simp only [collapseIncident, hidden, if_true]
  exact H.hiddenInternalPath?_complete path.toSpecification

end FiniteHiddenDAG

namespace FiniteHiddenDAGSCM

/-! ## Restricted inputs for the collapsed mechanism -/

/-- Missing observed-index data really means hidden, by the supplied total
node classification.  This stays in `Prop`: no observed index or hidden value
is chosen from a propositional existence statement. -/
private theorem hidden_of_observedIndex_none (M : FiniteHiddenDAGSCM S P)
    (node : Fin P.hiddenDAG.count) (missing : M.observedIndex node = none) :
    P.hiddenDAG.hidden node = true := by
  rcases P.hiddenDAG.node_classified node with hidden | ⟨index, embedding⟩
  · exact hidden
  · have found := M.observedIndex_observed index
    rw [embedding, missing] at found
    cases found

/-- Keep the original private-noise types and their complete finite
presentations.  Even unused coordinates remain in the prior, which makes
the probability-record preservation literal rather than only marginal. -/
def collapsedLatentExtension (M : FiniteHiddenDAGSCM S P) : LatentExtension S where
  count := P.hiddenDAG.count
  Value := M.Noise
  valueEnumeration := M.noiseEnumeration
  value_complete := M.noise_complete
  valueDecidableEq := M.noiseDecidableEq
  incident := P.hiddenDAG.collapseIncident

/-- Evaluate one ancestor on a typed hidden-internal route to the observed
child.  An observed ancestor is a projected parent and is read from `parents`.
A hidden ancestor uses its old mechanism, its incident private noise, and
recursively restricted inputs.  No default value is needed off the route.

Recursion decreases the original DAG rank, independently of how the route
was found.  Thus arbitrary finite hidden domains and nontrivial hidden chains
are retained without a fuel limit or a two-child restriction. -/
private def collapseAncestorValue (M : FiniteHiddenDAGSCM S P)
    (child : Fin S.count) (parents : S.ParentValues child)
    (inputs : M.collapsedLatentExtension.Inputs child)
    (node : Fin P.hiddenDAG.count)
    (path : P.hiddenDAG.HiddenInternalPathData node (P.hiddenDAG.observedNode child)) :
    M.NodeValue node :=
  match selected : M.observedIndex node with
  | some index =>
      M.observedIndex_sound node index selected ▸
        (M.observedEquiv index).backward
          (parents index ((P.directed_matches index child).mpr (by
            rw [M.observedIndex_sound node index selected]
            exact path.toSpecification)))
  | none =>
      let hidden := hidden_of_observedIndex_none M node selected
      M.mechanism node
        (fun parent edge =>
          collapseAncestorValue M child parents inputs parent
            (path.prepend edge hidden))
        (inputs node (P.hiddenDAG.collapseIncident_of_hidden_path hidden path))
termination_by P.hiddenDAG.rank node
decreasing_by exact P.hiddenDAG.edge_rank_lt edge

/-- The observed endpoint is evaluated once, with its own private noise.
Its full-DAG parent values are supplied by the restricted ancestor evaluator;
the observed value equivalence keeps the original public value domain. -/
private def collapseMechanism (M : FiniteHiddenDAGSCM S P)
    (child : Fin S.count) (parents : S.ParentValues child)
    (inputs : M.collapsedLatentExtension.Inputs child) : S.Value child :=
  (M.observedEquiv child).forward
    (M.mechanism (P.hiddenDAG.observedNode child)
      (fun parent edge => collapseAncestorValue M child parents inputs parent (.direct edge))
      (inputs (P.hiddenDAG.observedNode child)
        (P.hiddenDAG.collapseIncident_observed child)))

/-- The actual latent-root SCM obtained by eliminating internal hidden
vertices.  Its complete independent-noise law is reused.  This constructor
does not request positivity, richness, a semantic transfer assumption, or
canonical semi-Markovian compatibility of the resulting multi-child roots. -/
def toLatentRootSCM (M : FiniteHiddenDAGSCM S P) : ExactModel S where
  latent := M.collapsedLatentExtension
  factor := M.factor
  prior := M.prior
  product_law := M.product_law
  mechanism := collapseMechanism M

/-! ## Unit-level preservation under every hard intervention -/

/-- Restricting the actual full evaluation to projected parent inputs gives
the same value at every ancestor.  The hidden case unfolds its old equation;
the observed case uses the two-sided value equivalence and does not unfold
an observed equation past an intervention. -/
private theorem collapseAncestorValue_eq_evalNode
    (M : FiniteHiddenDAGSCM S P) (intervention : HardIntervention S)
    (noise : M.NoiseAssignment) (child : Fin S.count)
    (node : Fin P.hiddenDAG.count)
    (path : P.hiddenDAG.HiddenInternalPathData node (P.hiddenDAG.observedNode child)) :
    collapseAncestorValue M child
      (fun parent _ => M.evalObserved intervention noise parent)
      (fun source _ => noise source) node path =
        M.evalNode intervention noise node := by
  rw [collapseAncestorValue]
  split
  · rename_i index selected
    have embedding := M.observedIndex_sound node index selected
    cases embedding
    exact (M.observedEquiv index).backward_forward _
  · rename_i missing
    have hidden := hidden_of_observedIndex_none M node missing
    rw [evalNode]
    simp only [interventionValueAt, M.hidden_has_no_observed_index node hidden]
    congr 1
    funext parent edge
    exact collapseAncestorValue_eq_evalNode M intervention noise child parent
      (path.prepend edge hidden)
termination_by P.hiddenDAG.rank node
decreasing_by exact P.hiddenDAG.edge_rank_lt edge

/-- The new observed equation agrees with the old equation on the actual
full-model parent values.  This is an equation identity, not yet the recursive
observed evaluation theorem; the next proof supplies that induction. -/
private theorem collapseMechanism_eq_fullEquation
    (M : FiniteHiddenDAGSCM S P) (intervention : HardIntervention S)
    (noise : M.NoiseAssignment) (child : Fin S.count) :
    collapseMechanism M child
      (fun parent _ => M.evalObserved intervention noise parent)
      (fun source _ => noise source) =
      (M.observedEquiv child).forward
        (M.mechanism (P.hiddenDAG.observedNode child)
          (fun parent _ => M.evalNode intervention noise parent)
          (noise (P.hiddenDAG.observedNode child))) := by
  unfold collapseMechanism
  have parentsEqual :
      (fun parent edge => collapseAncestorValue M child
        (fun parent _ => M.evalObserved intervention noise parent)
        (fun source _ => noise source) parent (.direct edge)) =
      (fun parent (_edge : P.hiddenDAG.edge parent (P.hiddenDAG.observedNode child) = true) =>
        M.evalNode intervention noise parent) := by
    funext parent edge
    exact collapseAncestorValue_eq_evalNode M intervention noise child parent (.direct edge)
  rw [parentsEqual]

/-- At an embedded observed vertex, the full-DAG intervention is exactly the
public intervention converted back through that vertex's value equivalence.
The supplied index lookup removes the dependent embedding cast. -/
private theorem interventionValueAt_observed (M : FiniteHiddenDAGSCM S P)
    (intervention : HardIntervention S) (child : Fin S.count) :
    M.interventionValueAt intervention (P.hiddenDAG.observedNode child) =
      (intervention.value child).map (M.observedEquiv child).backward := by
  simp only [interventionValueAt, M.observedIndex_observed]
  cases intervention.value child <;> rfl

/-- The full-model observed evaluator obeys the same intervention match as
a latent-root evaluator.  Hidden recursion is confined to its unforced
mechanism branch; forced observed values are kept literally. -/
private theorem evalObserved_equation (M : FiniteHiddenDAGSCM S P)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment)
    (child : Fin S.count) :
    M.evalObserved intervention noise child =
      match intervention.value child with
      | some value => value
      | none => (M.observedEquiv child).forward
          (M.mechanism (P.hiddenDAG.observedNode child)
            (fun parent _ => M.evalNode intervention noise parent)
            (noise (P.hiddenDAG.observedNode child))) := by
  unfold evalObserved
  rw [evalNode, interventionValueAt_observed]
  cases intervention.value child with
  | none => rfl
  | some value => exact (M.observedEquiv child).forward_backward value

/-- Pointwise evaluation preservation follows the observed topological order.
Every projected parent is earlier in `S`, so the induction replaces exactly
the parent inputs already produced under the same hard intervention. -/
theorem toLatentRootSCM_evalNodeUnder (M : FiniteHiddenDAGSCM S P)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment)
    (child : Fin S.count) :
    M.toLatentRootSCM.evalNodeUnder intervention.value noise child =
      M.evalObserved intervention noise child := by
  rw [FiniteLatentSCM.evalNodeUnder, evalObserved_equation]
  unfold FiniteLatentSCM.equationUnder
  cases selected : intervention.value child with
  | some value => rfl
  | none =>
      have parentsEqual :
          (fun parent (_edge : S.directed parent child = true) =>
            M.toLatentRootSCM.evalNodeUnder intervention.value noise parent) =
          (fun parent (_edge : S.directed parent child = true) =>
            M.evalObserved intervention noise parent) := by
        funext parent edge
        exact toLatentRootSCM_evalNodeUnder M intervention noise parent
      rw [parentsEqual]
      exact collapseMechanism_eq_fullEquation M intervention noise child
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Complete observed assignments agree at every original noise unit, under
arbitrary partial hard interventions.  The latent assignment type is unchanged. -/
theorem toLatentRootSCM_evalUnder (M : FiniteHiddenDAGSCM S P)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment) :
    M.toLatentRootSCM.evalUnder intervention.value noise =
      M.evalObserved intervention noise := by
  funext child
  exact M.toLatentRootSCM_evalNodeUnder intervention noise child

/-! ## Complete finite-record preservation, including zeros -/

/-- Each intervention pushforward is the very same finite probability record.
This is stronger than agreement of selected events or positive cells. -/
theorem toLatentRootSCM_interventionalDist (M : FiniteHiddenDAGSCM S P)
    (intervention : HardIntervention S) :
    M.toLatentRootSCM.interventionalDist intervention.value =
      M.interventionalDist intervention := by
  unfold FiniteLatentSCM.interventionalDist interventionalDist
  change M.prior.map (M.toLatentRootSCM.evalUnder intervention.value) =
    M.prior.map (M.evalObserved intervention)
  have evaluations : M.toLatentRootSCM.evalUnder intervention.value =
      M.evalObserved intervention := by
    funext noise
    exact M.toLatentRootSCM_evalUnder intervention noise
  rw [evaluations]

/-- The no-intervention instance preserves the whole observational record,
without positivity, support qualification, or a changed latent prior. -/
theorem toLatentRootSCM_observationalDist (M : FiniteHiddenDAGSCM S P) :
    M.toLatentRootSCM.observationalDist = M.observationalDist := by
  exact M.toLatentRootSCM_interventionalDist (HardIntervention.empty S)

/-- All interventional Boolean event probabilities are preserved literally.
Thus zero and positive event masses, not just rational equivalence, coincide. -/
theorem toLatentRootSCM_interventionalValue (M : FiniteHiddenDAGSCM S P)
    (intervention : HardIntervention S) (event : S.Assignment -> Bool) :
    M.toLatentRootSCM.interventionalValue intervention.value event =
      M.interventionalValue intervention event := by
  unfold FiniteLatentSCM.interventionalValue interventionalValue
  rw [M.toLatentRootSCM_interventionalDist intervention]

/-- All observational Boolean event probabilities are preserved literally. -/
theorem toLatentRootSCM_observationalValue (M : FiniteHiddenDAGSCM S P)
    (event : S.Assignment -> Bool) :
    M.toLatentRootSCM.observationalValue event = M.observationalValue event := by
  unfold FiniteLatentSCM.observationalValue observationalValue
  rw [M.toLatentRootSCM_observationalDist]

/-! ## Exact projected graph, without a pairwise-root claim -/

/-- Shared roots of the collapsed model are exactly the hidden common
ancestors in the original projection.  An observed private-noise coordinate
cannot create a bidirected edge between distinct observed vertices. -/
theorem collapsedLatentExtension_projectedBidirected_iff
    (M : FiniteHiddenDAGSCM S P) (left right : Fin S.count) :
    M.collapsedLatentExtension.projectedBidirected left right = true <->
      P.hiddenDAG.projectedBidirected left right := by
  constructor
  · intro selected
    have different : left ≠ right := by
      intro same
      subst right
      rw [M.collapsedLatentExtension.projectedBidirected_irreflexive] at selected
      cases selected
    have common := (Bool.and_eq_true_iff.mp selected).2
    rcases (finAny_eq_true_iff _).mp common with ⟨source, incident⟩
    have leftIncident := (Bool.and_eq_true_iff.mp incident).1
    have rightIncident := (Bool.and_eq_true_iff.mp incident).2
    cases hidden : P.hiddenDAG.hidden source with
    | true =>
        have leftPath : P.hiddenDAG.HiddenInternalPath source
            (P.hiddenDAG.observedNode left) :=
          P.hiddenDAG.hiddenInternalPath?_sound (by
            simpa only [collapsedLatentExtension, FiniteHiddenDAG.collapseIncident,
              hidden, if_true] using leftIncident)
        have rightPath : P.hiddenDAG.HiddenInternalPath source
            (P.hiddenDAG.observedNode right) :=
          P.hiddenDAG.hiddenInternalPath?_sound (by
            simpa only [collapsedLatentExtension, FiniteHiddenDAG.collapseIncident,
              hidden, if_true] using rightIncident)
        exact ⟨different, source, hidden, leftPath, rightPath⟩
    | false =>
        have leftNode : source = P.hiddenDAG.observedNode left := of_decide_eq_true (by
          simpa only [collapsedLatentExtension, FiniteHiddenDAG.collapseIncident,
            hidden, Bool.false_eq_true, if_false] using leftIncident)
        have rightNode : source = P.hiddenDAG.observedNode right := of_decide_eq_true (by
          simpa only [collapsedLatentExtension, FiniteHiddenDAG.collapseIncident,
            hidden, Bool.false_eq_true, if_false] using rightIncident)
        exact False.elim (different
          (P.hiddenDAG.observedNode_injective (leftNode.symm.trans rightNode)))
  · rintro ⟨different, source, hidden, leftPath, rightPath⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, (finAny_eq_true_iff _).mpr ⟨source, ?_⟩⟩
    · have differentValues : left.val ≠ right.val := fun equal => different (Fin.ext equal)
      simpa only [Bool.not_eq_true', Nat.beq_eq_false_iff_ne] using differentValues
    · apply Bool.and_eq_true_iff.mpr
      constructor
      · exact P.hiddenDAG.collapseIncident_of_hidden_path hidden leftPath.toData
      · exact P.hiddenDAG.collapseIncident_of_hidden_path hidden rightPath.toData

/-- The collapsed model has exactly the supplied ADMG projection.  This is
the projected-graph part of compatibility only; it deliberately does not
claim the generally false bound of two children per latent input. -/
theorem toLatentRootSCM_projectedGraph (M : FiniteHiddenDAGSCM S P)
    (left right : Fin S.count) :
    M.toLatentRootSCM.observedGraph.bidirected left right =
      P.observedGraph.bidirected left right := by
  cases sourceEdge : M.toLatentRootSCM.observedGraph.bidirected left right with
  | false =>
      cases targetEdge : P.observedGraph.bidirected left right with
      | false => rfl
      | true =>
          have projected := (P.bidirected_matches left right).mp targetEdge
          have found := (M.collapsedLatentExtension_projectedBidirected_iff left right).mpr projected
          rw [sourceEdge] at found
          cases found
  | true =>
      exact ((P.bidirected_matches left right).mpr
        ((M.collapsedLatentExtension_projectedBidirected_iff left right).mp sourceEdge)).symm

end FiniteHiddenDAGSCM
end Causality
end Thesis
