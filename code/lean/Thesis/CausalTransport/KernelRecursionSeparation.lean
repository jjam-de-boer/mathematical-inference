import Thesis.CausalTransport.KernelSeparation
import Thesis.Causality.IdentificationKernel

namespace Thesis
namespace Causality
namespace ObservedGraph

/-!
# Graph side conditions for current-kernel recursive ID

Ordinary ancestral pruning and action augmentation both use rule 3, but
their ancestry tests are different.  Pruning removes actions outside the
*uncut* host ancestry.  Augmentation intervenes on free host vertices outside
the outcome's ancestry *after incoming action arrows have been cut*.  Neither
operation can be justified by substituting the other test.

This module proves a general incoming-cut non-ancestor separation theorem,
then relates full expanded-DAG ancestry to the actual induced-host tests.
The recursive host's parent closure rules out a path leaving the host and
re-entering it through an uncontrolled parent.  Existing external actions
remain explicitly conditioned and incoming-cut throughout the argument.

The proofs establish actual graph side conditions.  They do not take a
new separation Boolean, a semantic do-rule hypothesis, or a completeness
package as an input, and do not import the soundness implementation.
-/

/-! ## Incoming-cut non-ancestors are isolated in the moral graph -/

/-- If every search target is either incoming-cut or an ancestor of the
left family, the same alternative holds for every observed ancestor.

Backward traversal cannot enter an incoming-cut child.  Otherwise a true
expanded arrow prepends to the child's left-family ancestry.  Latent roots
need no observed conclusion and are left unrestricted in the induction. -/
theorem ancestorOf_observed_cut_or_ancestor
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets left : NodeSet S)
    (targetsCovered : forall target, targets target = true ->
      mutilation.removeIncoming target = true ∨
        G.ancestorOf mutilation left (.observed target) = true)
    (source : Fin S.count)
    (ancestor : G.ancestorOf mutilation targets (.observed source) = true) :
    mutilation.removeIncoming source = true ∨
      G.ancestorOf mutilation left (.observed source) = true := by
  let property : SeparationNode S -> Prop := fun vertex =>
    match vertex with
    | .observed node => mutilation.removeIncoming node = true ∨
        G.ancestorOf mutilation left (.observed node) = true
    | .latentPair _ _ => True
  have backwards : forall {parent child},
      G.expandedMutilatedEdge mutilation parent child = true ->
        property child -> property parent := by
    intro parent child edge childProperty
    cases parent with
    | latentPair _ _ => trivial
    | observed parent =>
        cases child with
        | latentPair _ _ => cases edge
        | observed child =>
            cases childProperty with
            | inl cut =>
                rw [G.expandedMutilatedEdge_into_cut_false mutilation
                  (.observed parent) child cut] at edge
                cases edge
            | inr ancestor => exact Or.inr (G.ancestorOf_prepend mutilation left edge ancestor)
  rcases (G.ancestorOf_eq_true_iff mutilation targets (.observed source)).mp ancestor with
    ⟨target, selected, _length, _bound, walk⟩
  rcases walk with ⟨walk⟩
  have backwardsWalk {length : Nat} {parent child : SeparationNode S}
      (walk : FiniteReachability.ExactWalk (G.expandedMutilatedEdge mutilation)
        length parent child) (childProperty : property child) : property parent := by
    induction walk with
    | refl => exact childProperty
    | step first _rest inductionHypothesis =>
        exact backwards first (inductionHypothesis childProperty)
  exact backwardsWalk walk (targetsCovered target selected)

/-- An incoming-cut observed non-ancestor has no moral adjacency when the
other targets are either incoming-cut or ancestral of the left family.

Incoming edges are absent by the cut.  An outgoing edge into an ancestral
child would make this vertex a left-family ancestor; an edge into a cut
child is impossible.  The same outgoing-edge argument excludes co-parent
moral edges through a shared ancestral child. -/
theorem ancestralMoralEdge_from_cut_nonancestor_false
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets left : NodeSet S)
    (targetsCovered : forall target, targets target = true ->
      mutilation.removeIncoming target = true ∨
        G.ancestorOf mutilation left (.observed target) = true)
    (source : Fin S.count) (cut : mutilation.removeIncoming source = true)
    (notAncestor : G.ancestorOf mutilation left (.observed source) = false)
    (other : SeparationNode S) :
    G.ancestralMoralEdge mutilation targets (.observed source) other = false := by
  have noForward (child : SeparationNode S)
      (ancestor : G.ancestorOf mutilation targets child = true) :
      G.expandedMutilatedEdge mutilation (.observed source) child = false := by
    cases child with
    | latentPair _ _ => rfl
    | observed child =>
        cases G.ancestorOf_observed_cut_or_ancestor mutilation targets left
            targetsCovered child ancestor with
        | inl childCut =>
            exact G.expandedMutilatedEdge_into_cut_false mutilation (.observed source) child childCut
        | inr leftAncestor =>
            cases edge : G.expandedMutilatedEdge mutilation (.observed source) (.observed child) with
            | false => rfl
            | true =>
                have impossible := G.ancestorOf_prepend mutilation left edge leftAncestor
                rw [notAncestor] at impossible
                cases impossible
  cases moral : G.ancestralMoralEdge mutilation targets (.observed source) other with
  | false => rfl
  | true =>
      have otherAncestor := (G.ancestorOf_of_ancestralMoralEdge mutilation targets moral).2
      cases G.ancestralMoralEdge_cases mutilation targets moral with
      | inl adjacent =>
          cases adjacent with
          | inl forward => rw [noForward other otherAncestor] at forward; cases forward
          | inr reverse =>
              rw [G.expandedMutilatedEdge_into_cut_false mutilation other source cut] at reverse
              cases reverse
      | inr common =>
          rcases common with ⟨child, ancestor, forward, _otherParent⟩
          rw [noForward child ancestor] at forward
          cases forward

/-- General rule-3 separation at an empty ordinary conditioner.
Incoming-cut right vertices that do not ancestor the left family are
isolated in its relevant moral graph once the conditioned action vertices
are also incoming-cut.  No topological-index bound is required here. -/
theorem dSeparated_of_incoming_cut_nonancestors
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (cutsRight : NodeSet.Subset right mutilation.removeIncoming)
    (cutsConditioned : NodeSet.Subset conditioned mutilation.removeIncoming)
    (rightNotAncestor : forall source, right source = true ->
      G.ancestorOf mutilation left (.observed source) = false) :
    G.dSeparated mutilation left right conditioned = true := by
  apply G.dSeparated_of_ancestrally_isolated_right mutilation left right conditioned
  · intro source selected
    cases selectedRight : right source with
    | false => rfl
    | true =>
        have ancestor := G.ancestorOf_target mutilation left selected
        rw [rightNotAncestor source selectedRight] at ancestor
        cases ancestor
  · intro source selected other
    refine G.ancestralMoralEdge_from_cut_nonancestor_false mutilation
      (NodeSet.union left (NodeSet.union right conditioned)) left
      ?_ source (cutsRight source selected) (rightNotAncestor source selected) other
    intro target member
    cases (NodeSet.union_eq_true left (NodeSet.union right conditioned) target).mp member with
    | inl leftTarget => exact Or.inr (G.ancestorOf_target mutilation left leftTarget)
    | inr others =>
        cases (NodeSet.union_eq_true right conditioned target).mp others with
        | inl rightTarget => exact Or.inl (cutsRight target rightTarget)
        | inr conditionedTarget => exact Or.inl (cutsConditioned target conditionedTarget)

/-! ## Full ancestry respects the parent-closed recursive host -/

/-- Expanded observed ancestry reduces to an induced-host ancestry test,
except at the explicitly fixed external actions.

The full mutilation may remove more arrows than the induced-host test.  The
`observedEdges` inclusion records this direction: a surviving full-graph
arrow must survive the host test as well.  This covers uncut pruning and
incoming-cut action augmentation with one backward-walk induction. -/
theorem KernelHostClosed.ancestorOf_in_ancestralSet
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : KernelHostClosed G remaining externalAction)
    (mutilation hostMutilation : GraphMutilation S)
    (cutsExternal : NodeSet.Subset externalAction mutilation.removeIncoming)
    (observedEdges : forall {parent child},
      G.observedDirectedEdge mutilation parent child = true ->
        G.observedDirectedEdge hostMutilation parent child = true)
    (targets : NodeSet S)
    (targetsInside : forall target, targets target = true ->
      remaining target = true ∨ externalAction target = true)
    (source : Fin S.count)
    (ancestor : G.ancestorOf mutilation targets (.observed source) = true) :
    externalAction source = true ∨ G.ancestralSet remaining hostMutilation targets source = true := by
  let property : SeparationNode S -> Prop := fun vertex =>
    match vertex with
    | .observed node => externalAction node = true ∨
        G.ancestralSet remaining hostMutilation targets node = true
    | .latentPair _ _ => True
  have backwards : forall {parent child},
      G.expandedMutilatedEdge mutilation parent child = true ->
        property child -> property parent := by
    intro parent child edge childProperty
    cases parent with
    | latentPair _ _ => trivial
    | observed parent =>
        cases child with
        | latentPair _ _ => cases edge
        | observed child =>
            cases childProperty with
            | inl external =>
                rw [G.expandedMutilatedEdge_into_cut_false mutilation
                  (.observed parent) child (cutsExternal child external)] at edge
                cases edge
            | inr internalAncestor =>
                have childHost := ancestralSet_subset G remaining hostMutilation targets
                  child internalAncestor
                have directed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp edge).1).1
                cases closed.parent_closed childHost directed with
                | inr external => exact Or.inl external
                | inl parentHost =>
                    apply Or.inr
                    apply G.ancestorOfWithin_prepend remaining hostMutilation targets
                      (childAncestor := internalAncestor)
                    exact Bool.and_eq_true_iff.mpr
                      ⟨Bool.and_eq_true_iff.mpr ⟨parentHost, childHost⟩,
                        observedEdges edge⟩
  rcases (G.ancestorOf_eq_true_iff mutilation targets (.observed source)).mp ancestor with
    ⟨target, selected, _length, _bound, walk⟩
  rcases walk with ⟨walk⟩
  have backwardsWalk {length : Nat} {parent child : SeparationNode S}
      (walk : FiniteReachability.ExactWalk (G.expandedMutilatedEdge mutilation)
        length parent child) (childProperty : property child) : property parent := by
    induction walk with
    | refl => exact childProperty
    | step first _rest inductionHypothesis =>
        exact backwards first (inductionHypothesis childProperty)
  apply backwardsWalk walk
  cases targetsInside target selected with
  | inr external => exact Or.inl external
  | inl internal =>
      exact Or.inr (ancestralSet_contains_targets G remaining hostMutilation targets internal selected)

/-! ## The induced-host tests entail the actual rule-3 side conditions -/

/-- Adding incoming cuts can only remove directed arrows.  The executable
edge inclusion is constructive and is used to compare the full side graph
with the host-local incoming-cut ancestry search. -/
theorem observedDirectedEdge_bar_mono
    (G : ObservedGraph S) {smaller larger : NodeSet S}
    (included : NodeSet.Subset smaller larger) {parent child : Fin S.count}
    (edge : G.observedDirectedEdge (GraphMutilation.bar larger) parent child = true) :
    G.observedDirectedEdge (GraphMutilation.bar smaller) parent child = true := by
  have parts := Bool.and_eq_true_iff.mp edge
  have directed := (Bool.and_eq_true_iff.mp parts.1).1
  have notLarger : larger child = false := by simpa [GraphMutilation.bar] using parts.2
  have notSmaller : smaller child = false := by
    cases selected : smaller child with
    | false => rfl
    | true =>
        have impossible := included child selected
        rw [notLarger] at impossible
        cases impossible
  simp [observedDirectedEdge, GraphMutilation.bar, NodeSet.empty, directed, notSmaller]

/-- A host non-ancestor test suffices for rule 3's incoming-cut separation.

The removed block lies in the parent-closed host.  Its failure to reach the
outcome in `hostMutilation` precludes full expanded ancestry in the stronger
side graph: such ancestry would either end at an external action (excluded
by disjointness) or give the forbidden induced-host reachability witness.
The ancestry criterion may be uncut or incoming-cut, as specified by the
edge-inclusion premise; the two engine branches specialize it separately. -/
theorem dSeparated_host_nonancestors
    (G : ObservedGraph S) (remaining externalAction baseAction outcome removed : NodeSet S)
    (closed : KernelHostClosed G remaining externalAction)
    (hostMutilation : GraphMutilation S)
    (externalIncluded : NodeSet.Subset externalAction baseAction)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (removedSubset : NodeSet.Subset removed remaining)
    (observedEdges : forall {parent child},
      G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union baseAction removed))
        parent child = true -> G.observedDirectedEdge hostMutilation parent child = true)
    (removedNotAncestor : forall source, removed source = true ->
      G.ancestralSet remaining hostMutilation outcome source = false) :
    G.dSeparated (GraphMutilation.bar (NodeSet.union baseAction removed))
      outcome removed baseAction = true := by
  let mutilation := GraphMutilation.bar (NodeSet.union baseAction removed)
  apply G.dSeparated_of_incoming_cut_nonancestors mutilation outcome removed baseAction
    (NodeSet.subset_union_right baseAction removed)
    (NodeSet.subset_union_left baseAction removed)
  intro source selected
  cases ancestor : G.ancestorOf mutilation outcome (.observed source) with
  | false => rfl
  | true =>
      have externalFalse := closed.action_disjoint.symm source (removedSubset source selected)
      have hostAncestor := closed.ancestorOf_in_ancestralSet mutilation hostMutilation
        (externalIncluded.trans (NodeSet.subset_union_left baseAction removed))
        observedEdges outcome (fun target member => Or.inl (outcomeSubset target member))
        source ancestor
      cases hostAncestor with
      | inl external => rw [externalFalse] at external; cases external
      | inr internal => rw [removedNotAncestor source selected] at internal; cases internal

/-- The path-syntax rule-3 side condition retains its published `Z(W)`
definition.  Since the ordinary conditioner is empty, the removable set is
the entire removed block; the existing empty-conditioner theorem performs
that checked conversion rather than replacing the definition by fiat. -/
theorem pathDSeparated_rule3_host_nonancestors
    (G : ObservedGraph S) (remaining externalAction baseAction outcome removed : NodeSet S)
    (closed : KernelHostClosed G remaining externalAction)
    (hostMutilation : GraphMutilation S)
    (externalIncluded : NodeSet.Subset externalAction baseAction)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (removedSubset : NodeSet.Subset removed remaining)
    (observedEdges : forall {parent child},
      G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union baseAction removed))
        parent child = true -> G.observedDirectedEdge hostMutilation parent child = true)
    (removedNotAncestor : forall source, removed source = true ->
      G.ancestralSet remaining hostMutilation outcome source = false) :
    let base := GraphMutilation.bar baseAction
    let removable := G.nonAncestorsOf base removed NodeSet.empty
    PathSpecification.PathDSeparated G
      { removeIncoming := NodeSet.union baseAction removable, removeOutgoing := NodeSet.empty }
      outcome removed (NodeSet.union baseAction NodeSet.empty) :=
  pathDSeparated_rule3_empty_w G baseAction outcome removed
    (G.dSeparationCorrectness.pathDSeparated_of_dSeparated
      (G.dSeparated_host_nonancestors remaining externalAction baseAction outcome removed
        closed hostMutilation externalIncluded outcomeSubset removedSubset observedEdges
        removedNotAncestor))

/-- Ordinary ancestral pruning may delete the local actions outside the
uncut outcome ancestry.  External actions are retained, and the kept local
action is the intersection with that same uncut host ancestry. -/
theorem pathDSeparated_rule3_prune_actions
    (G : ObservedGraph S) (remaining externalAction action outcome : NodeSet S)
    (closed : KernelHostClosed G remaining externalAction)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining) :
    let kept := G.ancestralSet remaining (GraphMutilation.none S) outcome
    let baseAction := NodeSet.union externalAction (NodeSet.inter action kept)
    let removed := NodeSet.diff action kept
    let removable := G.nonAncestorsOf (GraphMutilation.bar baseAction) removed NodeSet.empty
    PathSpecification.PathDSeparated G
      { removeIncoming := NodeSet.union baseAction removable, removeOutgoing := NodeSet.empty }
      outcome removed (NodeSet.union baseAction NodeSet.empty) := by
  dsimp
  apply G.pathDSeparated_rule3_host_nonancestors remaining externalAction
    (NodeSet.union externalAction
      (NodeSet.inter action (G.ancestralSet remaining (GraphMutilation.none S) outcome)))
    outcome (NodeSet.diff action (G.ancestralSet remaining (GraphMutilation.none S) outcome))
    closed (GraphMutilation.none S) (NodeSet.subset_union_left _ _) outcomeSubset
    ((NodeSet.diff_subset_left _ _).trans actionSubset)
  · intro parent child edge
    have directed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp edge).1).1
    simpa [observedDirectedEdge, GraphMutilation.none, NodeSet.empty] using directed
  · intro source selected
    have excluded := (Bool.and_eq_true_iff.mp selected).2
    simpa using excluded

/-- Action augmentation uses the incoming-cut host ancestry, not the
ordinary pruning ancestry.  Every selected extra vertex is a free host
non-ancestor by the exact definition of `identificationAdditionalAction`. -/
theorem pathDSeparated_rule3_additional_action
    (G : ObservedGraph S) (remaining externalAction action outcome : NodeSet S)
    (closed : KernelHostClosed G remaining externalAction) :
    let localAction := NodeSet.inter action remaining
    let localOutcome := NodeSet.inter outcome remaining
    let baseAction := NodeSet.union externalAction localAction
    let additional := identificationAdditionalAction G remaining outcome action
    let removable := G.nonAncestorsOf (GraphMutilation.bar baseAction) additional NodeSet.empty
    PathSpecification.PathDSeparated G
      { removeIncoming := NodeSet.union baseAction removable, removeOutgoing := NodeSet.empty }
      localOutcome additional (NodeSet.union baseAction NodeSet.empty) := by
  dsimp
  apply G.pathDSeparated_rule3_host_nonancestors remaining externalAction
    (NodeSet.union externalAction (NodeSet.inter action remaining))
    (NodeSet.inter outcome remaining) (identificationAdditionalAction G remaining outcome action)
    closed (GraphMutilation.bar (NodeSet.inter action remaining))
    (NodeSet.subset_union_left _ _) (NodeSet.inter_subset_right _ _)
    (identificationAdditionalAction_subset_remaining G remaining outcome action)
  · intro parent child edge
    exact G.observedDirectedEdge_bar_mono
      ((NodeSet.subset_union_right externalAction (NodeSet.inter action remaining)).trans
        (NodeSet.subset_union_left _ _)) edge
  · intro source selected
    have excluded := (Bool.and_eq_true_iff.mp selected).2
    simpa using excluded

end ObservedGraph
end Causality
end Thesis
