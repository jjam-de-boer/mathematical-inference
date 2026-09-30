import Thesis.CausalTransport.KernelRecursionCompilation

namespace Thesis
namespace Causality

variable {S : ObservedSignature}

/-!
# Hedge transport for current-kernel recursion

The replacement program prunes ordinary ancestry and separately augments the
action by incoming-cut non-ancestors.  Its failure proof therefore cannot use
the older program's incoming-cut whole-host ancestry invariant unchanged.

This module works with actual c-forests and directed walks.  At an immediate
failure, ordinary ancestry supplies an outgoing kept edge for each action
vertex, while the empty additional-action test supplies incoming-cut ancestry
for the free vertices, including every common root.  Recursive transport keeps
the same two forests and changes only the query they witness.

Concrete action and outcome coordinates are recovered by finite Boolean member
search.  Existential reachability is used only to prove that the computed
search cannot be empty, never to choose a value in `Type`.  No soundness theorem,
semantic countermodel assumption, or published completeness record is imported.
-/

/-! ## Query-indexed forests with constructive stored coordinates -/

/-- Package two common-root forests as a hedge, recovering the stored action
and outcome seeds by finite search.  Root reachability guarantees an outcome
exists, but does not select it: `getMember` reads the enumerated node set. -/
noncomputable def HedgeWitness.ofForests
    {G : ObservedGraph S} (query : JointKernelQuery S)
    (large small roots : NodeSet S) (child : ForestChild S)
    (largeForest : CForest G large roots child)
    (smallForest : CForest G small roots (restrictChild small child))
    (subset : NodeSet.Subset small large)
    (meets : NodeSet.meetsBool large query.action = true)
    (avoids : NodeSet.Disjoint small query.action)
    (reaches : forall root, roots root = true ->
      Exists fun outcome => query.outcome outcome = true ∧
        DirectedReachableBy S (fun parent child =>
          mutilatedDirected S query.action parent child = true) root outcome) :
    HedgeWitness G query := by
  let actionSeed := NodeSet.getMeeting large query.action meets
  have actionSelected : large actionSeed = true := NodeSet.getMeeting_left meets
  let sink := forestSink large child largeForest.wellFormedBool actionSeed actionSelected
  have rootSelected : roots sink = true :=
    (largeForest.roots_exact sink).mpr
      (forestSink_spec large child largeForest.wellFormedBool actionSeed actionSelected)
  have outcomeNonempty : NodeSet.isEmpty query.outcome = false := by
    cases empty : NodeSet.isEmpty query.outcome with
    | false => rfl
    | true =>
        rcases reaches sink rootSelected with ⟨outcome, selected, _⟩
        have absent := (NodeSet.isEmpty_eq_true_iff query.outcome).mp empty outcome
        exact False.elim (Bool.false_ne_true (absent.symm.trans selected))
  exact {
    large := large
    small := small
    roots := roots
    child := child
    large_forest := largeForest
    small_forest := smallForest
    small_subset_large := subset
    large_meets_intervention := (NodeSet.meetsBool_eq_true_iff large query.action).mp meets
    small_avoids_intervention := avoids
    roots_reach_outcome := reaches
    actionSeed := actionSeed
    actionSeed_in_large := actionSelected
    actionSeed_in_action := NodeSet.getMeeting_right meets
    outcomeSeed := NodeSet.getMember query.outcome outcomeNonempty
    outcomeSeed_in_outcome := NodeSet.getMember_mem query.outcome outcomeNonempty
  }

/-- Retarget a hedge without changing its selected subgraphs.  Only contact
with the new action, avoidance by the small side, and common-root reachability
need to be proved; stored coordinates are recomputed constructively. -/
noncomputable def HedgeWitness.retargetQuery
    {G : ObservedGraph S} {oldQuery : JointKernelQuery S}
    (witness : HedgeWitness G oldQuery) (query : JointKernelQuery S)
    (meets : NodeSet.meetsBool witness.large query.action = true)
    (avoids : NodeSet.Disjoint witness.small query.action)
    (reaches : forall root, witness.roots root = true ->
      Exists fun outcome => query.outcome outcome = true ∧
        DirectedReachableBy S (fun parent child =>
          mutilatedDirected S query.action parent child = true) root outcome) :
    HedgeWitness G query :=
  HedgeWitness.ofForests query witness.large witness.small witness.roots witness.child
    witness.large_forest witness.small_forest witness.small_subset_large meets avoids reaches

/-! ## Directed reachability through a parent-closed host -/

/-- Enlarging the incoming cut can only delete edges.  This helper is for
propositional directed walks, not for deciding arbitrary propositions. -/
private theorem incomingWalk_mono {smaller larger : NodeSet S}
    (subset : NodeSet.Subset smaller larger) {source target : Fin S.count}
    (walk : DirectedReachableBy S (fun parent child =>
      mutilatedDirected S larger parent child = true) source target) :
    DirectedReachableBy S (fun parent child =>
      mutilatedDirected S smaller parent child = true) source target := by
  induction walk with
  | refl => exact .refl _
  | tail previous edge inductionHypothesis =>
      rename_i parent child
      apply DirectedReachableBy.tail inductionHypothesis
      have childNotCut : larger child = false := by
        cases selected : larger child with
        | false => rfl
        | true => simp [mutilatedDirected, selected] at edge
      have childNotSmaller : smaller child = false := by
        cases selected : smaller child with
        | false => rfl
        | true =>
            have impossible := subset _ selected
            rw [childNotCut] at impossible
            cases impossible
      simpa only [mutilatedDirected, childNotCut, childNotSmaller] using edge

/-- A walk starting outside the incoming cut never enters that cut.  The
positive-length case reads the surviving final edge; the reflexive case keeps
the supplied source fact. -/
private theorem incomingWalk_target_not_cut (action : NodeSet S)
    {source target : Fin S.count}
    (walk : DirectedReachableBy S (fun parent child =>
      mutilatedDirected S action parent child = true) source target)
    (sourceNotCut : action source = false) : action target = false := by
  cases walk with
  | refl => exact sourceNotCut
  | tail _ edge =>
      cases selected : action target with
      | false => rfl
      | true => simp [mutilatedDirected, selected] at edge

/-- Inside a parent-closed host, a surviving incoming-cut walk can be replayed
under another action that agrees on host children.  External parents cannot
occur on the walk because they were already cut and the root is not cut.

This is the pruning transport: an action removed outside the ancestral host
does not appear as an internal child of the root-to-outcome route. -/
theorem ObservedGraph.KernelHostClosed.incomingWalk_transport
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (oldAction newAction : NodeSet S)
    (cutsExternal : NodeSet.Subset externalAction oldAction)
    (sameOnHost : forall child, remaining child = true -> oldAction child = newAction child)
    {source target : Fin S.count}
    (walk : DirectedReachableBy S (fun parent child =>
      mutilatedDirected S oldAction parent child = true) source target)
    (sourceNotCut : oldAction source = false) (targetInside : remaining target = true) :
    DirectedReachableBy S (fun parent child =>
      mutilatedDirected S newAction parent child = true) source target := by
  induction walk with
  | refl => exact .refl _
  | tail previous edge inductionHypothesis =>
      rename_i parent child
      have directed : S.directed parent child = true := by
        unfold mutilatedDirected at edge
        split at edge
        · cases edge
        · exact edge
      have parentInside : remaining parent = true := by
        cases closed.parent_closed targetInside directed with
        | inl internal => exact internal
        | inr external =>
            have parentNotCut := incomingWalk_target_not_cut oldAction previous sourceNotCut
            have parentCut := cutsExternal _ external
            rw [parentNotCut] at parentCut
            cases parentCut
      apply DirectedReachableBy.tail (inductionHypothesis parentInside)
      simpa only [mutilatedDirected, sameOnHost _ targetInside] using edge

/-- A global incoming-cut route to a selected host outcome establishes the
host's executable ancestry test.  Closure rules out external parents on the
route, while the source's not-cut fact rules out even an initial external root.
This is the contradiction used to remove a spurious augmented-action hedge. -/
theorem ObservedGraph.KernelHostClosed.ancestorOfWithin_of_incomingWalk
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) (outcomeSubset : NodeSet.Subset outcome remaining)
    {source target : Fin S.count}
    (walk : DirectedReachableBy S (fun parent child =>
      mutilatedDirected S (NodeSet.union externalAction action) parent child = true) source target)
    (sourceNotCut : NodeSet.union externalAction action source = false)
    (selected : outcome target = true) :
    G.ancestorOfWithin remaining (GraphMutilation.bar action) outcome source = true := by
  have backwards : G.ancestorOfWithin remaining (GraphMutilation.bar action) outcome target = true ->
      G.ancestorOfWithin remaining (GraphMutilation.bar action) outcome source = true := by
    clear selected
    induction walk with
    | refl => exact fun ancestor => ancestor
    | tail previous edge inductionHypothesis =>
        rename_i parent child
        intro childAncestor
        have childInside := ancestralSet_subset G remaining (GraphMutilation.bar action) outcome
          _ childAncestor
        have childFree : NodeSet.union externalAction action child = false := by
          cases cut : NodeSet.union externalAction action child with
          | false => rfl
          | true => simp [mutilatedDirected, cut] at edge
        have directed : S.directed parent child = true := by
          simpa only [mutilatedDirected, childFree] using edge
        have parentInside : remaining parent = true := by
          cases closed.parent_closed childInside directed with
          | inl internal => exact internal
          | inr external =>
              have parentNotCut := incomingWalk_target_not_cut _ previous sourceNotCut
              have parentCut : NodeSet.union externalAction action parent = true :=
                Bool.or_eq_true_iff.mpr (Or.inl external)
              rw [parentNotCut] at parentCut
              cases parentCut
        have actionFree : action child = false := (Bool.or_eq_false_iff.mp childFree).2
        apply inductionHypothesis
        apply G.ancestorOfWithin_prepend remaining (GraphMutilation.bar action) outcome
          (childAncestor := childAncestor)
        exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨parentInside, childInside⟩,
          (observedDirectedEdge_bar G action).mpr ⟨directed, actionFree⟩⟩
  apply backwards
  exact ancestralSet_contains_targets G remaining (GraphMutilation.bar action) outcome
    (outcomeSubset _ selected) selected

/-! ## The replacement program's two distinct ancestry guarantees -/

/-- Query denoted by a host-local invocation, including its already fixed
external actions.  This is the same intervention split used by success
certificates, but requires only graph closure and query well-formedness. -/
def currentKernelJointQuery
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome) : JointKernelQuery S where
  outcome := outcome
  action := NodeSet.union externalAction action
  action_outcome_disjoint := NodeSet.disjoint_union_left_of
    (NodeSet.disjoint_of_subset_right closed.action_disjoint outcomeSubset) disjoint

/-- Empty augmentation means every free host vertex already belongs to the
incoming-cut outcome ancestry.  It does *not* assert this for action vertices,
which is why the older whole-host cut-ancestry failure lemma cannot be reused. -/
theorem currentKernelFree_ancestorOfWithin
    (G : ObservedGraph S) (remaining action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (noAdditional : NodeSet.isEmpty (identificationAdditionalAction G remaining outcome action) = true)
    {node : Fin S.count} (free : NodeSet.diff remaining action node = true) :
    G.ancestorOfWithin remaining (GraphMutilation.bar action) outcome node = true := by
  have localAction : NodeSet.inter action remaining = action := by
    rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset actionSubset]
  have localOutcome : NodeSet.inter outcome remaining = outcome := by
    rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset outcomeSubset]
  have absent := (NodeSet.isEmpty_eq_true_iff _).mp noAdditional node
  cases ancestor : G.ancestralSet remaining (GraphMutilation.bar action) outcome node with
  | true => exact ancestor
  | false =>
      have additional : identificationAdditionalAction G remaining outcome action node = true := by
        simp only [identificationAdditionalAction, localAction, localOutcome, NodeSet.diff,
          ancestor, Bool.not_false, Bool.and_true]
        exact free
      exact False.elim (Bool.false_ne_true (absent.symm.trans additional))

/-- Cutting external actions changes no directed edge inside their disjoint
host.  The equality is purely Boolean and retains the current local action. -/
private theorem hostIncomingEdges_external_eq
    (G : ObservedGraph S) (remaining externalAction action : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining) :
    G.directedEdgeWithin remaining (GraphMutilation.bar (NodeSet.union externalAction action)) =
      G.directedEdgeWithin remaining (GraphMutilation.bar action) := by
  funext parent child
  cases inside : remaining child with
  | false => simp only [ObservedGraph.directedEdgeWithin, inside, Bool.and_false, Bool.false_and]
  | true =>
      have externalFalse := outside.symm child inside
      simp only [ObservedGraph.directedEdgeWithin, ObservedGraph.observedDirectedEdge,
        GraphMutilation.bar, NodeSet.union, NodeSet.empty, externalFalse, Bool.false_or]

/-- A host-local cut ancestor reaches an outcome under the full external/local
action.  The executable walk stays inside the host, where the two cuts agree. -/
theorem currentKernelAncestor_reaches
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) {root : Fin S.count}
    (ancestor : G.ancestorOfWithin remaining (GraphMutilation.bar action) outcome root = true) :
    Exists fun target => outcome target = true ∧
      DirectedReachableBy S (fun parent child =>
        mutilatedDirected S (NodeSet.union externalAction action) parent child = true) root target := by
  have fullAncestor : G.ancestorOfWithin remaining
      (GraphMutilation.bar (NodeSet.union externalAction action)) outcome root = true := by
    unfold ObservedGraph.ancestorOfWithin
    rw [hostIncomingEdges_external_eq G remaining externalAction action closed.action_disjoint]
    exact ancestor
  rcases ancestorOfWithin_reaches_outcome G remaining (NodeSet.union externalAction action)
    outcome fullAncestor with ⟨target, selected, reachable⟩
  exact ⟨target, selected, directedReachableBy_of_within _ reachable⟩

/-! ## Immediate failure is a genuine hedge for the current query -/

/-- Construct the terminal hedge from the replacement branch's actual guards.

Ordinary host ancestry makes every non-free vertex have a directed successor
in the host.  The closed child map therefore has all roots in the free side,
and that side's bidirected component is child-closed.  Empty augmentation then
makes precisely those roots reach the outcome after the full incoming cut.
No whole-host incoming-cut ancestry hypothesis is imposed. -/
noncomputable def currentKernelImmediateHedge
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (actionNonempty : NodeSet.isEmpty action = false)
    (ancestral : NodeSet.equal (G.ancestralSet remaining (GraphMutilation.none S) outcome) remaining = true)
    (noAdditional : NodeSet.isEmpty (identificationAdditionalAction G remaining outcome action) = true)
    {component : NodeSet S}
    (partition : G.cComponents (NodeSet.diff remaining action) = [component])
    (single : G.isSingleCComponent remaining = true) :
    HedgeWitness G (currentKernelJointQuery closed action outcome outcomeSubset disjoint) := by
  have componentEqual := cComponents_eq_of_singleton G (NodeSet.diff remaining action) partition
  have subset : NodeSet.Subset component remaining := by
    rw [componentEqual]
    exact NodeSet.diff_subset_left _ _
  have listed : component ∈ G.cComponents (NodeSet.diff remaining action) := by rw [partition]; exact List.mem_cons_self
  have componentConnected : BidirectedComponent G component := by
    rcases cComponents_mem G _ listed with ⟨root, selected, equal⟩
    rw [equal]
    exact cComponentOf_is_component G _ selected
  let child := closedForestChild remaining component
  have wellFormed := closedForestChild_wellFormed remaining component subset
  have childClosed := closedForestChild_childClosed remaining component
  have rootsInComponent : NodeSet.Subset (keptSinks remaining child) component := by
    apply closedForestChild_keptSinks_subset remaining component
    intro parent inside notFree
    have ancestor := ancestorOfWithin_of_ancestralSet G remaining (GraphMutilation.none S) outcome
      ancestral inside
    have notOutcome : outcome parent = false := by
      have actionSelected : action parent = true := by
        cases selected : action parent with
        | true => rfl
        | false =>
            have free : NodeSet.diff remaining action parent = true := by
              simp only [NodeSet.diff, inside, selected, Bool.not_false, Bool.and_true]
            have selectedComponent : component parent = true := componentEqual.symm ▸ free
            rw [notFree] at selectedComponent
            cases selectedComponent
      exact disjoint parent actionSelected
    rcases ancestorOfWithin_first_successor G remaining (GraphMutilation.none S) outcome
      ancestor notOutcome with ⟨successor, successorInside, edge, _⟩
    have directed : S.directed parent successor = true := by
      simpa only [ObservedGraph.observedDirectedEdge, GraphMutilation.none, NodeSet.empty,
        Bool.not_false, Bool.and_true] using edge
    exact ⟨successor, (mem_directedChildren_iff remaining parent successor).mpr ⟨successorInside, directed⟩⟩
  have sameRoots := keptSinks_restrict_eq remaining component child subset childClosed rootsInComponent
  let largeForest := cForest_of_child G remaining child single wellFormed
  have smallForest : CForest G component (keptSinks remaining child) (restrictChild component child) := by
    rw [← sameRoots]
    exact cForest_of_component_child G component (restrictChild component child) componentConnected
      (childWellFormed_restrict remaining component child wellFormed subset childClosed)
  have meets : NodeSet.meetsBool remaining (NodeSet.union externalAction action) = true := by
    rcases (NodeSet.isEmpty_eq_false_iff action).mp actionNonempty with ⟨node, selected⟩
    exact (NodeSet.meetsBool_eq_true_iff _ _).mpr
      ⟨node, actionSubset node selected, Bool.or_eq_true_iff.mpr (Or.inr selected)⟩
  have avoids : NodeSet.Disjoint component (NodeSet.union externalAction action) :=
    NodeSet.disjoint_union_of
      (NodeSet.Disjoint.of_subset_left closed.action_disjoint.symm subset)
      (by rw [componentEqual]; exact NodeSet.Disjoint.diff_right _ _)
  exact HedgeWitness.ofForests (currentKernelJointQuery closed action outcome outcomeSubset disjoint)
    remaining component (keptSinks remaining child) child largeForest smallForest subset meets avoids
    (fun root selected => currentKernelAncestor_reaches closed action outcome
      (currentKernelFree_ancestorOfWithin G remaining action outcome actionSubset outcomeSubset noAdditional
        (componentEqual ▸ rootsInComponent root selected)))

/-! ## Pruning and restriction retain the same selected forests -/

/-- Lift a hedge through ordinary ancestral pruning.  Closure of the smaller
host is the graph fact supplied by `KernelHostClosed.ancestral`; it forces
every cut root-to-outcome walk to stay in that host.  Actions discarded outside
it can therefore be restored without breaking the route. -/
noncomputable def currentKernelPruneHedge
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome kept : NodeSet S) (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (keptClosed : G.KernelHostClosed kept externalAction)
    (outcomeInKept : NodeSet.Subset outcome kept)
    (witness : HedgeWitness G (currentKernelJointQuery keptClosed (NodeSet.inter action kept)
      outcome outcomeInKept (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _))))
    (largeInKept : NodeSet.Subset witness.large kept) :
    HedgeWitness G (currentKernelJointQuery closed action outcome outcomeSubset disjoint) := by
  have sameActions : forall node, kept node = true ->
      NodeSet.union externalAction (NodeSet.inter action kept) node =
        NodeSet.union externalAction action node := by
    intro node selected
    simp only [NodeSet.union, NodeSet.inter, selected, Bool.and_true]
  have meets : NodeSet.meetsBool witness.large (NodeSet.union externalAction action) = true := by
    rcases witness.large_meets_intervention with ⟨node, selected, fixed⟩
    exact (NodeSet.meetsBool_eq_true_iff _ _).mpr
      ⟨node, selected, (sameActions node (largeInKept node selected)).symm.trans fixed⟩
  have avoids : NodeSet.Disjoint witness.small (NodeSet.union externalAction action) := by
    intro node selected
    rw [← sameActions node (largeInKept node (witness.small_subset_large node selected))]
    exact witness.small_avoids_intervention node selected
  exact witness.retargetQuery (currentKernelJointQuery closed action outcome outcomeSubset disjoint) meets avoids
    (fun root selected => by
      have inSmall := ((witness.small_forest.roots_exact root).mp selected).1
      have notCut := witness.small_avoids_intervention root inSmall
      rcases witness.roots_reach_outcome root selected with ⟨target, targetSelected, walk⟩
      exact ⟨target, targetSelected,
        keptClosed.incomingWalk_transport _ _ (NodeSet.subset_union_left _ _) sameActions
          walk notCut (outcomeInKept target targetSelected)⟩)

/-- Containing-component restriction merely changes the local/external split
of the same intervention.  Discarded vertices are already actions, so the
forests and the incoming-cut root walks need no new graph transformation. -/
noncomputable def currentKernelRestrictionHedge
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome kept : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (keptSubset : NodeSet.Subset kept remaining)
    (outcomeInKept : NodeSet.Subset outcome kept)
    (discardedAction : NodeSet.Subset (NodeSet.diff remaining kept) action)
    (witness : HedgeWitness G (currentKernelJointQuery (closed.restrict kept keptSubset)
      (NodeSet.inter action kept) outcome outcomeInKept
      (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _)))) :
    HedgeWitness G (currentKernelJointQuery closed action outcome outcomeSubset disjoint) := by
  have actionEqual : NodeSet.union (NodeSet.union externalAction (NodeSet.diff remaining kept))
      (NodeSet.inter action kept) = NodeSet.union externalAction action := by
    rw [NodeSet.union_assoc, currentKernelRestrictionAction_eq remaining kept action actionSubset discardedAction]
  have meets : NodeSet.meetsBool witness.large (NodeSet.union externalAction action) = true := by
    rw [← actionEqual]
    exact (NodeSet.meetsBool_eq_true_iff _ _).mpr witness.large_meets_intervention
  have avoids : NodeSet.Disjoint witness.small (NodeSet.union externalAction action) := by
    rw [← actionEqual]
    exact witness.small_avoids_intervention
  exact witness.retargetQuery (currentKernelJointQuery closed action outcome outcomeSubset disjoint) meets avoids
    (fun root selected => by
      rcases witness.roots_reach_outcome root selected with ⟨target, inOutcome, walk⟩
      exact ⟨target, inOutcome, by simpa only [currentKernelJointQuery, actionEqual] using walk⟩)

/-! ## Product-factor hedges reconnect to the parent query -/

/-- A hedge for a product factor lies inside the parent host.  Its small side
avoids the host-complement action, so all its roots lie in that factor.  If
its large side avoided the parent's action as well, bidirected connectivity
would force the *whole* large forest into the same maximal free component,
contradicting the hedge's contact with the factor-complement action. -/
noncomputable def currentKernelProductHedge
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (noAdditional : NodeSet.isEmpty (identificationAdditionalAction G remaining outcome action) = true)
    {component : NodeSet S} (listed : component ∈ G.cComponents (NodeSet.diff remaining action))
    (witness : HedgeWitness G (currentKernelJointQuery closed (NodeSet.diff remaining component)
      component ((cComponents_subset G _ listed).trans (NodeSet.diff_subset_left _ _))
      (NodeSet.disjoint_diff_right _ _)))
    (largeInside : NodeSet.Subset witness.large remaining) :
    HedgeWitness G (currentKernelJointQuery closed action outcome outcomeSubset disjoint) := by
  have componentSubset := cComponents_subset G _ listed
  have smallInComponent : NodeSet.Subset witness.small component := by
    intro node selected
    have inside := largeInside node (witness.small_subset_large node selected)
    have notCut := witness.small_avoids_intervention node selected
    have notComplement : NodeSet.diff remaining component node = false := (Bool.or_eq_false_iff.mp notCut).2
    cases inComponent : component node with
    | true => rfl
    | false => simp only [NodeSet.diff, inside, inComponent, Bool.not_false, Bool.and_true] at notComplement; cases notComplement
  have meets : NodeSet.meetsBool witness.large (NodeSet.union externalAction action) = true := by
    cases contact : NodeSet.meetsBool witness.large (NodeSet.union externalAction action) with
    | true => rfl
    | false =>
        have largeFree : NodeSet.Subset witness.large (NodeSet.diff remaining action) := by
          intro node selected
          have notAction : action node = false := by
            cases fixed : action node with
            | false => rfl
            | true =>
                have impossible := (NodeSet.meetsBool_eq_true_iff witness.large
                  (NodeSet.union externalAction action)).mpr
                  ⟨node, selected, Bool.or_eq_true_iff.mpr (Or.inr fixed)⟩
                rw [contact] at impossible
                cases impossible
          exact Bool.and_eq_true_iff.mpr ⟨largeInside node selected, by rw [notAction]; rfl⟩
        have seedOutside : component witness.actionSeed = false := by
          have externalFalse := closed.action_disjoint.symm _ (largeInside _ witness.actionSeed_in_large)
          have fixed := witness.actionSeed_in_action
          have notComponent : NodeSet.diff remaining component witness.actionSeed = true := by
            simpa only [currentKernelJointQuery, NodeSet.union, externalFalse, Bool.false_or] using fixed
          exact NodeSet.Disjoint.diff_right remaining component _ notComponent
        have rootInside : component witness.actionRoot = true := smallInComponent _ witness.actionRoot_in_small
        have connected := witness.large_forest.component.2 witness.actionRoot witness.actionSeed
          witness.actionRoot_in_large witness.actionSeed_in_large
        have freeWalk := BidirectedConnectedWithin.mono largeFree connected
        rcases cComponents_mem G _ listed with ⟨root, rootSelected, equal⟩
        have rootComponent : G.cComponentOf (NodeSet.diff remaining action) root witness.actionRoot = true := by
          rw [← equal]
          exact rootInside
        have rootToActionRoot := (cComponentOf_eq_true_iff G _ rootSelected).mp rootComponent
        have seedInside : component witness.actionSeed = true := by
          have reached := (cComponentOf_eq_true_iff G _ rootSelected).mpr
            (BidirectedConnectedWithin.trans rootToActionRoot freeWalk)
          exact (congrArg (fun nodes => nodes witness.actionSeed) equal).trans reached
        exact False.elim (Bool.false_ne_true (seedOutside.symm.trans seedInside))
  have avoids : NodeSet.Disjoint witness.small (NodeSet.union externalAction action) := by
    intro node selected
    have free := componentSubset node (smallInComponent node selected)
    have inside := (Bool.and_eq_true_iff.mp free).1
    have actionFalse := NodeSet.Disjoint.diff_right remaining action node free
    exact Bool.or_eq_false_iff.mpr ⟨closed.action_disjoint.symm node inside, actionFalse⟩
  exact witness.retargetQuery (currentKernelJointQuery closed action outcome outcomeSubset disjoint) meets avoids
    (fun root selected => currentKernelAncestor_reaches closed action outcome
      (currentKernelFree_ancestorOfWithin G remaining action outcome actionSubset outcomeSubset noAdditional
        (componentSubset root (smallInComponent root ((witness.small_forest.roots_exact root).mp selected).1))))

/-! ## Augmentation cannot create a hedge meeting only its added action -/

/-- Following a well-formed kept child map stays in its selected forest.
If that forest avoids an incoming cut, every kept edge survives that cut. -/
private theorem forestFollow_incomingWalk
    (nodes : NodeSet S) (child : ForestChild S)
    (wellFormed : childWellFormedBool nodes child = true)
    (action : NodeSet S) (avoids : NodeSet.Disjoint nodes action)
    (fuel : Nat) (start : Fin S.count) (selected : nodes start = true) :
    DirectedReachableBy S (fun parent child => mutilatedDirected S action parent child = true)
      start (forestFollow child start fuel) := by
  induction fuel generalizing start with
  | zero => exact .refl _
  | succ fuel inductionHypothesis =>
      cases next : child start with
      | none => simpa only [forestFollow, next] using (DirectedReachableBy.refl (S := S)
          (edge := fun parent child => mutilatedDirected S action parent child = true) start)
      | some successor =>
          have edge := childWellFormed_edge nodes child wellFormed next
          have survives : mutilatedDirected S action start successor = true := by
            simpa only [mutilatedDirected, avoids successor edge.2.1] using edge.2.2
          simpa only [forestFollow, next] using DirectedReachableBy.step_left survives
            (inductionHypothesis successor edge.2.1)

/-- Lift a hedge through non-ancestor action augmentation.  If its large
forest met only newly added actions, a stored action seed would have a kept
path to a common root and then to an outcome under the original action.
Host closure would make that seed an incoming-cut outcome ancestor, contrary
to the exact definition of the added block.  Boolean contact decides the
case; no excluded middle on an arbitrary proposition is used. -/
noncomputable def currentKernelAdditionalActionHedge
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (witness : HedgeWitness G (currentKernelJointQuery closed
      (NodeSet.union action (identificationAdditionalAction G remaining outcome action)) outcome outcomeSubset
      (NodeSet.disjoint_union_left_of disjoint (by
        have localOutcome : NodeSet.inter outcome remaining = outcome := by
          rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset outcomeSubset]
        simpa only [localOutcome] using identificationAdditionalAction_disjoint_outcome G remaining outcome action)))) :
    HedgeWitness G (currentKernelJointQuery closed action outcome outcomeSubset disjoint) := by
  have parentActionSubset : NodeSet.Subset (NodeSet.union externalAction action)
      (NodeSet.union externalAction (NodeSet.union action (identificationAdditionalAction G remaining outcome action))) :=
    NodeSet.union_subset (NodeSet.subset_union_left _ _)
      ((NodeSet.subset_union_left _ _).trans (NodeSet.subset_union_right _ _))
  have meets : NodeSet.meetsBool witness.large (NodeSet.union externalAction action) = true := by
    cases contact : NodeSet.meetsBool witness.large (NodeSet.union externalAction action) with
    | true => rfl
    | false =>
        have avoidsParent : NodeSet.Disjoint witness.large (NodeSet.union externalAction action) := by
          intro node selected
          cases fixed : NodeSet.union externalAction action node with
          | false => rfl
          | true =>
              have impossible := (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨node, selected, fixed⟩
              rw [contact] at impossible
              cases impossible
        have seedNotCut : (externalAction witness.actionSeed || action witness.actionSeed) = false :=
          avoidsParent _ witness.actionSeed_in_large
        have seedAdded : identificationAdditionalAction G remaining outcome action witness.actionSeed = true := by
          have fixed := witness.actionSeed_in_action
          have externalFalse : externalAction witness.actionSeed = false := (Bool.or_eq_false_iff.mp seedNotCut).1
          have actionFalse : action witness.actionSeed = false := (Bool.or_eq_false_iff.mp seedNotCut).2
          change (externalAction witness.actionSeed ||
            (action witness.actionSeed || identificationAdditionalAction G remaining outcome action witness.actionSeed)) = true at fixed
          rw [externalFalse, actionFalse] at fixed
          exact fixed
        have toRoot := forestFollow_incomingWalk witness.large witness.child witness.large_forest.wellFormedBool
          (NodeSet.union externalAction action) avoidsParent S.count witness.actionSeed witness.actionSeed_in_large
        have toActionRoot : DirectedReachableBy S (fun parent child =>
            mutilatedDirected S (NodeSet.union externalAction action) parent child = true)
            witness.actionSeed witness.actionRoot := by
          simpa only [HedgeWitness.actionRoot, forestSink] using toRoot
        rcases witness.roots_reach_outcome witness.actionRoot witness.actionRoot_in_roots with
          ⟨target, selected, rootWalk⟩
        have seedWalk := DirectedReachableBy.trans toActionRoot (incomingWalk_mono parentActionSubset rootWalk)
        have ancestor := closed.ancestorOfWithin_of_incomingWalk action outcome outcomeSubset seedWalk seedNotCut selected
        have localAction : NodeSet.inter action remaining = action := by
          rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset actionSubset]
        have localOutcome : NodeSet.inter outcome remaining = outcome := by
          rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset outcomeSubset]
        have impossible : identificationAdditionalAction G remaining outcome action witness.actionSeed = false := by
          simp only [identificationAdditionalAction, localAction, localOutcome, NodeSet.diff,
            ObservedGraph.ancestralSet, ancestor,
            Bool.not_true, Bool.and_false]
        exact False.elim (Bool.false_ne_true (impossible.symm.trans seedAdded))
  have avoids : NodeSet.Disjoint witness.small (NodeSet.union externalAction action) := by
    intro node selected
    cases fixed : NodeSet.union externalAction action node with
    | false => rfl
    | true =>
        have addedFixed := parentActionSubset node fixed
        have impossible := witness.small_avoids_intervention node selected
        change NodeSet.union externalAction
          (NodeSet.union action (identificationAdditionalAction G remaining outcome action)) node = false at impossible
        rw [addedFixed] at impossible
        cases impossible
  exact witness.retargetQuery (currentKernelJointQuery closed action outcome outcomeSubset disjoint) meets avoids
    (fun root selected => by
      rcases witness.roots_reach_outcome root selected with ⟨target, inOutcome, walk⟩
      exact ⟨target, inOutcome, incomingWalk_mono parentActionSubset walk⟩)

end Causality
end Thesis
