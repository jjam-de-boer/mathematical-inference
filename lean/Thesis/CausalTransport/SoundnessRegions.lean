import Thesis.CausalTransport.SoundnessFoundations

namespace Thesis
namespace Causality

open Probability

/-!
# Kernel regions for the finite soundness proof

The original agreement-cylinder, intervention-prefix and latent-relevance
arguments live here. They turn ancestry, open cores and conditioned regions
into exact statements about which latent coordinates an event can inspect.

The probability and enumeration foundations are imported, not restated.
Declarations retain their existing Thesis.Causality.Kernel names and original
proof bodies. No private helper crosses this module boundary. Keeping this
region layer separate reduces local compilation state; it does not strengthen
a graph assumption or restrict the model class certified by soundness.
-/

namespace Kernel

/-- Agreement cylinders are unchanged when the latent assignments agree on
all roots relevant to a backward-closed node set containing the cylinder. -/
theorem agreesOn_evalUnder_congr_of_rootAgreement
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (relevant observed : NodeSet S) (reference : S.Assignment)
    (closed : model.BackwardClosedUnder intervention relevant)
    (contained : NodeSet.Subset observed relevant)
    (left right : model.latent.Assignment)
    (rootsAgree : forall root,
      model.latentRelevantUnder intervention relevant root = true ->
      left root = right root) :
    Kernel.agreesOn observed reference (model.evalUnder intervention left) =
      Kernel.agreesOn observed reference
        (model.evalUnder intervention right) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases selected : observed child with
  | false => rfl
  | true =>
      have relevantChild := contained child selected
      have evaluated := model.evalUnder_eq_on_of_rootAgreement intervention
        relevant closed left right rootsAgree child relevantChild
      simp only [↓reduceIte]
      rw [evaluated]

theorem agreesOn_evalUnder_dependsOnSelected
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (relevant observed : NodeSet S) (reference : S.Assignment)
    (closed : model.BackwardClosedUnder intervention relevant)
    (contained : NodeSet.Subset observed relevant) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value (model.latentRelevantUnder intervention relevant)
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder intervention roots)) := by
  intro left right rootsAgree
  exact agreesOn_evalUnder_congr_of_rootAgreement model intervention
    relevant observed reference closed contained left right rootsAgree

/-!
### Agreement cylinders across the canonical moral cut

The two lemmas below connect the graph-theoretic separator to the product
factorization API.  They intentionally retain an arbitrary backward-closed
evaluation region: the three do-calculus rules use different interventions
and may enlarge an outcome cylinder by fixed action vertices, but only its
free ancestral vertices determine which latent coordinates are observed.
-/

/-- A cylinder supported in the left open ancestral moral component depends
only on the concrete latent coordinates selected by the canonical cut. -/
theorem agreesOn_evalUnder_dependsOnMoralLeftSide
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (mutilation : GraphMutilation S)
    (left right conditioned relevant observed : NodeSet S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (reference : S.Assignment)
    (closed : model.BackwardClosedUnder intervention relevant)
    (contained : NodeSet.Subset observed relevant)
    (free : forall child, intervention child = none ->
      mutilation.removeIncoming child = false)
    (ancestral : NodeSet.Subset relevant (fun child =>
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        (.observed child)))
    (openNodes : NodeSet.Subset relevant (fun child => !conditioned child))
    (onLeft : NodeSet.Subset relevant (fun child =>
      G.moralLeftSide mutilation left right conditioned (.observed child))) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentMoralLeftSide G mutilation left right conditioned)
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder intervention roots)) := by
  apply CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots => Kernel.agreesOn observed reference
      (model.evalUnder intervention roots))
  · intro root relevantRoot
    exact model.latentMoralLeftSide_eq_true_of_relevant G projected
      mutilation left right conditioned relevant intervention free ancestral
      openNodes onLeft root relevantRoot
  · exact agreesOn_evalUnder_dependsOnSelected model intervention
      relevant observed reference closed contained

/-- A cylinder supported in the right open ancestral moral component depends
only on the coordinates unselected by the canonical cut.  The proof first
views the cylinder as depending on the complement mask, then converts that
statement to the unselected-coordinate formulation expected by product
independence. -/
theorem agreesOn_evalUnder_dependsOnMoralRightSide
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (mutilation : GraphMutilation S)
    (left right conditioned relevant observed : NodeSet S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (reference : S.Assignment)
    (closed : model.BackwardClosedUnder intervention relevant)
    (contained : NodeSet.Subset observed relevant)
    (free : forall child, intervention child = none ->
      mutilation.removeIncoming child = false)
    (ancestral : NodeSet.Subset relevant (fun child =>
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        (.observed child)))
    (openNodes : NodeSet.Subset relevant (fun child => !conditioned child))
    (onRight : NodeSet.Subset relevant (fun child =>
      !G.moralLeftSide mutilation left right conditioned (.observed child))) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentMoralLeftSide G mutilation left right conditioned)
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder intervention roots)) := by
  apply CanonicalFactorization.DependsOnUnselected.of_compl_selected
    model.latent.count model.latent.Value
    (model.latentMoralLeftSide G mutilation left right conditioned)
  apply CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots => Kernel.agreesOn observed reference
      (model.evalUnder intervention roots))
  · intro root relevantRoot
    have onRightRoot :=
      model.latentMoralLeftSide_eq_false_of_relevant G projected
        mutilation left right conditioned relevant intervention free ancestral
        openNodes onRight root relevantRoot
    simp [onRightRoot]
  · exact agreesOn_evalUnder_dependsOnSelected model intervention
      relevant observed reference closed contained

/-- If two backward-closed regions share no latent root, a cylinder over the
right region depends only on coordinates unselected by the left region. -/
theorem agreesOn_evalUnder_dependsOnUnselected
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (leftRelevant rightRelevant observed : NodeSet S)
    (reference : S.Assignment)
    (rightClosed : model.BackwardClosedUnder intervention rightRelevant)
    (contained : NodeSet.Subset observed rightRelevant)
    (separated : model.LatentSeparatedUnder intervention
      leftRelevant rightRelevant) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
        (model.latentRelevantUnder intervention leftRelevant)
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder intervention roots)) := by
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model intervention
    rightRelevant observed reference rightClosed contained
  intro root rightRelevantRoot
  apply rootsAgree root
  cases leftRelevantRoot :
      model.latentRelevantUnder intervention leftRelevant root with
  | false => rfl
  | true =>
      have impossible := separated root leftRelevantRoot
      rw [rightRelevantRoot] at impossible
      contradiction

/-- A cylinder under one intervention ignores the selected mask of
another intervention when those two relevance families are disjoint. -/
theorem agreesOn_evalUnder_dependsOnUnselected_across
    (model : FiniteLatentSCM S)
    (selectedInt evalInt : (i : Fin S.count) -> Option (S.Value i))
    (selectedNodes evalNodes observed : NodeSet S)
    (reference : S.Assignment)
    (evalClosed : model.BackwardClosedUnder evalInt evalNodes)
    (contained : NodeSet.Subset observed evalNodes)
    (separated : model.LatentSeparatedAcross selectedInt selectedNodes
      evalInt evalNodes) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
        (model.latentRelevantUnder selectedInt selectedNodes)
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder evalInt roots)) := by
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model evalInt
    evalNodes observed reference evalClosed contained
  intro root evalRelevant
  apply rootsAgree root
  cases hsel : model.latentRelevantUnder selectedInt selectedNodes root with
  | false =>
      rfl
  | true =>
      have hfalse := separated root hsel
      rw [evalRelevant] at hfalse
      cases hfalse

/--
A cylinder depends only on unselected coordinates whenever every latent root
relevant to its backward-closed evaluation region is explicitly outside the
selected mask.

Unlike `agreesOn_evalUnder_dependsOnUnselected_across`, the selected mask may
combine relevance families from several interventions.  This is needed by
rule 3, whose common selected factor contains both the `Y` ancestors under
`do(X ∪ W)` and the invariant-`W` ancestors under `do(X ∪ Z)`.
-/
theorem agreesOn_evalUnder_dependsOnUnselected_of_relevance_avoids
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (relevant observed : NodeSet S) (reference : S.Assignment)
    (closed : model.BackwardClosedUnder intervention relevant)
    (contained : NodeSet.Subset observed relevant)
    (avoids : forall root,
      model.latentRelevantUnder intervention relevant root = true ->
        selected root = false) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value selected
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder intervention roots)) := by
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model intervention
    relevant observed reference closed contained
  intro root relevantRoot
  exact rootsAgree root (avoids root relevantRoot)

/-- Adding hard interventions at nodes that already have their requested
values under a base intervention does not change the evaluated assignment. -/
theorem evalUnder_union_intervention_eq_of_agreesOn
    (model : FiniteLatentSCM S) (baseAction addedAction : NodeSet S)
    (reference : S.Assignment) (roots : model.latent.Assignment)
    (agreement : Kernel.agreesOn addedAction reference
      (model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) roots) = true) :
    model.evalUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
          NodeSet.empty).intervention reference) roots =
      model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) roots := by
  let base := (Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
    reference
  let extension :=
    (Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
      NodeSet.empty).intervention reference
  have addedAgrees : forall node, addedAction node = true ->
      model.evalUnder base roots node = reference node := by
    intro node selected
    have components := (finAll_eq_true_iff _).mp agreement node
    simpa [Kernel.agreesOn, base, selected] using components
  apply model.evalUnder_composition base extension roots
  · intro node extensionNone
    cases baseSelected : baseAction node with
    | false => simp [base, Kernel.intervention, baseSelected]
    | true =>
        simp [extension, Kernel.intervention, NodeSet.union,
          baseSelected] at extensionNone
  · intro node value extensionValue
    cases baseSelected : baseAction node with
    | true =>
        have referenceEq : reference node = value := by
          simpa [extension, Kernel.intervention, NodeSet.union,
            baseSelected] using extensionValue
        subst value
        apply model.evalUnder_effectiveness
        simp [base, Kernel.intervention, baseSelected]
    | false =>
        cases addedSelected : addedAction node with
        | false =>
            simp [extension, Kernel.intervention, NodeSet.union,
              baseSelected, addedSelected] at extensionValue
        | true =>
            have referenceEq : reference node = value := by
              simpa [extension, Kernel.intervention, NodeSet.union,
                baseSelected, addedSelected] using extensionValue
            subst value
            exact addedAgrees node addedSelected

/-!
### Topological local factors for a conditioning cylinder

Agreement on a family of conditioned variables is not, in general, a
rectangle in the latent roots of its full ancestral evaluation: an earlier
conditioned node can transmit a root into every later descendant even though
conditioning blocks that transmission in the factor graph.  The correct
finite factorization fixes earlier conditioned coordinates before evaluating
each local equation.  Topological ordering of `ObservedSignature.directed`
makes this construction constructive.
-/

/-- Conditioned vertices strictly earlier than `child` in the signature's
fixed topological order. -/
def conditioningPrefix (condition : NodeSet S) (child : Fin S.count) :
    NodeSet S :=
  fun node => condition node && decide (node.val < child.val)

/-- The action used to read one local conditioning factor. -/
def localConditionAction (baseAction condition : NodeSet S)
    (child : Fin S.count) : NodeSet S :=
  NodeSet.union baseAction (conditioningPrefix condition child)

/-- The local equality constraint at one conditioned node, after every
earlier conditioned coordinate has been fixed to its reference value. -/
def localConditionFactor (model : FiniteLatentSCM S)
    (baseAction condition : NodeSet S) (reference : S.Assignment)
    (child : Fin S.count) (roots : model.latent.Assignment) : Bool :=
  decide
    (model.evalUnder
      ((Kernel.mk NodeSet.empty
        (localConditionAction baseAction condition child)
        NodeSet.empty).intervention reference) roots child = reference child)

/-- Conjunction of the local constraints indexed by `selected`; the full
conditioning family remains visible to every factor through its topological
prefix. -/
def localConditionEvent (model : FiniteLatentSCM S)
    (baseAction condition selected : NodeSet S) (reference : S.Assignment)
    (roots : model.latent.Assignment) : Bool :=
  finAll S.count (fun child =>
    if selected child then
      localConditionFactor model baseAction condition reference child roots
    else true)

/-- Agreement on the complete conditioning cylinder is exactly the
conjunction of its topological local factors. -/
theorem agreesOn_evalUnder_eq_localConditionEvent
    (model : FiniteLatentSCM S) (baseAction condition : NodeSet S)
    (reference : S.Assignment) (roots : model.latent.Assignment) :
    Kernel.agreesOn condition reference
        (model.evalUnder
          ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
            reference) roots) =
      localConditionEvent model baseAction condition condition reference
        roots := by
  let base :=
    (Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention reference
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro agreement
    have components := (finAll_eq_true_iff _).mp (by
      simpa [Kernel.agreesOn, base] using agreement)
    apply (finAll_eq_true_iff _).mpr
    intro child
    cases selected : condition child with
    | false =>
        simp
    | true =>
        have earlierAgreement : Kernel.agreesOn
            (conditioningPrefix condition child) reference
            (model.evalUnder base roots) = true := by
          unfold Kernel.agreesOn
          apply (finAll_eq_true_iff _).mpr
          intro node
          cases earlier : conditioningPrefix condition child node with
          | false => simp
          | true =>
              have earlierParts : condition node = true ∧
                  node.val < child.val := by
                simpa [conditioningPrefix] using earlier
              have nodeSelected : condition node = true := earlierParts.1
              have nodeComponent := components node
              simpa [earlier, nodeSelected] using nodeComponent
        have evaluationsEqual :
            model.evalUnder
                ((Kernel.mk NodeSet.empty
                  (localConditionAction baseAction condition child)
                  NodeSet.empty).intervention reference) roots =
              model.evalUnder base roots := by
          simpa [localConditionAction, base] using
            (evalUnder_union_intervention_eq_of_agreesOn model baseAction
              (conditioningPrefix condition child) reference roots
              earlierAgreement)
        have childValue : model.evalUnder base roots child = reference child := by
          have childComponent := components child
          simpa [selected] using childComponent
        have localValue :
            model.evalUnder
              ((Kernel.mk NodeSet.empty
                (localConditionAction baseAction condition child)
                NodeSet.empty).intervention reference) roots child =
              reference child := by
          rw [evaluationsEqual]
          exact childValue
        simp [localConditionFactor, localValue]
  · intro localAgreement
    have localComponents := (finAll_eq_true_iff _).mp (by
      simpa [localConditionEvent] using localAgreement)
    have selectedAgreesByValue : forall value,
        forall child : Fin S.count, child.val = value ->
          condition child = true ->
            model.evalUnder base roots child = reference child := by
      intro value
      induction value using Nat.strongRecOn with
      | ind value ih =>
          intro child childValue selected
          have earlierAgreement : Kernel.agreesOn
              (conditioningPrefix condition child) reference
              (model.evalUnder base roots) = true := by
            unfold Kernel.agreesOn
            apply (finAll_eq_true_iff _).mpr
            intro node
            cases earlier : conditioningPrefix condition child node with
            | false => simp
            | true =>
                have parts : condition node = true ∧
                    node.val < child.val := by
                  simpa [conditioningPrefix] using earlier
                have nodeEarlier : node.val < value := by
                  simpa [childValue] using parts.2
                have nodeValue := ih node.val nodeEarlier node rfl parts.1
                simp [nodeValue]
          have evaluationsEqual :
              model.evalUnder
                  ((Kernel.mk NodeSet.empty
                    (localConditionAction baseAction condition child)
                    NodeSet.empty).intervention reference) roots =
                model.evalUnder base roots := by
            simpa [localConditionAction, base] using
              (evalUnder_union_intervention_eq_of_agreesOn model baseAction
                (conditioningPrefix condition child) reference roots
                earlierAgreement)
          have localComponent := localComponents child
          have localValue :
              model.evalUnder
                ((Kernel.mk NodeSet.empty
                  (localConditionAction baseAction condition child)
                  NodeSet.empty).intervention reference) roots child =
                reference child := by
            have decided : decide
                (model.evalUnder
                  ((Kernel.mk NodeSet.empty
                    (localConditionAction baseAction condition child)
                    NodeSet.empty).intervention reference) roots child =
                  reference child) = true := by
              simpa [selected, localConditionFactor] using localComponent
            exact of_decide_eq_true decided
          rw [evaluationsEqual] at localValue
          exact localValue
    unfold Kernel.agreesOn
    apply (finAll_eq_true_iff _).mpr
    intro child
    cases selected : condition child with
    | false => simp
    | true =>
        have value := selectedAgreesByValue child.val child rfl selected
        simpa [base, selected] using value

/-- Selecting a union of local factors is pointwise conjunction of the two
selected subfamilies. -/
theorem localConditionEvent_union
    (model : FiniteLatentSCM S)
    (baseAction condition left right : NodeSet S)
    (reference : S.Assignment) (roots : model.latent.Assignment) :
    localConditionEvent model baseAction condition
        (NodeSet.union left right) reference roots =
      (localConditionEvent model baseAction condition left reference roots &&
        localConditionEvent model baseAction condition right reference
          roots) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro unionTrue
    have components := (finAll_eq_true_iff _).mp (by
      simpa [localConditionEvent] using unionTrue)
    apply Bool.and_eq_true_iff.mpr
    constructor <;> apply (finAll_eq_true_iff _).mpr <;> intro child
    · cases selected : left child with
      | false => simp
      | true =>
          have unionSelected : NodeSet.union left right child = true := by
            simp [NodeSet.union, selected]
          simpa [selected, unionSelected] using components child
    · cases selected : right child with
      | false => simp
      | true =>
          have unionSelected : NodeSet.union left right child = true := by
            simp [NodeSet.union, selected]
          simpa [selected, unionSelected] using components child
  · intro parts
    rcases Bool.and_eq_true_iff.mp parts with ⟨leftTrue, rightTrue⟩
    have leftComponents := (finAll_eq_true_iff _).mp (by
      simpa [localConditionEvent] using leftTrue)
    have rightComponents := (finAll_eq_true_iff _).mp (by
      simpa [localConditionEvent] using rightTrue)
    apply (finAll_eq_true_iff _).mpr
    intro child
    cases leftSelected : left child <;> cases rightSelected : right child
    · simp [NodeSet.union, leftSelected, rightSelected]
    · simpa [NodeSet.union, leftSelected, rightSelected] using
        rightComponents child
    · simpa [NodeSet.union, leftSelected, rightSelected] using
        leftComponents child
    · simpa [NodeSet.union, leftSelected, rightSelected] using
        leftComponents child

/-!
### Local-factor walks in the rule-3 side graph

The factor graph below records latent roots rather than observed paths.  To
connect its finite reachability relation back to path d-separation, each root
relevance witness must first be represented inside the graph used by rule 3.
The lemmas in this section isolate that translation.  Topological order is
load-bearing: every proper predecessor on a directed walk into `child` is
strictly earlier than `child`, so a conditioned predecessor belongs to the
fixed prefix and cannot occur on the walk.
-/

/-- Directed walks are nondecreasing in the signature's fixed topological
order.  This weak form includes the reflexive walk and is convenient when a
vertex is selected from an arbitrary suffix. -/
theorem observedDirectedWalk_source_le_target
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target) :
    source.val <= target.val := by
  induction walk with
  | refl => exact Nat.le_refl _
  | @step length source middle target first rest ih =>
      have directed : S.directed source middle = true := by
        exact (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp first).1).1
      exact Nat.le_trans (Nat.le_of_lt (S.directed_earlier directed)) ih

/-- Every displayed vertex of a directed walk occurs no later than its
target in topological order. -/
theorem observedDirectedWalk_node_le_target_of_mem
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    {length : Nat} {source target node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (member : node ∈ walk.nodes) :
    node.val <= target.val := by
  rcases walk.suffix_of_mem member with
    ⟨_suffixLength, _bound, suffix⟩
  rcases suffix with ⟨suffix⟩
  exact observedDirectedWalk_source_le_target G mutilation suffix

/-- Every proper vertex of a directed walk precedes its target in
topological order. -/
theorem observedDirectedWalk_node_lt_target_of_mem_ne
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    {length : Nat} {source target node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (member : node ∈ walk.nodes) (different : node ≠ target) :
    node.val < target.val := by
  rcases walk.suffix_of_mem member with
    ⟨_suffixLength, _bound, suffix⟩
  rcases suffix with ⟨suffix⟩
  have ordered := observedDirectedWalk_source_le_target G mutilation suffix
  exact Nat.lt_of_le_of_ne ordered (fun equal =>
    different (Fin.ext equal))

/-- Split the last edge from a non-reflexive exact walk while retaining the
fact that the prefix's vertices occurred in the original walk.  The result is
Prop-valued, so this is constructive witness elimination rather than a choice
operator. -/
theorem exists_observedDirectedWalk_prefix_last
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (different : source ≠ target) :
    Exists fun prefixLength : Nat =>
      Exists fun parent : Fin S.count =>
        Exists fun prefixWalk : FiniteReachability.ExactWalk
          (G.observedDirectedEdge mutilation) prefixLength source parent =>
          G.observedDirectedEdge mutilation parent target = true /\
            forall node, node ∈ prefixWalk.nodes -> node ∈ walk.nodes := by
  induction walk with
  | refl node => exact (different rfl).elim
  | @step length source middle target first rest ih =>
      by_cases middleIsTarget : middle = target
      · subst target
        refine ⟨0, source,
          FiniteReachability.ExactWalk.refl source, first, ?_⟩
        intro node member
        have nodeEq : node = source := by
          simpa [FiniteReachability.ExactWalk.nodes] using member
        subst node
        simp [FiniteReachability.ExactWalk.nodes]
      · rcases ih middleIsTarget with
          ⟨prefixLength, parent, prefixWalk, last, subset⟩
        let extended : FiniteReachability.ExactWalk
            (G.observedDirectedEdge mutilation) (prefixLength + 1)
            source parent :=
          .step first prefixWalk
        refine ⟨prefixLength + 1, parent, extended, last, ?_⟩
        intro node member
        have parts : node = source ∨ node ∈ prefixWalk.nodes := by
          simpa [extended, FiniteReachability.ExactWalk.nodes] using member
        rcases parts with same | later
        · subst node
          simp [FiniteReachability.ExactWalk.nodes]
        · simp [FiniteReachability.ExactWalk.nodes, subset node later]

/-- Select the last vertex satisfying a Boolean predicate along a simple
exact walk and return the suffix beginning there.  Recursion follows the walk
itself: if the tail contains a selected vertex, recurse into it; otherwise
the current source is the last selected vertex. -/
theorem exists_last_selected_observedDirectedWalk_suffix
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (selected : Fin S.count -> Bool)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (simple : walk.nodes.Nodup)
    (someSelected : walk.nodes.any selected = true) :
    Exists fun pivot : Fin S.count =>
      Exists fun suffixLength : Nat =>
        Exists fun suffixWalk : FiniteReachability.ExactWalk
          (G.observedDirectedEdge mutilation) suffixLength pivot target =>
          selected pivot = true /\
            suffixWalk.nodes.Nodup /\
              (forall node, node ∈ suffixWalk.nodes -> node ≠ pivot ->
                selected node = false) /\
                forall node, node ∈ suffixWalk.nodes -> node ∈ walk.nodes := by
  induction walk with
  | refl node =>
      have nodeSelected : selected node = true := by
        simpa [FiniteReachability.ExactWalk.nodes] using someSelected
      refine ⟨node, 0, FiniteReachability.ExactWalk.refl node,
        nodeSelected, by simp [FiniteReachability.ExactWalk.nodes], ?_, ?_⟩
      · intro other member different
        have same : other = node := by
          simpa [FiniteReachability.ExactWalk.nodes] using member
        exact (different same).elim
      · intro other member
        simpa [FiniteReachability.ExactWalk.nodes] using member
  | @step length source middle target first rest ih =>
      have simpleParts : source ∉ rest.nodes ∧ rest.nodes.Nodup := by
        simpa [FiniteReachability.ExactWalk.nodes] using
          (List.nodup_cons.mp (by
            simpa [FiniteReachability.ExactWalk.nodes] using simple))
      cases tailSelected : rest.nodes.any selected with
      | true =>
          rcases ih simpleParts.2 tailSelected with
            ⟨pivot, suffixLength, suffixWalk, pivotSelected,
              suffixSimple, suffixLast, suffixSubset⟩
          refine ⟨pivot, suffixLength, suffixWalk, pivotSelected,
            suffixSimple, suffixLast, ?_⟩
          intro node member
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr (suffixSubset node member)
      | false =>
          have sourceSelected : selected source = true := by
            simpa [FiniteReachability.ExactWalk.nodes, tailSelected] using
              someSelected
          have tailUnselected : forall node, node ∈ rest.nodes ->
              selected node = false := by
            intro node member
            have notTrue := (List.any_eq_false.mp tailSelected) node member
            cases value : selected node with
            | false => rfl
            | true => exact (notTrue value).elim
          refine ⟨source, length + 1,
            FiniteReachability.ExactWalk.step first rest, sourceSelected,
            simple, ?_, ?_⟩
          · intro node member different
            have inTail : node ∈ rest.nodes := by
              have parts : node = source ∨ node ∈ rest.nodes := by
                simpa [FiniteReachability.ExactWalk.nodes] using member
              rcases parts with same | later
              · exact (different same).elim
              · exact later
            exact tailUnselected node inTail
          · intro node member
            exact member

/-- Moral-side membership is constant along an open directed walk contained
in the ancestral graph.  Each directed edge is an open moral edge; closure in
both directions yields Boolean equality without deciding any proposition. -/
theorem moralLeftSide_eq_of_open_observed_walk
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (openNodes : forall node, node ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed node) = false)
    (ancestorNodes : forall node, node ∈ walk.nodes ->
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        (.observed node) = true) :
    G.moralLeftSide mutilation left right conditioned (.observed source) =
      G.moralLeftSide mutilation left right conditioned
        (.observed target) := by
  induction walk with
  | refl => rfl
  | @step length source middle target first rest ih =>
      have middleInFull : middle ∈
          (FiniteReachability.ExactWalk.step first rest).nodes := by
        simp [FiniteReachability.ExactWalk.nodes]
        exact Or.inr rest.mem_source
      have sourceAncestor := ancestorNodes source (by
        simp [FiniteReachability.ExactWalk.nodes])
      have middleAncestor := ancestorNodes middle middleInFull
      have sourceOpen := openNodes source (by
        simp [FiniteReachability.ExactWalk.nodes])
      have middleOpen := openNodes middle middleInFull
      have expanded : G.expandedMutilatedEdge mutilation
          (.observed source) (.observed middle) = true := first
      have moral := G.moralOpenEdge_of_directed mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) conditioned
        expanded sourceAncestor middleAncestor sourceOpen middleOpen
      have firstSides :
          G.moralLeftSide mutilation left right conditioned
              (.observed source) =
            G.moralLeftSide mutilation left right conditioned
              (.observed middle) := by
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro sourceIn
          exact G.moralLeftSide_closed mutilation left right conditioned
            sourceIn moral
        · intro middleIn
          exact G.moralLeftSide_closed mutilation left right conditioned
            middleIn
            (G.moralOpenEdge_symmetric mutilation
              (NodeSet.union left (NodeSet.union right conditioned))
              conditioned moral)
      have restOpen : forall node, node ∈ rest.nodes ->
          ObservedGraph.blockedBy conditioned (.observed node) = false := by
        intro node member
        exact openNodes node (by
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr member)
      have restAncestor : forall node, node ∈ rest.nodes ->
          G.ancestorOf mutilation
            (NodeSet.union left (NodeSet.union right conditioned))
            (.observed node) = true := by
        intro node member
        exact ancestorNodes node (by
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr member)
      exact firstSides.trans (ih restOpen restAncestor)

/-- Two directed routes into one conditioned vertex have sources on the
same moral side.  Their open prefixes reach the final parents; moralization
then marries those parents at the conditioned collider.  This is the precise
graph operation represented by one local conditioning factor. -/
theorem moralLeftSide_eq_of_open_observed_walks_to_conditioned
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    {leftLength rightLength : Nat}
    {leftSource rightSource child : Fin S.count}
    (leftWalk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) leftLength leftSource child)
    (rightWalk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) rightLength rightSource child)
    (leftDifferent : leftSource ≠ child)
    (rightDifferent : rightSource ≠ child)
    (childConditioned : conditioned child = true)
    (leftProperOpen : forall node, node ∈ leftWalk.nodes -> node ≠ child ->
      ObservedGraph.blockedBy conditioned (.observed node) = false)
    (rightProperOpen : forall node, node ∈ rightWalk.nodes ->
      node ≠ child ->
      ObservedGraph.blockedBy conditioned (.observed node) = false) :
    G.moralLeftSide mutilation left right conditioned
        (.observed leftSource) =
      G.moralLeftSide mutilation left right conditioned
        (.observed rightSource) := by
  rcases exists_observedDirectedWalk_prefix_last G mutilation leftWalk
      leftDifferent with
    ⟨leftPrefixLength, leftParent, leftPrefix, leftLast, leftSubset⟩
  rcases exists_observedDirectedWalk_prefix_last G mutilation rightWalk
      rightDifferent with
    ⟨rightPrefixLength, rightParent, rightPrefix, rightLast,
      rightSubset⟩
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childConditioned]
  have leftLastDirected : S.directed leftParent child = true :=
    (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp leftLast).1).1
  have rightLastDirected : S.directed rightParent child = true :=
    (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp rightLast).1).1
  have leftParentEarlier : leftParent.val < child.val :=
    S.directed_earlier leftLastDirected
  have rightParentEarlier : rightParent.val < child.val :=
    S.directed_earlier rightLastDirected
  have leftPrefixNotChild : forall node, node ∈ leftPrefix.nodes ->
      node ≠ child := by
    intro node member equal
    have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
      leftPrefix member
    subst node
    exact (Nat.not_lt_of_ge nodeLe leftParentEarlier).elim
  have rightPrefixNotChild : forall node, node ∈ rightPrefix.nodes ->
      node ≠ child := by
    intro node member equal
    have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
      rightPrefix member
    subst node
    exact (Nat.not_lt_of_ge nodeLe rightParentEarlier).elim
  have leftPrefixOpen : forall node, node ∈ leftPrefix.nodes ->
      ObservedGraph.blockedBy conditioned (.observed node) = false := by
    intro node member
    exact leftProperOpen node (leftSubset node member)
      (leftPrefixNotChild node member)
  have rightPrefixOpen : forall node, node ∈ rightPrefix.nodes ->
      ObservedGraph.blockedBy conditioned (.observed node) = false := by
    intro node member
    exact rightProperOpen node (rightSubset node member)
      (rightPrefixNotChild node member)
  have leftPrefixAncestor : forall node, node ∈ leftPrefix.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      leftWalk childTarget (leftSubset node member)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have rightPrefixAncestor : forall node, node ∈ rightPrefix.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      rightWalk childTarget (rightSubset node member)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have leftSourceToParent := moralLeftSide_eq_of_open_observed_walk G
    mutilation left right conditioned leftPrefix leftPrefixOpen (by
      simpa [targets] using leftPrefixAncestor)
  have rightSourceToParent := moralLeftSide_eq_of_open_observed_walk G
    mutilation left right conditioned rightPrefix rightPrefixOpen (by
      simpa [targets] using rightPrefixAncestor)
  have leftParentAncestor : G.ancestorOf mutilation targets
      (.observed leftParent) = true :=
    leftPrefixAncestor leftParent leftPrefix.mem_target
  have rightParentAncestor : G.ancestorOf mutilation targets
      (.observed rightParent) = true :=
    rightPrefixAncestor rightParent rightPrefix.mem_target
  have childAncestor : G.ancestorOf mutilation targets
      (.observed child) = true :=
    G.ancestorOf_target mutilation targets childTarget
  have leftParentOpen := leftPrefixOpen leftParent leftPrefix.mem_target
  have rightParentOpen := rightPrefixOpen rightParent rightPrefix.mem_target
  have parentSides :
      G.moralLeftSide mutilation left right conditioned
          (.observed leftParent) =
        G.moralLeftSide mutilation left right conditioned
          (.observed rightParent) := by
    by_cases sameParent : leftParent = rightParent
    · subst rightParent
      rfl
    · have leftExpanded : G.expandedMutilatedEdge mutilation
          (.observed leftParent) (.observed child) = true := leftLast
      have rightExpanded : G.expandedMutilatedEdge mutilation
          (.observed rightParent) (.observed child) = true := rightLast
      have observedDifferent :
          (SeparationNode.observed leftParent : SeparationNode S) ≠
            .observed rightParent := by
        intro equal
        cases equal
        exact sameParent rfl
      have collider : PathSpecification.IsCollider G mutilation
          (.observed leftParent) (.observed child)
          (.observed rightParent) := ⟨leftExpanded, rightExpanded⟩
      have ancestralMoral := G.ancestralMoralEdge_of_collider mutilation
        targets leftParentAncestor childAncestor rightParentAncestor
        observedDifferent collider
      have moral := G.moralOpenEdge_of_ancestral mutilation targets
        conditioned leftParentOpen rightParentOpen ancestralMoral
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro leftIn
        exact G.moralLeftSide_closed mutilation left right conditioned
          leftIn moral
      · intro rightIn
        exact G.moralLeftSide_closed mutilation left right conditioned
          rightIn
          (G.moralOpenEdge_symmetric mutilation targets conditioned moral)
  exact leftSourceToParent.trans
    (parentSides.trans rightSourceToParent.symm)

/-- Moral-side membership agrees across one open edge of the ancestral moral
graph.  This small closure lemma is useful when a later argument assembles a
mixed path containing both projected latent edges and moralized collider
edges, rather than a purely observed directed walk. -/
theorem moralLeftSide_eq_of_moralOpenEdge
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    {first second : SeparationNode S}
    (edge : G.MoralOpenEdge mutilation
      (NodeSet.union left (NodeSet.union right conditioned)) conditioned
      first second = true) :
    G.moralLeftSide mutilation left right conditioned first =
      G.moralLeftSide mutilation left right conditioned second := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro firstIn
    exact G.moralLeftSide_closed mutilation left right conditioned
      firstIn edge
  · intro secondIn
    exact G.moralLeftSide_closed mutilation left right conditioned
      secondIn
      (G.moralOpenEdge_symmetric mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned edge)

/-- A free representative of a concrete latent root and an open observed
route into another child of that root's conditioned collider have the same
canonical moral side.

The route is split at its last directed edge.  Projection supplies the
canonical latent-pair vertex between the representative and the conditioned
child.  Moralization then joins that latent-pair parent to the route's final
observed parent at the conditioned collider.  Thus the open moral chain is

`representative — latent pair — final route parent — route source`.

This is the direct-incidence counterpart of
`moralLeftSide_eq_of_open_observed_walks_to_conditioned`: one of the two
routes may have length zero at the conditioned child, but its concrete latent
root still supplies a genuine parent in the expanded projected graph. -/
theorem moralLeftSide_eq_of_shared_latent_and_open_walk_to_conditioned
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (root : Fin model.latent.count)
    (representative child routeSource : Fin S.count)
    (representativeIncident :
      model.latent.incident root representative = true)
    (childIncident : model.latent.incident root child = true)
    (representativeFree : mutilation.removeIncoming representative = false)
    (representativeAncestor : G.ancestorOf mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      (.observed representative) = true)
    (representativeOpen :
      ObservedGraph.blockedBy conditioned (.observed representative) = false)
    {length : Nat}
    (route : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length routeSource child)
    (routeSourceDifferent : routeSource ≠ child)
    (childConditioned : conditioned child = true)
    (routeProperOpen : forall node, node ∈ route.nodes -> node ≠ child ->
      ObservedGraph.blockedBy conditioned (.observed node) = false) :
    G.moralLeftSide mutilation left right conditioned
        (.observed representative) =
      G.moralLeftSide mutilation left right conditioned
        (.observed routeSource) := by
  have representativeDifferent : representative ≠ child := by
    intro same
    subst representative
    have childOpen : conditioned child = false := by
      simpa [ObservedGraph.blockedBy] using representativeOpen
    rw [childConditioned] at childOpen
    contradiction
  have bidirected := model.bidirected_of_shared_latent G projected root
    representativeDifferent representativeIncident childIncident
  rcases exists_observedDirectedWalk_prefix_last G mutilation route
      routeSourceDifferent with
    ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let latent : SeparationNode S := .latentPair representative child
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childConditioned]
  have childFree : mutilation.removeIncoming child = false := by
    have incoming := (Bool.and_eq_true_iff.mp last).2
    simpa using incoming
  have edgeRepresentative : G.expandedMutilatedEdge mutilation latent
      (.observed representative) = true := by
    have self : finBeq representative representative = true :=
      (finBeq_eq_true_iff representative representative).mpr rfl
    simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
      representativeFree, self]
  have edgeChild : G.expandedMutilatedEdge mutilation latent
      (.observed child) = true := by
    have self : finBeq child child = true :=
      (finBeq_eq_true_iff child child).mpr rfl
    simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
      childFree, self]
  have latentAncestor : G.ancestorOf mutilation targets latent = true :=
    G.ancestorOf_prepend mutilation targets edgeRepresentative
      representativeAncestor
  have childAncestor : G.ancestorOf mutilation targets (.observed child) =
      true :=
    G.ancestorOf_target mutilation targets childTarget
  have parentAncestor : G.ancestorOf mutilation targets (.observed parent) =
      true := by
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      route childTarget (prefixSubset parent prefixWalk.mem_target)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets parent observed
  have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
      node ≠ child := by
    intro node member equal
    have parentDirected : S.directed parent child = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
    have parentEarlier := S.directed_earlier parentDirected
    have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
      prefixWalk member
    subst node
    exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
  have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed node) = false := by
    intro node member
    exact routeProperOpen node (prefixSubset node member)
      (prefixNotChild node member)
  have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      route childTarget (prefixSubset node member)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have representativeLatentMoral : G.MoralOpenEdge mutilation targets
      conditioned (.observed representative) latent = true :=
    G.moralOpenEdge_of_ancestral mutilation targets conditioned
      representativeOpen (by dsimp [latent]; rfl)
      (G.ancestralMoralEdge_of_adjacent mutilation targets
        representativeAncestor latentAncestor (Or.inr edgeRepresentative))
  have latentParentDifferent : latent ≠ (.observed parent : SeparationNode S) := by
    simp [latent]
  have collider : PathSpecification.IsCollider G mutilation latent
      (.observed child) (.observed parent) := ⟨edgeChild, last⟩
  have latentParentMoral : G.MoralOpenEdge mutilation targets conditioned
      latent (.observed parent) = true :=
    G.moralOpenEdge_of_ancestral mutilation targets conditioned
      (by dsimp [latent]; rfl)
      (prefixOpen parent prefixWalk.mem_target)
      (G.ancestralMoralEdge_of_collider mutilation targets latentAncestor
        childAncestor parentAncestor latentParentDifferent collider)
  have representativeToLatent := moralLeftSide_eq_of_moralOpenEdge G
    mutilation left right conditioned representativeLatentMoral
  have latentToParent := moralLeftSide_eq_of_moralOpenEdge G mutilation
    left right conditioned latentParentMoral
  have routeSourceToParent := moralLeftSide_eq_of_open_observed_walk G
    mutilation left right conditioned prefixWalk prefixOpen (by
      simpa [targets] using prefixAncestor)
  exact representativeToLatent.trans
    (latentToParent.trans routeSourceToParent.symm)

/-- An internal vertex of a local-factor ancestry walk is open after
conditioning on `conditionedBase ∪ condition`.  Membership after the source
keeps it outside the incoming cut; topological order then rules out membership
in the conditioning family itself. -/
theorem localConditionWalk_internal_open
    (G : ObservedGraph S)
    (baseAction conditionedBase condition : NodeSet S)
    (baseSubset : NodeSet.Subset conditionedBase baseAction)
    (child : Fin S.count)
    {length : Nat} {source node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar
          (localConditionAction baseAction condition child)))
      length source child)
    (member : node ∈ walk.nodes) (notSource : node ≠ source)
    (notTarget : node ≠ child) :
    ObservedGraph.blockedBy (NodeSet.union conditionedBase condition)
      (.observed node) = false := by
  have outsideAction :
      localConditionAction baseAction condition child node = false := by
    have incoming :=
      PathSpecification.directed_walk_mem_not_removeIncoming G
        (GraphMutilation.bar
          (localConditionAction baseAction condition child))
        walk member notSource
    simpa [GraphMutilation.bar] using incoming
  have outsideBase : conditionedBase node = false := by
    cases selected : conditionedBase node with
    | false => rfl
    | true =>
        have inBase : baseAction node = true := baseSubset node selected
        have inAction :
            localConditionAction baseAction condition child node = true := by
          simp [localConditionAction, NodeSet.union, inBase]
        rw [inAction] at outsideAction
        contradiction
  have outsideCondition : condition node = false := by
    cases selected : condition node with
    | false => rfl
    | true =>
        have earlier := observedDirectedWalk_node_lt_target_of_mem_ne
          G
          (GraphMutilation.bar
            (localConditionAction baseAction condition child))
          walk member notTarget
        have inPrefix : conditioningPrefix condition child node = true := by
          simp [conditioningPrefix, selected, earlier]
        have inAction :
            localConditionAction baseAction condition child node = true := by
          simp [localConditionAction, NodeSet.union, inPrefix]
        rw [inAction] at outsideAction
        contradiction
  simp [ObservedGraph.blockedBy, NodeSet.union, outsideBase,
    outsideCondition]

/-- A root-incidence source that is free under the local intervention is
also open in the rule-3 conditioning set.  Unlike an internal walk vertex,
the source has no incoming edge from which freeness could be recovered, so
the relevance witness supplies it explicitly. -/
theorem localConditionWalk_source_open_of_free
    (G : ObservedGraph S)
    (baseAction conditionedBase condition : NodeSet S)
    (baseSubset : NodeSet.Subset conditionedBase baseAction)
    (reference : S.Assignment) (child : Fin S.count)
    {length : Nat} {source : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar
          (localConditionAction baseAction condition child)))
      length source child)
    (different : source ≠ child)
    (free :
      ((Kernel.mk NodeSet.empty
        (localConditionAction baseAction condition child)
        NodeSet.empty).intervention reference) source = none) :
    ObservedGraph.blockedBy (NodeSet.union conditionedBase condition)
      (.observed source) = false := by
  have outsideAction :
      localConditionAction baseAction condition child source = false := by
    simpa [Kernel.intervention] using free
  have sourceMember : source ∈ walk.nodes := walk.mem_source
  have earlier := observedDirectedWalk_node_lt_target_of_mem_ne G
    (GraphMutilation.bar
      (localConditionAction baseAction condition child))
    walk sourceMember different
  have outsideBase : conditionedBase source = false := by
    cases selected : conditionedBase source with
    | false => rfl
    | true =>
        have inBase := baseSubset source selected
        have inAction :
            localConditionAction baseAction condition child source = true := by
          simp [localConditionAction, NodeSet.union, inBase]
        rw [inAction] at outsideAction
        contradiction
  have outsideCondition : condition source = false := by
    cases selected : condition source with
    | false => rfl
    | true =>
        have inPrefix : conditioningPrefix condition child source = true := by
          simp [conditioningPrefix, selected, earlier]
        have inAction :
            localConditionAction baseAction condition child source = true := by
          simp [localConditionAction, NodeSet.union, inPrefix]
        rw [inAction] at outsideAction
        contradiction
  simp [ObservedGraph.blockedBy, NodeSet.union, outsideBase,
    outsideCondition]

/-- A left local-factor walk uses a stricter incoming cut than the rule-3
side-condition graph, because the latter removes only `Z(W) ⊆ Z`. -/
def remapRule3LeftLocalConditionWalk
    (G : ObservedGraph S) (x z w : NodeSet S) (child : Fin S.count)
    {length : Nat} {source : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar
          (localConditionAction (NodeSet.union x z) w child)))
      length source child) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar
          (NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w))))
      length source child :=
  FiniteLatentSCM.remapBarWalk_of_incoming_subset G (by
    intro node selected
    rcases Bool.or_eq_true_iff.mp selected with inX | inRemovable
    · simp [localConditionAction, NodeSet.union, inX]
    · have inZ :=
        ObservedGraph.nonAncestorsOf_subset_actions G
          (GraphMutilation.bar x) z w node inRemovable
      simp [localConditionAction, NodeSet.union, inZ]) walk

@[simp] theorem remapRule3LeftLocalConditionWalk_nodes
    (G : ObservedGraph S) (x z w : NodeSet S) (child : Fin S.count)
    {length : Nat} {source : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar
          (localConditionAction (NodeSet.union x z) w child)))
      length source child) :
    (remapRule3LeftLocalConditionWalk G x z w child walk).nodes =
      walk.nodes :=
  FiniteLatentSCM.remapBarWalk_of_incoming_subset_nodes G _ walk

/-- A right local-factor walk also embeds into the rule-3 graph.  The only
extra cut there is at `Z(W)`.  Such a vertex cannot occur after the walk's
source: its remaining suffix reaches the selected `W` endpoint already in
`G_{̅X}`, contradicting the definition of `Z(W)`. -/
def remapRule3RightLocalConditionWalk
    (G : ObservedGraph S) (x z w : NodeSet S) (child : Fin S.count)
    (childInW : w child = true)
    {length : Nat} {source : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar (localConditionAction x w child)))
      length source child) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar
          (NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w))))
      length source child :=
  match walk with
  | .refl node => .refl node
  | @FiniteReachability.ExactWalk.step _ _ len src middle target first rest =>
      have firstParts :
          S.directed src middle = true ∧
            localConditionAction x w target middle = false := by
        have outer := Bool.and_eq_true_iff.mp first
        have inner := Bool.and_eq_true_iff.mp outer.1
        exact ⟨inner.1, by
          simpa [GraphMutilation.bar] using outer.2⟩
      have outsideRemovable :
          G.nonAncestorsOf (GraphMutilation.bar x) z w middle = false := by
        cases removable :
            G.nonAncestorsOf (GraphMutilation.bar x) z w middle with
        | false => rfl
        | true =>
            have xSubset : NodeSet.Subset x
                (localConditionAction x w target) := by
              intro node selected
              simp [localConditionAction, NodeSet.union, selected]
            have restInBarX :=
              FiniteLatentSCM.remapBarWalk_of_incoming_subset G xSubset rest
            have ancestor :
                G.observedAncestorOf (GraphMutilation.bar x) w middle =
                  true :=
              G.observedAncestorOf_of_mem_walk (GraphMutilation.bar x) w
                restInBarX childInW restInBarX.mem_source
            simp [ObservedGraph.nonAncestorsOf, ancestor] at removable
      have outsideX : x middle = false := by
        cases selected : x middle with
        | false => rfl
        | true =>
            have inAction : localConditionAction x w target middle = true := by
              simp [localConditionAction, NodeSet.union, selected]
            have impossible := firstParts.2
            rw [inAction] at impossible
            contradiction
      have mappedFirst : G.observedDirectedEdge
          (GraphMutilation.bar
            (NodeSet.union x
              (G.nonAncestorsOf (GraphMutilation.bar x) z w)))
          src middle = true := by
        unfold ObservedGraph.observedDirectedEdge
        exact Bool.and_eq_true_iff.mpr
          ⟨Bool.and_eq_true_iff.mpr ⟨firstParts.1, rfl⟩,
            by
              change Bool.not (NodeSet.union x
                (G.nonAncestorsOf (GraphMutilation.bar x) z w) middle) = true
              simp [NodeSet.union, outsideX, outsideRemovable]⟩
      .step mappedFirst
        (remapRule3RightLocalConditionWalk G x z w target childInW rest)

@[simp] theorem remapRule3RightLocalConditionWalk_nodes
    (G : ObservedGraph S) (x z w : NodeSet S) (child : Fin S.count)
    (childInW : w child = true)
    {length : Nat} {source : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar (localConditionAction x w child)))
      length source child) :
    (remapRule3RightLocalConditionWalk G x z w child childInW walk).nodes =
      walk.nodes := by
  cases walk with
  | refl => rfl
  | step first rest =>
      simp only [remapRule3RightLocalConditionWalk,
        FiniteReachability.ExactWalk.nodes]
      rw [remapRule3RightLocalConditionWalk_nodes G x z w child childInW
        rest]

/-- An edge of `G_{̅(X ∪ W)}` whose child is not in `Z` survives in the
rule-3 side graph.  The latter cuts `X ∪ Z(W)`; membership in `Z(W)` would
contradict the supplied Boolean nonmembership in `Z`. -/
theorem observedDirectedEdge_rule3_of_bar_union_of_child_not_z
    (G : ObservedGraph S) (x z w : NodeSet S)
    {parent child : Fin S.count}
    (edge : G.observedDirectedEdge
      (GraphMutilation.bar (NodeSet.union x w)) parent child = true)
    (childNotZ : z child = false) :
    G.observedDirectedEdge
      (GraphMutilation.bar
        (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w)))
      parent child = true := by
  have outer := Bool.and_eq_true_iff.mp edge
  have inner := Bool.and_eq_true_iff.mp outer.1
  have directed : S.directed parent child = true := inner.1
  have outsideUnion : NodeSet.union x w child = false := by
    simpa [GraphMutilation.bar] using outer.2
  have outsideX : x child = false :=
    (Bool.or_eq_false_iff.mp (by
      simpa [NodeSet.union] using outsideUnion)).1
  have outsideRemovable :
      G.nonAncestorsOf (GraphMutilation.bar x) z w child = false := by
    cases removable :
        G.nonAncestorsOf (GraphMutilation.bar x) z w child with
    | false => rfl
    | true =>
        have inZ := ObservedGraph.nonAncestorsOf_subset_actions G
          (GraphMutilation.bar x) z w child removable
        rw [childNotZ] at inZ
        contradiction
  unfold ObservedGraph.observedDirectedEdge
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨directed, rfl⟩,
      by
        change Bool.not (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w) child) = true
        simp [NodeSet.union, outsideX, outsideRemovable]⟩

/-- A `G_{̅(X ∪ W)}` walk containing no `Z` vertex embeds edge-for-edge
in rule 3's side graph. -/
def remapRule3ConditionedWalk_of_no_z
    (G : ObservedGraph S) (x z w : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union x w)))
      length source target)
    (noZ : forall node, node ∈ walk.nodes -> z node = false) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar
          (NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w))))
      length source target :=
  match walk with
  | .refl node => .refl node
  | @FiniteReachability.ExactWalk.step _ _ len src middle target first rest =>
      have middleNotZ : z middle = false :=
        noZ middle (by
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr rest.mem_source)
      have restNoZ : forall node, node ∈ rest.nodes -> z node = false :=
        fun node member => noZ node (by
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr member)
      .step
        (observedDirectedEdge_rule3_of_bar_union_of_child_not_z G x z w
          first middleNotZ)
        (remapRule3ConditionedWalk_of_no_z G x z w rest restNoZ)

@[simp] theorem remapRule3ConditionedWalk_of_no_z_nodes
    (G : ObservedGraph S) (x z w : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union x w)))
      length source target)
    (noZ : forall node, node ∈ walk.nodes -> z node = false) :
    (remapRule3ConditionedWalk_of_no_z G x z w walk noZ).nodes =
      walk.nodes := by
  induction walk with
  | refl => rfl
  | @step length source middle target first rest ih =>
      simp only [remapRule3ConditionedWalk_of_no_z,
        FiniteReachability.ExactWalk.nodes]
      rw [ih _]

/-- A local conditioning subfamily depends only on selected roots when every
root relevant to each displayed factor is routed into the selected mask. -/
theorem localConditionEvent_dependsOnSelected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (baseAction condition factors : NodeSet S)
    (reference : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (routes : forall child, factors child = true -> forall root,
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty
            (localConditionAction baseAction condition child)
            NodeSet.empty).intervention reference)
          (FiniteLatentSCM.ancestralInBar G
            (localConditionAction baseAction condition child)
            (NodeSet.singleton child)) root = true ->
        selected root = true) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value selected
      (localConditionEvent model baseAction condition factors reference) := by
  intro left right rootsAgree
  unfold localConditionEvent
  apply finAll_congr
  intro child
  cases factorSelected : factors child with
  | false => rfl
  | true =>
      simp only [↓reduceIte]
      unfold localConditionFactor
      let action := localConditionAction baseAction condition child
      let intervention :=
        (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference
      let relevant :=
        FiniteLatentSCM.ancestralInBar G action (NodeSet.singleton child)
      have evaluated : model.evalUnder intervention left child =
          model.evalUnder intervention right child := by
        exact model.evalNodeUnder_eq_of_rootAgreement intervention relevant
          (by
            dsimp [intervention, relevant, action]
            exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
              model G (localConditionAction baseAction condition child)
                (NodeSet.singleton child) reference)
          left right
          (by
            intro root relevantRoot
            exact rootsAgree root (routes child factorSelected root (by
              simpa [intervention, relevant, action] using relevantRoot)))
          child
          (by
            dsimp [relevant, action]
            exact FiniteLatentSCM.ancestralInBar_contains_targets G
              (localConditionAction baseAction condition child)
                (NodeSet.singleton child) child
                ((NodeSet.singleton_eq_true_iff child child).mpr rfl))
      simpa [intervention, action] using congrArg
        (fun value => decide (value = reference child)) evaluated

/-- The complementary routing principle for local conditioning factors. -/
theorem localConditionEvent_dependsOnUnselected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (baseAction condition factors : NodeSet S)
    (reference : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (routes : forall child, factors child = true -> forall root,
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty
            (localConditionAction baseAction condition child)
            NodeSet.empty).intervention reference)
          (FiniteLatentSCM.ancestralInBar G
            (localConditionAction baseAction condition child)
            (NodeSet.singleton child)) root = true ->
        selected root = false) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value selected
      (localConditionEvent model baseAction condition factors reference) := by
  intro left right rootsAgree
  unfold localConditionEvent
  apply finAll_congr
  intro child
  cases factorSelected : factors child with
  | false => rfl
  | true =>
      simp only [↓reduceIte]
      unfold localConditionFactor
      let action := localConditionAction baseAction condition child
      let intervention :=
        (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference
      let relevant :=
        FiniteLatentSCM.ancestralInBar G action (NodeSet.singleton child)
      have evaluated : model.evalUnder intervention left child =
          model.evalUnder intervention right child := by
        exact model.evalNodeUnder_eq_of_rootAgreement intervention relevant
          (by
            dsimp [intervention, relevant, action]
            exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
              model G (localConditionAction baseAction condition child)
                (NodeSet.singleton child) reference)
          left right
          (by
            intro root relevantRoot
            exact rootsAgree root (routes child factorSelected root (by
              simpa [intervention, relevant, action] using relevantRoot)))
          child
          (by
            dsimp [relevant, action]
            exact FiniteLatentSCM.ancestralInBar_contains_targets G
              (localConditionAction baseAction condition child)
                (NodeSet.singleton child) child
                ((NodeSet.singleton_eq_true_iff child child).mpr rfl))
      simpa [intervention, action] using congrArg
        (fun value => decide (value = reference child)) evaluated

/--
On the cylinder where the added action already matches the reference,
evaluation under `do(base)` agrees with evaluation under `do(base ∪ added)`.
Observed coordinates in a backward-closed region of the heavier graph then
depend only on latents still relevant after both interventions.
-/
theorem agreesOn_evalUnder_congr_of_agreesOn_added
    (model : FiniteLatentSCM S)
    (baseAction addedAction observed relevant : NodeSet S)
    (reference : S.Assignment)
    (closed : model.BackwardClosedUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
        NodeSet.empty).intervention reference)
      relevant)
    (contained : NodeSet.Subset observed relevant)
    (left right : model.latent.Assignment)
    (hleft : Kernel.agreesOn addedAction reference
      (model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) left) = true)
    (hright : Kernel.agreesOn addedAction reference
      (model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) right) = true)
    (rootsAgree : forall root,
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
          NodeSet.empty).intervention reference)
        relevant root = true ->
      left root = right root) :
    Kernel.agreesOn observed reference
      (model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) left) =
      Kernel.agreesOn observed reference
        (model.evalUnder
          ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
            reference) right) := by
  let extension :=
    (Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
      NodeSet.empty).intervention reference
  have hleftEq :=
    evalUnder_union_intervention_eq_of_agreesOn model baseAction addedAction
      reference left hleft
  have hrightEq :=
    evalUnder_union_intervention_eq_of_agreesOn model baseAction addedAction
      reference right hright
  have congrEval :=
    agreesOn_evalUnder_congr_of_rootAgreement model extension relevant
      observed reference closed contained left right rootsAgree
  rw [← hleftEq, ← hrightEq]
  exact congrEval

/--
Given `W`, `Y` is evaluated as if `W` were intervened, so it depends only
on latents still relevant to the ancestors of `Y` in `G_{\overline{X ∪ W}}`.
-/
theorem agreesOn_rule1Y_congr_given_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (left right : model.latent.Assignment)
    (hleft : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) = true)
    (hright : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) right) = true)
    (rootsAgree : forall root,
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root =
          true ->
      left root = right root) :
    Kernel.agreesOn y assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) right) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_congr_of_agreesOn_added model x w y
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
        (NodeSet.union x w) y assignment)
      (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x w) y y
        (fun _i hi => hi))
      left right (by simpa [hinter] using hleft)
      (by simpa [hinter] using hright) rootsAgree

/--
Given `W`, `Z` is evaluated as if `W` were intervened, so it depends only
on latents still relevant to the ancestors of `Z` in `G_{\overline{X ∪ W}}`.
-/
theorem agreesOn_rule1Z_congr_given_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (left right : model.latent.Assignment)
    (hleft : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) = true)
    (hright : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) right) = true)
    (rootsAgree : forall root,
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root =
          true ->
      left root = right root) :
    Kernel.agreesOn z assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) =
      Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) right) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_congr_of_agreesOn_added model x w z
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
        (NodeSet.union x w) z assignment)
      (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x w) z z
        (fun _i hi => hi))
      left right (by simpa [hinter] using hleft)
      (by simpa [hinter] using hright) rootsAgree

/-- Given `W`, agreement on the open `Y` core latents already determines `Y`. -/
theorem agreesOn_rule1Y_congr_given_w_of_openCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (left right : model.latent.Assignment)
    (hleft : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) = true)
    (hright : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) right) = true)
    (rootsAgree : forall root,
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.rule1RightOpenCore G x y z w) root = true ->
      left root = right root) :
    Kernel.agreesOn y assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) right) :=
  agreesOn_rule1Y_congr_given_w model G x y z w assignment left right
    hleft hright (fun root hanc =>
      rootsAgree root (by
        simpa [FiniteLatentSCM.rule1RightOpenCore,
          FiniteLatentSCM.latentRelevantUnder_openAncestralIn] using hanc))

/-- Given `W`, agreement on the open `Z` core latents already determines `Z`. -/
theorem agreesOn_rule1Z_congr_given_w_of_openCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (left right : model.latent.Assignment)
    (hleft : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) = true)
    (hright : Kernel.agreesOn w assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) right) = true)
    (rootsAgree : forall root,
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.rule1LeftOpenCore G x z w) root = true ->
      left root = right root) :
    Kernel.agreesOn z assignment
      (model.evalUnder
        ((rule1Right x y z w).intervention assignment) left) =
      Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) right) :=
  agreesOn_rule1Z_congr_given_w model G x y z w assignment left right
    hleft hright (fun root hanc =>
      rootsAgree root (by
        simpa [FiniteLatentSCM.rule1LeftOpenCore,
          FiniteLatentSCM.latentRelevantUnder_openAncestralIn] using hanc))

/--
On every latent assignment, agreement with `added` under `do(base)` lets
the remaining observed coordinates be read under `do(base ∪ added)`
instead.  If `added` already disagrees, both sides are `false`.
-/
theorem agreesOn_and_evalUnder_union_eq
    (model : FiniteLatentSCM S)
    (baseAction addedAction observed : NodeSet S)
    (reference : S.Assignment) (roots : model.latent.Assignment) :
    Eq
      (Kernel.agreesOn addedAction reference
        (model.evalUnder
          ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
            reference) roots) &&
        Kernel.agreesOn observed reference
          (model.evalUnder
            ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
              reference) roots))
      (Kernel.agreesOn addedAction reference
        (model.evalUnder
          ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
            reference) roots) &&
        Kernel.agreesOn observed reference
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
              NodeSet.empty).intervention reference) roots)) := by
  generalize hC :
    Kernel.agreesOn addedAction reference
      (model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) roots) = cylinder
  cases cylinder with
  | false =>
      rw [Bool.false_and, Bool.false_and]
  | true =>
      have heq :=
        evalUnder_union_intervention_eq_of_agreesOn model baseAction
          addedAction reference roots hC
      rw [Bool.true_and, Bool.true_and, heq]

/-- Rule-1 numerator/condition events rewrite as the `W`-cylinder times
open-core events of the heavier intervention. -/
theorem agreesOn_rule1_evalUnder_union_eq
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (roots : model.latent.Assignment) :
    (Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots) &&
      (Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots))) =
      (Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots) &&
      (Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots) &&
        Kernel.agreesOn z assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots))) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  rw [hinter]
  have hy :=
    agreesOn_and_evalUnder_union_eq model x w y assignment roots
  have hz :=
    agreesOn_and_evalUnder_union_eq model x w z assignment roots
  generalize hw :
    Kernel.agreesOn w assignment
      (model.evalUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment) roots) = cylinderW
  cases cylinderW with
  | false =>
      rw [Bool.and_false, Bool.and_false, Bool.false_and]
  | true =>
      have hy' :
          Kernel.agreesOn y assignment
            (model.evalUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment) roots) =
            Kernel.agreesOn y assignment
              (model.evalUnder
                ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                  NodeSet.empty).intervention assignment) roots) := by
        rw [hw, Bool.true_and, Bool.true_and] at hy
        exact hy
      have hz' :
          Kernel.agreesOn z assignment
            (model.evalUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment) roots) =
            Kernel.agreesOn z assignment
              (model.evalUnder
                ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                  NodeSet.empty).intervention assignment) roots) := by
        rw [hw, Bool.true_and, Bool.true_and] at hz
        exact hz
      rw [Bool.and_true, Bool.true_and, hy', hz']

/-- Under `do(X ∪ W)`, `Z` depends only on latents of the open `Z` core. -/
theorem agreesOn_rule1Z_dependsOnSelected_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x _y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z))
      (fun roots =>
        Kernel.agreesOn z assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)) :=
  agreesOn_evalUnder_dependsOnSelected model
    ((Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment)
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) z assignment
    (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x w) z assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x w) z z
      (fun _i hi => hi))

/-- Under `do(X ∪ W)`, `Y` depends only on latents complementary to the
open `Z` core. -/
theorem agreesOn_rule1Y_dependsOnUnselected_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w)) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z))
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)) :=
  agreesOn_evalUnder_dependsOnUnselected model
    ((Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment)
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) y assignment
    (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x w) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x w) y y
      (fun _i hi => hi))
    (FiniteLatentSCM.rule1Ancestral_latentSeparated_union model G projected
      x y z w assignment separated)

/-- Under `do(X ∪ W)`, `Y` depends only on latents of the open `Y` core. -/
theorem agreesOn_rule1Y_dependsOnSelected_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y _z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y))
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)) :=
  agreesOn_evalUnder_dependsOnSelected model
    ((Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment)
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) y assignment
    (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x w) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x w) y y
      (fun _i hi => hi))

/-- Under `do(X)`, `W` depends only on latents of its ancestors in
`G_{\overline{X}}`. -/
theorem agreesOn_rule1W_dependsOnSelected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x w))
      (fun roots =>
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x w) w assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G x w
        assignment)
      (FiniteLatentSCM.subset_ancestralInBar G x w w (fun _i hi => hi))

/--
A latent is shared between the ancestors of `W` in `G_{\overline{X}}` and
the ancestral set of `other` in `G_{\overline{X ∪ W}}`.
-/
def rule1WMeetsUnionAncestral (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (other : NodeSet S) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) other) root &&
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x w) root)

/-- Ancestral overlap with `W` is vacuous when `W` is empty: the `do(X)`
side of the meet searches an empty ancestral family. -/
theorem rule1WMeetsUnionAncestral_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (other : NodeSet S)
    (hw : NodeSet.isEmpty w = true) :
    rule1WMeetsUnionAncestral model G x w assignment other = false := by
  have hw' : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  subst hw'
  refine (finAny_eq_false_iff _).mpr ?_
  intro root
  have hrel :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x NodeSet.empty) root = false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      model.latentRelevantUnder_empty
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        root
  simp [hrel]

/-- Overlap unpacks as a single latent relevant to both ancestral families. -/
theorem rule1WMeetsUnionAncestral_eq_true_iff
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (other : NodeSet S) :
    rule1WMeetsUnionAncestral model G x w assignment other = true ↔
      Exists fun root : Fin model.latent.count =>
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) other)
            root = true ∧
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x w) root = true := by
  constructor
  · intro hmeet
    rcases (finAny_eq_true_iff _).mp (by
      simpa [rule1WMeetsUnionAncestral] using hmeet) with ⟨root, hroot⟩
    exact ⟨root, Bool.and_eq_true_iff.mp hroot⟩
  · rintro ⟨root, hcore, hwanc⟩
    apply (finAny_eq_true_iff _).mpr
    refine ⟨root, ?_⟩
    exact Bool.and_eq_true_iff.mpr ⟨hcore, hwanc⟩

/-- One latent cannot be relevant to both open ancestral families. -/
theorem rule1WMeets_not_same_root_both_cores
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (root : Fin model.latent.count)
    (hZ : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true)
    (hY : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true) :
    False := by
  have hsep :=
    FiniteLatentSCM.rule1Ancestral_latentSeparated_union model G projected
      x y z w assignment separated
  have hy := hsep root hZ
  rw [hy] at hY
  cases hY

/-- A meet unpacks into a core child (free under `do(X ∪ W)`) and a
`W`-ancestor child (free under `do(X)`), both incident to the same latent. -/
theorem rule1WMeetsUnionAncestral_exists_children
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (other : NodeSet S)
    (hmeet : rule1WMeetsUnionAncestral model G x w assignment other = true) :
    Exists fun root : Fin model.latent.count =>
      Exists fun coreChild : Fin S.count =>
        Exists fun wChild : Fin S.count =>
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) other
              coreChild = true ∧
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) coreChild = none ∧
            model.latent.incident root coreChild = true ∧
              FiniteLatentSCM.ancestralInBar G x w wChild = true ∧
                ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                  assignment) wChild = none ∧
                model.latent.incident root wChild = true := by
  rcases (rule1WMeetsUnionAncestral_eq_true_iff model G x w assignment
      other).mp hmeet with ⟨root, hcore, hwanc⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) other)
      root).mp hcore with ⟨coreChild, hsel, hfree, hinc⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x w) root).mp hwanc with
    ⟨wChild, hwsel, hwfree, hwinc⟩
  exact ⟨root, coreChild, wChild, hsel, hfree, hinc, hwsel, hwfree, hwinc⟩

/-- Free under `do(X)` but bound under `do(X ∪ W)` means the vertex lies in
`W`. -/
theorem mem_w_of_base_none_union_some (x w : NodeSet S)
    (assignment : S.Assignment) {i : Fin S.count} {value : S.Value i}
    (hbase :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment) i =
        none)
    (hunion :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) i = some value) :
    w i = true := by
  simp [Kernel.intervention, NodeSet.union] at hbase hunion
  cases hx : x i with
  | true =>
      simp [hx] at hbase
  | false =>
      simp [hx] at hunion
      cases hw : w i with
      | false =>
          simp [hw] at hunion
      | true =>
          rfl

/-- A `W`-side child that is still free under `do(X ∪ W)` cannot sit in the
other family's ancestral set: the same latent would then be relevant to both
cores. -/
theorem rule1WMeet_free_w_child_not_in_other_ancestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (root : Fin model.latent.count) (wChild : Fin S.count)
    (hZ : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true)
    (hwFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) wChild = none)
    (hwInc : model.latent.incident root wChild = true)
    (hYanc : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y wChild =
      true) :
    False :=
  rule1WMeets_not_same_root_both_cores model G projected x y z w assignment
    separated root hZ
    (model.latentRelevantUnder_of_incident
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root wChild
      hYanc hwFree hwInc)

/-- Core children of the two meets cannot coincide: they would be a vertex
in both open cores. -/
theorem rule1Meet_core_children_ne
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {zChild yChild : Fin S.count}
    (hz : FiniteLatentSCM.openAncestralIn G (NodeSet.union x w) z zChild =
      true)
    (hy : FiniteLatentSCM.openAncestralIn G (NodeSet.union x w) y yChild =
      true) :
    zChild ≠ yChild := by
  intro heq
  subst yChild
  have hdis :=
    FiniteLatentSCM.rule1OpenCores_disjoint G x y z w separated zChild
      (by simpa [FiniteLatentSCM.rule1LeftOpenCore] using hz)
  simp [FiniteLatentSCM.rule1RightOpenCore, hy] at hdis

/-- A core child free under `do(X ∪ W)` and a `W`-child bound under that
intervention are distinct, so their shared latent is a bidirected edge. -/
theorem rule1Meet_bidirected_core_to_bound_w_child
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x w : NodeSet S) (assignment : S.Assignment)
    (root : Fin model.latent.count)
    {coreChild wChild : Fin S.count} {value : S.Value wChild}
    (hcoreInc : model.latent.incident root coreChild = true)
    (hwInc : model.latent.incident root wChild = true)
    (hcoreFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) coreChild = none)
    (hwBound :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) wChild = some value) :
    G.bidirected coreChild wChild = true := by
  have hne : coreChild ≠ wChild := by
    intro heq
    subst wChild
    simp [hcoreFree] at hwBound
  exact FiniteLatentSCM.bidirected_eq_true_of_shared_latent model G projected
    root coreChild wChild hne hcoreInc hwInc

/--
The same bound `W`-child cannot join both open cores by bidirected edges:
that is an activated collider between `Y` and `Z`.
-/
theorem rule1W_not_both_meet_of_same_bound_w_child
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {zChild yChild wChild : Fin S.count}
    (hzOpen : FiniteLatentSCM.openAncestralIn G (NodeSet.union x w) z
      zChild = true)
    (hyOpen : FiniteLatentSCM.openAncestralIn G (NodeSet.union x w) y
      yChild = true)
    (hedgeZ : G.bidirected zChild wChild = true)
    (hedgeY : G.bidirected yChild wChild = true)
    (hx : x wChild = false)
    (hw : w wChild = true) :
    False := by
  rcases FiniteLatentSCM.openAncestralIn_exists_open_walk G x w z zChild
      hzOpen with ⟨zEnd, hz, lengthZ, walkZ, simpleZ, openZ⟩
  rcases FiniteLatentSCM.openAncestralIn_exists_open_walk G x w y yChild
      hyOpen with ⟨yEnd, hy, lengthY, walkY, simpleY, openY⟩
  exact FiniteLatentSCM.pathDSeparated_no_bidirected_collider_open_walks_yz
    G x y z w separated walkZ walkY simpleZ simpleY hz hy openZ openY
    hedgeZ (G.bidirected_symmetric hedgeY) hx hw

/--
Unpacking both meets onto the same `W`-child that is bound under
`do(X ∪ W)` is already a collider contradiction.
-/
theorem rule1WMeets_same_bound_w_child_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (rootZ rootY : Fin model.latent.count)
    {zChild yChild wChild : Fin S.count} {value : S.Value wChild}
    (hzSel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z zChild =
      true)
    (hzFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) zChild = none)
    (hzInc : model.latent.incident rootZ zChild = true)
    (hySel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y yChild =
      true)
    (hyFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) yChild = none)
    (hyInc : model.latent.incident rootY yChild = true)
    (hwZInc : model.latent.incident rootZ wChild = true)
    (hwYInc : model.latent.incident rootY wChild = true)
    (hwBound :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) wChild = some value)
    (hwXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        wChild = none) :
    False := by
  have hzOpen :=
    FiniteLatentSCM.openAncestralIn_of_free_ancestor G (NodeSet.union x w) z
      assignment zChild hzSel hzFree
  have hyOpen :=
    FiniteLatentSCM.openAncestralIn_of_free_ancestor G (NodeSet.union x w) y
      assignment yChild hySel hyFree
  have hedgeZ :=
    rule1Meet_bidirected_core_to_bound_w_child model G projected x w
      assignment rootZ hzInc hwZInc hzFree hwBound
  have hedgeY :=
    rule1Meet_bidirected_core_to_bound_w_child model G projected x w
      assignment rootY hyInc hwYInc hyFree hwBound
  have hx : x wChild = false := by
    simp [Kernel.intervention] at hwXFree
    exact hwXFree
  have hw : w wChild = true :=
    mem_w_of_base_none_union_some x w assignment hwXFree hwBound
  exact rule1W_not_both_meet_of_same_bound_w_child G x y z w separated
    hzOpen hyOpen hedgeZ hedgeY hx hw

/--
The same free `W`-child is an ancestor of `W`, hence an activated collider
between the open cores even though it is not itself in `W`.
-/
theorem rule1WMeets_same_free_w_child_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (rootZ rootY : Fin model.latent.count)
    {zChild yChild wChild : Fin S.count}
    (hzSel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z zChild =
      true)
    (hzFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) zChild = none)
    (hzInc : model.latent.incident rootZ zChild = true)
    (hySel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y yChild =
      true)
    (hyFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) yChild = none)
    (hyInc : model.latent.incident rootY yChild = true)
    (hwSel : FiniteLatentSCM.ancestralInBar G x w wChild = true)
    (hwZInc : model.latent.incident rootZ wChild = true)
    (hwYInc : model.latent.incident rootY wChild = true)
    (hwXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        wChild = none)
    (_hwUnionFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) wChild = none) :
    False := by
  have hzOpen :=
    FiniteLatentSCM.openAncestralIn_of_free_ancestor G (NodeSet.union x w) z
      assignment zChild hzSel hzFree
  have hyOpen :=
    FiniteLatentSCM.openAncestralIn_of_free_ancestor G (NodeSet.union x w) y
      assignment yChild hySel hyFree
  have hx : x wChild = false := by
    simp [Kernel.intervention] at hwXFree
    exact hwXFree
  by_cases hzEq : zChild = wChild
  · subst wChild
    have hfalse :=
      FiniteLatentSCM.rule1OpenCores_no_bidirected G x y z w separated
        (by simpa [FiniteLatentSCM.rule1LeftOpenCore] using hzOpen)
        (by simpa [FiniteLatentSCM.rule1RightOpenCore] using hyOpen)
    have hne : zChild ≠ yChild :=
      rule1Meet_core_children_ne G x y z w separated hzOpen hyOpen
    have hedgeY :=
      FiniteLatentSCM.bidirected_eq_true_of_shared_latent model G projected
        rootY yChild zChild hne.symm hyInc hwYInc
    exact Bool.false_ne_true
      (hfalse.symm.trans (G.bidirected_symmetric hedgeY))
  · by_cases hyEq : yChild = wChild
    · subst wChild
      have hfalse :=
        FiniteLatentSCM.rule1OpenCores_no_bidirected G x y z w separated
          (by simpa [FiniteLatentSCM.rule1LeftOpenCore] using hzOpen)
          (by simpa [FiniteLatentSCM.rule1RightOpenCore] using hyOpen)
      have hedgeZ :=
        FiniteLatentSCM.bidirected_eq_true_of_shared_latent model G projected
          rootZ zChild yChild hzEq hzInc hwZInc
      exact Bool.false_ne_true (hfalse.symm.trans hedgeZ)
    · have hedgeZ :=
        FiniteLatentSCM.bidirected_eq_true_of_shared_latent model G projected
          rootZ zChild wChild hzEq hzInc hwZInc
      have hedgeY :=
        FiniteLatentSCM.bidirected_eq_true_of_shared_latent model G projected
          rootY yChild wChild hyEq hyInc hwYInc
      have activated :
          PathSpecification.ColliderActivated G (GraphMutilation.bar x)
            (NodeSet.union x w) (.observed wChild) :=
        G.ancestorOf_mono (GraphMutilation.bar x) w (NodeSet.union x w)
          (fun i hi => by simp [NodeSet.union, hi])
          (FiniteLatentSCM.ancestorOf_of_observedAncestorOf G
            (GraphMutilation.bar x) w wChild (by
              simpa [FiniteLatentSCM.ancestralInBar] using hwSel))
      rcases FiniteLatentSCM.openAncestralIn_exists_open_walk G x w z
          zChild hzOpen with ⟨zEnd, hz, lengthZ, walkZ, simpleZ, openZ⟩
      rcases FiniteLatentSCM.openAncestralIn_exists_open_walk G x w y
          yChild hyOpen with ⟨yEnd, hy, lengthY, walkY, simpleY, openY⟩
      exact
        FiniteLatentSCM.pathDSeparated_no_bidirected_collider_open_walks_yz_of_activated
          G x y z w separated walkZ walkY simpleZ simpleY hz hy openZ openY
          hedgeZ (G.bidirected_symmetric hedgeY) hx activated

/--
The same `W`-child, whether bound or free under `do(X ∪ W)`, cannot join
both open cores.
-/
theorem rule1WMeets_same_w_child_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (rootZ rootY : Fin model.latent.count)
    {zChild yChild wChild : Fin S.count}
    (hzSel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z zChild =
      true)
    (hzFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) zChild = none)
    (hzInc : model.latent.incident rootZ zChild = true)
    (hySel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y yChild =
      true)
    (hyFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) yChild = none)
    (hyInc : model.latent.incident rootY yChild = true)
    (hwSel : FiniteLatentSCM.ancestralInBar G x w wChild = true)
    (hwZInc : model.latent.incident rootZ wChild = true)
    (hwYInc : model.latent.incident rootY wChild = true)
    (hwXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        wChild = none) :
    False := by
  cases hIu :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) wChild with
  | none =>
      exact rule1WMeets_same_free_w_child_false model G projected x y z w
        assignment separated rootZ rootY hzSel hzFree hzInc hySel hyFree
        hyInc hwSel hwZInc hwYInc hwXFree hIu
  | some value =>
      exact rule1WMeets_same_bound_w_child_false model G projected x y z w
        assignment separated rootZ rootY hzSel hzFree hzInc hySel hyFree
        hyInc hwZInc hwYInc hIu hwXFree

/-- Unpacking both meets onto equal `W`-children is impossible. -/
theorem rule1WMeets_unpacked_w_children_ne
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (rootZ rootY : Fin model.latent.count)
    {zChild yChild wZ wY : Fin S.count}
    (hzSel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z zChild =
      true)
    (hzFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) zChild = none)
    (hzInc : model.latent.incident rootZ zChild = true)
    (hySel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y yChild =
      true)
    (hyFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) yChild = none)
    (hyInc : model.latent.incident rootY yChild = true)
    (hwZSel : FiniteLatentSCM.ancestralInBar G x w wZ = true)
    (hwYSel : FiniteLatentSCM.ancestralInBar G x w wY = true)
    (hwZInc : model.latent.incident rootZ wZ = true)
    (hwYInc : model.latent.incident rootY wY = true)
    (hwZXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        wZ = none)
    (hwYXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        wY = none) :
    wZ ≠ wY := by
  intro heq
  subst wY
  exact rule1WMeets_same_w_child_false model G projected x y z w assignment
    separated rootZ rootY hzSel hzFree hzInc hySel hyFree hyInc hwZSel
    hwZInc hwYInc hwZXFree

/--
Distinct bound `W`-children joined by a bidirected edge are two activated
colliders between the open cores.
-/
theorem rule1WMeets_distinct_bound_mid_hedge_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (rootZ rootY : Fin model.latent.count)
    {zChild yChild wZ wY : Fin S.count} {valueZ : S.Value wZ}
    {valueY : S.Value wY}
    (hzSel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z zChild =
      true)
    (hzFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) zChild = none)
    (hzInc : model.latent.incident rootZ zChild = true)
    (hySel : FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y yChild =
      true)
    (hyFree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) yChild = none)
    (hyInc : model.latent.incident rootY yChild = true)
    (hwZInc : model.latent.incident rootZ wZ = true)
    (hwYInc : model.latent.incident rootY wY = true)
    (hwZBound :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) wZ = some valueZ)
    (hwYBound :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) wY = some valueY)
    (hwZXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        wZ = none)
    (hwYXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        wY = none)
    (hedgeMid : G.bidirected wZ wY = true) :
    False := by
  have hzOpen :=
    FiniteLatentSCM.openAncestralIn_of_free_ancestor G (NodeSet.union x w) z
      assignment zChild hzSel hzFree
  have hyOpen :=
    FiniteLatentSCM.openAncestralIn_of_free_ancestor G (NodeSet.union x w) y
      assignment yChild hySel hyFree
  have hedgeZ :=
    rule1Meet_bidirected_core_to_bound_w_child model G projected x w
      assignment rootZ hzInc hwZInc hzFree hwZBound
  have hedgeY :=
    rule1Meet_bidirected_core_to_bound_w_child model G projected x w
      assignment rootY hyInc hwYInc hyFree hwYBound
  have hxZ : x wZ = false := by
    simp [Kernel.intervention] at hwZXFree
    exact hwZXFree
  have hxY : x wY = false := by
    simp [Kernel.intervention] at hwYXFree
    exact hwYXFree
  have hwZ : w wZ = true :=
    mem_w_of_base_none_union_some x w assignment hwZXFree hwZBound
  have hwY : w wY = true :=
    mem_w_of_base_none_union_some x w assignment hwYXFree hwYBound
  have blockedZ :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed wZ) = true := by
    simp [ObservedGraph.blockedBy, NodeSet.union, hwZ]
  have blockedY :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed wY) = true := by
    simp [ObservedGraph.blockedBy, NodeSet.union, hwY]
  have activatedZ :
      PathSpecification.ColliderActivated G (GraphMutilation.bar x)
        (NodeSet.union x w) (.observed wZ) :=
    G.ancestorOf_target (GraphMutilation.bar x) (NodeSet.union x w)
      (by simp [NodeSet.union, hwZ])
  have activatedY :
      PathSpecification.ColliderActivated G (GraphMutilation.bar x)
        (NodeSet.union x w) (.observed wY) :=
    G.ancestorOf_target (GraphMutilation.bar x) (NodeSet.union x w)
      (by simp [NodeSet.union, hwY])
  rcases FiniteLatentSCM.openAncestralIn_exists_open_walk G x w z zChild
      hzOpen with ⟨zEnd, hz, lengthZ, walkZ, simpleZ, openZ⟩
  rcases FiniteLatentSCM.openAncestralIn_exists_open_walk G x w y yChild
      hyOpen with ⟨yEnd, hy, lengthY, walkY, simpleY, openY⟩
  exact FiniteLatentSCM.pathDSeparated_no_two_bidirected_colliders_open_walks_yz
    G x y z w separated walkZ walkY simpleZ simpleY hz hy openZ openY
    hedgeZ hedgeMid (G.bidirected_symmetric hedgeY) hxZ hxY blockedZ blockedY
    activatedZ activatedY

/--
A `W` vertex meets `other`'s ancestral family when it is still free under
`do(X)` and some latent that is relevant to that family under `do(X ∪ W)`
is incident to it.
-/
def rule1WVertexMeetsCore (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (other : NodeSet S) : NodeSet S :=
  fun i =>
    (w i &&
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
        assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) other)
          root &&
        model.latent.incident root i)

theorem rule1WVertexMeetsCore_subset_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (other : NodeSet S) :
    NodeSet.Subset (rule1WVertexMeetsCore model G x w assignment other) w := by
  intro i hi
  have hparts :
      (w i &&
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) other)
              root &&
            model.latent.incident root i) = true := by
    simpa [rule1WVertexMeetsCore] using hi
  exact (Bool.and_eq_true_iff.mp hparts.1).1

/-- Meeting both cores at the same `W` vertex is the same-child case. -/
theorem rule1WVertexMeetsCore_not_both
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {i : Fin S.count}
    (hZ : rule1WVertexMeetsCore model G x w assignment z i = true)
    (hY : rule1WVertexMeetsCore model G x w assignment y i = true) :
    False := by
  have hZparts :
      (w i &&
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
              root &&
            model.latent.incident root i) = true := by
    simpa [rule1WVertexMeetsCore] using hZ
  have hYparts :
      (w i &&
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
              root &&
            model.latent.incident root i) = true := by
    simpa [rule1WVertexMeetsCore] using hY
  have hw : w i = true := (Bool.and_eq_true_iff.mp hZparts.1).1
  have hwXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        i = none :=
    Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hZparts.1).2
  rcases (finAny_eq_true_iff _).mp hZparts.2 with ⟨rootZ, hrootZ⟩
  rcases Bool.and_eq_true_iff.mp hrootZ with ⟨hZcore, hwZInc⟩
  rcases (finAny_eq_true_iff _).mp hYparts.2 with ⟨rootY, hrootY⟩
  rcases Bool.and_eq_true_iff.mp hrootY with ⟨hYcore, hwYInc⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
      rootZ).mp hZcore with ⟨zChild, hzSel, hzFree, hzInc⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
      rootY).mp hYcore with ⟨yChild, hySel, hyFree, hyInc⟩
  have hwSel : FiniteLatentSCM.ancestralInBar G x w i = true :=
    FiniteLatentSCM.observedAncestorOf_self G (GraphMutilation.bar x) w hw
  exact rule1WMeets_same_w_child_false model G projected x y z w assignment
    separated rootZ rootY hzSel hzFree hzInc hySel hyFree hyInc hwSel
    hwZInc hwYInc hwXFree

/-- The `W` vertices that meet `Z` are disjoint from those that meet `Y`. -/
theorem rule1WVertexMeetsCore_disjoint
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w)) :
    NodeSet.Disjoint
      (rule1WVertexMeetsCore model G x w assignment z)
      (rule1WVertexMeetsCore model G x w assignment y) := by
  intro i hiZ
  cases hY : rule1WVertexMeetsCore model G x w assignment y i with
  | false =>
      rfl
  | true =>
      exact (rule1WVertexMeetsCore_not_both model G projected x y z w
        assignment separated hiZ hY).elim

/-- `W` vertices that meet the `Y` core; the complementary slice of `W`
avoids that core. -/
def rule1WSplitUnselected (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) : NodeSet S :=
  rule1WVertexMeetsCore model G x w assignment y

def rule1WSplitSelected (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) : NodeSet S :=
  NodeSet.diff w (rule1WSplitUnselected model G x w assignment y)

theorem rule1WSplit_disjoint (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) :
    NodeSet.Disjoint
      (rule1WSplitSelected model G x w assignment y)
      (rule1WSplitUnselected model G x w assignment y) :=
  NodeSet.Disjoint.diff_right w
    (rule1WSplitUnselected model G x w assignment y)

theorem rule1WSplit_union (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) :
    NodeSet.union
      (rule1WSplitSelected model G x w assignment y)
      (rule1WSplitUnselected model G x w assignment y) = w := by
  funext i
  have hsub :=
    rule1WVertexMeetsCore_subset_w model G x w assignment y i
  simp [rule1WSplitSelected, rule1WSplitUnselected, NodeSet.union,
    NodeSet.diff]
  cases hw : w i with
  | false =>
      cases hm : rule1WVertexMeetsCore model G x w assignment y i with
      | false =>
          simp
      | true =>
          exact (Bool.false_ne_true (hw.symm.trans (hsub hm))).elim
  | true =>
      cases hm : rule1WVertexMeetsCore model G x w assignment y i with
      | false =>
          simp
      | true =>
          simp

/--
`do(X)`-free ancestors of `W` that carry an open-`Y`-core latent.  This
includes the `Y`-meeting `W` vertices and also extra ancestors that sit
outside `W`; descendant closure in `W` then absorbs every `W` vertex
those seeds reach.
-/
def rule1WYSideSeed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) : NodeSet S :=
  fun i =>
    (FiniteLatentSCM.ancestralInBar G x w i &&
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
        assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
        model.latent.incident root i)

/-- A `Y`-meeting `W` vertex is a `Y`-side seed. -/
theorem rule1WYSideSeed_of_meets_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hi : rule1WVertexMeetsCore model G x w assignment y i = true) :
    rule1WYSideSeed model G x w assignment y i = true := by
  have hparts :
      (w i &&
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
              root &&
            model.latent.incident root i) = true := by
    simpa [rule1WVertexMeetsCore] using hi
  have hw : w i = true := (Bool.and_eq_true_iff.mp hparts.1).1
  have hself :
      FiniteLatentSCM.ancestralInBar G x w i = true :=
    FiniteLatentSCM.observedAncestorOf_self G (GraphMutilation.bar x) w hw
  refine Bool.and_eq_true_iff.mpr ⟨?_, hparts.2⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hself, (Bool.and_eq_true_iff.mp hparts.1).2⟩

/--
`W` vertices that are directed descendants of a `Y`-side seed in
`G_{\overline{X}}`, including every `Y`-meeting `W` vertex.  Directed
`W_Y → W'` and extra `do(X)`-free `Y`-core ancestors outside `W` are
absorbed into the `Y` block.
-/
def rule1WSplitUnselectedClosed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) : NodeSet S :=
  fun i =>
    w i &&
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton i))
        (rule1WYSideSeed model G x w assignment y)

def rule1WSplitSelectedClosed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) : NodeSet S :=
  NodeSet.diff w (rule1WSplitUnselectedClosed model G x w assignment y)

theorem rule1WSplitClosed_disjoint (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) :
    NodeSet.Disjoint
      (rule1WSplitSelectedClosed model G x w assignment y)
      (rule1WSplitUnselectedClosed model G x w assignment y) :=
  NodeSet.Disjoint.diff_right w
    (rule1WSplitUnselectedClosed model G x w assignment y)

theorem rule1WSplitClosed_union (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S) (assignment : S.Assignment)
    (y : NodeSet S) :
    NodeSet.union
      (rule1WSplitSelectedClosed model G x w assignment y)
      (rule1WSplitUnselectedClosed model G x w assignment y) = w := by
  funext i
  simp [rule1WSplitSelectedClosed, rule1WSplitUnselectedClosed,
    NodeSet.union, NodeSet.diff]
  cases hw : w i with
  | false =>
      simp
  | true =>
      cases hm :
          NodeSet.meetsBool
            (FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton i))
            (rule1WYSideSeed model G x w assignment y) with
      | false =>
          simp
      | true =>
          simp

/-- Every `Y`-meeting `W` vertex is a descendant of itself, hence sits
in the closed `Y` block. -/
theorem rule1WSplitClosed_contains_meets
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hi : rule1WVertexMeetsCore model G x w assignment y i = true) :
    rule1WSplitUnselectedClosed model G x w assignment y i = true := by
  have hw : w i = true :=
    rule1WVertexMeetsCore_subset_w model G x w assignment y i hi
  have hseed :
      rule1WYSideSeed model G x w assignment y i = true :=
    rule1WYSideSeed_of_meets_core model G x w assignment y hi
  have hself :
      FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton i) i = true :=
    FiniteLatentSCM.observedAncestorOf_self G (GraphMutilation.bar x)
      (NodeSet.singleton i)
      ((NodeSet.singleton_eq_true_iff i i).mpr rfl)
  have hmeets :
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton i))
        (rule1WYSideSeed model G x w assignment y) = true :=
    (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨i, hself, hseed⟩
  simp [rule1WSplitUnselectedClosed, hw, hmeets]

/-- A vertex of the closed `Y` block cannot ancestor a selected vertex:
that selected vertex would itself be a descendant of a `Y`-meeting
vertex, hence unselected. -/
theorem rule1WSplitClosed_no_unselected_ancestor
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hunsel : rule1WSplitUnselectedClosed model G x w assignment y i = true)
    (hanc : FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y) i = true) :
    False := by
  have hparts :
      w i = true ∧
        NodeSet.meetsBool
          (FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton i))
          (rule1WYSideSeed model G x w assignment y) = true := by
    simpa [rule1WSplitUnselectedClosed] using hunsel
  rcases (NodeSet.meetsBool_eq_true_iff _ _).mp hparts.2 with
    ⟨seed, hseedAnc, hseedY⟩
  have hany :
      (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
        rule1WSplitSelectedClosed model G x w assignment y target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun k : Fin S.count => k))
            (G.observedDirectedEdge (GraphMutilation.bar x))
            (List.ofFn (fun k : Fin S.count => k)).length i target) =
        true := by
    simpa [FiniteLatentSCM.ancestralInBar, ObservedGraph.observedAncestorOf]
      using hanc
  rcases List.any_eq_true.mp hany with ⟨t, tMem, ht⟩
  have htParts := Bool.and_eq_true_iff.mp ht
  have hsel :
      rule1WSplitSelectedClosed model G x w assignment y t = true :=
    htParts.1
  have hiAncT :
      FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton t) i = true := by
    have hanyT :
        (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
          NodeSet.singleton t target &&
            FiniteReachability.within finBeq
              (List.ofFn (fun k : Fin S.count => k))
              (G.observedDirectedEdge (GraphMutilation.bar x))
              (List.ofFn (fun k : Fin S.count => k)).length i target) =
          true :=
      List.any_eq_true.mpr
        ⟨t, tMem,
          Bool.and_eq_true_iff.mpr
            ⟨(NodeSet.singleton_eq_true_iff t t).mpr rfl, htParts.2⟩⟩
    simpa [FiniteLatentSCM.ancestralInBar, ObservedGraph.observedAncestorOf]
      using hanyT
  have hseedT :
      FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton t) seed = true :=
    FiniteLatentSCM.ancestralInBar_trans G x hseedAnc hiAncT
  have hwT : w t = true := by
    have hdiff :
        (w t &&
          !(rule1WSplitUnselectedClosed model G x w assignment y t)) =
          true := by
      simpa [rule1WSplitSelectedClosed, NodeSet.diff] using hsel
    exact (Bool.and_eq_true_iff.mp hdiff).1
  have hunselT :
      rule1WSplitUnselectedClosed model G x w assignment y t = true := by
    have hmeetsT :
        NodeSet.meetsBool
          (FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton t))
          (rule1WYSideSeed model G x w assignment y) = true :=
      (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨seed, hseedT, hseedY⟩
    simp [rule1WSplitUnselectedClosed, hwT, hmeetsT]
  have hfalse :
      rule1WSplitUnselectedClosed model G x w assignment y t = false :=
    rule1WSplitClosed_disjoint model G x w assignment y t hsel
  exact Bool.false_ne_true (hfalse.symm.trans hunselT)

/-- By construction, the descendant-closed selected slice of `W` does
not meet the `Y` core. -/
theorem rule1WSplitClosedSelected_not_meet_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hi : rule1WSplitSelectedClosed model G x w assignment y i = true) :
    rule1WVertexMeetsCore model G x w assignment y i = false := by
  cases hm : rule1WVertexMeetsCore model G x w assignment y i with
  | false =>
      rfl
  | true =>
      have hunsel :=
        rule1WSplitClosed_contains_meets model G x w assignment y hm
      have hfalse :
          rule1WSplitUnselectedClosed model G x w assignment y i = false :=
        rule1WSplitClosed_disjoint model G x w assignment y i hi
      exact False.elim (Bool.false_ne_true (hfalse.symm.trans hunsel))

/-- A selected closed `W` vertex cannot carry a latent of the `Y` core. -/
theorem rule1WSplitClosedSelected_not_incident_y_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    (root : Fin model.latent.count) {i : Fin S.count}
    (hi : rule1WSplitSelectedClosed model G x w assignment y i = true)
    (hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        i = none)
    (hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true)
    (hinc : model.latent.incident root i = true) :
    False := by
  have hw : w i = true :=
    NodeSet.diff_subset_left w
      (rule1WSplitUnselectedClosed model G x w assignment y) i hi
  have hmeet :
      rule1WVertexMeetsCore model G x w assignment y i = true := by
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · exact Bool.and_eq_true_iff.mpr
        ⟨hw, Option.isNone_iff_eq_none.mpr hfree⟩
    · exact finAny_eq_true_of _ root
        (Bool.and_eq_true_iff.mpr ⟨hcore, hinc⟩)
  have hnot :=
    rule1WSplitClosedSelected_not_meet_y model G x w assignment y hi
  simp [hmeet] at hnot

/-- A `W` vertex that is not in the closed selected slice is unselected. -/
theorem rule1WSplitClosed_mem_w_of_not_selected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hw : w i = true)
    (hnot : rule1WSplitSelectedClosed model G x w assignment y i = false) :
    rule1WSplitUnselectedClosed model G x w assignment y i = true := by
  have hdiff :
      (w i &&
        !(rule1WSplitUnselectedClosed model G x w assignment y i)) =
        false := by
    simpa [rule1WSplitSelectedClosed, NodeSet.diff] using hnot
  simp [hw] at hdiff
  cases hY : rule1WSplitUnselectedClosed model G x w assignment y i with
  | true =>
      rfl
  | false =>
      simp [hY] at hdiff

/-- If a `Y`-core latent is relevant to the ancestors of the closed
selected slice under `do(X)`, its `do(X)`-free child in that ancestral
set cannot lie in the selected slice. -/
theorem rule1WSplitClosedSelected_y_core_child_not_selected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (root : Fin model.latent.count)
    (hrel : model.latentRelevantUnder
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y)) root = true)
    (hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true) :
    Exists fun child : Fin S.count =>
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y) child =
        true ∧
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          child = none ∧
        model.latent.incident root child = true ∧
          rule1WSplitSelectedClosed model G x w assignment y child =
            false := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext j
    simp [rule1Right, Kernel.intervention]
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y))
      root).mp hrel with ⟨child, hanc, hfreeR, hinc⟩
  have hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        child = none := by
    simpa [hinter] using hfreeR
  have hnotSel :
      rule1WSplitSelectedClosed model G x w assignment y child = false := by
    cases hsel :
        rule1WSplitSelectedClosed model G x w assignment y child with
    | false =>
        rfl
    | true =>
        exact (rule1WSplitClosedSelected_not_incident_y_core model G x w
          assignment y root hsel hfree hcore hinc).elim
  exact ⟨child, hanc, hfree, hinc, hnotSel⟩

/-- Overlap of the closed selected-slice ancestors with the open `Y` core. -/
def rule1WSplitClosedSelectedMeetsYCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y)) root)

/--
The closed selected slice cannot share a latent with the open `Y` core:
a `do(X)`-free `Y`-core child in its ancestral set is a `Y`-side seed,
so every selected vertex it reaches is already unselected.
-/
theorem rule1WSplitClosedSelectedMeetsYCore_eq_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    rule1WSplitClosedSelectedMeetsYCore model G x y z w assignment =
      false := by
  cases hmeet :
      rule1WSplitClosedSelectedMeetsYCore model G x y z w assignment with
  | false =>
      rfl
  | true =>
      rcases (finAny_eq_true_iff _).mp
          (by simpa [rule1WSplitClosedSelectedMeetsYCore] using hmeet) with
        ⟨root, hparts⟩
      rcases Bool.and_eq_true_iff.mp hparts with ⟨hcore, hrel⟩
      rcases rule1WSplitClosedSelected_y_core_child_not_selected model G
          x y z w assignment root hrel hcore with
        ⟨child, hanc, hfree, hinc, _hnotSel⟩
      have hselSub :
          NodeSet.Subset
            (rule1WSplitSelectedClosed model G x w assignment y) w :=
        NodeSet.diff_subset_left w
          (rule1WSplitUnselectedClosed model G x w assignment y)
      have hancW :
          FiniteLatentSCM.ancestralInBar G x w child = true :=
        FiniteLatentSCM.ancestralInBar_mono G x hselSub hanc
      have hseed :
          rule1WYSideSeed model G x w assignment y child = true := by
        refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
        · exact Bool.and_eq_true_iff.mpr
            ⟨hancW, Option.isNone_iff_eq_none.mpr hfree⟩
        · exact finAny_eq_true_of _ root
            (Bool.and_eq_true_iff.mpr ⟨hcore, hinc⟩)
      have hany :
          (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
            rule1WSplitSelectedClosed model G x w assignment y target &&
              FiniteReachability.within finBeq
                (List.ofFn (fun k : Fin S.count => k))
                (G.observedDirectedEdge (GraphMutilation.bar x))
                (List.ofFn (fun k : Fin S.count => k)).length child
                target) = true := by
        simpa [FiniteLatentSCM.ancestralInBar,
          ObservedGraph.observedAncestorOf] using hanc
      rcases List.any_eq_true.mp hany with ⟨t, tMem, ht⟩
      have htParts := Bool.and_eq_true_iff.mp ht
      have hsel :
          rule1WSplitSelectedClosed model G x w assignment y t = true :=
        htParts.1
      have hchildAncT :
          FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton t) child =
            true := by
        have hanyT :
            (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
              NodeSet.singleton t target &&
                FiniteReachability.within finBeq
                  (List.ofFn (fun k : Fin S.count => k))
                  (G.observedDirectedEdge (GraphMutilation.bar x))
                  (List.ofFn (fun k : Fin S.count => k)).length child
                  target) = true :=
          List.any_eq_true.mpr
            ⟨t, tMem,
              Bool.and_eq_true_iff.mpr
                ⟨(NodeSet.singleton_eq_true_iff t t).mpr rfl, htParts.2⟩⟩
        simpa [FiniteLatentSCM.ancestralInBar,
          ObservedGraph.observedAncestorOf] using hanyT
      have hwT : w t = true := hselSub t hsel
      have hunselT :
          rule1WSplitUnselectedClosed model G x w assignment y t = true := by
        have hmeetsT :
            NodeSet.meetsBool
              (FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton t))
              (rule1WYSideSeed model G x w assignment y) = true :=
          (NodeSet.meetsBool_eq_true_iff _ _).mpr
            ⟨child, hchildAncT, hseed⟩
        simp [rule1WSplitUnselectedClosed, hwT, hmeetsT]
      have hfalse :
          rule1WSplitUnselectedClosed model G x w assignment y t = false :=
        rule1WSplitClosed_disjoint model G x w assignment y t hsel
      exact False.elim (Bool.false_ne_true (hfalse.symm.trans hunselT))

/-- A shared ancestral child that already sits in the closed `Y` block
cannot also ancestor the selected slice. -/
theorem rule1WSplitClosedOverlap_same_unselected_child_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {child : Fin S.count}
    (hunsel : rule1WSplitUnselectedClosed model G x w assignment y child =
      true)
    (hancS : FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y) child =
      true) :
    False :=
  rule1WSplitClosed_no_unselected_ancestor model G x w assignment y hunsel
    hancS

/--
A `Y`-side seed cannot ancestor the closed selected slice: every selected
vertex it reaches is already unselected.
-/
theorem rule1WSplitClosed_no_yside_seed_ancestor
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {child : Fin S.count}
    (hseed : rule1WYSideSeed model G x w assignment y child = true)
    (hancS : FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y) child =
      true) :
    False := by
  have hselSub :
      NodeSet.Subset
        (rule1WSplitSelectedClosed model G x w assignment y) w :=
    NodeSet.diff_subset_left w
      (rule1WSplitUnselectedClosed model G x w assignment y)
  have hany :
      (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
        rule1WSplitSelectedClosed model G x w assignment y target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun k : Fin S.count => k))
            (G.observedDirectedEdge (GraphMutilation.bar x))
            (List.ofFn (fun k : Fin S.count => k)).length child
            target) = true := by
    simpa [FiniteLatentSCM.ancestralInBar,
      ObservedGraph.observedAncestorOf] using hancS
  rcases List.any_eq_true.mp hany with ⟨t, tMem, ht⟩
  have htParts := Bool.and_eq_true_iff.mp ht
  have hsel :
      rule1WSplitSelectedClosed model G x w assignment y t = true :=
    htParts.1
  have hchildAncT :
      FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton t) child =
        true := by
    have hanyT :
        (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
          NodeSet.singleton t target &&
            FiniteReachability.within finBeq
              (List.ofFn (fun k : Fin S.count => k))
              (G.observedDirectedEdge (GraphMutilation.bar x))
              (List.ofFn (fun k : Fin S.count => k)).length child
              target) = true :=
      List.any_eq_true.mpr
        ⟨t, tMem,
          Bool.and_eq_true_iff.mpr
            ⟨(NodeSet.singleton_eq_true_iff t t).mpr rfl, htParts.2⟩⟩
    simpa [FiniteLatentSCM.ancestralInBar,
      ObservedGraph.observedAncestorOf] using hanyT
  have hwT : w t = true := hselSub t hsel
  have hunselT :
      rule1WSplitUnselectedClosed model G x w assignment y t = true := by
    have hmeetsT :
        NodeSet.meetsBool
          (FiniteLatentSCM.ancestralInBar G x (NodeSet.singleton t))
          (rule1WYSideSeed model G x w assignment y) = true :=
      (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨child, hchildAncT, hseed⟩
    simp [rule1WSplitUnselectedClosed, hwT, hmeetsT]
  have hfalse :
      rule1WSplitUnselectedClosed model G x w assignment y t = false :=
    rule1WSplitClosed_disjoint model G x w assignment y t hsel
  exact Bool.false_ne_true (hfalse.symm.trans hunselT)

/-- Overlap of the closed `Y`-block ancestors with the open `Z` core. -/
def rule1WSplitClosedUnselectedMeetsZCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root &&
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselectedClosed model G x w assignment y)) root)

/-- A latent relevant to both closed slices of `W` under `do(X)`. -/
def rule1WSplitClosedAncestralLatentsOverlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y)) root &&
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselectedClosed model G x w assignment y)) root)

/-- A shared ancestral latent of the two closed `W` slices unpacks as a
pair of `do(X)`-free children, one in each ancestral set. -/
theorem rule1WSplitClosedAncestralLatentsOverlap_unpack
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
        true) :
    Exists fun root : Fin model.latent.count =>
      Exists fun childSel : Fin S.count =>
        Exists fun childUnsel : Fin S.count =>
          FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitSelectedClosed model G x w assignment y)
              childSel = true ∧
            FiniteLatentSCM.ancestralInBar G x
                (rule1WSplitUnselectedClosed model G x w assignment y)
                childUnsel = true ∧
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                  assignment) childSel = none ∧
                ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                    assignment) childUnsel = none ∧
                  model.latent.incident root childSel = true ∧
                    model.latent.incident root childUnsel = true := by
  rcases (finAny_eq_true_iff _).mp
      (by simpa [rule1WSplitClosedAncestralLatentsOverlap] using hoverlap) with
    ⟨root, hparts⟩
  rcases Bool.and_eq_true_iff.mp hparts with ⟨hSel, hUnsel⟩
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext j
    simp [rule1Right, Kernel.intervention]
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y))
      root).mp hSel with ⟨childSel, hancS, hfreeSR, hincS⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselectedClosed model G x w assignment y))
      root).mp hUnsel with ⟨childUnsel, hancU, hfreeUR, hincU⟩
  refine ⟨root, childSel, childUnsel, hancS, hancU, ?_, ?_, hincS, hincU⟩
  · simpa [hinter] using hfreeSR
  · simpa [hinter] using hfreeUR

/-- A shared ancestral child that is a `Y`-side seed cannot also ancestor
the selected slice. -/
theorem rule1WSplitClosedAncestralLatentsOverlap_same_yside_seed_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {child : Fin S.count}
    (hseed : rule1WYSideSeed model G x w assignment y child = true)
    (hancS : FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y) child =
      true) :
    False :=
  rule1WSplitClosed_no_yside_seed_ancestor model G x w assignment y hseed
    hancS

/-- A shared ancestral child in the closed `Y` block or a `Y`-side seed
cannot also ancestor the selected slice. -/
theorem rule1WSplitClosedAncestralLatentsOverlap_same_child_false_of
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {child : Fin S.count}
    (hancS : FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y) child =
      true)
    (hblock :
      (rule1WSplitUnselectedClosed model G x w assignment y child ||
        rule1WYSideSeed model G x w assignment y child) = true) :
    False := by
  cases hunsel :
      rule1WSplitUnselectedClosed model G x w assignment y child with
  | true =>
      exact rule1WSplitClosedOverlap_same_unselected_child_false model G
        x w assignment y hunsel hancS
  | false =>
      have hseed :
          rule1WYSideSeed model G x w assignment y child = true := by
        simpa [hunsel] using hblock
      exact rule1WSplitClosedAncestralLatentsOverlap_same_yside_seed_false
        model G x w assignment y hseed hancS

/--
A `Z`-core latent relevant to the closed `Y` block unpacks as a
`do(X)`-free child in that block's ancestral set.
-/
theorem rule1WSplitClosedUnselected_z_core_child
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (root : Fin model.latent.count)
    (hrel : model.latentRelevantUnder
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselectedClosed model G x w assignment y)) root = true)
    (_hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true) :
    Exists fun child : Fin S.count =>
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselectedClosed model G x w assignment y) child =
        true ∧
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          child = none ∧
        model.latent.incident root child = true := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext j
    simp [rule1Right, Kernel.intervention]
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselectedClosed model G x w assignment y))
      root).mp hrel with ⟨child, hanc, hfreeR, hinc⟩
  refine ⟨child, hanc, ?_, hinc⟩
  simpa [hinter] using hfreeR

/--
A `Y`-side seed cannot also carry a latent of the open `Z` core: that is
the same `W`-ancestor joining both cores.
-/
theorem rule1WSplitClosedUnselected_z_core_child_not_yside_seed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (rootZ : Fin model.latent.count) {child : Fin S.count}
    (hcoreZ : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) rootZ = true)
    (hincZ : model.latent.incident rootZ child = true)
    (hseed : rule1WYSideSeed model G x w assignment y child = true) :
    False := by
  have hseedParts :
      (FiniteLatentSCM.ancestralInBar G x w child &&
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment child).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
              root &&
            model.latent.incident root child) = true := by
    simpa [rule1WYSideSeed] using hseed
  have hwSel : FiniteLatentSCM.ancestralInBar G x w child = true :=
    (Bool.and_eq_true_iff.mp hseedParts.1).1
  have hwXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        child = none :=
    Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hseedParts.1).2
  rcases (finAny_eq_true_iff _).mp hseedParts.2 with ⟨rootY, hYparts⟩
  rcases Bool.and_eq_true_iff.mp hYparts with ⟨hcoreY, hincY⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
      rootZ).mp hcoreZ with ⟨zChild, hzSel, hzFree, hzInc⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
      rootY).mp hcoreY with ⟨yChild, hySel, hyFree, hyInc⟩
  exact rule1WMeets_same_w_child_false model G projected x y z w assignment
    separated rootZ rootY hzSel hzFree hzInc hySel hyFree hyInc hwSel
    hincZ hincY hwXFree

/--
If every `do(X)`-free ancestral child of the closed `Y` block that
carries a `Z`-core latent is a `Y`-side seed, that block cannot share a
latent with the open `Z` core.
-/
theorem rule1WSplitClosedUnselectedMeetsZCore_eq_false_of
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hSeed : forall child,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselectedClosed model G x w assignment y) child =
        true ->
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment) child = none ->
          finAny model.latent.count (fun root =>
              model.latentRelevantUnder
                  ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                    NodeSet.empty).intervention assignment)
                  (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
                  root &&
                model.latent.incident root child) = true ->
            rule1WYSideSeed model G x w assignment y child = true) :
    rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment =
      false := by
  cases hmeet :
      rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment with
  | false =>
      rfl
  | true =>
      rcases (finAny_eq_true_iff _).mp
          (by simpa [rule1WSplitClosedUnselectedMeetsZCore] using hmeet) with
        ⟨root, hparts⟩
      rcases Bool.and_eq_true_iff.mp hparts with ⟨hcore, hrel⟩
      rcases rule1WSplitClosedUnselected_z_core_child model G x y z w
          assignment root hrel hcore with
        ⟨child, hanc, hfree, hinc⟩
      have hincAny :
          finAny model.latent.count (fun r =>
            model.latentRelevantUnder
                ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                  NodeSet.empty).intervention assignment)
                (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
                r &&
              model.latent.incident r child) = true :=
        finAny_eq_true_of _ root (Bool.and_eq_true_iff.mpr ⟨hcore, hinc⟩)
      have hseed := hSeed child hanc hfree hincAny
      exact (rule1WSplitClosedUnselected_z_core_child_not_yside_seed model G
        projected x y z w assignment separated root hcore hinc hseed).elim

/-- Unselected coordinates of the descendant-closed split: the open `Y`
core together with ancestral latents of the closed `Y` block. Extra
`W`-only latents stay with `Y`. -/
def rule1WSplitClosedYBlockLatents
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    Fin model.latent.count -> Bool :=
  fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root ||
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselectedClosed model G x w assignment y)) root

/-- The closed selected slice of `W` observes only latents of its own
ancestors in `G_{\overline{X}}`. -/
theorem agreesOn_rule1WSplitClosedSelected_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y)))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitSelectedClosed model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y))
      (rule1WSplitSelectedClosed model G x w assignment y) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G x
        (rule1WSplitSelectedClosed model G x w assignment y) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G x
        (rule1WSplitSelectedClosed model G x w assignment y)
        (rule1WSplitSelectedClosed model G x w assignment y)
        (fun _i hi => hi))

/-- The closed `Y` block of `W` observes only latents of its own ancestors
in `G_{\overline{X}}`. -/
theorem agreesOn_rule1WSplitClosedUnselected_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselectedClosed model G x w assignment y)))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselectedClosed model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselectedClosed model G x w assignment y))
      (rule1WSplitUnselectedClosed model G x w assignment y) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G x
        (rule1WSplitUnselectedClosed model G x w assignment y) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G x
        (rule1WSplitUnselectedClosed model G x w assignment y)
        (rule1WSplitUnselectedClosed model G x w assignment y)
        (fun _i hi => hi))

/-- The selected slice of `W` observes only latents of its own ancestors
in `G_{\overline{X}}`. -/
theorem agreesOn_rule1WSplitSelected_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y)))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitSelected model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelected model G x w assignment y))
      (rule1WSplitSelected model G x w assignment y) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G x
        (rule1WSplitSelected model G x w assignment y) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G x
        (rule1WSplitSelected model G x w assignment y)
        (rule1WSplitSelected model G x w assignment y)
        (fun _i hi => hi))

/-- The `Y`-meeting slice of `W` observes only latents of its own ancestors
in `G_{\overline{X}}`. -/
theorem agreesOn_rule1WSplitUnselected_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y)))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselected model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselected model G x w assignment y))
      (rule1WSplitUnselected model G x w assignment y) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G x
        (rule1WSplitUnselected model G x w assignment y) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G x
        (rule1WSplitUnselected model G x w assignment y)
        (rule1WSplitUnselected model G x w assignment y)
        (fun _i hi => hi))

/-- By construction, the selected slice of `W` does not meet the `Y` core. -/
theorem rule1WSplitSelected_not_meet_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hi : rule1WSplitSelected model G x w assignment y i = true) :
    rule1WVertexMeetsCore model G x w assignment y i = false :=
  rule1WSplit_disjoint model G x w assignment y i hi

/-- A `W` vertex incident to a core-relevant latent, and still free under
`do(X)`, meets that core. -/
theorem rule1WVertexMeetsCore_of_incident
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (other : NodeSet S)
    (root : Fin model.latent.count) {i : Fin S.count}
    (hw : w i = true)
    (hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        i = none)
    (hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) other) root =
        true)
    (hinc : model.latent.incident root i = true) :
    rule1WVertexMeetsCore model G x w assignment other i = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · exact Bool.and_eq_true_iff.mpr
      ⟨hw, Option.isNone_iff_eq_none.mpr hfree⟩
  · exact finAny_eq_true_of _ root
      (Bool.and_eq_true_iff.mpr ⟨hcore, hinc⟩)

/-- A selected `W` vertex cannot carry a latent of the `Y` core. -/
theorem rule1WSplitSelected_not_incident_y_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    (root : Fin model.latent.count) {i : Fin S.count}
    (hi : rule1WSplitSelected model G x w assignment y i = true)
    (hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        i = none)
    (hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true)
    (hinc : model.latent.incident root i = true) :
    False := by
  have hw : w i = true :=
    NodeSet.diff_subset_left w
      (rule1WSplitUnselected model G x w assignment y) i hi
  have hmeet :=
    rule1WVertexMeetsCore_of_incident model G x w assignment y root hw hfree
      hcore hinc
  have hnot :=
    rule1WSplitSelected_not_meet_y model G x w assignment y hi
  simp [hmeet] at hnot

/-- If a `Y`-core latent is relevant to the ancestors of the selected slice
under `do(X)`, its `do(X)`-free child in that ancestral set cannot lie in
the selected slice. -/
theorem rule1WSplitSelected_y_core_child_not_selected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (root : Fin model.latent.count)
    (hrel : model.latentRelevantUnder
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelected model G x w assignment y)) root = true)
    (hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true) :
    Exists fun child : Fin S.count =>
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y) child = true ∧
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          child = none ∧
        model.latent.incident root child = true ∧
          rule1WSplitSelected model G x w assignment y child = false := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext j
    simp [rule1Right, Kernel.intervention]
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelected model G x w assignment y))
      root).mp hrel with ⟨child, hanc, hfreeR, hinc⟩
  have hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        child = none := by
    simpa [hinter] using hfreeR
  have hnotSel : rule1WSplitSelected model G x w assignment y child = false := by
    cases hsel : rule1WSplitSelected model G x w assignment y child with
    | false =>
        rfl
    | true =>
        exact (rule1WSplitSelected_not_incident_y_core model G x w assignment
          y root hsel hfree hcore hinc).elim
  exact ⟨child, hanc, hfree, hinc, hnotSel⟩

/-- A `W` vertex that is not in the selected slice meets the `Y` core. -/
theorem rule1WSplit_mem_w_of_not_selected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hw : w i = true)
    (hnot : rule1WSplitSelected model G x w assignment y i = false) :
    rule1WSplitUnselected model G x w assignment y i = true := by
  have hdiff :
      (w i &&
        !(rule1WSplitUnselected model G x w assignment y i)) = false := by
    simpa [rule1WSplitSelected, NodeSet.diff] using hnot
  simp [hw] at hdiff
  cases hY : rule1WSplitUnselected model G x w assignment y i with
  | true =>
      rfl
  | false =>
      simp [hY] at hdiff

/-- Overlap of the selected-slice ancestors with the open `Y` core. -/
def rule1WSplitSelectedMeetsYCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y)) root)

/-- A latent of the `Y`-meeting slice that is not a `Y`-core latent. -/
def rule1WSplitUnselectedMeetsNotYCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y)) root &&
      !(model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root))

/-- Overlap of the `Y`-meeting-slice ancestors with the open `Z` core. -/
def rule1WSplitUnselectedMeetsZCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root &&
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y)) root)

/-- A latent relevant to both slices of `W` under `do(X)`. -/
def rule1WSplitAncestralLatentsOverlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y)) root &&
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y)) root)

/-- Unselected coordinates of the two-block split: the open `Y` core
together with every ancestral latent of the `Y`-meeting slice. Extra
`W`-only latents stay with `Y`, which is the most general product that
still places `Z` and the complementary slice on the selected side. -/
def rule1WSplitYBlockLatents
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    Fin model.latent.count -> Bool :=
  fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root ||
      model.latentRelevantUnder
        ((rule1Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y)) root

/-- If no `Y`-meeting vertex ancestors the selected slice, and every
`do(X)`-free ancestor of that slice still lies in `W`, then the selected
slice cannot share a latent with the open `Y` core. -/
theorem rule1WSplitSelectedMeetsYCore_eq_false_of
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hnoUnselectedAncestor : forall i,
      rule1WSplitUnselected model G x w assignment y i = true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelected model G x w assignment y) i = false)
    (hFreeAncestorInW : forall i,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y) i = true ->
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment i = none ->
          w i = true)) :
    rule1WSplitSelectedMeetsYCore model G x y z w assignment = false := by
  cases hmeet : rule1WSplitSelectedMeetsYCore model G x y z w assignment with
  | false =>
      rfl
  | true =>
      rcases (finAny_eq_true_iff _).mp (by simpa [rule1WSplitSelectedMeetsYCore]
          using hmeet) with ⟨root, hparts⟩
      rcases Bool.and_eq_true_iff.mp hparts with ⟨hcore, hrel⟩
      rcases rule1WSplitSelected_y_core_child_not_selected model G x y z w
          assignment root hrel hcore with
        ⟨child, hanc, hfree, _hinc, hnotSel⟩
      have hw : w child = true :=
        hFreeAncestorInW child hanc hfree
      have hunsel :=
        rule1WSplit_mem_w_of_not_selected model G x w assignment y hw hnotSel
      have hnotAnc := hnoUnselectedAncestor child hunsel
      simp [hanc] at hnotAnc

/-- A `W` vertex that is not in the `Y`-meeting slice is selected. -/
theorem rule1WSplit_mem_w_of_not_unselected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment) (y : NodeSet S)
    {i : Fin S.count}
    (hw : w i = true)
    (hnot : rule1WSplitUnselected model G x w assignment y i = false) :
    rule1WSplitSelected model G x w assignment y i = true := by
  simp [rule1WSplitSelected, NodeSet.diff, hw, hnot]

/-- A `Y`-meeting `W` vertex cannot carry a latent of the `Z` core. -/
theorem rule1WSplitUnselected_not_incident_z_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (root : Fin model.latent.count) {i : Fin S.count}
    (hi : rule1WSplitUnselected model G x w assignment y i = true)
    (hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        i = none)
    (hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true)
    (hinc : model.latent.incident root i = true) :
    False := by
  have hw : w i = true :=
    rule1WVertexMeetsCore_subset_w model G x w assignment y i hi
  have hmeetZ :=
    rule1WVertexMeetsCore_of_incident model G x w assignment z root hw hfree
      hcore hinc
  exact rule1WVertexMeetsCore_not_both model G projected x y z w assignment
    separated hmeetZ hi

/-- If a `Z`-core latent is relevant to the ancestors of the `Y`-meeting
slice under `do(X)`, its `do(X)`-free child in that ancestral set cannot
lie in the `Y`-meeting slice. -/
theorem rule1WSplitUnselected_z_core_child_not_unselected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (root : Fin model.latent.count)
    (hrel : model.latentRelevantUnder
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselected model G x w assignment y)) root = true)
    (hcore : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true) :
    Exists fun child : Fin S.count =>
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y) child = true ∧
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          child = none ∧
        model.latent.incident root child = true ∧
          rule1WSplitUnselected model G x w assignment y child = false := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext j
    simp [rule1Right, Kernel.intervention]
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselected model G x w assignment y))
      root).mp hrel with ⟨child, hanc, hfreeR, hinc⟩
  have hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        child = none := by
    simpa [hinter] using hfreeR
  have hnotUnsel :
      rule1WSplitUnselected model G x w assignment y child = false := by
    cases hsel : rule1WSplitUnselected model G x w assignment y child with
    | false =>
        rfl
    | true =>
        exact (rule1WSplitUnselected_not_incident_z_core model G projected
          x y z w assignment separated root hsel hfree hcore hinc).elim
  exact ⟨child, hanc, hfree, hinc, hnotUnsel⟩

/-- If no selected vertex ancestors the `Y`-meeting slice, and every
`do(X)`-free ancestor of that slice still lies in `W`, then the
`Y`-meeting slice cannot share a latent with the open `Z` core. -/
theorem rule1WSplitUnselectedMeetsZCore_eq_false_of
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hnoSelectedAncestor : forall i,
      rule1WSplitSelected model G x w assignment y i = true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselected model G x w assignment y) i = false)
    (hFreeAncestorInW : forall i,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y) i = true ->
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment i = none ->
          w i = true)) :
    rule1WSplitUnselectedMeetsZCore model G x y z w assignment = false := by
  cases hmeet : rule1WSplitUnselectedMeetsZCore model G x y z w assignment with
  | false =>
      rfl
  | true =>
      rcases (finAny_eq_true_iff _).mp
          (by simpa [rule1WSplitUnselectedMeetsZCore] using hmeet) with
        ⟨root, hparts⟩
      rcases Bool.and_eq_true_iff.mp hparts with ⟨hcore, hrel⟩
      rcases rule1WSplitUnselected_z_core_child_not_unselected model G
          projected x y z w assignment separated root hrel hcore with
        ⟨child, hanc, hfree, _hinc, hnotUnsel⟩
      have hw : w child = true :=
        hFreeAncestorInW child hanc hfree
      have hsel :=
        rule1WSplit_mem_w_of_not_unselected model G x w assignment y hw
          hnotUnsel
      have hnotAnc := hnoSelectedAncestor child hsel
      simp [hanc] at hnotAnc

/-- A shared ancestral latent of the two `W` slices unpacks as a pair of
`do(X)`-free children, one in each ancestral set. -/
theorem rule1WSplitAncestralLatentsOverlap_unpack
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap :
      rule1WSplitAncestralLatentsOverlap model G x y z w assignment = true) :
    Exists fun root : Fin model.latent.count =>
      Exists fun childSel : Fin S.count =>
        Exists fun childUnsel : Fin S.count =>
          FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitSelected model G x w assignment y) childSel =
            true ∧
            FiniteLatentSCM.ancestralInBar G x
                (rule1WSplitUnselected model G x w assignment y)
                childUnsel = true ∧
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                  assignment) childSel = none ∧
                ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                    assignment) childUnsel = none ∧
                  model.latent.incident root childSel = true ∧
                    model.latent.incident root childUnsel = true := by
  rcases (finAny_eq_true_iff _).mp
      (by simpa [rule1WSplitAncestralLatentsOverlap] using hoverlap) with
    ⟨root, hparts⟩
  rcases Bool.and_eq_true_iff.mp hparts with ⟨hSel, hUnsel⟩
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext j
    simp [rule1Right, Kernel.intervention]
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitSelected model G x w assignment y))
      root).mp hSel with ⟨childSel, hancS, hfreeSR, hincS⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((rule1Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x
        (rule1WSplitUnselected model G x w assignment y))
      root).mp hUnsel with ⟨childUnsel, hancU, hfreeUR, hincU⟩
  refine ⟨root, childSel, childUnsel, hancS, hancU, ?_, ?_, hincS, hincU⟩
  · simpa [hinter] using hfreeSR
  · simpa [hinter] using hfreeUR

/-- Under the same no-cross-ancestry hypotheses used to keep each slice off
the opposite core, a shared latent cannot have the same `W` child in both
ancestral sets. Distinct children remain the bidirected-middle case. -/
theorem rule1WSplitAncestralLatentsOverlap_same_child_false_of
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y _z w : NodeSet S) (assignment : S.Assignment)
    (hnoUnselectedAncestor : forall i,
      rule1WSplitUnselected model G x w assignment y i = true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelected model G x w assignment y) i = false)
    (hnoSelectedAncestor : forall i,
      rule1WSplitSelected model G x w assignment y i = true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselected model G x w assignment y) i = false)
    (hFreeAncestorInW : forall i,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y) i = true ->
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment i = none ->
          w i = true))
    {child : Fin S.count}
    (hancS : FiniteLatentSCM.ancestralInBar G x
      (rule1WSplitSelected model G x w assignment y) child = true)
    (hancU : FiniteLatentSCM.ancestralInBar G x
      (rule1WSplitUnselected model G x w assignment y) child = true)
    (hfree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        child = none) :
    False := by
  have hw : w child = true :=
    hFreeAncestorInW child hancS hfree
  cases hY : rule1WSplitUnselected model G x w assignment y child with
  | true =>
      have hnot := hnoUnselectedAncestor child hY
      simp [hancS] at hnot
  | false =>
      have hsel :=
        rule1WSplit_mem_w_of_not_unselected model G x w assignment y hw hY
      have hnot := hnoSelectedAncestor child hsel
      simp [hancU] at hnot

/-- Distinct `do(X)`-free children of a shared ancestral latent are a
projected bidirected edge. -/
theorem rule1WSplitAncestralLatentsOverlap_bidirected_of_ne
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (root : Fin model.latent.count) {childSel childUnsel : Fin S.count}
    (hne : childSel ≠ childUnsel)
    (hincS : model.latent.incident root childSel = true)
    (hincU : model.latent.incident root childUnsel = true) :
    G.bidirected childSel childUnsel = true :=
  FiniteLatentSCM.bidirected_eq_true_of_shared_latent model G projected
    root childSel childUnsel hne hincS hincU

/-- Distinct `W` children of a shared ancestral latent, each meeting one
open core, are two bound colliders joined by a bidirected middle edge. -/
theorem rule1WSplitAncestralLatentsOverlap_distinct_bound_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (root : Fin model.latent.count) {childSel childUnsel : Fin S.count}
    (hne : childSel ≠ childUnsel)
    (hincS : model.latent.incident root childSel = true)
    (hincU : model.latent.incident root childUnsel = true)
    (hmeetZ : rule1WVertexMeetsCore model G x w assignment z childSel = true)
    (hmeetY : rule1WVertexMeetsCore model G x w assignment y childUnsel =
      true) :
    False := by
  have hZparts :
      (w childSel &&
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment childSel).isNone) = true ∧
        finAny model.latent.count (fun r =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
              r &&
            model.latent.incident r childSel) = true := by
    simpa [rule1WVertexMeetsCore] using hmeetZ
  have hYparts :
      (w childUnsel &&
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment childUnsel).isNone) = true ∧
        finAny model.latent.count (fun r =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
              r &&
            model.latent.incident r childUnsel) = true := by
    simpa [rule1WVertexMeetsCore] using hmeetY
  have hwS : w childSel = true :=
    (Bool.and_eq_true_iff.mp hZparts.1).1
  have hwU : w childUnsel = true :=
    (Bool.and_eq_true_iff.mp hYparts.1).1
  have hwZXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        childSel = none :=
    Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hZparts.1).2
  have hwYXFree :
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        childUnsel = none :=
    Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hYparts.1).2
  have hwZBound :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) childSel =
        some (assignment childSel) := by
    have hact : NodeSet.union x w childSel = true := by
      simp [NodeSet.union, hwS]
    simp [Kernel.intervention, hact]
  have hwYBound :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) childUnsel =
        some (assignment childUnsel) := by
    have hact : NodeSet.union x w childUnsel = true := by
      simp [NodeSet.union, hwU]
    simp [Kernel.intervention, hact]
  rcases (finAny_eq_true_iff _).mp hZparts.2 with ⟨rootZ, hrootZ⟩
  rcases Bool.and_eq_true_iff.mp hrootZ with ⟨hZcore, hwZInc⟩
  rcases (finAny_eq_true_iff _).mp hYparts.2 with ⟨rootY, hrootY⟩
  rcases Bool.and_eq_true_iff.mp hrootY with ⟨hYcore, hwYInc⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
      rootZ).mp hZcore with ⟨zChild, hzSel, hzFree, hzInc⟩
  rcases (model.latentRelevantUnder_eq_true_iff
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
      rootY).mp hYcore with ⟨yChild, hySel, hyFree, hyInc⟩
  have hedgeMid :=
    rule1WSplitAncestralLatentsOverlap_bidirected_of_ne model G projected
      root hne hincS hincU
  exact rule1WMeets_distinct_bound_mid_hedge_false model G projected x y z w
    assignment separated rootZ rootY hzSel hzFree hzInc hySel hyFree hyInc
    hwZInc hwYInc hwZBound hwYBound hwZXFree hwYXFree hedgeMid

/--
The closed slices share no ancestral latent once a shared child is already
in the `Y` block or is a `Y`-side seed, and distinct children that meet
the two open cores are a bidirected middle hedge.
-/
theorem rule1WSplitClosedAncestralLatentsOverlap_eq_false_of
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hSame : forall child,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y) child =
        true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselectedClosed model G x w assignment y) child =
          true ->
          (rule1WSplitUnselectedClosed model G x w assignment y child ||
            rule1WYSideSeed model G x w assignment y child) = true)
    (hDistinct : forall childSel childUnsel,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y) childSel =
        true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselectedClosed model G x w assignment y)
            childUnsel = true ->
          childSel ≠ childUnsel ->
            (rule1WVertexMeetsCore model G x w assignment z childSel &&
              rule1WVertexMeetsCore model G x w assignment y childUnsel) =
              true) :
    rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
      false := by
  cases hoverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment with
  | false =>
      rfl
  | true =>
      rcases rule1WSplitClosedAncestralLatentsOverlap_unpack model G x y z w
          assignment hoverlap with
        ⟨root, childSel, childUnsel, hancS, hancU, _hfreeS, _hfreeU, hincS,
          hincU⟩
      if hEq : childSel = childUnsel then
        subst childUnsel
        exact (rule1WSplitClosedAncestralLatentsOverlap_same_child_false_of
          model G x w assignment y hancS (hSame childSel hancS hancU)).elim
      else
        have hmeets := hDistinct childSel childUnsel hancS hancU hEq
        have hparts := Bool.and_eq_true_iff.mp hmeets
        exact (rule1WSplitAncestralLatentsOverlap_distinct_bound_false
          model G projected x y z w assignment separated root hEq hincS
          hincU hparts.1 hparts.2).elim

/-- If neither slice ancestors the other, free ancestors still lie in `W`,
and a distinct selected-side child meets the `Z` core, the two slices
share no ancestral latent. -/
theorem rule1WSplitAncestralLatentsOverlap_eq_false_of
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hnoUnselectedAncestor : forall i,
      rule1WSplitUnselected model G x w assignment y i = true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelected model G x w assignment y) i = false)
    (hnoSelectedAncestor : forall i,
      rule1WSplitSelected model G x w assignment y i = true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselected model G x w assignment y) i = false)
    (hFreeSelectedInW : forall i,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y) i = true ->
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment i = none ->
          w i = true))
    (hFreeUnselectedInW : forall i,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselected model G x w assignment y) i = true ->
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment i = none ->
          w i = true))
    (hDistinctMeetsZ : forall childSel childUnsel,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelected model G x w assignment y) childSel = true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselected model G x w assignment y) childUnsel =
          true ->
          childSel ≠ childUnsel ->
            rule1WVertexMeetsCore model G x w assignment z childSel =
              true) :
    rule1WSplitAncestralLatentsOverlap model G x y z w assignment = false := by
  cases hoverlap :
      rule1WSplitAncestralLatentsOverlap model G x y z w assignment with
  | false =>
      rfl
  | true =>
      rcases rule1WSplitAncestralLatentsOverlap_unpack model G x y z w
          assignment hoverlap with
        ⟨root, childSel, childUnsel, hancS, hancU, hfreeS, hfreeU, hincS,
          hincU⟩
      if hEq : childSel = childUnsel then
        subst childUnsel
        exact (rule1WSplitAncestralLatentsOverlap_same_child_false_of
          model G x y z w assignment hnoUnselectedAncestor
          hnoSelectedAncestor hFreeSelectedInW hancS hancU hfreeS).elim
      else
        have hwU : w childUnsel = true :=
          hFreeUnselectedInW childUnsel hancU hfreeU
        have hmeetY :
            rule1WVertexMeetsCore model G x w assignment y childUnsel =
              true := by
          cases hY :
              rule1WSplitUnselected model G x w assignment y childUnsel with
          | true =>
              exact hY
          | false =>
              have hsel :=
                rule1WSplit_mem_w_of_not_unselected model G x w assignment
                  y hwU hY
              have hnot := hnoSelectedAncestor childUnsel hsel
              simp [hancU] at hnot
        have hmeetZ :=
          hDistinctMeetsZ childSel childUnsel hancS hancU hEq
        exact (rule1WSplitAncestralLatentsOverlap_distinct_bound_false
          model G projected x y z w assignment separated root hEq hincS
          hincU hmeetZ hmeetY).elim

/-- If no latent of the open `Z` core is relevant to `W` under `do(X)`, then
`W` is a function of the complementary coordinates. -/
theorem agreesOn_rule1W_dependsOnUnselected_of_avoids_z
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule1WMeetsUnionAncestral model G x w assignment z = false) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z))
      (fun roots =>
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have wDepends :=
    agreesOn_rule1W_dependsOnSelected model G x y z w assignment
  have hall :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root &&
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x w) root)).mp
      (by simpa [rule1WMeetsUnionAncestral] using havoid)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x w) root = true ->
          (!model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
              root) = true := by
    intro root hr
    have hroot := hall root
    have hr' : model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x w) root = true := by
      simpa [hinter] using hr
    cases hz :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root with
    | false =>
        rfl
    | true =>
        simp [hz, hr'] at hroot
  have wCompl :=
    CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots))
      hsub wDepends
  exact CanonicalFactorization.DependsOnUnselected.of_compl_selected
    model.latent.count model.latent.Value _ _ wCompl

/-- If no latent of the open `Y` core is relevant to `W` under `do(X)`, then
`W` is a function of the complementary coordinates. -/
theorem agreesOn_rule1W_dependsOnSelected_of_avoids_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule1WMeetsUnionAncestral model G x w assignment y = false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root))
      (fun roots =>
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have wDepends :=
    agreesOn_rule1W_dependsOnSelected model G x y z w assignment
  have hall :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x w) root)).mp
      (by simpa [rule1WMeetsUnionAncestral] using havoid)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x w) root = true ->
          (!model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
              root) = true := by
    intro root hr
    have hroot := hall root
    have hr' : model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x w) root = true := by
      simpa [hinter] using hr
    cases hy :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root with
    | false =>
        rfl
    | true =>
        simp [hy, hr'] at hroot
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    hsub wDepends

/-- The selected slice of `W` depends only on the complement of the open
`Y` core, once it shares no latent with that core. -/
theorem agreesOn_rule1WSplitSelected_dependsOnNotYCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (havoid :
      rule1WSplitSelectedMeetsYCore model G x y z w assignment = false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitSelected model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hall :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelected model G x w assignment y)) root)).mp
      (by simpa [rule1WSplitSelectedMeetsYCore] using havoid)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitSelected model G x w assignment y)) root = true ->
          (!model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
              root) = true := by
    intro root hr
    have hroot := hall root
    cases hy :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root with
    | false =>
        rfl
    | true =>
        simp [hy, hr] at hroot
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitSelected model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    hsub
    (agreesOn_rule1WSplitSelected_dependsOnAncestral model G x y z w
      assignment)

/-- The `Y`-meeting slice of `W` depends only on the open `Y` core, once
every one of its ancestral latents is a core latent. -/
theorem agreesOn_rule1WSplitUnselected_dependsOnYCore
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hinside :
      rule1WSplitUnselectedMeetsNotYCore model G x y z w assignment = false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselected model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hall :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselected model G x w assignment y)) root &&
        !(model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
            root))).mp
      (by simpa [rule1WSplitUnselectedMeetsNotYCore] using hinside)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitUnselected model G x w assignment y)) root = true ->
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
              root = true := by
    intro root hr
    have hroot := hall root
    cases hy :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root with
    | true =>
        rfl
    | false =>
        simp [hy, hr] at hroot
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitUnselected model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    hsub
    (agreesOn_rule1WSplitUnselected_dependsOnAncestral model G x y z w
      assignment)

/-- The selected slice depends only on the complement of the `Y` block. -/
theorem agreesOn_rule1WSplitSelected_dependsOnNotYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hY :
      rule1WSplitSelectedMeetsYCore model G x y z w assignment = false)
    (hOverlap :
      rule1WSplitAncestralLatentsOverlap model G x y z w assignment = false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitSelected model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hallY :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelected model G x w assignment y)) root)).mp
      (by simpa [rule1WSplitSelectedMeetsYCore] using hY)
  have hallO :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelected model G x w assignment y)) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselected model G x w assignment y)) root)).mp
      (by simpa [rule1WSplitAncestralLatentsOverlap] using hOverlap)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitSelected model G x w assignment y)) root = true ->
          (!(rule1WSplitYBlockLatents model G x y z w assignment root)) =
            true := by
    intro root hr
    have hYroot := hallY root
    have hOroot := hallO root
    cases hy :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root with
    | true =>
        simp [hy, hr] at hYroot
    | false =>
        cases hu :
            model.latentRelevantUnder
              ((rule1Right x y z w).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G x
                (rule1WSplitUnselected model G x w assignment y)) root with
        | true =>
            simp [hr, hu] at hOroot
        | false =>
            simp [rule1WSplitYBlockLatents, hy, hu]
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitSelected model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    hsub
    (agreesOn_rule1WSplitSelected_dependsOnAncestral model G x y z w
      assignment)

/-- Under `do(X ∪ W)`, `Z` depends only on the complement of the `Y` block
once the `Y`-meeting slice shares no latent with the open `Z` core. -/
theorem agreesOn_rule1Z_dependsOnNotYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hUnselZ :
      rule1WSplitUnselectedMeetsZCore model G x y z w assignment = false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn z assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)) := by
  have hsep :=
    FiniteLatentSCM.rule1Ancestral_latentSeparated_union model G projected
      x y z w assignment separated
  have hallZ :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselected model G x w assignment y)) root)).mp
      (by simpa [rule1WSplitUnselectedMeetsZCore] using hUnselZ)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
            root = true ->
          (!(rule1WSplitYBlockLatents model G x y z w assignment root)) =
            true := by
    intro root hz
    have hy := hsep root hz
    have hZroot := hallZ root
    cases hy' :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root with
    | true =>
        simp [hy'] at hy
    | false =>
        cases hu :
            model.latentRelevantUnder
              ((rule1Right x y z w).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G x
                (rule1WSplitUnselected model G x w assignment y)) root with
        | true =>
            simp [hz, hu] at hZroot
        | false =>
            simp [rule1WSplitYBlockLatents, hy', hu]
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn z assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots))
    hsub
    (agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment)

/-- `Y` ignores the complement of the `Y` block. -/
theorem agreesOn_rule1Y_dependsOnYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)) := by
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
            root = true ->
          rule1WSplitYBlockLatents model G x y z w assignment root = true := by
    intro root hr
    simp [rule1WSplitYBlockLatents, hr]
  exact CanonicalFactorization.DependsOnUnselected.of_selected_compl
    model.latent.count model.latent.Value
    (rule1WSplitYBlockLatents model G x y z w assignment)
    (fun roots =>
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots))
    (CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots))
      hsub
      (agreesOn_rule1Y_dependsOnSelected_union model G x y z w assignment))

/-- The `Y`-meeting slice ignores the complement of the `Y` block. -/
theorem agreesOn_rule1WSplitUnselected_dependsOnYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselected model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitUnselected model G x w assignment y))
            root = true ->
          rule1WSplitYBlockLatents model G x y z w assignment root = true := by
    intro root hr
    simp [rule1WSplitYBlockLatents, hr]
  exact CanonicalFactorization.DependsOnUnselected.of_selected_compl
    model.latent.count model.latent.Value
    (rule1WSplitYBlockLatents model G x y z w assignment)
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitUnselected model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    (CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselected model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots))
      hsub
      (agreesOn_rule1WSplitUnselected_dependsOnAncestral model G x y z w
        assignment))


end Kernel
end Causality
end Thesis
