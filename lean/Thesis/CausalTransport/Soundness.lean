import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.DSeparationCorrectness

namespace Thesis
namespace Causality

open Probability

/-!
Constructive ingredients for inhabiting the finite-source soundness interface.

This module proves the graph-independent probability-algebra leaves first.
The d-separation/global-Markov layer and the three causal rules are kept
separate so that each stage can be audited independently.  Empty-`W` rule 1
and empty-`W` rule 2 now inhabit their product-partition witnesses from
path d-separation and a projected graph: rule 2 uses open ancestral cores
in `G_{\overline{X}\underline{Z}}` so a directed `Z → Y` edge does not
identify the two cores.  For the general global-Markov step,
`ObservedGraph.moralLeftSide` computes the left component of the open
ancestral moral graph, and `FiniteLatentSCM.latentMoralLeftSide` lifts that
separator to the concrete latent coordinates of any compatible model;
shared-root incidence is proved unable to cross the partition.  Generic
agreement cylinders over left and right open ancestral regions are then
routed to complementary halves of the canonical independent latent product.
For rule 3, `Rule3GivenWFactorization` records the more delicate conditioned
case: a `W` factor shared with `Y` is retained on the selected roots, while
only the intervention-sensitive residual factors are separated.  This avoids
the false general requirement that conditioned `W` share no latent root with
`Y`.
-/

namespace FiniteLatentSCM

private instance factorizationAssignmentDecidableEq
    (model : FiniteLatentSCM S) : DecidableEq model.latent.Assignment :=
  FiniteProduct.assignmentDecidableEq model.latent.count
    model.latent.Value model.latent.valueDecidableEq

private def factorizationAssignments (model : FiniteLatentSCM S) :
    List model.latent.Assignment := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  exact deduplicate (FiniteProduct.enumeration model.latent.count
    model.latent.Value model.latent.valueEnumeration)

private theorem factorizationAssignments_complete (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    assignment ∈ factorizationAssignments model := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  rw [factorizationAssignments, mem_deduplicate]
  exact FiniteProduct.enumeration_complete model.latent.count
    model.latent.Value model.latent.valueEnumeration
      model.latent.value_complete assignment

private theorem factorizationAssignments_nodup (model : FiniteLatentSCM S) :
    (factorizationAssignments model).Nodup := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  exact deduplicate_nodup _

private def assignmentEvents (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    (root : Fin model.latent.count) -> model.latent.Value root -> Bool :=
  fun root value => decide (value = assignment root)

private theorem rectangular_assignmentEvents (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    model.latent.rectangularEvent (assignmentEvents model assignment) =
      FiniteProbRecord.singletonEvent assignment := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  funext candidate
  apply Bool.eq_iff_iff.mpr
  change
    FiniteProduct.rectangularEvent model.latent.count model.latent.Value
        (assignmentEvents model assignment) candidate = true <->
      FiniteProbRecord.singletonEvent assignment candidate = true
  rw [FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro equal
    have same : candidate = assignment := by
      funext root
      exact of_decide_eq_true (equal root)
    simp [FiniteProbRecord.singletonEvent, same]
  · intro equal root
    have same : candidate = assignment := by
      simpa [FiniteProbRecord.singletonEvent] using equal
    subst candidate
    simp [assignmentEvents]

/--
The rectangular-event product law determines the complete latent prior, not
only its rectangular marginals.  Consequently all subsequent finite
factorization arguments may work with the canonical dependent product record.
-/
theorem prior_probVal_productRecord (model : FiniteLatentSCM S)
    (event : model.latent.Assignment -> Bool) :
    QProb.Equiv (model.prior.probVal event)
      ((FiniteProduct.record model.latent.count model.latent.Value
        model.factor).probVal event) := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  apply FiniteProbRecord.probVal_extensional_of_singletons
    model.prior
    (FiniteProduct.record model.latent.count model.latent.Value model.factor)
    (factorizationAssignments model)
    (factorizationAssignments_nodup model)
    (factorizationAssignments_complete model)
  intro assignment
  let events := assignmentEvents model assignment
  have supplied := model.product_law events
  have canonical := FiniteProduct.record_rectangular_probVal
    model.latent.count model.latent.Value model.factor events
  have eventEq : FiniteProduct.rectangularEvent model.latent.count
      model.latent.Value events =
        FiniteProbRecord.singletonEvent assignment := by
    simpa [events, LatentExtension.rectangularEvent] using
      rectangular_assignmentEvents model assignment
  change QProb.Equiv
    (model.prior.probVal
      (FiniteProduct.rectangularEvent model.latent.count
        model.latent.Value events)) _ at supplied
  rw [eventEq] at supplied canonical
  exact QProb.equiv_trans supplied (QProb.equiv_symm canonical)

theorem interventionalValue_productRecord (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) :
    QProb.Equiv (model.interventionalValue intervention event)
      ((FiniteProduct.record model.latent.count model.latent.Value
        model.factor).probVal
          (fun roots => event (model.evalUnder intervention roots))) :=
  QProb.equiv_trans (model.interventionalValue_eq intervention event)
    (model.prior_probVal_productRecord
      (fun roots => event (model.evalUnder intervention roots)))

theorem observationalValue_productRecord (model : FiniteLatentSCM S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (model.observationalValue event)
      ((FiniteProduct.record model.latent.count model.latent.Value
        model.factor).probVal (fun roots => event (model.eval roots))) :=
  QProb.equiv_trans (model.observationalValue_eq event)
    (model.prior_probVal_productRecord
      (fun roots => event (model.eval roots)))

/-- A latent root is relevant to a node set under an intervention when it is
incident to at least one non-intervened node in that set. -/
def latentRelevantUnder (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S)
    (root : Fin model.latent.count) : Bool :=
  finAny S.count (fun child =>
    nodes child && (intervention child).isNone &&
      model.latent.incident root child)

theorem latentRelevantUnder_eq_true_iff (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (root : Fin model.latent.count) :
    model.latentRelevantUnder intervention nodes root = true <->
      Exists fun child : Fin S.count =>
        nodes child = true /\ intervention child = none /\
          model.latent.incident root child = true := by
  rw [latentRelevantUnder, finAny_eq_true_iff]
  constructor
  · rintro ⟨child, holds⟩
    rcases Bool.and_eq_true_iff.mp holds with ⟨selectedAndFree, incident⟩
    rcases Bool.and_eq_true_iff.mp selectedAndFree with
      ⟨selected, notIntervened⟩
    exact ⟨child, selected, Option.isNone_iff_eq_none.mp notIntervened,
      incident⟩
  · rintro ⟨child, selected, notIntervened, incident⟩
    refine ⟨child, Bool.and_eq_true_iff.mpr ⟨?_, incident⟩⟩
    exact Bool.and_eq_true_iff.mpr
      ⟨selected, Option.isNone_iff_eq_none.mpr notIntervened⟩

/-- No observed child of the empty selection can witness a latent. -/
theorem latentRelevantUnder_empty (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (root : Fin model.latent.count) :
    model.latentRelevantUnder intervention NodeSet.empty root = false := by
  cases h : model.latentRelevantUnder intervention NodeSet.empty root with
  | false => rfl
  | true =>
      rcases (model.latentRelevantUnder_eq_true_iff intervention
          NodeSet.empty root).mp h with ⟨child, hnodes, _hfree, _hinc⟩
      simp [NodeSet.empty] at hnodes

theorem latentRelevantUnder_of_incident (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (root : Fin model.latent.count)
    (child : Fin S.count) (selected : nodes child = true)
    (notIntervened : intervention child = none)
    (incident : model.latent.incident root child = true) :
    model.latentRelevantUnder intervention nodes root = true := by
  apply finAny_eq_true_of _ child
  simp [selected, notIntervened, incident]

/-- A heavier intervention (fewer free nodes) can only drop latent
relevance. -/
theorem latentRelevantUnder_mono (model : FiniteLatentSCM S)
    {heavier lighter : (i : Fin S.count) -> Option (S.Value i)}
    (nodes : NodeSet S) (root : Fin model.latent.count)
    (freeOfHeavier : forall i, heavier i = none -> lighter i = none)
    (relevant : model.latentRelevantUnder heavier nodes root = true) :
    model.latentRelevantUnder lighter nodes root = true := by
  rcases (model.latentRelevantUnder_eq_true_iff heavier nodes root).mp
      relevant with
    ⟨child, selected, notIntervened, incident⟩
  exact model.latentRelevantUnder_of_incident lighter nodes root child
    selected (freeOfHeavier child notIntervened) incident

/-!
### Lifting the moral separator to concrete latent roots

`ObservedGraph.moralLeftSide` partitions the canonical expanded graph.  A
compatible model can use an arbitrary finite canonical latent extension, so
the soundness proof must transfer that graph partition to the model's actual
latent coordinates.  Shared incidence projects to a bidirected edge; two
free ancestral children of one concrete root are therefore connected through
the corresponding canonical latent-pair vertex and must lie on the same side.
This is the key invariant that the earlier ad-hoc overlap Booleans did not
express.
-/

/-- Two distinct observed children of one concrete latent root are joined by
the projected bidirected graph. -/
theorem bidirected_of_shared_latent
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (root : Fin model.latent.count) {left right : Fin S.count}
    (different : left ≠ right)
    (leftIncident : model.latent.incident root left = true)
    (rightIncident : model.latent.incident root right = true) :
    G.bidirected left right = true := by
  have neq : Nat.beq left.val right.val = false := by
    cases equal : Nat.beq left.val right.val with
    | false => rfl
    | true =>
        exact False.elim
          (different (Fin.ext (Nat.eq_of_beq_eq_true equal)))
  have shared :
      finAny model.latent.count (fun latent =>
        model.latent.incident latent left &&
          model.latent.incident latent right) = true :=
    finAny_eq_true_of _ root
      (Bool.and_eq_true_iff.mpr ⟨leftIncident, rightIncident⟩)
  have modelEdge : model.observedGraph.bidirected left right = true := by
    simp [FiniteLatentSCM.observedGraph, LatentExtension.observedGraph,
      LatentExtension.projectedBidirected, neq, shared]
  rw [projected left right] at modelEdge
  exact modelEdge

/--
Free ancestral children of the same concrete latent root occupy the same
canonical moral side.  The proof walks from the first observed child through
the projected latent-pair vertex to the second; closure of `moralLeftSide`
then works in either direction.
-/
theorem moralLeftSide_eq_of_shared_latent
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (root : Fin model.latent.count) (first second : Fin S.count)
    (firstIncident : model.latent.incident root first = true)
    (secondIncident : model.latent.incident root second = true)
    (firstFree : mutilation.removeIncoming first = false)
    (secondFree : mutilation.removeIncoming second = false)
    (firstAncestor : G.ancestorOf mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      (.observed first) = true)
    (secondAncestor : G.ancestorOf mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      (.observed second) = true)
    (firstOpen : conditioned first = false)
    (secondOpen : conditioned second = false) :
    G.moralLeftSide mutilation left right conditioned (.observed first) =
      G.moralLeftSide mutilation left right conditioned (.observed second) := by
  by_cases same : first = second
  · subst second
    rfl
  · have bidirected := model.bidirected_of_shared_latent G projected
        root same firstIncident secondIncident
    let latent : SeparationNode S := .latentPair first second
    have edgeFirst :
        G.expandedMutilatedEdge mutilation latent (.observed first) = true := by
      have self : finBeq first first = true :=
        (finBeq_eq_true_iff first first).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        firstFree, self]
    have edgeSecond :
        G.expandedMutilatedEdge mutilation latent (.observed second) = true := by
      have self : finBeq second second = true :=
        (finBeq_eq_true_iff second second).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        secondFree, self]
    have latentAncestor : G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) latent = true :=
      G.ancestorOf_prepend mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        edgeFirst firstAncestor
    have firstMoral : G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) conditioned
        (.observed first) latent = true :=
      G.moralOpenEdge_of_ancestral mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) conditioned
        (by simp [ObservedGraph.blockedBy, firstOpen]) (by
          dsimp [latent]
          rfl)
        (G.ancestralMoralEdge_of_adjacent mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          firstAncestor latentAncestor (Or.inr edgeFirst))
    have secondMoral : G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) conditioned
        latent (.observed second) = true :=
      G.moralOpenEdge_of_ancestral mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) conditioned
        (by
          dsimp [latent]
          rfl)
        (by simp [ObservedGraph.blockedBy, secondOpen])
        (G.ancestralMoralEdge_of_adjacent mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          latentAncestor secondAncestor (Or.inl edgeSecond))
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro firstIn
      have latentIn := G.moralLeftSide_closed mutilation
        left right conditioned firstIn firstMoral
      exact G.moralLeftSide_closed mutilation left right conditioned
        latentIn secondMoral
    · intro secondIn
      have latentIn := G.moralLeftSide_closed mutilation left right conditioned
        secondIn (G.moralOpenEdge_symmetric mutilation
          (NodeSet.union left (NodeSet.union right conditioned)) conditioned
          secondMoral)
      exact G.moralLeftSide_closed mutilation left right conditioned
        latentIn (G.moralOpenEdge_symmetric mutilation
          (NodeSet.union left (NodeSet.union right conditioned)) conditioned
          firstMoral)

/-- Concrete latent roots assigned to the left moral side.  Only incident
children that are free, ancestral to the relevant cylinders, and open under
conditioning participate in the test. -/
def latentMoralLeftSide
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (root : Fin model.latent.count) : Bool :=
  finAny S.count (fun child =>
    model.latent.incident root child &&
      !(mutilation.removeIncoming child) &&
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        (.observed child) &&
      !(conditioned child) &&
      G.moralLeftSide mutilation left right conditioned (.observed child))

/-- For every relevant incident child, the concrete latent-root partition is
exactly that child's canonical moral side.  Hence one latent coordinate can
never straddle the separator. -/
theorem latentMoralLeftSide_eq_child
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (root : Fin model.latent.count) (child : Fin S.count)
    (incident : model.latent.incident root child = true)
    (free : mutilation.removeIncoming child = false)
    (ancestor : G.ancestorOf mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      (.observed child) = true)
    (openChild : conditioned child = false) :
    model.latentMoralLeftSide G mutilation left right conditioned root =
      G.moralLeftSide mutilation left right conditioned (.observed child) := by
  cases childSide : G.moralLeftSide mutilation left right conditioned
      (.observed child) with
  | true =>
      apply finAny_eq_true_of _ child
      simp [incident, free, ancestor, openChild, childSide]
  | false =>
      apply (finAny_eq_false_iff _).mpr
      intro other
      cases selected :
          (model.latent.incident root other &&
            !(mutilation.removeIncoming other) &&
            G.ancestorOf mutilation
              (NodeSet.union left (NodeSet.union right conditioned))
              (.observed other) &&
            !(conditioned other) &&
            G.moralLeftSide mutilation left right conditioned
              (.observed other)) with
      | false => rfl
      | true =>
          have parts := Bool.and_eq_true_iff.mp selected
          have partsA := Bool.and_eq_true_iff.mp parts.1
          have partsB := Bool.and_eq_true_iff.mp partsA.1
          have partsC := Bool.and_eq_true_iff.mp partsB.1
          have otherIncident : model.latent.incident root other = true :=
            partsC.1
          have otherFree : mutilation.removeIncoming other = false := by
            simpa using partsC.2
          have otherAncestor : G.ancestorOf mutilation
              (NodeSet.union left (NodeSet.union right conditioned))
              (.observed other) = true := partsB.2
          have otherOpen : conditioned other = false := by
            simpa using partsA.2
          have otherSide : G.moralLeftSide mutilation left right conditioned
              (.observed other) = true := parts.2
          have equalSides := moralLeftSide_eq_of_shared_latent
            model G projected mutilation left right conditioned root child other
            incident otherIncident free otherFree ancestor otherAncestor
            openChild otherOpen
          rw [childSide, otherSide] at equalSides
          contradiction

/-- Every latent root relevant to a node family contained in the left open
ancestral moral component is selected by `latentMoralLeftSide`.

The hypotheses are deliberately stated as four small containment facts.  A
later do-rule proof may choose whichever backward-closed region is convenient
for evaluation, while this lemma records only the properties of its free
vertices that the moral separator needs. -/
theorem latentMoralLeftSide_eq_true_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (mutilation : GraphMutilation S)
    (left right conditioned nodes : NodeSet S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (free : forall child, intervention child = none ->
      mutilation.removeIncoming child = false)
    (ancestral : NodeSet.Subset nodes (fun child =>
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        (.observed child)))
    (openNodes : NodeSet.Subset nodes (fun child => !conditioned child))
    (onLeft : NodeSet.Subset nodes (fun child =>
      G.moralLeftSide mutilation left right conditioned (.observed child)))
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder intervention nodes root = true) :
    model.latentMoralLeftSide G mutilation left right conditioned root =
      true := by
  rcases (model.latentRelevantUnder_eq_true_iff intervention nodes root).mp
      relevant with
    ⟨child, selected, notIntervened, incident⟩
  have childSide := model.latentMoralLeftSide_eq_child G projected
    mutilation left right conditioned root child incident
    (free child notIntervened) (ancestral child selected)
    (by simpa using openNodes child selected)
  exact childSide.trans (onLeft child selected)

/-- Every latent root relevant to a node family contained in the right open
ancestral moral component is unselected by `latentMoralLeftSide`.

Together with `latentMoralLeftSide_eq_true_of_relevant`, this turns the
canonical graph cut into complementary coordinate families of the model's
actual finite latent product. -/
theorem latentMoralLeftSide_eq_false_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (mutilation : GraphMutilation S)
    (left right conditioned nodes : NodeSet S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (free : forall child, intervention child = none ->
      mutilation.removeIncoming child = false)
    (ancestral : NodeSet.Subset nodes (fun child =>
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        (.observed child)))
    (openNodes : NodeSet.Subset nodes (fun child => !conditioned child))
    (onRight : NodeSet.Subset nodes (fun child =>
      !G.moralLeftSide mutilation left right conditioned (.observed child)))
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder intervention nodes root = true) :
    model.latentMoralLeftSide G mutilation left right conditioned root =
      false := by
  rcases (model.latentRelevantUnder_eq_true_iff intervention nodes root).mp
      relevant with
    ⟨child, selected, notIntervened, incident⟩
  have childSide := model.latentMoralLeftSide_eq_child G projected
    mutilation left right conditioned root child incident
    (free child notIntervened) (ancestral child selected)
    (by simpa using openNodes child selected)
  have rightSide : G.moralLeftSide mutilation left right conditioned
      (.observed child) = false :=
    by simpa using onRight child selected
  exact childSide.trans rightSide

/-- A set contains every non-intervened directed parent of each of its
members. -/
def BackwardClosedUnder (_model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) : Prop :=
  forall parent child,
    nodes child = true -> intervention child = none ->
      S.directed parent child = true -> nodes parent = true

/-- Evaluation on a backward-closed family depends only on the
intervention coordinates inside that family.  Intervening elsewhere
(rule-3 `Z` that does not ancestor `Y`) is invisible. -/
theorem evalNodeUnder_eq_of_intervention_agree_on_closed
    (model : FiniteLatentSCM S)
    (left right : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (roots : model.latent.Assignment)
    (closed : model.BackwardClosedUnder left nodes)
    (agree : forall i, nodes i = true -> left i = right i)
    (child : Fin S.count) (hmem : nodes child = true) :
    model.evalNodeUnder left roots child =
      model.evalNodeUnder right roots child := by
  have hsame := agree child hmem
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [hsame]
  cases hsel : right child with
  | some _value =>
      rfl
  | none =>
      have hleftNone : left child = none := by
        rw [hsame, hsel]
      simp only
      congr 1
      funext parent hedge
      exact model.evalNodeUnder_eq_of_intervention_agree_on_closed
        left right nodes roots closed agree parent
        (closed parent child hmem hleftNone hedge)
termination_by child.val
decreasing_by
  exact S.directed_earlier hedge

theorem evalUnder_eq_on_of_intervention_agree_on_closed
    (model : FiniteLatentSCM S)
    (left right : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (roots : model.latent.Assignment)
    (closed : model.BackwardClosedUnder left nodes)
    (agree : forall i, nodes i = true -> left i = right i)
    (child : Fin S.count) (hmem : nodes child = true) :
    model.evalUnder left roots child =
      model.evalUnder right roots child :=
  model.evalNodeUnder_eq_of_intervention_agree_on_closed
    left right nodes roots closed agree child hmem

/--
Ancestors of a target set in `G_{\overline{X}}` are backward-closed under
`do(X)`: every remaining directed parent of a non-intervened ancestor is
again an ancestor.  Shortest-path bounding on the finite vertex list keeps
the Boolean ancestry search's fuel.
-/
theorem observedAncestorOf_backwardClosedUnder
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (action targets : NodeSet S) (reference : S.Assignment) :
    model.BackwardClosedUnder
      (fun i => if action i then some (reference i) else none)
      (fun i =>
        G.observedAncestorOf (GraphMutilation.bar action) targets i) := by
  intro parent child hchild hnone hedge
  have hact : action child = false := by
    cases h : action child with
    | false =>
        rfl
    | true =>
        simp [h] at hnone
  have hedgeBar :
      G.observedDirectedEdge (GraphMutilation.bar action) parent child =
        true := by
    simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
      NodeSet.empty, hedge, hact]
  have hany :
      (List.ofFn (fun i : Fin S.count => i)).any (fun target =>
        targets target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun i : Fin S.count => i))
            (G.observedDirectedEdge (GraphMutilation.bar action))
            (List.ofFn (fun i : Fin S.count => i)).length child target) =
        true := by
    simpa [ObservedGraph.observedAncestorOf] using hchild
  rcases List.any_eq_true.mp hany with ⟨y, yMem, hy⟩
  have hyParts := Bool.and_eq_true_iff.mp hy
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have bounded :
      FiniteReachability.BoundedWalk
        (G.observedDirectedEdge (GraphMutilation.bar action))
        (List.ofFn (fun i : Fin S.count => i)).length child y :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge (GraphMutilation.bar action))
      finBeq_eq_true_iff complete
      (List.ofFn (fun i : Fin S.count => i)).length child y).mp hyParts.2
  have reachableParent :
      FiniteReachability.Reachable
        (G.observedDirectedEdge (GraphMutilation.bar action)) parent y :=
    FiniteReachability.Reachable.prepend hedgeBar
      (FiniteReachability.Reachable.of_bounded bounded)
  have boundedParent :
      FiniteReachability.BoundedWalk
        (G.observedDirectedEdge (GraphMutilation.bar action))
        (List.ofFn (fun i : Fin S.count => i)).length parent y :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge (GraphMutilation.bar action))
      finBeq_eq_true_iff complete reachableParent
  have hyParent :
      FiniteReachability.within finBeq
        (List.ofFn (fun i : Fin S.count => i))
        (G.observedDirectedEdge (GraphMutilation.bar action))
        (List.ofFn (fun i : Fin S.count => i)).length parent y = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge (GraphMutilation.bar action))
      finBeq_eq_true_iff complete
      (List.ofFn (fun i : Fin S.count => i)).length parent y).mpr
      boundedParent
  have hparent :
      (List.ofFn (fun i : Fin S.count => i)).any (fun target =>
        targets target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun i : Fin S.count => i))
            (G.observedDirectedEdge (GraphMutilation.bar action))
            (List.ofFn (fun i : Fin S.count => i)).length parent target) =
        true :=
    List.any_eq_true.mpr
      ⟨y, yMem, Bool.and_eq_true_iff.mpr ⟨hyParts.1, hyParent⟩⟩
  simpa [ObservedGraph.observedAncestorOf] using hparent

theorem backwardClosedUnder_of_rule1Right
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (targets : NodeSet S) :
    model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment)
      (fun i => G.observedAncestorOf (GraphMutilation.bar x) targets i) := by
  simpa [rule1Right, Kernel.intervention] using
    observedAncestorOf_backwardClosedUnder model G x targets assignment

/-- Every selected vertex is an ancestor of itself. -/
theorem observedAncestorOf_self (G : ObservedGraph S)
    (m : GraphMutilation S) (targets : NodeSet S) {i : Fin S.count}
    (hi : targets i = true) :
    G.observedAncestorOf m targets i = true := by
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun j : Fin S.count => j) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have bounded :
      FiniteReachability.BoundedWalk (G.observedDirectedEdge m)
        (List.ofFn (fun j : Fin S.count => j)).length i i :=
    FiniteReachability.BoundedWalk.refl _ _ _
  have hy :
      FiniteReachability.within finBeq
        (List.ofFn (fun j : Fin S.count => j))
        (G.observedDirectedEdge m)
        (List.ofFn (fun j : Fin S.count => j)).length i i = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (List.ofFn (fun j : Fin S.count => j))
      (G.observedDirectedEdge m) finBeq_eq_true_iff complete
      (List.ofFn (fun j : Fin S.count => j)).length i i).mpr bounded
  have hany :
      (List.ofFn (fun j : Fin S.count => j)).any (fun target =>
        targets target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun j : Fin S.count => j))
            (G.observedDirectedEdge m)
            (List.ofFn (fun j : Fin S.count => j)).length i target) =
        true :=
    List.any_eq_true.mpr
      ⟨i, complete i, Bool.and_eq_true_iff.mpr ⟨hi, hy⟩⟩
  simpa [ObservedGraph.observedAncestorOf] using hany

/-- Ancestry is monotone in the target set. -/
theorem observedAncestorOf_mono (G : ObservedGraph S)
    (m : GraphMutilation S) {targets targets' : NodeSet S}
    (hsub : NodeSet.Subset targets targets') {i : Fin S.count}
    (h : G.observedAncestorOf m targets i = true) :
    G.observedAncestorOf m targets' i = true := by
  have hany :
      (List.ofFn (fun j : Fin S.count => j)).any (fun target =>
        targets target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun j : Fin S.count => j))
            (G.observedDirectedEdge m)
            (List.ofFn (fun j : Fin S.count => j)).length i target) =
        true := by
    simpa [ObservedGraph.observedAncestorOf] using h
  rcases List.any_eq_true.mp hany with ⟨y, yMem, hy⟩
  have hyParts := Bool.and_eq_true_iff.mp hy
  have hany' :
      (List.ofFn (fun j : Fin S.count => j)).any (fun target =>
        targets' target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun j : Fin S.count => j))
            (G.observedDirectedEdge m)
            (List.ofFn (fun j : Fin S.count => j)).length i target) =
        true :=
    List.any_eq_true.mpr
      ⟨y, yMem,
        Bool.and_eq_true_iff.mpr ⟨hsub y hyParts.1, hyParts.2⟩⟩
  simpa [ObservedGraph.observedAncestorOf] using hany'

/-- Directed ancestry of `targets` in `G_{\overline{X}}`. -/
def ancestralInBar (G : ObservedGraph S) (action targets : NodeSet S) :
    NodeSet S :=
  fun i => G.observedAncestorOf (GraphMutilation.bar action) targets i

/-- The empty target set has no ancestors: the Boolean search never finds
a selected sink. -/
theorem ancestralInBar_empty (G : ObservedGraph S) (action : NodeSet S)
    (i : Fin S.count) :
    ancestralInBar G action NodeSet.empty i = false := by
  simp only [ancestralInBar, ObservedGraph.observedAncestorOf, NodeSet.empty]
  refine List.any_eq_false.mpr ?_
  intro _target _ht
  simp

theorem ancestralInBar_eq_empty (G : ObservedGraph S) (action : NodeSet S) :
    ancestralInBar G action NodeSet.empty = NodeSet.empty := by
  funext i
  exact ancestralInBar_empty G action i

/-- Every target is an ancestor of itself, so the ancestral family
contains the seeds. -/
theorem ancestralInBar_contains_targets (G : ObservedGraph S)
    (action targets : NodeSet S) :
    NodeSet.Subset targets (ancestralInBar G action targets) :=
  fun _i hi =>
    observedAncestorOf_self G (GraphMutilation.bar action) targets hi

/--
Vertices that remain unconditioned and still reach `targets` after every
conditioned child is cut.  An open directed walk into `Z` (respectively `Y`)
is exactly membership in this set for `targets = Z` (respectively `Y`).
-/
def openAncestralIn (G : ObservedGraph S)
    (conditioned targets : NodeSet S) : NodeSet S :=
  fun i =>
    !(ObservedGraph.blockedBy conditioned (.observed i)) &&
      ancestralInBar G conditioned targets i

/-- Vertices that remain unconditioned and still reach `targets` in an
arbitrary mutilated DAG.  Rule 1's `openAncestralIn` is the instance
whose mutilation is `G_{\overline{conditioned}}`; rule 2 uses
`G_{\overline{X}\underline{Z}}`. -/
def openAncestralInGraph (G : ObservedGraph S)
    (m : GraphMutilation S) (conditioned targets : NodeSet S) : NodeSet S :=
  fun i =>
    !(ObservedGraph.blockedBy conditioned (.observed i)) &&
      G.observedAncestorOf m targets i

/-- Open ancestors of `Z` in `G_{\overline{X ∪ W}\underline{Z}}` given
`X ∪ W`.  Ancestry is taken after also cutting incoming arrows to `W`,
so a shortest walk into `Z` never meets the conditioning set.  Empty `W`
recovers ancestry in `G_{\overline{X}\underline{Z}}`. -/
def rule2ZOpenCore (G : ObservedGraph S) (x z w : NodeSet S) : NodeSet S :=
  openAncestralInGraph G
    (GraphMutilation.barUnderline (NodeSet.union x w) z)
    (NodeSet.union x w) z

/-- Open ancestors of `Y` in `G_{\overline{X ∪ W}\underline{Z}}` given
`X ∪ W`. -/
def rule2YOpenCore (G : ObservedGraph S) (x y z w : NodeSet S) : NodeSet S :=
  openAncestralInGraph G
    (GraphMutilation.barUnderline (NodeSet.union x w) z)
    (NodeSet.union x w) y

/-- Open ancestors of `Z` in `G_{\overline{X}}` given `X ∪ W`. -/
def rule1LeftOpenCore (G : ObservedGraph S) (x z w : NodeSet S) : NodeSet S :=
  openAncestralIn G (NodeSet.union x w) z

/-- Open ancestors of `Y` in `G_{\overline{X}}` given `X ∪ W`. -/
def rule1RightOpenCore (G : ObservedGraph S) (x y _z w : NodeSet S) : NodeSet S :=
  openAncestralIn G (NodeSet.union x w) y

/-- Open ancestral vertices sit among the full ancestral set. -/
theorem openAncestralIn_subset (G : ObservedGraph S)
    (conditioned targets : NodeSet S) :
    NodeSet.Subset (openAncestralIn G conditioned targets)
      (ancestralInBar G conditioned targets) := by
  intro i hi
  have hparts :
      ObservedGraph.blockedBy conditioned (.observed i) = false ∧
        ancestralInBar G conditioned targets i = true := by
    simpa [openAncestralIn] using hi
  exact hparts.2

/-- Hard-intervening a node is the same as conditioning it, for observed
vertices. -/
theorem intervention_none_iff_unblocked
    (conditioned : NodeSet S) (reference : S.Assignment)
    (i : Fin S.count) :
    ((Kernel.mk NodeSet.empty conditioned NodeSet.empty).intervention
      reference) i = none ↔
      ObservedGraph.blockedBy conditioned (.observed i) = false := by
  simp [Kernel.intervention, ObservedGraph.blockedBy]

/-- A free ancestor in `G_{\overline{conditioned}}` is an open-core vertex. -/
theorem openAncestralIn_of_free_ancestor (G : ObservedGraph S)
    (conditioned targets : NodeSet S) (reference : S.Assignment)
    (i : Fin S.count)
    (hanc : ancestralInBar G conditioned targets i = true)
    (hfree :
      ((Kernel.mk NodeSet.empty conditioned NodeSet.empty).intervention
        reference) i = none) :
    openAncestralIn G conditioned targets i = true := by
  have hunb :=
    (intervention_none_iff_unblocked conditioned reference i).mp hfree
  simp [openAncestralIn, hunb, hanc]

/--
Under `do(conditioned)`, latents relevant to the ancestral set are exactly
those relevant to the open core: intervened ancestral vertices do not
contribute incident children.
-/
theorem latentRelevantUnder_openAncestralIn
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (conditioned targets : NodeSet S) (reference : S.Assignment)
    (root : Fin model.latent.count) :
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty conditioned NodeSet.empty).intervention
          reference)
        (openAncestralIn G conditioned targets) root =
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty conditioned NodeSet.empty).intervention
          reference)
        (ancestralInBar G conditioned targets) root := by
  let intervention :=
    (Kernel.mk NodeSet.empty conditioned NodeSet.empty).intervention
      reference
  cases hopen :
      model.latentRelevantUnder intervention
        (openAncestralIn G conditioned targets) root with
  | true =>
      rcases (model.latentRelevantUnder_eq_true_iff intervention
          (openAncestralIn G conditioned targets) root).mp hopen with
        ⟨child, selected, notIntervened, incident⟩
      have ancestral :=
        openAncestralIn_subset G conditioned targets child selected
      have hanc :=
        model.latentRelevantUnder_of_incident intervention
          (ancestralInBar G conditioned targets) root child ancestral
          notIntervened incident
      simpa [hanc]
  | false =>
      cases hanc :
          model.latentRelevantUnder intervention
            (ancestralInBar G conditioned targets) root with
      | false =>
          rfl
      | true =>
          rcases (model.latentRelevantUnder_eq_true_iff intervention
              (ancestralInBar G conditioned targets) root).mp hanc with
            ⟨child, selected, notIntervened, incident⟩
          have unblocked :=
            (intervention_none_iff_unblocked conditioned reference child).mp
              notIntervened
          have inCore : openAncestralIn G conditioned targets child = true := by
            simp [openAncestralIn, unblocked, selected]
          have hopen' :=
            model.latentRelevantUnder_of_incident intervention
              (openAncestralIn G conditioned targets) root child inCore
              notIntervened incident
          rw [hopen] at hopen'
          cases hopen'

/-- `W` vertices that already lie among the ancestors of `Z`. -/
def rule1WSelected (G : ObservedGraph S) (x z w : NodeSet S) : NodeSet S :=
  NodeSet.inter w (ancestralInBar G x z)

/-- `W` vertices that are not ancestors of `Z`. -/
def rule1WUnselected (G : ObservedGraph S) (x z w : NodeSet S) : NodeSet S :=
  fun i => w i && !(ancestralInBar G x z i)

theorem rule1W_union (G : ObservedGraph S) (x z w : NodeSet S) :
    NodeSet.union (rule1WSelected G x z w) (rule1WUnselected G x z w) =
      w := by
  funext i
  simp [NodeSet.union, rule1WSelected, rule1WUnselected, NodeSet.inter,
    ancestralInBar]
  cases hw : w i with
  | false =>
      simp
  | true =>
      cases hA : G.observedAncestorOf (GraphMutilation.bar x) z i <;>
        simp

def rule1LeftTargets (G : ObservedGraph S) (x z w : NodeSet S) : NodeSet S :=
  NodeSet.union z (rule1WSelected G x z w)

def rule1RightTargets (G : ObservedGraph S) (x y z w : NodeSet S) :
    NodeSet S :=
  NodeSet.union y (rule1WUnselected G x z w)

def rule1LeftRegion (G : ObservedGraph S) (x z w : NodeSet S) : NodeSet S :=
  ancestralInBar G x (rule1LeftTargets G x z w)

def rule1RightRegion (G : ObservedGraph S) (x y z w : NodeSet S) : NodeSet S :=
  ancestralInBar G x (rule1RightTargets G x y z w)

theorem subset_ancestralInBar (G : ObservedGraph S)
    (action observed targets : NodeSet S)
    (hsub : NodeSet.Subset observed targets) :
    NodeSet.Subset observed (ancestralInBar G action targets) := by
  intro i hi
  exact observedAncestorOf_self G _ targets (hsub i hi)

theorem rule1WSelected_subset_left (G : ObservedGraph S)
    (x z w : NodeSet S) :
    NodeSet.Subset (rule1WSelected G x z w)
      (rule1LeftRegion G x z w) := by
  intro i hi
  have hz : ancestralInBar G x z i = true :=
    NodeSet.inter_subset_right w (ancestralInBar G x z) i hi
  have hsub : NodeSet.Subset z (rule1LeftTargets G x z w) := by
    intro j hj
    simp [rule1LeftTargets, NodeSet.union, hj]
  exact observedAncestorOf_mono G _ hsub hz

theorem rule1Z_subset_left (G : ObservedGraph S) (x z w : NodeSet S) :
    NodeSet.Subset z (rule1LeftRegion G x z w) :=
  subset_ancestralInBar G x z (rule1LeftTargets G x z w) (by
    intro i hi
    simp [rule1LeftTargets, NodeSet.union, hi])

theorem rule1Y_subset_right (G : ObservedGraph S) (x y z w : NodeSet S) :
    NodeSet.Subset y (rule1RightRegion G x y z w) :=
  subset_ancestralInBar G x y (rule1RightTargets G x y z w) (by
    intro i hi
    simp [rule1RightTargets, NodeSet.union, hi])

theorem rule1WUnselected_subset_right (G : ObservedGraph S)
    (x y z w : NodeSet S) :
    NodeSet.Subset (rule1WUnselected G x z w)
      (rule1RightRegion G x y z w) := by
  intro i hi
  have hself : ancestralInBar G x (rule1WUnselected G x z w) i = true :=
    observedAncestorOf_self G _ (rule1WUnselected G x z w) hi
  have hsub :
      NodeSet.Subset (rule1WUnselected G x z w)
        (rule1RightTargets G x y z w) := by
    intro j hj
    simp [rule1RightTargets, NodeSet.union, hj]
  exact observedAncestorOf_mono G _ hsub hself

theorem rule1LeftRegion_backwardClosed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment)
      (rule1LeftRegion G x z w) :=
  backwardClosedUnder_of_rule1Right model G x y z w assignment
    (rule1LeftTargets G x z w)

theorem rule1RightRegion_backwardClosed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment)
      (rule1RightRegion G x y z w) :=
  backwardClosedUnder_of_rule1Right model G x y z w assignment
    (rule1RightTargets G x y z w)

/--
Path d-separation of two observed families forbids a bidirected edge
between open endpoints whose incoming arrows were not cut.
-/
theorem pathDSeparated_no_bidirected
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (separated : PathSpecification.PathDSeparated G mutilation left right
      conditioned)
    {a b : Fin S.count}
    (ha : left a = true) (hb : right b = true)
    (haOpen : ObservedGraph.blockedBy conditioned (.observed a) = false)
    (hbOpen : ObservedGraph.blockedBy conditioned (.observed b) = false)
    (haIn : mutilation.removeIncoming a = false)
    (hbIn : mutilation.removeIncoming b = false) :
    G.bidirected a b = false := by
  by_cases hEq : a = b
  · subst b
    cases hbid : G.bidirected a a with
    | false =>
        rfl
    | true =>
        exact False.elim
          (Bool.false_ne_true
            ((G.bidirected_irreflexive a).symm.trans hbid))
  · cases hbid : G.bidirected a b with
    | false =>
        rfl
    | true =>
        exact False.elim
          (separated
            ⟨a, b, ha, hb,
              ⟨PathSpecification.ActivePath.ofBidirected G mutilation
                conditioned hbid hEq haOpen hbOpen haIn hbIn⟩⟩)

/--
Path d-separation of two observed families forbids an all-open directed
walk between them, including the empty walk at a shared open vertex.
-/
theorem pathDSeparated_no_open_directed_walk
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (separated : PathSpecification.PathDSeparated G mutilation left right
      conditioned)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (simple : walk.nodes.Nodup)
    (ha : left source = true) (hb : right target = true)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false) :
    False :=
  separated
    ⟨source, target, ha, hb,
      ⟨PathSpecification.ActivePath.ofOpenDirectedWalk G mutilation
        conditioned walk simple openNodes⟩⟩

/--
Path d-separation of two observed families forbids a pair of all-open
directed walks from a common source, one ending in each family.  A
common open ancestor of `Z` and `Y` is the displayed case.
-/
theorem pathDSeparated_no_open_directed_fork
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (separated : PathSpecification.PathDSeparated G mutilation left right
      conditioned)
    {lengthZ lengthY : Nat} {shared zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthZ shared zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthY shared yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : left zEnd = true) (hy : right yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false) :
    False :=
  separated
    ⟨zEnd, yEnd, hz, hy,
      ⟨PathSpecification.ActivePath.ofOpenDirectedFork G mutilation
        conditioned walkZ walkY simpleZ simpleY openZ openY⟩⟩

/-- A `G_{\overline{large}}` edge is already an edge of `G_{\overline{small}}`
whenever `small ⊆ large`: incoming arrows to the larger family are a
stricter cut. -/
theorem observedDirectedEdge_bar_of_incoming_subset
    (G : ObservedGraph S) {small large : NodeSet S}
    (hsub : NodeSet.Subset small large) {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge (GraphMutilation.bar large)
      parent child = true) :
    G.observedDirectedEdge (GraphMutilation.bar small)
      parent child = true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
    NodeSet.empty] at hedge ⊢
  refine ⟨hedge.1, ?_⟩
  cases hs : small child with
  | false =>
      rfl
  | true =>
      have hlarge : large child = true := hsub child hs
      cases (hlarge.symm.trans hedge.2)

/-- Rebuild a `G_{\overline{large}}` walk inside `G_{\overline{small}}`
along an incoming-cut inclusion. -/
def remapBarWalk_of_incoming_subset
    (G : ObservedGraph S) {small large : NodeSet S}
    (hsub : NodeSet.Subset small large)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar large))
      length source target) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar small))
      length source target :=
  match walk with
  | .refl node =>
      .refl node
  | @FiniteReachability.ExactWalk.step _ _ _len src mid _tgt first rest =>
      .step (observedDirectedEdge_bar_of_incoming_subset G hsub first)
        (remapBarWalk_of_incoming_subset G hsub rest)

theorem remapBarWalk_of_incoming_subset_nodes
    (G : ObservedGraph S) {small large : NodeSet S}
    (hsub : NodeSet.Subset small large)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar large))
      length source target) :
    (remapBarWalk_of_incoming_subset G hsub walk).nodes = walk.nodes := by
  match walk with
  | .refl node =>
      rfl
  | @FiniteReachability.ExactWalk.step _ _ _len src mid _tgt first rest =>
      simp [remapBarWalk_of_incoming_subset,
        FiniteReachability.ExactWalk.nodes]
      exact remapBarWalk_of_incoming_subset_nodes G hsub rest

/-- Ancestry in `G_{\overline{large}}` is ancestry in `G_{\overline{small}}`
along an incoming-cut inclusion. -/
theorem observedAncestorOf_bar_of_incoming_subset
    (G : ObservedGraph S) {small large : NodeSet S}
    (hsub : NodeSet.Subset small large) (targets : NodeSet S)
    {source : Fin S.count}
    (hanc : G.observedAncestorOf (GraphMutilation.bar large) targets
      source = true) :
    G.observedAncestorOf (GraphMutilation.bar small) targets source =
      true := by
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar large) targets source hanc with
    ⟨target, htarget, length, walk, _simple, _minimal⟩
  let mapped := remapBarWalk_of_incoming_subset G hsub walk
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have reachable :
      FiniteReachability.Reachable
        (G.observedDirectedEdge (GraphMutilation.bar small)) source target :=
    ⟨length, ⟨mapped⟩⟩
  have bounded :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge (GraphMutilation.bar small)) finBeq_eq_true_iff
      complete reachable
  exact (G.observedAncestorOf_eq_true_iff (GraphMutilation.bar small)
      targets source).mpr ⟨target, htarget, bounded⟩

/-- A `G_{\overline{X ∪ Z}}` edge is already an edge of `G_{\overline{X}}`:
incoming arrows to `Z` are a stricter cut. -/
theorem observedDirectedEdge_bar_of_bar_union
    (G : ObservedGraph S) (x z : NodeSet S) {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge
      (GraphMutilation.bar (NodeSet.union x z)) parent child = true) :
    G.observedDirectedEdge (GraphMutilation.bar x) parent child = true :=
  observedDirectedEdge_bar_of_incoming_subset G
    (NodeSet.subset_union_left x z) hedge

/-- Rebuild a `G_{\overline{X ∪ Z}}` walk inside `G_{\overline{X}}`. -/
def remapBarUnionWalk_to_bar
    (G : ObservedGraph S) (x z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union x z)))
      length source target) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x))
      length source target :=
  remapBarWalk_of_incoming_subset G (NodeSet.subset_union_left x z) walk

/-- Ancestry in `G_{\overline{X ∪ Z}}` is ancestry in `G_{\overline{X}}`. -/
theorem observedAncestorOf_bar_of_bar_union
    (G : ObservedGraph S) (x z targets : NodeSet S)
    {source : Fin S.count}
    (hanc : G.observedAncestorOf
      (GraphMutilation.bar (NodeSet.union x z)) targets source = true) :
    G.observedAncestorOf (GraphMutilation.bar x) targets source = true :=
  observedAncestorOf_bar_of_incoming_subset G
    (NodeSet.subset_union_left x z) targets hanc

/-- When every `Z` node avoids `W` in `G_{\overline{X}}`, the rule-3
mutilation is `G_{\overline{X ∪ Z}}`. -/
theorem rule3_mutilation_eq_bar_union_of_z_avoids_w
    (G : ObservedGraph S) (x z w : NodeSet S)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z) :
    { removeIncoming :=
        NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
      removeOutgoing := NodeSet.empty } =
      GraphMutilation.bar (NodeSet.union x z) :=
  congrArg
    (fun removable =>
      ({ removeIncoming := NodeSet.union x removable,
          removeOutgoing := NodeSet.empty } : GraphMutilation S))
    hrem

/-- Empty-`W` rule 3 cuts incoming arrows to `X ∪ Z`, so `Z(W) = Z`. -/
theorem rule3_mutilation_eq_bar_union_of_empty_w
    (G : ObservedGraph S) (x z w : NodeSet S)
    (hw : NodeSet.isEmpty w = true) :
    { removeIncoming :=
        NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
      removeOutgoing := NodeSet.empty } =
      GraphMutilation.bar (NodeSet.union x z) :=
  rule3_mutilation_eq_bar_union_of_z_avoids_w G x z w
    (ObservedGraph.nonAncestorsOf_of_isEmpty G (GraphMutilation.bar x) z w hw)

/-- Path d-separation of `Y` from `Z` in `G_{\overline{X ∪ Z}}` forbids a
directed ancestral walk from a `Z` vertex into `Y`, once no `Z` node
ancestors `W`.  A walk into `Y` that met `W` would already ancestor `W`. -/
theorem rule3_z_not_ancestral_of_z_avoids_w
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    {i : Fin S.count} (hz : z i = true) :
    G.observedAncestorOf (GraphMutilation.bar (NodeSet.union x z)) y i =
      false := by
  have hm := rule3_mutilation_eq_bar_union_of_z_avoids_w G x z w hrem
  cases hanc :
      G.observedAncestorOf (GraphMutilation.bar (NodeSet.union x z)) y i with
  | false =>
      rfl
  | true =>
      rcases G.exists_minimal_walk_of_observedAncestorOf
          (GraphMutilation.bar (NodeSet.union x z)) y i hanc with
        ⟨yEnd, hy, _length, walkY, simpleY, _minimal⟩
      let walkZ :
          FiniteReachability.ExactWalk
            (G.observedDirectedEdge
              (GraphMutilation.bar (NodeSet.union x z)))
            0 i i :=
        FiniteReachability.ExactWalk.refl i
      have simpleZ : walkZ.nodes.Nodup := by
        simp [walkZ]
      have hx : x i = false := by
        cases hx : x i with
        | false =>
            rfl
        | true =>
            have hzFalse := disjoint.xz i hx
            rw [hz] at hzFalse
            cases hzFalse
      have hw : w i = false := by
        cases hw : w i with
        | false =>
            rfl
        | true =>
            have hwFalse := disjoint.zw i hz
            rw [hw] at hwFalse
            cases hwFalse
      have hcond : NodeSet.union x w i = false :=
        Bool.or_eq_false_iff.mpr ⟨hx, hw⟩
      have openZ : forall n, n ∈ walkZ.nodes ->
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
            false := by
        intro n hn
        have : n = i := by
          simpa [walkZ] using hn
        subst n
        simpa [ObservedGraph.blockedBy] using hcond
      have openY : forall n, n ∈ walkY.nodes ->
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
            false := by
        intro n hn
        by_cases hsrc : n = i
        · subst n
          simpa [ObservedGraph.blockedBy] using hcond
        · have hin :=
            PathSpecification.directed_walk_mem_not_removeIncoming G
              (GraphMutilation.bar (NodeSet.union x z)) walkY hn hsrc
          have hunion : NodeSet.union x z n = false := by
            simpa [GraphMutilation.bar] using hin
          have hxN : x n = false := (Bool.or_eq_false_iff.mp hunion).1
          have hwN : w n = false := by
            cases hwN : w n with
            | false =>
                rfl
            | true =>
                rcases FiniteReachability.ExactWalk.exists_prefix_with_subset
                    walkY hn with
                  ⟨_plen, preWalk, _bound, _subset, _rest, _hsplit⟩
                have hancW :
                    G.observedAncestorOf
                      (GraphMutilation.bar (NodeSet.union x z)) w i =
                        true :=
                  G.observedAncestorOf_of_mem_walk
                    (GraphMutilation.bar (NodeSet.union x z)) w preWalk hwN
                    preWalk.mem_source
                have hancX :=
                  observedAncestorOf_bar_of_bar_union G x z w hancW
                have hnon :
                    G.nonAncestorsOf (GraphMutilation.bar x) z w i = true := by
                  simpa [hrem] using hz
                have hfalse :
                    G.observedAncestorOf (GraphMutilation.bar x) w i =
                      false := by
                  cases hanc' :
                      G.observedAncestorOf (GraphMutilation.bar x) w i with
                  | false =>
                      rfl
                  | true =>
                      simp [ObservedGraph.nonAncestorsOf, hz, hanc'] at hnon
                rw [hancX] at hfalse
                cases hfalse
          simpa [ObservedGraph.blockedBy, NodeSet.union] using
            Bool.or_eq_false_iff.mpr ⟨hxN, hwN⟩
      have separated' :
          PathSpecification.PathDSeparated G
            (GraphMutilation.bar (NodeSet.union x z)) y z
            (NodeSet.union x w) := by
        simpa [hm] using separated
      exact (pathDSeparated_no_open_directed_fork G
          (GraphMutilation.bar (NodeSet.union x z)) y z
          (NodeSet.union x w) separated' walkY walkZ simpleY simpleZ
          hy hz openY openZ).elim

/-- `Z(W) = Z` means no `Z` vertex ancestors `W` in `G_{\overline{X}}`,
hence none ancestors `W` in the stricter `G_{\overline{X ∪ Z}}`. -/
theorem rule3_z_not_ancestral_w_of_z_avoids_w
    (G : ObservedGraph S) (x z w : NodeSet S)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    {i : Fin S.count} (hz : z i = true) :
    G.observedAncestorOf (GraphMutilation.bar (NodeSet.union x z)) w i =
      false := by
  cases hanc :
      G.observedAncestorOf (GraphMutilation.bar (NodeSet.union x z)) w i with
  | false =>
      rfl
  | true =>
      have hancX :=
        observedAncestorOf_bar_of_bar_union G x z w hanc
      have hnon :
          G.nonAncestorsOf (GraphMutilation.bar x) z w i = true := by
        simpa [hrem] using hz
      simp [ObservedGraph.nonAncestorsOf, hz, hancX] at hnon

/-- Path d-separation of `Y` from `Z` in `G_{\overline{X ∪ Z}}` forbids a
directed ancestral walk from a `Z` vertex into `Y`. -/
theorem rule3_z_not_ancestral_of_empty_w
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    {i : Fin S.count} (hz : z i = true) :
    G.observedAncestorOf (GraphMutilation.bar (NodeSet.union x z)) y i =
      false :=
  rule3_z_not_ancestral_of_z_avoids_w G x y z w disjoint
    (ObservedGraph.nonAncestorsOf_of_isEmpty G (GraphMutilation.bar x) z w hw)
    separated hz

/--
Path d-separation of `Y` from `Z` given `X ∪ W` in `G_{\overline{X ∪ Z(W)}}`
forbids a directed ancestral walk from a `Z` vertex into `Y` in the
stricter `G_{\overline{X ∪ W ∪ Z}}`.  Incoming arrows to the conditioned
family `W` are cut, so a shortest walk into `Y` never meets `W`; its
edges already exist in the side-condition graph, where the walk plus a
reflexive fork at `Z` would be open.
-/
theorem rule3_z_not_ancestral_of_union_xw
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    {i : Fin S.count} (hz : z i = true) :
    G.observedAncestorOf
      (GraphMutilation.bar (NodeSet.union (NodeSet.union x w) z)) y i =
      false := by
  let removable := G.nonAncestorsOf (GraphMutilation.bar x) z w
  have hsub : NodeSet.Subset (NodeSet.union x removable)
      (NodeSet.union (NodeSet.union x w) z) :=
    NodeSet.union_subset
      (NodeSet.Subset.trans (NodeSet.subset_union_left x w)
        (NodeSet.subset_union_left (NodeSet.union x w) z))
      (NodeSet.Subset.trans
        (ObservedGraph.nonAncestorsOf_subset_actions G
          (GraphMutilation.bar x) z w)
        (NodeSet.subset_union_right (NodeSet.union x w) z))
  cases hanc :
      G.observedAncestorOf
        (GraphMutilation.bar (NodeSet.union (NodeSet.union x w) z)) y i with
  | false =>
      rfl
  | true =>
      rcases G.exists_minimal_walk_of_observedAncestorOf
          (GraphMutilation.bar (NodeSet.union (NodeSet.union x w) z))
          y i hanc with
        ⟨yEnd, hy, _length, walkY, simpleY, _minimal⟩
      let walkZ :
          FiniteReachability.ExactWalk
            (G.observedDirectedEdge
              (GraphMutilation.bar (NodeSet.union x removable)))
            0 i i :=
        FiniteReachability.ExactWalk.refl i
      have simpleZ : walkZ.nodes.Nodup := by
        simp [walkZ]
      have hx : x i = false := by
        cases hx : x i with
        | false =>
            rfl
        | true =>
            have hzFalse := disjoint.xz i hx
            rw [hz] at hzFalse
            cases hzFalse
      have hw : w i = false := by
        cases hw : w i with
        | false =>
            rfl
        | true =>
            have hwFalse := disjoint.zw i hz
            rw [hw] at hwFalse
            cases hwFalse
      have hcond : NodeSet.union x w i = false :=
        Bool.or_eq_false_iff.mpr ⟨hx, hw⟩
      have openZ : forall n, n ∈ walkZ.nodes ->
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
            false := by
        intro n hn
        have : n = i := by
          simpa [walkZ] using hn
        subst n
        simpa [ObservedGraph.blockedBy] using hcond
      have openY : forall n, n ∈ walkY.nodes ->
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
            false := by
        intro n hn
        by_cases hsrc : n = i
        · subst n
          simpa [ObservedGraph.blockedBy] using hcond
        · have hin :=
            PathSpecification.directed_walk_mem_not_removeIncoming G
              (GraphMutilation.bar
                (NodeSet.union (NodeSet.union x w) z)) walkY hn hsrc
          have hunion : NodeSet.union (NodeSet.union x w) z n = false := by
            simpa [GraphMutilation.bar] using hin
          have hxw : NodeSet.union x w n = false :=
            (Bool.or_eq_false_iff.mp hunion).1
          simpa [ObservedGraph.blockedBy] using hxw
      let mapped :=
        remapBarWalk_of_incoming_subset G hsub walkY
      have hnodes :=
        remapBarWalk_of_incoming_subset_nodes G hsub walkY
      have simpleMapped : mapped.nodes.Nodup := by
        rw [hnodes]
        exact simpleY
      have openMapped : forall n, n ∈ mapped.nodes ->
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
            false := by
        intro n hn
        rw [hnodes] at hn
        exact openY n hn
      have separated' :
          PathSpecification.PathDSeparated G
            (GraphMutilation.bar (NodeSet.union x removable)) y z
            (NodeSet.union x w) := by
        simpa [GraphMutilation.bar, removable] using separated
      exact (pathDSeparated_no_open_directed_fork G
          (GraphMutilation.bar (NodeSet.union x removable)) y z
          (NodeSet.union x w) separated' mapped walkZ simpleMapped simpleZ
          hy hz openMapped openZ).elim

/--
Path d-separation forbids a bidirected edge between the sources of two
all-open directed walks into the two families.  A shared vertex is already
a fork; the remaining case glues the walks across the bidirected edge.
-/
theorem pathDSeparated_no_bidirected_open_walk_sources
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (separated : PathSpecification.PathDSeparated G mutilation left right
      conditioned)
    {lengthZ lengthY : Nat} {sourceZ sourceY zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : left zEnd = true) (hy : right yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (sourceZIncoming : mutilation.removeIncoming sourceZ = false)
    (sourceYIncoming : mutilation.removeIncoming sourceY = false) :
    G.bidirected sourceZ sourceY = false := by
  by_cases hEq : sourceZ = sourceY
  · subst sourceY
    cases hbid : G.bidirected sourceZ sourceZ with
    | false =>
        rfl
    | true =>
        exact False.elim
          (Bool.false_ne_true
            ((G.bidirected_irreflexive sourceZ).symm.trans hbid))
  · cases hbid : G.bidirected sourceZ sourceY with
    | false =>
        rfl
    | true =>
        have notOnZ : sourceY ∉ walkZ.nodes := by
          intro member
          rcases walkZ.exists_simple_suffix_of_mem simpleZ member with
            ⟨_slen, swalk, ssimple, _pre, hnodes⟩
          have subset : forall n, n ∈ swalk.nodes -> n ∈ walkZ.nodes :=
            fun n hn => by
              rw [hnodes]
              exact List.mem_append.mpr (Or.inr hn)
          exact pathDSeparated_no_open_directed_fork G mutilation left right
            conditioned separated swalk walkY ssimple simpleY hz hy
            (fun n hn => openZ n (subset n hn)) openY
        have notOnY : sourceZ ∉ walkY.nodes := by
          intro member
          rcases walkY.exists_simple_suffix_of_mem simpleY member with
            ⟨_slen, swalk, ssimple, _pre, hnodes⟩
          have subset : forall n, n ∈ swalk.nodes -> n ∈ walkY.nodes :=
            fun n hn => by
              rw [hnodes]
              exact List.mem_append.mpr (Or.inr hn)
          exact pathDSeparated_no_open_directed_fork G mutilation left right
            conditioned separated walkZ swalk simpleZ ssimple hz hy openZ
            (fun n hn => openY n (subset n hn))
        have disjointWalks :
            forall n, n ∈ walkZ.nodes -> n ∈ walkY.nodes -> False := by
          intro n hnZ hnY
          rcases walkZ.exists_simple_suffix_of_mem simpleZ hnZ with
            ⟨_lenZ, sufZ, simpleSufZ, _preZ, hnodesZ⟩
          rcases walkY.exists_simple_suffix_of_mem simpleY hnY with
            ⟨_lenY, sufY, simpleSufY, _preY, hnodesY⟩
          have subZ : forall m, m ∈ sufZ.nodes -> m ∈ walkZ.nodes :=
            fun m hm => by
              rw [hnodesZ]
              exact List.mem_append.mpr (Or.inr hm)
          have subY : forall m, m ∈ sufY.nodes -> m ∈ walkY.nodes :=
            fun m hm => by
              rw [hnodesY]
              exact List.mem_append.mpr (Or.inr hm)
          exact pathDSeparated_no_open_directed_fork G mutilation left right
            conditioned separated sufZ sufY simpleSufZ simpleSufY hz hy
            (fun m hm => openZ m (subZ m hm))
            (fun m hm => openY m (subY m hm))
        exact False.elim
          (separated
            ⟨zEnd, yEnd, hz, hy,
              ⟨PathSpecification.ActivePath.ofOpenWalks_glue_bidirected G
                mutilation conditioned walkZ walkY simpleZ simpleY openZ
                openY hbid hEq sourceZIncoming sourceYIncoming notOnZ notOnY
                disjointWalks⟩⟩)

/--
Rule 1's `Y ⊥ Z | X ∪ W` forbids a pair of all-open directed walks from a
common source, one ending in `Z` and one ending in `Y`.  The fork is
reversed so the active path runs from the `Y` endpoint to the `Z`
endpoint.
-/
theorem pathDSeparated_no_open_directed_fork_yz
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {lengthZ lengthY : Nat} {shared zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthZ shared zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthY shared yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : z zEnd = true) (hy : y yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false) :
    False :=
  separated
    ⟨yEnd, zEnd, hy, hz,
      ⟨(PathSpecification.ActivePath.ofOpenDirectedFork G
          (GraphMutilation.bar x) (NodeSet.union x w)
          walkZ walkY simpleZ simpleY openZ openY).reverse⟩⟩

/--
Path d-separation of `left` from `right` forbids a bidirected edge from the
source of an all-open directed walk into `right` onto an open `left` vertex.
-/
theorem pathDSeparated_no_bidirected_of_open_directed_walk
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (separated : PathSpecification.PathDSeparated G mutilation left right
      conditioned)
    {length : Nat} {source target other : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (simple : walk.nodes.Nodup)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (ht : right target = true) (hother : left other = true)
    (otherOpen : ObservedGraph.blockedBy conditioned (.observed other) =
      false)
    (sourceIncoming : mutilation.removeIncoming source = false)
    (otherIncoming : mutilation.removeIncoming other = false) :
    G.bidirected source other = false := by
  by_cases hEq : source = other
  · subst other
    cases hbid : G.bidirected source source with
    | false =>
        rfl
    | true =>
        exact False.elim
          (Bool.false_ne_true
            ((G.bidirected_irreflexive source).symm.trans hbid))
  · cases hbid : G.bidirected source other with
    | false =>
        rfl
    | true =>
        have notOnWalk : other ∉ walk.nodes := by
          intro member
          rcases walk.exists_simple_suffix_of_mem simple member with
            ⟨_slen, swalk, ssimple, _pre, hnodes⟩
          have subset : forall n, n ∈ swalk.nodes -> n ∈ walk.nodes :=
            fun n hn => by
              rw [hnodes]
              exact List.mem_append.mpr (Or.inr hn)
          exact pathDSeparated_no_open_directed_walk G mutilation left right
            conditioned separated swalk ssimple hother ht
            (fun n hn => openNodes n (subset n hn))
        exact False.elim
          (separated
            ⟨other, target, hother, ht,
              ⟨(PathSpecification.ActivePath.ofOpenDirectedWalk_glue_bidirected
                  G mutilation conditioned walk simple openNodes hbid hEq
                  otherOpen sourceIncoming otherIncoming notOnWalk).reverse⟩⟩)

/-- Ancestry in `G_{\overline{X}}` supplies a simple shortest walk into the
target family.  Internals of that walk lie outside the family, so they are
unconditioned whenever the family already absorbs every conditioned ancestor. -/
theorem ancestralInBar_exists_minimal_walk
    (G : ObservedGraph S) (action targets : NodeSet S)
    (source : Fin S.count)
    (hanc : ancestralInBar G action targets source = true) :
    Exists fun target : Fin S.count =>
      targets target = true /\
        Exists fun length : Nat =>
          Exists fun walk :
              FiniteReachability.ExactWalk
                (G.observedDirectedEdge (GraphMutilation.bar action))
                length source target =>
            walk.nodes.Nodup /\
              (forall target' alternative,
                targets target' = true ->
                  Nonempty (FiniteReachability.ExactWalk
                    (G.observedDirectedEdge (GraphMutilation.bar action))
                    alternative source target') ->
                    length <= alternative) :=
  G.exists_minimal_walk_of_observedAncestorOf
    (GraphMutilation.bar action) targets source hanc

/-- Cutting every conditioned child is a coarser bar-`X` DAG, so its directed
walks remain walks in `G_{\overline{X}}`. -/
theorem observedDirectedEdge_bar_of_union
    (G : ObservedGraph S) (x w : NodeSet S) {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge
      (GraphMutilation.bar (NodeSet.union x w)) parent child = true) :
    G.observedDirectedEdge (GraphMutilation.bar x) parent child = true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar, NodeSet.union]
    at hedge ⊢
  cases hx : x child with
  | true =>
      simp [hx] at hedge
  | false =>
      simpa [hx] using hedge.1

/-- The converse: a `G_{\overline{X}}` edge whose child is unconditioned
given `X ∪ W` is already an edge of `G_{\overline{X ∪ W}}`. -/
theorem observedDirectedEdge_union_bar_of_open
    (G : ObservedGraph S) (x w : NodeSet S) {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge (GraphMutilation.bar x) parent child =
      true)
    (hopen : ObservedGraph.blockedBy (NodeSet.union x w) (.observed child) =
      false) :
    G.observedDirectedEdge
      (GraphMutilation.bar (NodeSet.union x w)) parent child = true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
    ObservedGraph.blockedBy, NodeSet.union] at hedge hopen ⊢
  exact ⟨hedge.1, hopen⟩

/-- A `G_{\overline{X}}` edge whose parent is not in `Z` survives the extra
outgoing cut of `G_{\overline{X}\underline{Z}}`. -/
theorem observedDirectedEdge_barUnderline_of_bar
    (G : ObservedGraph S) (x z : NodeSet S) {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge (GraphMutilation.bar x) parent child =
      true)
    (hparent : z parent = false) :
    G.observedDirectedEdge (GraphMutilation.barUnderline x z) parent child =
      true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
    GraphMutilation.barUnderline, NodeSet.empty] at hedge ⊢
  exact ⟨⟨hedge.1, hparent⟩, hedge.2⟩

/-- A `G_{\overline{X ∪ Z}}` edge whose parent is not in `Z` is already an
edge of `G_{\overline{X}\underline{Z}}`: the child is outside `X ∪ Z`, so
it is outside `X`, and the extra outgoing cut only deletes edges out of
`Z`. -/
theorem observedDirectedEdge_barUnderline_of_barUnion
    (G : ObservedGraph S) (x z : NodeSet S) {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge
      (GraphMutilation.bar (NodeSet.union x z)) parent child = true)
    (hparent : z parent = false) :
    G.observedDirectedEdge (GraphMutilation.barUnderline x z) parent child =
      true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
    GraphMutilation.barUnderline, NodeSet.union, NodeSet.empty] at hedge ⊢
  exact ⟨⟨hedge.1, hparent⟩, hedge.2.1⟩

/-- Cutting incoming arrows to `W` as well as `X` only deletes edges, so
every remaining directed edge of `G_{\overline{X ∪ W}\underline{Z}}` is
already an edge of `G_{\overline{X}\underline{Z}}`. -/
theorem observedDirectedEdge_barUnderline_of_unionBarUnderline
    (G : ObservedGraph S) (x w z : NodeSet S)
    {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge
      (GraphMutilation.barUnderline (NodeSet.union x w) z) parent child =
        true) :
    G.observedDirectedEdge (GraphMutilation.barUnderline x z) parent child =
      true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.barUnderline,
    NodeSet.union] at hedge ⊢
  cases hx : x child with
  | true =>
      simp [hx] at hedge
  | false =>
      simpa [hx] using hedge.1

/-- A `G_{\overline{X}\underline{Z}}` edge whose child is unconditioned
given `X ∪ W` is already an edge of `G_{\overline{X ∪ W}\underline{Z}}`. -/
theorem observedDirectedEdge_unionBarUnderline_of_barUnderline_open
    (G : ObservedGraph S) (x w z : NodeSet S)
    {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge (GraphMutilation.barUnderline x z)
      parent child = true)
    (hopen : NodeSet.union x w child = false) :
    G.observedDirectedEdge
      (GraphMutilation.barUnderline (NodeSet.union x w) z) parent child =
        true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.barUnderline,
    NodeSet.union] at hedge hopen ⊢
  exact ⟨hedge.1, hopen⟩

/-- A `G_{\overline{X}\underline{Z}}` edge whose child is not in `Z` is
already an edge of `G_{\overline{X ∪ Z}}`: outgoing arrows from `Z` are
unused, and the child is outside `X ∪ Z`. -/
theorem observedDirectedEdge_barUnion_of_barUnderline
    (G : ObservedGraph S) (x z : NodeSet S) {parent child : Fin S.count}
    (hedge : G.observedDirectedEdge (GraphMutilation.barUnderline x z)
      parent child = true)
    (hzChild : z child = false) :
    G.observedDirectedEdge
      (GraphMutilation.bar (NodeSet.union x z)) parent child = true := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.barUnderline,
    GraphMutilation.bar, NodeSet.union, NodeSet.empty] at hedge ⊢
  exact ⟨hedge.1.1, ⟨hedge.2, hzChild⟩⟩

/-- Rebuild a `G_{\overline{X}\underline{Z}}` walk that never meets `Z`
inside `G_{\overline{X ∪ Z}}`. -/
def remapBarUnderlineWalk_to_barUnion
    (G : ObservedGraph S) (x z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      length source target)
    (hnotZ : forall n, n ∈ walk.nodes -> z n = false) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union x z)))
      length source target :=
  match walk with
  | .refl node =>
      .refl node
  | @FiniteReachability.ExactWalk.step _ _ _len src mid _tgt first rest =>
      have hzMid : z mid = false :=
        hnotZ mid (by
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr rest.mem_source)
      have restNotZ : forall n, n ∈ rest.nodes -> z n = false :=
        fun n hn =>
          hnotZ n (by
            simp [FiniteReachability.ExactWalk.nodes]
            exact Or.inr hn)
      .step (observedDirectedEdge_barUnion_of_barUnderline G x z first hzMid)
        (remapBarUnderlineWalk_to_barUnion G x z rest restNotZ)

/-- A `G_{\overline{X}\underline{Z}}` walk that never meets `Z` is already
a walk of `G_{\overline{X ∪ Z}}`. -/
theorem observedAncestorOf_barUnion_of_barUnderline_walk
    (G : ObservedGraph S) (x z targets : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      length source target)
    (htarget : targets target = true)
    (hnotZ : forall n, n ∈ walk.nodes -> z n = false) :
    G.observedAncestorOf (GraphMutilation.bar (NodeSet.union x z))
      targets source = true := by
  let mapped := remapBarUnderlineWalk_to_barUnion G x z walk hnotZ
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have reachable :
      FiniteReachability.Reachable
        (G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union x z)))
        source target :=
    ⟨length, ⟨mapped⟩⟩
  have bounded :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union x z)))
      finBeq_eq_true_iff complete reachable
  exact (G.observedAncestorOf_eq_true_iff
      (GraphMutilation.bar (NodeSet.union x z)) targets source).mpr
    ⟨target, htarget, bounded⟩

/-- Rebuild an all-open `G_{\overline{X}\underline{Z}}` walk inside
`G_{\overline{X ∪ W}\underline{Z}}`. -/
def remapOpenBarUnderlineWalk_to_union
    (G : ObservedGraph S) (x w z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      length source target)
    (hopen : forall n, n ∈ walk.nodes -> NodeSet.union x w n = false) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.barUnderline (NodeSet.union x w) z))
      length source target :=
  match walk with
  | .refl node =>
      .refl node
  | @FiniteReachability.ExactWalk.step _ _ _len src mid _tgt first rest =>
      have hchild : NodeSet.union x w mid = false :=
        hopen mid (by
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr rest.mem_source)
      have restOpen :
          forall n, n ∈ rest.nodes -> NodeSet.union x w n = false :=
        fun n hn =>
          hopen n (by
            simp [FiniteReachability.ExactWalk.nodes]
            exact Or.inr hn)
      .step
        (observedDirectedEdge_unionBarUnderline_of_barUnderline_open G x w z
          first hchild)
        (remapOpenBarUnderlineWalk_to_union G x w z rest restOpen)

/-- Ancestry of `targets` in `G_{\overline{X}\underline{Z}}` along an
all-open walk is ancestry in `G_{\overline{X ∪ W}\underline{Z}}`. -/
theorem observedAncestorOf_unionBarUnderline_of_open_walk
    (G : ObservedGraph S) (x w z targets : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      length source target)
    (htarget : targets target = true)
    (hopen : forall n, n ∈ walk.nodes -> NodeSet.union x w n = false) :
    G.observedAncestorOf
      (GraphMutilation.barUnderline (NodeSet.union x w) z) targets source =
        true := by
  let mapped := remapOpenBarUnderlineWalk_to_union G x w z walk hopen
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have reachable :
      FiniteReachability.Reachable
        (G.observedDirectedEdge
          (GraphMutilation.barUnderline (NodeSet.union x w) z))
        source target :=
    ⟨length, ⟨mapped⟩⟩
  have bounded :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge
        (GraphMutilation.barUnderline (NodeSet.union x w) z))
      finBeq_eq_true_iff complete reachable
  exact (G.observedAncestorOf_eq_true_iff
      (GraphMutilation.barUnderline (NodeSet.union x w) z) targets source).mpr
    ⟨target, htarget, bounded⟩

/-- Ancestry of `Z` in `G_{\overline{X}\underline{Z}}` along an all-open
walk is ancestry in `G_{\overline{X ∪ W}\underline{Z}}`. -/
theorem observedAncestorOf_unionBarUnderline_z_of_open_walk
    (G : ObservedGraph S) (x w z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      length source target)
    (htarget : z target = true)
    (hopen : forall n, n ∈ walk.nodes -> NodeSet.union x w n = false) :
    G.observedAncestorOf
      (GraphMutilation.barUnderline (NodeSet.union x w) z) z source =
        true :=
  observedAncestorOf_unionBarUnderline_of_open_walk G x w z z walk htarget
    hopen

/-- Rebuild a set-minimal `G_{\overline{X}}` walk into `Z` inside
`G_{\overline{X}\underline{Z}}`.  Internals of a shortest walk into `Z`
are not themselves in `Z`, so they never use a deleted `Z`-outgoing
edge. -/
def remapMinimalBarWalkToBarUnderline
    (G : ObservedGraph S) (x z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (simple : walk.nodes.Nodup)
    (havoid : forall n, n ∈ walk.nodes -> n ≠ target -> z n = false) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      length source target :=
  match walk with
  | .refl node =>
      .refl node
  | @FiniteReachability.ExactWalk.step _ _ _len src _mid tgt first rest =>
      have parts :=
        List.nodup_cons.mp (by
          simpa [FiniteReachability.ExactWalk.nodes] using simple)
      have hne : src ≠ tgt := by
        intro same
        subst tgt
        exact parts.1 (FiniteReachability.ExactWalk.mem_target rest)
      have hparent : z src = false :=
        havoid src (by simp [FiniteReachability.ExactWalk.nodes]) hne
      have restAvoid :
          forall n, n ∈ rest.nodes -> n ≠ tgt -> z n = false :=
        fun n hn hne' =>
          havoid n (by
            simp [FiniteReachability.ExactWalk.nodes, hn]) hne'
      .step (observedDirectedEdge_barUnderline_of_bar G x z first hparent)
        (remapMinimalBarWalkToBarUnderline G x z rest parts.2 restAvoid)

/-- Vertices of a `G_{\overline{X ∪ Z}}` walk that starts outside `X ∪ Z`
never meet `Z`: the source is free, and every later vertex has incoming
arrows intact, hence is also outside `X ∪ Z`. -/
theorem barUnion_walk_vertices_not_in_z
    (G : ObservedGraph S) (x z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar (NodeSet.union x z))) length source target)
    (hfree : NodeSet.union x z source = false)
    {n : Fin S.count} (hn : n ∈ walk.nodes) :
    z n = false := by
  by_cases hsrc : n = source
  · subst n
    cases hx : x source with
    | true =>
        simp [NodeSet.union, hx] at hfree
    | false =>
        cases hz : z source with
        | false =>
            rfl
        | true =>
            simp [NodeSet.union, hx, hz] at hfree
  · have hin :=
      PathSpecification.directed_walk_mem_not_removeIncoming G
        (GraphMutilation.bar (NodeSet.union x z)) walk hn hsrc
    have hunion : NodeSet.union x z n = false := by
      simpa [GraphMutilation.bar] using hin
    cases hz : z n with
    | false =>
        rfl
    | true =>
        simp [NodeSet.union, hz] at hunion

/-- Rebuild a free `G_{\overline{X ∪ Z}}` walk inside
`G_{\overline{X}\underline{Z}}`. -/
def remapBarUnionWalkToBarUnderline
    (G : ObservedGraph S) (x z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar (NodeSet.union x z))) length source target)
    (hnotZ : forall n, n ∈ walk.nodes -> z n = false) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      length source target :=
  match walk with
  | .refl node =>
      .refl node
  | @FiniteReachability.ExactWalk.step _ _ _len src _mid _tgt first rest =>
      have hparent : z src = false :=
        hnotZ src (by simp [FiniteReachability.ExactWalk.nodes])
      have restNotZ : forall n, n ∈ rest.nodes -> z n = false :=
        fun n hn =>
          hnotZ n (by simp [FiniteReachability.ExactWalk.nodes, hn])
      .step
        (observedDirectedEdge_barUnderline_of_barUnion G x z first hparent)
        (remapBarUnionWalkToBarUnderline G x z rest restNotZ)

/-- Ancestry of `Z` in `G_{\overline{X}}` is ancestry in
`G_{\overline{X}\underline{Z}}`: a shortest walk into `Z` never leaves
`Z` and therefore never needs a deleted outgoing arrow. -/
theorem observedAncestorOf_barUnderline_z_of_bar
    (G : ObservedGraph S) (x z : NodeSet S) (source : Fin S.count)
    (hanc : G.observedAncestorOf (GraphMutilation.bar x) z source = true) :
    G.observedAncestorOf (GraphMutilation.barUnderline x z) z source =
      true := by
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar x) z source hanc with
    ⟨target, htarget, length, walk, simple, minimal⟩
  have havoid :
      forall n, n ∈ walk.nodes -> n ≠ target -> z n = false :=
    fun n hn hne =>
      FiniteReachability.ExactWalk.not_mem_targets_of_minimal_internal
        walk minimal hn hne
  let mapped :=
    remapMinimalBarWalkToBarUnderline G x z walk simple havoid
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have reachable :
      FiniteReachability.Reachable
        (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
        source target :=
    ⟨length, ⟨mapped⟩⟩
  have bounded :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      finBeq_eq_true_iff complete reachable
  exact (G.observedAncestorOf_eq_true_iff
      (GraphMutilation.barUnderline x z) z source).mpr
    ⟨target, htarget, bounded⟩

/-- A free ancestor of `Y` in `G_{\overline{X ∪ Z}}` is already an ancestor
in `G_{\overline{X}\underline{Z}}`: the walk never meets `Z`, so the extra
outgoing cut is unused. -/
theorem observedAncestorOf_barUnderline_y_of_barUnion
    (G : ObservedGraph S) (x y z : NodeSet S) (source : Fin S.count)
    (hanc : G.observedAncestorOf
      (GraphMutilation.bar (NodeSet.union x z)) y source = true)
    (hfree : NodeSet.union x z source = false) :
    G.observedAncestorOf (GraphMutilation.barUnderline x z) y source =
      true := by
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar (NodeSet.union x z)) y source hanc with
    ⟨target, htarget, length, walk, _simple, _minimal⟩
  have hnotZ : forall n, n ∈ walk.nodes -> z n = false :=
    fun n hn => barUnion_walk_vertices_not_in_z G x z walk hfree hn
  let mapped := remapBarUnionWalkToBarUnderline G x z walk hnotZ
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have reachable :
      FiniteReachability.Reachable
        (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
        source target :=
    ⟨length, ⟨mapped⟩⟩
  have bounded :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      finBeq_eq_true_iff complete reachable
  exact (G.observedAncestorOf_eq_true_iff
      (GraphMutilation.barUnderline x z) y source).mpr
    ⟨target, htarget, bounded⟩

/-- An all-open directed walk in `G_{\overline{X}}` is already a walk in
`G_{\overline{X ∪ W}}`, because every non-source vertex has incoming arrows
intact after also cutting `W`. -/
def mapOpenBarWalk_to_unionBar (G : ObservedGraph S) (x w : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false) :
    FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar (NodeSet.union x w)))
      length source target :=
  match walk with
  | .refl node =>
      .refl node
  | @FiniteReachability.ExactWalk.step _ _ len src mid tgt first rest =>
      have openMid :
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed mid) =
            false :=
        openNodes mid (by
          simp [FiniteReachability.ExactWalk.nodes]
          exact Or.inr rest.mem_source)
      have restOpen :
          forall n, n ∈ rest.nodes ->
            ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
              false :=
        fun n hn =>
          openNodes n (by
            simp [FiniteReachability.ExactWalk.nodes]
            exact Or.inr hn)
      .step (observedDirectedEdge_union_bar_of_open G x w first openMid)
        (mapOpenBarWalk_to_unionBar G x w rest restOpen)

theorem mapOpenBarWalk_to_unionBar_nodes
    (G : ObservedGraph S) (x w : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false) :
    (mapOpenBarWalk_to_unionBar G x w walk openNodes).nodes = walk.nodes := by
  induction walk with
  | refl node =>
      simp [mapOpenBarWalk_to_unionBar, FiniteReachability.ExactWalk.nodes]
  | @step length source middle target first rest ih =>
      simp [mapOpenBarWalk_to_unionBar, FiniteReachability.ExactWalk.nodes,
        ih]

/-- Every vertex of an all-open directed walk into a family sits in that
family's open ancestral core. -/
theorem openAncestralIn_of_mem_open_directed_walk
    (G : ObservedGraph S) (x w targets : NodeSet S)
    {length : Nat} {source target node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (ht : targets target = true)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (member : node ∈ walk.nodes) :
    openAncestralIn G (NodeSet.union x w) targets node = true := by
  have hanc :=
    ObservedGraph.observedAncestorOf_of_mem_walk G
      (GraphMutilation.bar (NodeSet.union x w)) targets
      (mapOpenBarWalk_to_unionBar G x w walk openNodes) ht (by
        rw [mapOpenBarWalk_to_unionBar_nodes]
        exact member)
  have hopen := openNodes node member
  simpa [openAncestralIn, ancestralInBar, hopen] using hanc

/-- Directed observed ancestry is expanded-DAG ancestry at the observed
tag: the observed-observed expansion is the same edge. -/
theorem ancestorOf_of_observedAncestorOf
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S) (source : Fin S.count)
    (hanc : G.observedAncestorOf mutilation targets source = true) :
    G.ancestorOf mutilation targets (.observed source) = true := by
  rcases (G.observedAncestorOf_eq_true_iff mutilation targets source).mp
      hanc with ⟨target, selected, bounded⟩
  rcases bounded with ⟨length, _hle, walk⟩
  rcases walk with ⟨walk⟩
  have walkAnc :
      forall {len : Nat} {src tgt : Fin S.count},
        FiniteReachability.ExactWalk (G.observedDirectedEdge mutilation)
          len src tgt ->
          G.ancestorOf mutilation targets (.observed tgt) = true ->
            G.ancestorOf mutilation targets (.observed src) = true := by
    intro len src tgt w htgt
    induction w with
    | refl node =>
        exact htgt
    | @step length source middle target first rest ih =>
        have midAnc := ih htgt
        have hedge :
            G.expandedMutilatedEdge mutilation (.observed source)
              (.observed middle) = true := by
          simpa [PathSpecification.expandedMutilatedEdge_observed] using first
        exact G.ancestorOf_prepend mutilation targets hedge midAnc
  exact walkAnc walk (G.ancestorOf_target mutilation targets selected)

/-- Membership in the open ancestral core supplies a simple all-open directed
walk in `G_{\overline{X}}` into the displayed family. -/
theorem openAncestralIn_exists_open_walk
    (G : ObservedGraph S) (x w targets : NodeSet S) (source : Fin S.count)
    (h : openAncestralIn G (NodeSet.union x w) targets source = true) :
    Exists fun target : Fin S.count =>
      targets target = true /\
        Exists fun length : Nat =>
          Exists fun walk :
              FiniteReachability.ExactWalk
                (G.observedDirectedEdge (GraphMutilation.bar x))
                length source target =>
            walk.nodes.Nodup /\
              (forall n, n ∈ walk.nodes ->
                ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
                  false) := by
  have hparts :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) = false ∧
        ancestralInBar G (NodeSet.union x w) targets source = true := by
    simpa [openAncestralIn] using h
  have hopen := hparts.1
  have hanc := hparts.2
  rcases ancestralInBar_exists_minimal_walk G (NodeSet.union x w) targets
      source hanc with
    ⟨target, htarget, length, walk, simple, _minimal⟩
  let included :=
    fun parent child hedge =>
      observedDirectedEdge_bar_of_union G x w (parent := parent)
        (child := child) hedge
  let walkX := FiniteReachability.ExactWalk.mapEdge included walk
  have hnodes :
      walkX.nodes = walk.nodes :=
    FiniteReachability.ExactWalk.mapEdge_nodes included walk
  refine ⟨target, htarget, length, walkX, ?_, ?_⟩
  · simpa [hnodes] using simple
  · intro n hn
    have hn' : n ∈ walk.nodes := by
      simpa [hnodes] using hn
    by_cases hsrc : n = source
    · subst n
      exact hopen
    · have hin :=
        PathSpecification.directed_walk_mem_not_removeIncoming G
          (GraphMutilation.bar (NodeSet.union x w)) walk hn' hsrc
      simpa [GraphMutilation.bar, ObservedGraph.blockedBy, NodeSet.union]
        using hin

/-- Left-side 4.1 seeds are already ancestors of `Z` in `G_{\overline{X}}`. -/
theorem rule1LeftTargets_mem_ancestral_z
    (G : ObservedGraph S) (x z w : NodeSet S) {i : Fin S.count}
    (hi : rule1LeftTargets G x z w i = true) :
    ancestralInBar G x z i = true := by
  simp only [rule1LeftTargets, NodeSet.union, rule1WSelected, NodeSet.inter]
    at hi
  cases hz : z i with
  | true =>
      exact observedAncestorOf_self G _ z hz
  | false =>
      simp [hz] at hi
      exact hi.2

/-- Ancestry of `Z ∪ W_Z` is ancestry of `Z`, because every left seed already
reaches `Z`. -/
theorem ancestralInBar_left_implies_z
    (G : ObservedGraph S) (x z w : NodeSet S) (source : Fin S.count)
    (hanc : ancestralInBar G x (rule1LeftTargets G x z w) source = true) :
    ancestralInBar G x z source = true :=
  G.observedAncestorOf_compose (GraphMutilation.bar x)
    (rule1LeftTargets G x z w) z source hanc
    (fun _i hi => rule1LeftTargets_mem_ancestral_z G x z w hi)

/-- Conditioned ancestors of the left family already sit inside that family. -/
theorem rule1Left_absorbs_w
    (G : ObservedGraph S) (x z w : NodeSet S) {i : Fin S.count}
    (hw : w i = true)
    (hanc : ancestralInBar G x (rule1LeftTargets G x z w) i = true) :
    rule1LeftTargets G x z w i = true := by
  have hz : ancestralInBar G x z i = true :=
    ancestralInBar_left_implies_z G x z w i hanc
  simp [rule1LeftTargets, NodeSet.union, rule1WSelected, NodeSet.inter, hw, hz]

/--
Internals of a shortest ancestral walk are unconditioned once the target
family already contains every `W`-ancestor.  Intervened children are excluded
by the bar-`X` edge predicate.
-/
theorem blockedBy_false_of_minimal_ancestral_internal
    (G : ObservedGraph S) (action targets conditionedW : NodeSet S)
    (absorbs : forall i, conditionedW i = true ->
      ancestralInBar G action targets i = true -> targets i = true)
    {length : Nat} {source target node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar action))
      length source target)
    (minimal : forall target' alternative,
      targets target' = true ->
        Nonempty (FiniteReachability.ExactWalk
          (G.observedDirectedEdge (GraphMutilation.bar action))
          alternative source target') ->
          length <= alternative)
    (selected : targets target = true)
    (member : node ∈ walk.nodes)
    (internal : node ≠ target)
    (sourceOpen :
      ObservedGraph.blockedBy (NodeSet.union action conditionedW)
        (.observed source) = false) :
    ObservedGraph.blockedBy (NodeSet.union action conditionedW)
      (.observed node) = false := by
  by_cases hsrc : node = source
  · subst node
    exact sourceOpen
  · have hact : action node = false := by
      have hin :
          (GraphMutilation.bar action).removeIncoming node = false :=
        PathSpecification.directed_walk_mem_not_removeIncoming G
          (GraphMutilation.bar action) walk member hsrc
      simpa [GraphMutilation.bar] using hin
    have hw : conditionedW node = false := by
      cases hsel : conditionedW node with
      | false =>
          rfl
      | true =>
          have hanc : ancestralInBar G action targets node = true :=
            G.observedAncestorOf_of_mem_walk (GraphMutilation.bar action)
              targets walk selected member
          have inTargets := absorbs node hsel hanc
          have notTarget :=
            walk.not_mem_targets_of_minimal_internal minimal member internal
          rw [inTargets] at notTarget
          contradiction
    simp [ObservedGraph.blockedBy, NodeSet.union, hact, hw]

/-- `Z` is disjoint from both `X` and `W`, so those vertices are open in
the rule-1 side graph. -/
theorem blockedBy_false_of_mem_z
    (x y z w : NodeSet S) (disjoint : FourWayDisjoint x y z w)
    {i : Fin S.count} (hz : z i = true) :
    ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) = false := by
  have hx : x i = false := by
    cases hx : x i with
    | false =>
        rfl
    | true =>
        have hz' := disjoint.xz i hx
        rw [hz] at hz'
        contradiction
  have hw : w i = false := disjoint.zw i hz
  simp [ObservedGraph.blockedBy, NodeSet.union, hx, hw]

/-- `Y` is likewise open given `X ∪ W`. -/
theorem blockedBy_false_of_mem_y
    (x y z w : NodeSet S) (disjoint : FourWayDisjoint x y z w)
    {i : Fin S.count} (hy : y i = true) :
    ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) = false := by
  have hx : x i = false := by
    cases hx : x i with
    | false =>
        rfl
    | true =>
        have hy' := disjoint.xy i hx
        rw [hy] at hy'
        contradiction
  have hw : w i = false := disjoint.yw i hy
  simp [ObservedGraph.blockedBy, NodeSet.union, hx, hw]

/-- Open given `X ∪ W` means incoming arrows were not cut in `G_{\overline{X}}`. -/
theorem bar_removeIncoming_false_of_open
    (x w : NodeSet S) {i : Fin S.count}
    (hopen : ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) =
      false) :
    (GraphMutilation.bar x).removeIncoming i = false := by
  simp [ObservedGraph.blockedBy, NodeSet.union, GraphMutilation.bar] at hopen ⊢
  exact hopen.1

/-- Incoming arrows in `G_{\overline{X}}` survive at any vertex outside `X`. -/
theorem bar_removeIncoming_false_of_not_action
    (x : NodeSet S) {i : Fin S.count} (hx : x i = false) :
    (GraphMutilation.bar x).removeIncoming i = false := by
  simp [GraphMutilation.bar, hx]

/-- A shortest left-family walk that ends in `Z` is open at every vertex. -/
theorem blockedBy_false_of_minimal_left_walk_to_z
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    {length : Nat} {source target node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (minimal : forall target' alternative,
      rule1LeftTargets G x z w target' = true ->
        Nonempty (FiniteReachability.ExactWalk
          (G.observedDirectedEdge (GraphMutilation.bar x))
          alternative source target') ->
          length <= alternative)
    (hz : z target = true)
    (member : node ∈ walk.nodes)
    (sourceOpen :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
        false) :
    ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) = false := by
  by_cases hend : node = target
  · subst node
    exact blockedBy_false_of_mem_z x y z w disjoint hz
  · have selected : rule1LeftTargets G x z w target = true := by
      simp [rule1LeftTargets, NodeSet.union, hz]
    exact blockedBy_false_of_minimal_ancestral_internal G x
      (rule1LeftTargets G x z w) w
      (fun i hw hanc => rule1Left_absorbs_w G x z w hw hanc)
      walk minimal selected member hend sourceOpen

/--
Path d-separation of `Y` from `Z` given `X ∪ W` forbids a shortest
left-family walk that starts in `Y` and ends in `Z`.
-/
theorem pathDSeparated_no_minimal_y_walk_to_z
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (simple : walk.nodes.Nodup)
    (minimal : forall target' alternative,
      rule1LeftTargets G x z w target' = true ->
        Nonempty (FiniteReachability.ExactWalk
          (G.observedDirectedEdge (GraphMutilation.bar x))
          alternative source target') ->
          length <= alternative)
    (hy : y source = true) (hz : z target = true) :
    False :=
  pathDSeparated_no_open_directed_walk G (GraphMutilation.bar x) y z
    (NodeSet.union x w) separated walk simple hy hz
    (fun _node member =>
      blockedBy_false_of_minimal_left_walk_to_z G x y z w disjoint walk
        minimal hz member (blockedBy_false_of_mem_y x y z w disjoint hy))

/--
Path d-separation of `Y` from `Z` given `X ∪ W` forbids a bidirected edge
from the source of a shortest left-family walk that ends in `Z` onto any
vertex of `Y`.
-/
theorem pathDSeparated_no_bidirected_y_of_left_walk_to_z
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {length : Nat} {source target other : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (simple : walk.nodes.Nodup)
    (minimal : forall target' alternative,
      rule1LeftTargets G x z w target' = true ->
        Nonempty (FiniteReachability.ExactWalk
          (G.observedDirectedEdge (GraphMutilation.bar x))
          alternative source target') ->
          length <= alternative)
    (hz : z target = true) (hy : y other = true)
    (sourceOpen :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
        false) :
    G.bidirected source other = false :=
  pathDSeparated_no_bidirected_of_open_directed_walk G
    (GraphMutilation.bar x) y z (NodeSet.union x w) separated walk simple
    (fun _node member =>
      blockedBy_false_of_minimal_left_walk_to_z G x y z w disjoint walk
        minimal hz member sourceOpen)
    hz hy
    (blockedBy_false_of_mem_y x y z w disjoint hy)
    (bar_removeIncoming_false_of_open x w sourceOpen)
    (bar_removeIncoming_false_of_open x w
      (blockedBy_false_of_mem_y x y z w disjoint hy))

/--
Rule 1 forbids a bidirected edge between the sources of all-open directed
walks into `Z` and `Y`.  The families are swapped by path symmetry so the
general source-glue applies.
-/
theorem pathDSeparated_no_bidirected_open_walk_sources_yz
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {lengthZ lengthY : Nat} {sourceZ sourceY zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : z zEnd = true) (hy : y yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false) :
    G.bidirected sourceZ sourceY = false :=
  pathDSeparated_no_bidirected_open_walk_sources G (GraphMutilation.bar x)
    z y (NodeSet.union x w)
    (PathSpecification.PathDSeparated.symm separated)
    walkZ walkY simpleZ simpleY hz hy openZ openY
    (bar_removeIncoming_false_of_open x w
      (openZ sourceZ walkZ.mem_source))
    (bar_removeIncoming_false_of_open x w
      (openY sourceY walkY.mem_source))

/--
Path d-separation of `Y` from `Z` given `X ∪ W` forbids two all-open
directed walks into the families joined by a pair of bidirected edges
through a conditioned collider.
-/
theorem pathDSeparated_no_bidirected_collider_open_walks_yz
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {lengthZ lengthY : Nat}
    {sourceZ sourceY collider zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : z zEnd = true) (hy : y yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (hedgeLeft : G.bidirected sourceZ collider = true)
    (hedgeRight : G.bidirected collider sourceY = true)
    (hx : x collider = false)
    (hw : w collider = true) :
    False := by
  have colliderBlocked :
      ObservedGraph.blockedBy (NodeSet.union x w)
        (.observed collider) = true := by
    simp [ObservedGraph.blockedBy, NodeSet.union, hw]
  have colliderNotOnZ : collider ∉ walkZ.nodes := by
    intro member
    have hopen := openZ collider member
    simp [hopen] at colliderBlocked
  have colliderNotOnY : collider ∉ walkY.nodes := by
    intro member
    have hopen := openY collider member
    simp [hopen] at colliderBlocked
  have sourceZNeCollider : sourceZ ≠ collider := by
    intro heq
    subst collider
    exact Bool.false_ne_true
      ((openZ sourceZ walkZ.mem_source).symm.trans colliderBlocked)
  have sourceYNeCollider : sourceY ≠ collider := by
    intro heq
    subst collider
    exact Bool.false_ne_true
      ((openY sourceY walkY.mem_source).symm.trans colliderBlocked)
  have sourceZNeSourceY : sourceZ ≠ sourceY := by
    intro heq
    subst sourceY
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      walkZ walkY simpleZ simpleY hz hy openZ openY
  have notOnZ : sourceY ∉ walkZ.nodes := by
    intro member
    rcases walkZ.exists_simple_suffix_of_mem simpleZ member with
      ⟨_slen, swalk, ssimple, _pre, hnodes⟩
    have subset : forall n, n ∈ swalk.nodes -> n ∈ walkZ.nodes :=
      fun n hn => by
        rw [hnodes]
        exact List.mem_append.mpr (Or.inr hn)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      swalk walkY ssimple simpleY hz hy
      (fun n hn => openZ n (subset n hn)) openY
  have notOnY : sourceZ ∉ walkY.nodes := by
    intro member
    rcases walkY.exists_simple_suffix_of_mem simpleY member with
      ⟨_slen, swalk, ssimple, _pre, hnodes⟩
    have subset : forall n, n ∈ swalk.nodes -> n ∈ walkY.nodes :=
      fun n hn => by
        rw [hnodes]
        exact List.mem_append.mpr (Or.inr hn)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      walkZ swalk simpleZ ssimple hz hy openZ
      (fun n hn => openY n (subset n hn))
  have disjointWalks :
      forall n, n ∈ walkZ.nodes -> n ∈ walkY.nodes -> False := by
    intro n hnZ hnY
    rcases walkZ.exists_simple_suffix_of_mem simpleZ hnZ with
      ⟨_lenZ, sufZ, simpleSufZ, _preZ, hnodesZ⟩
    rcases walkY.exists_simple_suffix_of_mem simpleY hnY with
      ⟨_lenY, sufY, simpleSufY, _preY, hnodesY⟩
    have subZ : forall m, m ∈ sufZ.nodes -> m ∈ walkZ.nodes :=
      fun m hm => by
        rw [hnodesZ]
        exact List.mem_append.mpr (Or.inr hm)
    have subY : forall m, m ∈ sufY.nodes -> m ∈ walkY.nodes :=
      fun m hm => by
        rw [hnodesY]
        exact List.mem_append.mpr (Or.inr hm)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      sufZ sufY simpleSufZ simpleSufY hz hy
      (fun m hm => openZ m (subZ m hm))
      (fun m hm => openY m (subY m hm))
  have activated :
      PathSpecification.ColliderActivated G (GraphMutilation.bar x)
        (NodeSet.union x w) (.observed collider) :=
    G.ancestorOf_target (GraphMutilation.bar x) (NodeSet.union x w)
      (by simp [NodeSet.union, hw])
  exact separated
    ⟨yEnd, zEnd, hy, hz,
      ⟨(PathSpecification.ActivePath.ofOpenWalks_glue_bidirected_collider G
          (GraphMutilation.bar x) (NodeSet.union x w) walkZ walkY simpleZ
          simpleY openZ openY hedgeLeft hedgeRight sourceZNeCollider
          sourceYNeCollider sourceZNeSourceY
          (bar_removeIncoming_false_of_open x w
            (openZ sourceZ walkZ.mem_source))
          (bar_removeIncoming_false_of_not_action x hx)
          (bar_removeIncoming_false_of_open x w
            (openY sourceY walkY.mem_source))
          activated colliderNotOnZ colliderNotOnY notOnZ notOnY
          disjointWalks).reverse⟩⟩

/-- `Z` vertices are open given `X ∪ W` and are ancestors of themselves. -/
theorem rule1Z_subset_leftOpenCore (G : ObservedGraph S)
    (x y z w : NodeSet S) (disjoint : FourWayDisjoint x y z w)
    {i : Fin S.count} (hi : z i = true) :
    rule1LeftOpenCore G x z w i = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · simpa [rule1LeftOpenCore, openAncestralIn] using
      blockedBy_false_of_mem_z x y z w disjoint hi
  · simpa [rule1LeftOpenCore, openAncestralIn, ancestralInBar] using
      observedAncestorOf_self G (GraphMutilation.bar (NodeSet.union x w)) z hi

/-- `Y` vertices are open given `X ∪ W` and are ancestors of themselves. -/
theorem rule1Y_subset_rightOpenCore (G : ObservedGraph S)
    (x y z w : NodeSet S) (disjoint : FourWayDisjoint x y z w)
    {i : Fin S.count} (hi : y i = true) :
    rule1RightOpenCore G x y z w i = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · simpa [rule1RightOpenCore, openAncestralIn] using
      blockedBy_false_of_mem_y x y z w disjoint hi
  · simpa [rule1RightOpenCore, openAncestralIn, ancestralInBar] using
      observedAncestorOf_self G (GraphMutilation.bar (NodeSet.union x w)) y hi

/--
A vertex cannot be an open ancestor of both `Z` and `Y`: that would be an
all-open directed fork, which path d-separation forbids.
-/
theorem rule1OpenCores_disjoint (G : ObservedGraph S)
    (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w)) :
    NodeSet.Disjoint (rule1LeftOpenCore G x z w)
      (rule1RightOpenCore G x y z w) := by
  intro i hiL
  cases hR : rule1RightOpenCore G x y z w i with
  | false =>
      rfl
  | true =>
      rcases openAncestralIn_exists_open_walk G x w z i (by
          simpa [rule1LeftOpenCore] using hiL) with
        ⟨zEnd, hz, _lengthZ, walkZ, simpleZ, openZ⟩
      rcases openAncestralIn_exists_open_walk G x w y i (by
          simpa [rule1RightOpenCore] using hR) with
        ⟨yEnd, hy, _lengthY, walkY, simpleY, openY⟩
      exact (pathDSeparated_no_open_directed_fork_yz G x y z w separated
        walkZ walkY simpleZ simpleY hz hy openZ openY).elim

/--
Path d-separation forbids a bidirected edge between the open ancestral cores
of `Z` and `Y`.
-/
theorem rule1OpenCores_no_bidirected (G : ObservedGraph S)
    (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {leftNode rightNode : Fin S.count}
    (hleft : rule1LeftOpenCore G x z w leftNode = true)
    (hright : rule1RightOpenCore G x y z w rightNode = true) :
    G.bidirected leftNode rightNode = false := by
  rcases openAncestralIn_exists_open_walk G x w z leftNode (by
      simpa [rule1LeftOpenCore] using hleft) with
    ⟨zEnd, hz, lengthZ, walkZ, simpleZ, openZ⟩
  rcases openAncestralIn_exists_open_walk G x w y rightNode (by
      simpa [rule1RightOpenCore] using hright) with
    ⟨yEnd, hy, lengthY, walkY, simpleY, openY⟩
  exact pathDSeparated_no_bidirected_open_walk_sources_yz G x y z w separated
    walkZ walkY simpleZ simpleY hz hy openZ openY

/-- When the mutilation's incoming cut is exactly the conditioning set,
an open ancestral vertex supplies a simple all-open directed walk in
that same mutilated DAG.  Empty-`W` rule 2 is the instance
`m = G_{\overline{X}\underline{Z}}`, `conditioned = X`. -/
theorem openAncestralInGraph_exists_open_walk
    (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned targets : NodeSet S) (source : Fin S.count)
    (hcut : forall i,
      m.removeIncoming i =
        ObservedGraph.blockedBy conditioned (.observed i))
    (h : openAncestralInGraph G m conditioned targets source = true) :
    Exists fun target : Fin S.count =>
      targets target = true /\
        Exists fun length : Nat =>
          Exists fun walk :
              FiniteReachability.ExactWalk
                (G.observedDirectedEdge m) length source target =>
            walk.nodes.Nodup /\
              (forall n, n ∈ walk.nodes ->
                ObservedGraph.blockedBy conditioned (.observed n) =
                  false) := by
  have hparts :
      ObservedGraph.blockedBy conditioned (.observed source) = false ∧
        G.observedAncestorOf m targets source = true := by
    simpa [openAncestralInGraph] using h
  rcases G.exists_minimal_walk_of_observedAncestorOf m targets source
      hparts.2 with
    ⟨target, htarget, length, walk, simple, _minimal⟩
  refine ⟨target, htarget, length, walk, simple, ?_⟩
  intro n hn
  by_cases hsrc : n = source
  · subst n
    exact hparts.1
  · have hin :=
      PathSpecification.directed_walk_mem_not_removeIncoming G m walk hn
        hsrc
    have hblocked :
        ObservedGraph.blockedBy conditioned (.observed n) =
          m.removeIncoming n :=
      (hcut n).symm
    simpa [hblocked] using hin

/-- The incoming cut of `G_{\overline{X ∪ W}\underline{Z}}` is exactly the
conditioning set `X ∪ W`. -/
theorem barUnderline_union_removeIncoming_eq_blocked
    (x z w : NodeSet S) (i : Fin S.count) :
    (GraphMutilation.barUnderline (NodeSet.union x w) z).removeIncoming i =
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) := by
  simp [GraphMutilation.barUnderline, ObservedGraph.blockedBy]

/-- Empty `W` makes the rule-2 incoming cut `X` agree with the
conditioning set `X ∪ W`. -/
theorem barUnderline_removeIncoming_eq_blocked_of_empty_w
    (x z w : NodeSet S) (hw : NodeSet.isEmpty w = true)
    (i : Fin S.count) :
    (GraphMutilation.barUnderline x z).removeIncoming i =
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) := by
  have hact : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  simpa [hact, NodeSet.union_empty_right] using
    barUnderline_union_removeIncoming_eq_blocked x z w i

/-- Membership in a rule-2 open core supplies a simple all-open directed
walk in the rule-2 graph `G_{\overline{X}\underline{Z}}`.  Ancestry is
computed after also cutting `W`; the walk is then mapped onto the lighter
mutilation. -/
theorem rule2_exists_open_walk
    (G : ObservedGraph S) (x z w targets : NodeSet S)
    (source : Fin S.count)
    (h : openAncestralInGraph G
      (GraphMutilation.barUnderline (NodeSet.union x w) z)
      (NodeSet.union x w) targets source = true) :
    Exists fun target : Fin S.count =>
      targets target = true /\
        Exists fun length : Nat =>
          Exists fun walk :
              FiniteReachability.ExactWalk
                (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
                length source target =>
            walk.nodes.Nodup /\
              (forall n, n ∈ walk.nodes ->
                ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) =
                  false) := by
  rcases openAncestralInGraph_exists_open_walk G
      (GraphMutilation.barUnderline (NodeSet.union x w) z)
      (NodeSet.union x w) targets source
      (barUnderline_union_removeIncoming_eq_blocked x z w) h with
    ⟨target, htarget, length, walk, simple, openNodes⟩
  let included :=
    fun parent child hedge =>
      observedDirectedEdge_barUnderline_of_unionBarUnderline G x w z
        (parent := parent) (child := child) hedge
  let mapped := FiniteReachability.ExactWalk.mapEdge included walk
  have hnodes : mapped.nodes = walk.nodes :=
    FiniteReachability.ExactWalk.mapEdge_nodes included walk
  refine ⟨target, htarget, length, mapped, ?_, ?_⟩
  · simpa [hnodes] using simple
  · intro n hn
    have hn' : n ∈ walk.nodes := by
      simpa [hnodes] using hn
    exact openNodes n hn'

/-- Path d-separation in `G_{\overline{X}\underline{Z}}` forbids a pair of
all-open directed walks from a common source. -/
theorem pathDSeparated_no_open_directed_fork_rule2
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    {lengthZ lengthY : Nat} {shared zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      lengthZ shared zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      lengthY shared yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : z zEnd = true) (hy : y yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false) :
    False :=
  separated
    ⟨yEnd, zEnd, hy, hz,
      ⟨(PathSpecification.ActivePath.ofOpenDirectedFork G
          (GraphMutilation.barUnderline x z) (NodeSet.union x w)
          walkZ walkY simpleZ simpleY openZ openY).reverse⟩⟩

/-- Empty-`W` rule 2 forbids a pair of all-open directed walks from a
common source in `G_{\overline{X}\underline{Z}}`. -/
theorem pathDSeparated_no_open_directed_fork_rule2_empty_w
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (_hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    {lengthZ lengthY : Nat} {shared zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      lengthZ shared zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
      lengthY shared yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : z zEnd = true) (hy : y yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false) :
    False :=
  pathDSeparated_no_open_directed_fork_rule2 G x y z w separated
    walkZ walkY simpleZ simpleY hz hy openZ openY

/-- A vertex cannot be an open ancestor of both `Z` and `Y` in
`G_{\overline{X ∪ W}\underline{Z}}`. -/
theorem rule2OpenCores_disjoint
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    NodeSet.Disjoint (rule2ZOpenCore G x z w)
      (rule2YOpenCore G x y z w) := by
  intro i hiL
  cases hR : rule2YOpenCore G x y z w i with
  | false =>
      rfl
  | true =>
      rcases rule2_exists_open_walk G x z w z i
          (by simpa [rule2ZOpenCore] using hiL) with
        ⟨zEnd, hz, _lengthZ, walkZ, simpleZ, openZ⟩
      rcases rule2_exists_open_walk G x z w y i
          (by simpa [rule2YOpenCore] using hR) with
        ⟨yEnd, hy, _lengthY, walkY, simpleY, openY⟩
      exact (pathDSeparated_no_open_directed_fork_rule2 G x y z w
        separated walkZ walkY simpleZ simpleY hz hy openZ openY).elim

/-- A vertex cannot be an open ancestor of both `Z` and `Y` in
`G_{\overline{X}\underline{Z}}` when `W` is empty. -/
theorem rule2OpenCores_disjoint_of_empty_w
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (_hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    NodeSet.Disjoint (rule2ZOpenCore G x z w)
      (rule2YOpenCore G x y z w) :=
  rule2OpenCores_disjoint G x y z w separated

/-- An open core vertex is outside `X`, so its incoming arrows survive in
`G_{\overline{X}\underline{Z}}`. -/
theorem rule2OpenCore_removeIncoming_false
    (_G : ObservedGraph S) (x z w : NodeSet S) {i : Fin S.count}
    (hopen : ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) =
      false) :
    (GraphMutilation.barUnderline x z).removeIncoming i = false := by
  have hunion : NodeSet.union x w i = false := by
    simpa [ObservedGraph.blockedBy] using hopen
  have hx : x i = false := (Bool.or_eq_false_iff.mp hunion).1
  simp [GraphMutilation.barUnderline, hx]

/-- Path d-separation forbids a bidirected edge between the rule-2 open
cores. -/
theorem rule2OpenCores_no_bidirected
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    {leftNode rightNode : Fin S.count}
    (hleft : rule2ZOpenCore G x z w leftNode = true)
    (hright : rule2YOpenCore G x y z w rightNode = true) :
    G.bidirected leftNode rightNode = false := by
  rcases rule2_exists_open_walk G x z w z leftNode
      (by simpa [rule2ZOpenCore] using hleft) with
    ⟨zEnd, hz, _lengthZ, walkZ, simpleZ, openZ⟩
  rcases rule2_exists_open_walk G x z w y rightNode
      (by simpa [rule2YOpenCore] using hright) with
    ⟨yEnd, hy, _lengthY, walkY, simpleY, openY⟩
  have hcutZ :
      (GraphMutilation.barUnderline x z).removeIncoming leftNode =
        false :=
    rule2OpenCore_removeIncoming_false G x z w (by
      simpa [openAncestralInGraph, rule2ZOpenCore] using
        (Bool.and_eq_true_iff.mp hleft).1)
  have hcutY :
      (GraphMutilation.barUnderline x z).removeIncoming rightNode =
        false :=
    rule2OpenCore_removeIncoming_false G x z w (by
      simpa [openAncestralInGraph, rule2YOpenCore] using
        (Bool.and_eq_true_iff.mp hright).1)
  exact pathDSeparated_no_bidirected_open_walk_sources G
    (GraphMutilation.barUnderline x z) z y (NodeSet.union x w)
    (PathSpecification.PathDSeparated.symm separated)
    walkZ walkY simpleZ simpleY hz hy openZ openY hcutZ hcutY

/-- Empty-`W` rule 2 forbids a bidirected edge between the open cores. -/
theorem rule2OpenCores_no_bidirected_of_empty_w
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (_hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    {leftNode rightNode : Fin S.count}
    (hleft : rule2ZOpenCore G x z w leftNode = true)
    (hright : rule2YOpenCore G x y z w rightNode = true) :
    G.bidirected leftNode rightNode = false :=
  rule2OpenCores_no_bidirected G x y z w separated hleft hright

/--
The same conclusion as `pathDSeparated_no_bidirected_collider_open_walks_yz`,
but the middle vertex need only be an *ancestor* of the conditioning set.
A collider on a descendant of `W` is activated even when it is not itself
in `W`.
-/
theorem pathDSeparated_no_bidirected_collider_open_walks_yz_of_activated
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {lengthZ lengthY : Nat}
    {sourceZ sourceY collider zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : z zEnd = true) (hy : y yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (hedgeLeft : G.bidirected sourceZ collider = true)
    (hedgeRight : G.bidirected collider sourceY = true)
    (hx : x collider = false)
    (activated : PathSpecification.ColliderActivated G
      (GraphMutilation.bar x) (NodeSet.union x w) (.observed collider)) :
    False := by
  have sourceZNeCollider : sourceZ ≠ collider := by
    intro heq
    subst collider
    exact Bool.false_ne_true
      ((G.bidirected_irreflexive sourceZ).symm.trans hedgeLeft)
  have sourceYNeCollider : sourceY ≠ collider := by
    intro heq
    subst collider
    exact Bool.false_ne_true
      ((G.bidirected_irreflexive sourceY).symm.trans hedgeRight)
  have sourceZNeSourceY : sourceZ ≠ sourceY := by
    intro heq
    subst sourceY
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      walkZ walkY simpleZ simpleY hz hy openZ openY
  have sourceYCore :
      openAncestralIn G (NodeSet.union x w) y sourceY = true :=
    openAncestralIn_of_mem_open_directed_walk G x w y walkY hy openY
      walkY.mem_source
  have sourceZCore :
      openAncestralIn G (NodeSet.union x w) z sourceZ = true :=
    openAncestralIn_of_mem_open_directed_walk G x w z walkZ hz openZ
      walkZ.mem_source
  have colliderNotOnZ : collider ∉ walkZ.nodes := by
    intro member
    have hZcore :=
      openAncestralIn_of_mem_open_directed_walk G x w z walkZ hz openZ
        member
    have hfalse :=
      rule1OpenCores_no_bidirected G x y z w separated
        (by simpa [rule1LeftOpenCore] using hZcore)
        (by simpa [rule1RightOpenCore] using sourceYCore)
    exact Bool.false_ne_true (hfalse.symm.trans hedgeRight)
  have colliderNotOnY : collider ∉ walkY.nodes := by
    intro member
    have hYcore :=
      openAncestralIn_of_mem_open_directed_walk G x w y walkY hy openY
        member
    have hfalse :=
      rule1OpenCores_no_bidirected G x y z w separated
        (by simpa [rule1LeftOpenCore] using sourceZCore)
        (by simpa [rule1RightOpenCore] using hYcore)
    exact Bool.false_ne_true (hfalse.symm.trans hedgeLeft)
  have notOnZ : sourceY ∉ walkZ.nodes := by
    intro member
    rcases walkZ.exists_simple_suffix_of_mem simpleZ member with
      ⟨_slen, swalk, ssimple, _pre, hnodes⟩
    have subset : forall n, n ∈ swalk.nodes -> n ∈ walkZ.nodes :=
      fun n hn => by
        rw [hnodes]
        exact List.mem_append.mpr (Or.inr hn)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      swalk walkY ssimple simpleY hz hy
      (fun n hn => openZ n (subset n hn)) openY
  have notOnY : sourceZ ∉ walkY.nodes := by
    intro member
    rcases walkY.exists_simple_suffix_of_mem simpleY member with
      ⟨_slen, swalk, ssimple, _pre, hnodes⟩
    have subset : forall n, n ∈ swalk.nodes -> n ∈ walkY.nodes :=
      fun n hn => by
        rw [hnodes]
        exact List.mem_append.mpr (Or.inr hn)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      walkZ swalk simpleZ ssimple hz hy openZ
      (fun n hn => openY n (subset n hn))
  have disjointWalks :
      forall n, n ∈ walkZ.nodes -> n ∈ walkY.nodes -> False := by
    intro n hnZ hnY
    rcases walkZ.exists_simple_suffix_of_mem simpleZ hnZ with
      ⟨_lenZ, sufZ, simpleSufZ, _preZ, hnodesZ⟩
    rcases walkY.exists_simple_suffix_of_mem simpleY hnY with
      ⟨_lenY, sufY, simpleSufY, _preY, hnodesY⟩
    have subZ : forall m, m ∈ sufZ.nodes -> m ∈ walkZ.nodes :=
      fun m hm => by
        rw [hnodesZ]
        exact List.mem_append.mpr (Or.inr hm)
    have subY : forall m, m ∈ sufY.nodes -> m ∈ walkY.nodes :=
      fun m hm => by
        rw [hnodesY]
        exact List.mem_append.mpr (Or.inr hm)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      sufZ sufY simpleSufZ simpleSufY hz hy
      (fun m hm => openZ m (subZ m hm))
      (fun m hm => openY m (subY m hm))
  exact separated
    ⟨yEnd, zEnd, hy, hz,
      ⟨(PathSpecification.ActivePath.ofOpenWalks_glue_bidirected_collider G
          (GraphMutilation.bar x) (NodeSet.union x w) walkZ walkY simpleZ
          simpleY openZ openY hedgeLeft hedgeRight sourceZNeCollider
          sourceYNeCollider sourceZNeSourceY
          (bar_removeIncoming_false_of_open x w
            (openZ sourceZ walkZ.mem_source))
          (bar_removeIncoming_false_of_not_action x hx)
          (bar_removeIncoming_false_of_open x w
            (openY sourceY walkY.mem_source))
          activated colliderNotOnZ colliderNotOnY notOnZ notOnY
          disjointWalks).reverse⟩⟩

/--
Path d-separation of `Y` from `Z` given `X ∪ W` forbids two all-open
directed walks into the families joined by two bidirected colliders.
-/
theorem pathDSeparated_no_two_bidirected_colliders_open_walks_yz
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    {lengthZ lengthY : Nat}
    {sourceZ sourceY first second zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (hz : z zEnd = true) (hy : y yEnd = true)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed n) = false)
    (hedgeLeft : G.bidirected sourceZ first = true)
    (hedgeMid : G.bidirected first second = true)
    (hedgeRight : G.bidirected second sourceY = true)
    (hxFirst : x first = false)
    (hxSecond : x second = false)
    (blockedFirst :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed first) = true)
    (blockedSecond :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed second) = true)
    (activatedFirst : PathSpecification.ColliderActivated G
      (GraphMutilation.bar x) (NodeSet.union x w) (.observed first))
    (activatedSecond : PathSpecification.ColliderActivated G
      (GraphMutilation.bar x) (NodeSet.union x w) (.observed second)) :
    False := by
  have sourceZNeFirst : sourceZ ≠ first := by
    intro heq
    subst first
    exact Bool.false_ne_true
      ((openZ sourceZ walkZ.mem_source).symm.trans blockedFirst)
  have sourceZNeSecond : sourceZ ≠ second := by
    intro heq
    subst second
    exact Bool.false_ne_true
      ((openZ sourceZ walkZ.mem_source).symm.trans blockedSecond)
  have sourceYNeFirst : sourceY ≠ first := by
    intro heq
    subst first
    exact Bool.false_ne_true
      ((openY sourceY walkY.mem_source).symm.trans blockedFirst)
  have sourceYNeSecond : sourceY ≠ second := by
    intro heq
    subst second
    exact Bool.false_ne_true
      ((openY sourceY walkY.mem_source).symm.trans blockedSecond)
  have sourceZNeSourceY : sourceZ ≠ sourceY := by
    intro heq
    subst sourceY
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      walkZ walkY simpleZ simpleY hz hy openZ openY
  have firstNeSecond : first ≠ second := by
    intro heq
    subst second
    exact Bool.false_ne_true
      ((G.bidirected_irreflexive first).symm.trans hedgeMid)
  have firstNotOnZ : first ∉ walkZ.nodes := by
    intro member
    exact Bool.false_ne_true
      ((openZ first member).symm.trans blockedFirst)
  have secondNotOnZ : second ∉ walkZ.nodes := by
    intro member
    exact Bool.false_ne_true
      ((openZ second member).symm.trans blockedSecond)
  have firstNotOnY : first ∉ walkY.nodes := by
    intro member
    exact Bool.false_ne_true
      ((openY first member).symm.trans blockedFirst)
  have secondNotOnY : second ∉ walkY.nodes := by
    intro member
    exact Bool.false_ne_true
      ((openY second member).symm.trans blockedSecond)
  have notOnZ : sourceY ∉ walkZ.nodes := by
    intro member
    rcases walkZ.exists_simple_suffix_of_mem simpleZ member with
      ⟨_slen, swalk, ssimple, _pre, hnodes⟩
    have subset : forall n, n ∈ swalk.nodes -> n ∈ walkZ.nodes :=
      fun n hn => by
        rw [hnodes]
        exact List.mem_append.mpr (Or.inr hn)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      swalk walkY ssimple simpleY hz hy
      (fun n hn => openZ n (subset n hn)) openY
  have notOnY : sourceZ ∉ walkY.nodes := by
    intro member
    rcases walkY.exists_simple_suffix_of_mem simpleY member with
      ⟨_slen, swalk, ssimple, _pre, hnodes⟩
    have subset : forall n, n ∈ swalk.nodes -> n ∈ walkY.nodes :=
      fun n hn => by
        rw [hnodes]
        exact List.mem_append.mpr (Or.inr hn)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      walkZ swalk simpleZ ssimple hz hy openZ
      (fun n hn => openY n (subset n hn))
  have disjointWalks :
      forall n, n ∈ walkZ.nodes -> n ∈ walkY.nodes -> False := by
    intro n hnZ hnY
    rcases walkZ.exists_simple_suffix_of_mem simpleZ hnZ with
      ⟨_lenZ, sufZ, simpleSufZ, _preZ, hnodesZ⟩
    rcases walkY.exists_simple_suffix_of_mem simpleY hnY with
      ⟨_lenY, sufY, simpleSufY, _preY, hnodesY⟩
    have subZ : forall m, m ∈ sufZ.nodes -> m ∈ walkZ.nodes :=
      fun m hm => by
        rw [hnodesZ]
        exact List.mem_append.mpr (Or.inr hm)
    have subY : forall m, m ∈ sufY.nodes -> m ∈ walkY.nodes :=
      fun m hm => by
        rw [hnodesY]
        exact List.mem_append.mpr (Or.inr hm)
    exact pathDSeparated_no_open_directed_fork_yz G x y z w separated
      sufZ sufY simpleSufZ simpleSufY hz hy
      (fun m hm => openZ m (subZ m hm))
      (fun m hm => openY m (subY m hm))
  exact separated
    ⟨yEnd, zEnd, hy, hz,
      ⟨(PathSpecification.ActivePath.ofOpenWalks_glue_two_bidirected_colliders
          G (GraphMutilation.bar x) (NodeSet.union x w) walkZ walkY simpleZ
          simpleY openZ openY hedgeLeft hedgeMid hedgeRight sourceZNeFirst
          sourceZNeSecond sourceZNeSourceY firstNeSecond
          sourceYNeFirst.symm sourceYNeSecond.symm
          (bar_removeIncoming_false_of_open x w
            (openZ sourceZ walkZ.mem_source))
          (bar_removeIncoming_false_of_not_action x hxFirst)
          (bar_removeIncoming_false_of_not_action x hxSecond)
          (bar_removeIncoming_false_of_open x w
            (openY sourceY walkY.mem_source))
          activatedFirst activatedSecond firstNotOnZ secondNotOnZ
          firstNotOnY secondNotOnY notOnZ notOnY disjointWalks).reverse⟩⟩

/-- Evaluation on a backward-closed node set observes only latent roots
incident to that set. -/
theorem evalNodeUnder_eq_of_rootAgreement (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (closed : model.BackwardClosedUnder intervention nodes)
    (left right : model.latent.Assignment)
    (rootsAgree : forall root,
      model.latentRelevantUnder intervention nodes root = true ->
      left root = right root)
    (child : Fin S.count) (selected : nodes child = true) :
    model.evalNodeUnder intervention left child =
      model.evalNodeUnder intervention right child := by
  rw [evalNodeUnder, evalNodeUnder]
  unfold equationUnder
  cases intervened : intervention child with
  | some value => rfl
  | none =>
      change model.mechanism child _ _ = model.mechanism child _ _
      congr 1
      · funext parent edge
        exact model.evalNodeUnder_eq_of_rootAgreement intervention nodes closed
          left right rootsAgree parent (closed parent child selected intervened edge)
      · funext root incident
        exact rootsAgree root
          (model.latentRelevantUnder_of_incident intervention nodes root child
            selected intervened incident)
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

theorem evalUnder_eq_on_of_rootAgreement (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (closed : model.BackwardClosedUnder intervention nodes)
    (left right : model.latent.Assignment)
    (rootsAgree : forall root,
      model.latentRelevantUnder intervention nodes root = true ->
      left root = right root) :
    forall child, nodes child = true ->
      model.evalUnder intervention left child =
        model.evalUnder intervention right child := by
  intro child selected
  exact model.evalNodeUnder_eq_of_rootAgreement intervention nodes closed
    left right rootsAgree child selected

/-- No latent root is relevant to both node sets. -/
def LatentSeparatedUnder (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (left right : NodeSet S) : Prop :=
  forall root, model.latentRelevantUnder intervention left root = true ->
    model.latentRelevantUnder intervention right root = false

/-- No latent root is relevant to both families, even when the two
families are read under different interventions.  Rule 3's given-`W`
cylinders live under `do(X ∪ W)` for `Y` and under `do(X)` / `do(X ∪ Z)`
for `W`. -/
def LatentSeparatedAcross (model : FiniteLatentSCM S)
    (leftInt : (i : Fin S.count) -> Option (S.Value i))
    (leftNodes : NodeSet S)
    (rightInt : (i : Fin S.count) -> Option (S.Value i))
    (rightNodes : NodeSet S) : Prop :=
  forall root, model.latentRelevantUnder leftInt leftNodes root = true ->
    model.latentRelevantUnder rightInt rightNodes root = false

/-- A heavier intervention can only drop relevance, so latent separation
survives adding more hard interventions. -/
theorem LatentSeparatedUnder.mono (model : FiniteLatentSCM S)
    {heavier lighter : (i : Fin S.count) -> Option (S.Value i)}
    (left right : NodeSet S)
    (freeOfHeavier : forall i, heavier i = none -> lighter i = none)
    (separated : model.LatentSeparatedUnder lighter left right) :
    model.LatentSeparatedUnder heavier left right := by
  intro root leftRelevant
  have leftLighter :=
    model.latentRelevantUnder_mono left root freeOfHeavier leftRelevant
  have rightLighter := separated root leftLighter
  cases rightHeavier :
      model.latentRelevantUnder heavier right root with
  | false =>
      rfl
  | true =>
      have rightAlsoLighter :=
        model.latentRelevantUnder_mono right root freeOfHeavier rightHeavier
      rw [rightLighter] at rightAlsoLighter
      cases rightAlsoLighter

/-- A shared latent parent of two distinct observed nodes is visible as a
bidirected edge in every graph compatible with the model. -/
theorem bidirected_eq_true_of_shared_latent
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (root : Fin model.latent.count) (left right : Fin S.count)
    (different : left ≠ right)
    (leftIncident : model.latent.incident root left = true)
    (rightIncident : model.latent.incident root right = true) :
    G.bidirected left right = true := by
  rw [← projected left right]
  change model.latent.projectedBidirected left right = true
  apply Bool.and_eq_true_iff.mpr
  constructor
  · have valueDifferent : left.val ≠ right.val := by
      intro equal
      exact different (Fin.ext equal)
    cases hbeq : Nat.beq left.val right.val with
    | true =>
        exact (valueDifferent (Nat.eq_of_beq_eq_true hbeq)).elim
    | false =>
        rfl
  · apply finAny_eq_true_of _ root
    exact Bool.and_eq_true_iff.mpr ⟨leftIncident, rightIncident⟩

/-- If two disjoint observed regions have no projected bidirected edge
between them, no non-intervened latent root can be relevant to both. -/
theorem latentSeparatedUnder_of_no_bidirected_across
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (left right : NodeSet S) (disjoint : NodeSet.Disjoint left right)
    (noBidirected : forall leftNode rightNode,
      left leftNode = true -> right rightNode = true ->
        G.bidirected leftNode rightNode = false) :
    model.LatentSeparatedUnder intervention left right := by
  intro root leftRelevant
  cases rightRelevant : model.latentRelevantUnder intervention right root with
  | false => rfl
  | true =>
      rcases (model.latentRelevantUnder_eq_true_iff intervention left root).mp
          leftRelevant with
        ⟨leftNode, leftSelected, _leftFree, leftIncident⟩
      rcases (model.latentRelevantUnder_eq_true_iff intervention right root).mp
          rightRelevant with
        ⟨rightNode, rightSelected, _rightFree, rightIncident⟩
      have different : leftNode ≠ rightNode := by
        intro same
        subst rightNode
        have excluded := disjoint leftNode leftSelected
        rw [rightSelected] at excluded
        contradiction
      have edgeTrue := bidirected_eq_true_of_shared_latent model G projected
        root leftNode rightNode different leftIncident rightIncident
      have edgeFalse := noBidirected leftNode rightNode
        leftSelected rightSelected
      rw [edgeTrue] at edgeFalse
      contradiction

/--
No latent root can be relevant to both open cores: they are disjoint and
share no projected bidirected edge.
-/
theorem rule1OpenCores_latentSeparated
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w)) :
    model.LatentSeparatedUnder
      ((rule1Right x y z w).intervention assignment)
      (rule1LeftOpenCore G x z w) (rule1RightOpenCore G x y z w) :=
  latentSeparatedUnder_of_no_bidirected_across model G projected
    ((rule1Right x y z w).intervention assignment)
    (rule1LeftOpenCore G x z w) (rule1RightOpenCore G x y z w)
    (rule1OpenCores_disjoint G x y z w separated)
    (fun _leftNode _rightNode hleft hright =>
      rule1OpenCores_no_bidirected G x y z w separated hleft hright)

/-- No latent root is relevant to both rule-2 open cores under `do(X)`.
The cores live in `G_{\overline{X ∪ W}\underline{Z}}`, so `Z → Y` does
not put `Z` into the `Y` core. -/
theorem rule2OpenCores_latentSeparated
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    model.LatentSeparatedUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (rule2ZOpenCore G x z w) (rule2YOpenCore G x y z w) :=
  latentSeparatedUnder_of_no_bidirected_across model G projected
    ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
    (rule2ZOpenCore G x z w) (rule2YOpenCore G x y z w)
    (rule2OpenCores_disjoint G x y z w separated)
    (fun _leftNode _rightNode hleft hright =>
      rule2OpenCores_no_bidirected G x y z w separated hleft hright)

/-- No latent root is relevant to both empty-`W` rule-2 open cores under
`do(X)`.  The cores live in `G_{\overline{X}\underline{Z}}`, so `Z → Y`
does not put `Z` into the `Y` core. -/
theorem rule2OpenCores_latentSeparated_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (_hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    model.LatentSeparatedUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (rule2ZOpenCore G x z w) (rule2YOpenCore G x y z w) :=
  rule2OpenCores_latentSeparated model G projected x y z w assignment
    separated

/-- A `do(X)`-free ancestor of `Z` in `G_{\overline{X}}` is already in the
empty-`W` rule-2 open `Z` core. -/
theorem rule2ZOpenCore_of_free_ancestral_of_empty_w
    (G : ObservedGraph S) (x z w : NodeSet S)
    (hw : NodeSet.isEmpty w = true) {i : Fin S.count}
    (hanc : ancestralInBar G x z i = true)
    (hfree : x i = false) :
    rule2ZOpenCore G x z w i = true := by
  have hact : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  have hopen :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) = false := by
    simp [ObservedGraph.blockedBy, hact, NodeSet.union_empty_right, hfree]
  have hbar := observedAncestorOf_barUnderline_z_of_bar G x z i hanc
  have hbarW :
      G.observedAncestorOf
        (GraphMutilation.barUnderline (NodeSet.union x w) z) z i = true := by
    simpa [hact, NodeSet.union_empty_right] using hbar
  simp [rule2ZOpenCore, openAncestralInGraph, hopen, hbarW]

/-- A `do(X ∪ Z)`-free ancestor of `Y` in `G_{\overline{X ∪ Z}}` is already
in the empty-`W` rule-2 open `Y` core. -/
theorem rule2YOpenCore_of_free_ancestral_of_empty_w
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (hw : NodeSet.isEmpty w = true) {i : Fin S.count}
    (hanc : ancestralInBar G (NodeSet.union x z) y i = true)
    (hfree : NodeSet.union x z i = false) :
    rule2YOpenCore G x y z w i = true := by
  have hact : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  have hx : x i = false := by
    cases hx : x i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.union, hx] at hfree
  have hopen :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed i) = false := by
    simp [ObservedGraph.blockedBy, hact, NodeSet.union_empty_right, hx]
  have hbar :=
    observedAncestorOf_barUnderline_y_of_barUnion G x y z i hanc hfree
  have hbarW :
      G.observedAncestorOf
        (GraphMutilation.barUnderline (NodeSet.union x w) z) y i = true := by
    simpa [hact, NodeSet.union_empty_right] using hbar
  simp [rule2YOpenCore, openAncestralInGraph, hopen, hbarW]

/-- A latent relevant to `An(Z)` under `do(X)` is already relevant to the
empty-`W` open `Z` core: its free incident child is in that core. -/
theorem latentRelevantUnder_rule2ZOpenCore_of_ancestral_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true)
    {root : Fin model.latent.count}
    (hrel : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (ancestralInBar G x z) root = true) :
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (rule2ZOpenCore G x z w) root = true := by
  let intervention :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  rcases (model.latentRelevantUnder_eq_true_iff intervention
      (ancestralInBar G x z) root).mp hrel with
    ⟨child, selected, notIntervened, incident⟩
  have hfree : x child = false := by
    dsimp [intervention, Kernel.intervention] at notIntervened
    cases hx : x child with
    | false =>
        rfl
    | true =>
        simp [hx] at notIntervened
  have hopen :=
    rule2ZOpenCore_of_free_ancestral_of_empty_w G x z w hw selected hfree
  exact model.latentRelevantUnder_of_incident intervention
    (rule2ZOpenCore G x z w) root child hopen notIntervened incident

/-- A latent relevant to `An(Y)` under `do(X ∪ Z)` is already relevant to
the empty-`W` open `Y` core under `do(X)`: its free incident child is in
that core, and dropping the extra intervention on `Z` only adds free
nodes. -/
theorem latentRelevantUnder_rule2YOpenCore_of_barUnion_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true)
    {root : Fin model.latent.count}
    (hrel : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (ancestralInBar G (NodeSet.union x z) y) root = true) :
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (rule2YOpenCore G x y z w) root = true := by
  let heavier :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z)
      NodeSet.empty).intervention assignment
  let lighter :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  rcases (model.latentRelevantUnder_eq_true_iff heavier
      (ancestralInBar G (NodeSet.union x z) y) root).mp hrel with
    ⟨child, selected, notIntervened, incident⟩
  have hfree : NodeSet.union x z child = false := by
    dsimp [heavier, Kernel.intervention] at notIntervened
    cases hunion : NodeSet.union x z child with
    | false =>
        rfl
    | true =>
        simp [hunion] at notIntervened
  have hopen :=
    rule2YOpenCore_of_free_ancestral_of_empty_w G x y z w hw selected hfree
  have notIntervenedLight : lighter child = none := by
    have hx : x child = false := by
      cases hx : x child with
      | false =>
          rfl
      | true =>
          simp [NodeSet.union, hx] at hfree
    simp [lighter, Kernel.intervention, hx]
  exact model.latentRelevantUnder_of_incident lighter
    (rule2YOpenCore G x y z w) root child hopen notIntervenedLight incident

/-- Intervening on `W` as well as `X` only drops free nodes. -/
theorem rule1_union_intervention_free_of_heavier
    (x y z w : NodeSet S) (assignment : S.Assignment) {i : Fin S.count}
    (hnone :
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment) i = none) :
    ((rule1Right x y z w).intervention assignment) i = none := by
  cases hx : x i with
  | false =>
      simp [Kernel.intervention, rule1Right, hx]
  | true =>
      simp [Kernel.intervention, NodeSet.union, hx] at hnone

/-- Latent separation of the open cores survives also intervening on `W`. -/
theorem rule1OpenCores_latentSeparated_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w)) :
    model.LatentSeparatedUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (rule1LeftOpenCore G x z w) (rule1RightOpenCore G x y z w) :=
  LatentSeparatedUnder.mono model
    (rule1LeftOpenCore G x z w) (rule1RightOpenCore G x y z w)
    (fun _i hnone =>
      rule1_union_intervention_free_of_heavier x y z w assignment hnone)
    (rule1OpenCores_latentSeparated model G projected x y z w assignment
      separated)

/--
The ancestral sets of `Z` and `Y` in `G_{\overline{X ∪ W}}` may share
intervened vertices, but the latents still relevant after intervening on
`W` are exactly those of the open cores.
-/
theorem rule1Ancestral_latentSeparated_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w)) :
    model.LatentSeparatedUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (ancestralInBar G (NodeSet.union x w) z)
      (ancestralInBar G (NodeSet.union x w) y) := by
  intro root hleft
  have hopen :
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (rule1LeftOpenCore G x z w) root = true := by
    simpa [rule1LeftOpenCore, latentRelevantUnder_openAncestralIn] using hleft
  have hrightOpen :=
    rule1OpenCores_latentSeparated_union model G projected x y z w assignment
      separated root hopen
  simpa [rule1RightOpenCore, latentRelevantUnder_openAncestralIn] using
    hrightOpen

/-- Directed ancestry in `G_{\overline{X}}` is transitive. -/
theorem ancestralInBar_trans (G : ObservedGraph S) (action : NodeSet S)
    {i j : Fin S.count} {targets : NodeSet S}
    (hij : ancestralInBar G action (NodeSet.singleton j) i = true)
    (hjt : ancestralInBar G action targets j = true) :
    ancestralInBar G action targets i = true := by
  have complete :
      forall node : Fin S.count,
        node ∈ List.ofFn (fun k : Fin S.count => k) :=
    fun node => List.mem_ofFn.mpr ⟨node, rfl⟩
  have hanyij :
      (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
        NodeSet.singleton j target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun k : Fin S.count => k))
            (G.observedDirectedEdge (GraphMutilation.bar action))
            (List.ofFn (fun k : Fin S.count => k)).length i target) =
        true := by
    simpa [ancestralInBar, ObservedGraph.observedAncestorOf] using hij
  rcases List.any_eq_true.mp hanyij with ⟨j', jMem, hj'⟩
  have hj'Parts := Bool.and_eq_true_iff.mp hj'
  have hjEq : j' = j := (NodeSet.singleton_eq_true_iff j j').mp hj'Parts.1
  subst j'
  have boundedij :
      FiniteReachability.BoundedWalk
        (G.observedDirectedEdge (GraphMutilation.bar action))
        (List.ofFn (fun k : Fin S.count => k)).length i j :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (List.ofFn (fun k : Fin S.count => k))
      (G.observedDirectedEdge (GraphMutilation.bar action))
      finBeq_eq_true_iff complete
      (List.ofFn (fun k : Fin S.count => k)).length i j).mp hj'Parts.2
  have hanyjt :
      (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
        targets target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun k : Fin S.count => k))
            (G.observedDirectedEdge (GraphMutilation.bar action))
            (List.ofFn (fun k : Fin S.count => k)).length j target) =
        true := by
    simpa [ancestralInBar, ObservedGraph.observedAncestorOf] using hjt
  rcases List.any_eq_true.mp hanyjt with ⟨t, tMem, ht⟩
  have htParts := Bool.and_eq_true_iff.mp ht
  have boundedjt :
      FiniteReachability.BoundedWalk
        (G.observedDirectedEdge (GraphMutilation.bar action))
        (List.ofFn (fun k : Fin S.count => k)).length j t :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (List.ofFn (fun k : Fin S.count => k))
      (G.observedDirectedEdge (GraphMutilation.bar action))
      finBeq_eq_true_iff complete
      (List.ofFn (fun k : Fin S.count => k)).length j t).mp htParts.2
  have reachableit :
      FiniteReachability.Reachable
        (G.observedDirectedEdge (GraphMutilation.bar action)) i t :=
    FiniteReachability.Reachable.of_bounded
      (FiniteReachability.BoundedWalk.trans boundedij boundedjt)
  have boundedit :
      FiniteReachability.BoundedWalk
        (G.observedDirectedEdge (GraphMutilation.bar action))
        (List.ofFn (fun k : Fin S.count => k)).length i t :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun k : Fin S.count => k))
      (G.observedDirectedEdge (GraphMutilation.bar action))
      finBeq_eq_true_iff complete reachableit
  have hyit :
      FiniteReachability.within finBeq
        (List.ofFn (fun k : Fin S.count => k))
        (G.observedDirectedEdge (GraphMutilation.bar action))
        (List.ofFn (fun k : Fin S.count => k)).length i t = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (List.ofFn (fun k : Fin S.count => k))
      (G.observedDirectedEdge (GraphMutilation.bar action))
      finBeq_eq_true_iff complete
      (List.ofFn (fun k : Fin S.count => k)).length i t).mpr boundedit
  have hanyit :
      (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
        targets target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun k : Fin S.count => k))
            (G.observedDirectedEdge (GraphMutilation.bar action))
            (List.ofFn (fun k : Fin S.count => k)).length i target) =
        true :=
    List.any_eq_true.mpr
      ⟨t, tMem, Bool.and_eq_true_iff.mpr ⟨htParts.1, hyit⟩⟩
  simpa [ancestralInBar, ObservedGraph.observedAncestorOf] using hanyit

/-- Enlarging the target set preserves directed ancestry in `G_{\overline{X}}`. -/
theorem ancestralInBar_mono (G : ObservedGraph S) (action : NodeSet S)
    {targets targets' : NodeSet S} (hsub : NodeSet.Subset targets targets')
    {i : Fin S.count}
    (h : ancestralInBar G action targets i = true) :
    ancestralInBar G action targets' i = true :=
  observedAncestorOf_mono G (GraphMutilation.bar action) hsub h

end FiniteLatentSCM

namespace CanonicalFactorization

open Probability.FiniteProduct

/-- Splice two dependent assignments along a decidable coordinate set. -/
def spliceAssignment (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (left right : Assignment n Value) :
    Assignment n Value :=
  fun coordinate => if selected coordinate then left coordinate
    else right coordinate

@[simp] theorem spliceAssignment_selected (n : Nat)
    (Value : Fin n -> Type u) (selected : Fin n -> Bool)
    (left right : Assignment n Value) (coordinate : Fin n)
    (isSelected : selected coordinate = true) :
    spliceAssignment n Value selected left right coordinate =
      left coordinate := by
  simp [spliceAssignment, isSelected]

@[simp] theorem spliceAssignment_unselected (n : Nat)
    (Value : Fin n -> Type u) (selected : Fin n -> Bool)
    (left right : Assignment n Value) (coordinate : Fin n)
    (isUnselected : selected coordinate = false) :
    spliceAssignment n Value selected left right coordinate =
      right coordinate := by
  simp [spliceAssignment, isUnselected]

theorem spliceAssignment_exchange (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (left right : Assignment n Value) :
    spliceAssignment n Value selected
        (spliceAssignment n Value selected left right)
        (spliceAssignment n Value selected right left) = left := by
  funext coordinate
  cases chosen : selected coordinate <;>
    simp [spliceAssignment, chosen]

/-- Swapping any selected family of independent coordinates between two
assignments preserves the product of their point masses. -/
theorem qProduct_splice_mul (n : Nat) (Value : Fin n -> Type u)
    (weight : (coordinate : Fin n) -> Value coordinate -> QProb)
    (selected : Fin n -> Bool) (left right : Assignment n Value) :
    QProb.Equiv
      (QProb.mul
        (qProduct n (fun coordinate => weight coordinate (left coordinate)))
        (qProduct n (fun coordinate => weight coordinate (right coordinate))))
      (QProb.mul
        (qProduct n (fun coordinate => weight coordinate
          (spliceAssignment n Value selected left right coordinate)))
        (qProduct n (fun coordinate => weight coordinate
          (spliceAssignment n Value selected right left coordinate)))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let prefixValue := fun coordinate : Fin n => Value coordinate.castSucc
      let prefixWeight := fun (coordinate : Fin n) => weight coordinate.castSucc
      let prefixSelected := fun coordinate : Fin n => selected coordinate.castSucc
      let leftPrefix : Assignment n prefixValue :=
        fun coordinate => left coordinate.castSucc
      let rightPrefix : Assignment n prefixValue :=
        fun coordinate => right coordinate.castSucc
      have prefixSwap := ih prefixValue prefixWeight prefixSelected
        leftPrefix rightPrefix
      let lastLeft := weight (Fin.last n) (left (Fin.last n))
      let lastRight := weight (Fin.last n) (right (Fin.last n))
      let leftProduct := qProduct n
        (fun coordinate => prefixWeight coordinate (leftPrefix coordinate))
      let rightProduct := qProduct n
        (fun coordinate => prefixWeight coordinate (rightPrefix coordinate))
      let firstSplice := qProduct n (fun coordinate =>
        prefixWeight coordinate
          (spliceAssignment n prefixValue prefixSelected
            leftPrefix rightPrefix coordinate))
      let secondSplice := qProduct n (fun coordinate =>
        prefixWeight coordinate
          (spliceAssignment n prefixValue prefixSelected
            rightPrefix leftPrefix coordinate))
      have groupedLeft : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft leftProduct)
            (QProb.mul lastRight rightProduct))
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul leftProduct rightProduct)) := by
        simp [QProb.Equiv, QProb.mul]
        ac_rfl
      have groupedMiddle : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul leftProduct rightProduct))
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul firstSplice secondSplice)) :=
        QProb.mul_congr (QProb.equiv_refl _)
          (by simpa [leftProduct, rightProduct, firstSplice,
            secondSplice] using prefixSwap)
      have groupedRightFalse : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul firstSplice secondSplice))
          (QProb.mul (QProb.mul lastRight firstSplice)
            (QProb.mul lastLeft secondSplice)) := by
        simp [QProb.Equiv, QProb.mul]
        ac_rfl
      have groupedRightTrue : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul firstSplice secondSplice))
          (QProb.mul (QProb.mul lastLeft firstSplice)
            (QProb.mul lastRight secondSplice)) := by
        simp [QProb.Equiv, QProb.mul]
        ac_rfl
      cases lastSelected : selected (Fin.last n) with
      | false =>
          simpa [qProduct, spliceAssignment, lastSelected, lastLeft,
            lastRight, leftProduct, rightProduct, firstSplice,
            secondSplice, prefixValue, prefixWeight, prefixSelected,
            leftPrefix, rightPrefix] using
            QProb.equiv_trans groupedLeft
              (QProb.equiv_trans groupedMiddle groupedRightFalse)
      | true =>
          simpa [qProduct, spliceAssignment, lastSelected, lastLeft,
            lastRight, leftProduct, rightProduct, firstSplice,
            secondSplice, prefixValue, prefixWeight, prefixSelected,
            leftPrefix, rightPrefix] using
            QProb.equiv_trans groupedLeft
              (QProb.equiv_trans groupedMiddle groupedRightTrue)

/-- An event observes only the coordinates marked by `selected`. -/
def DependsOnSelected (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool) : Prop :=
  forall left right,
    (forall coordinate, selected coordinate = true ->
      left coordinate = right coordinate) ->
    event left = event right

/-- An event observes only the coordinates not marked by `selected`. -/
def DependsOnUnselected (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool) : Prop :=
  forall left right,
    (forall coordinate, selected coordinate = false ->
      left coordinate = right coordinate) ->
    event left = event right

theorem DependsOnSelected.inter (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (leftEvent rightEvent : Assignment n Value -> Bool)
    (leftDepends : DependsOnSelected n Value selected leftEvent)
    (rightDepends : DependsOnSelected n Value selected rightEvent) :
    DependsOnSelected n Value selected
      (Probability.inter leftEvent rightEvent) := by
  intro left right agree
  simp [Probability.inter, leftDepends left right agree,
    rightDepends left right agree]

theorem DependsOnUnselected.inter (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (leftEvent rightEvent : Assignment n Value -> Bool)
    (leftDepends : DependsOnUnselected n Value selected leftEvent)
    (rightDepends : DependsOnUnselected n Value selected rightEvent) :
    DependsOnUnselected n Value selected
      (Probability.inter leftEvent rightEvent) := by
  intro left right agree
  simp [Probability.inter, leftDepends left right agree,
    rightDepends left right agree]

/-- A larger selected family still determines any event that already
depends only on a subfamily. -/
theorem DependsOnSelected.subset (n : Nat) (Value : Fin n -> Type u)
    {selected selected' : Fin n -> Bool}
    (event : Assignment n Value -> Bool)
    (hsub : forall coordinate, selected coordinate = true ->
      selected' coordinate = true)
    (depends : DependsOnSelected n Value selected event) :
    DependsOnSelected n Value selected' event := by
  intro left right agree'
  apply depends
  intro coordinate chosen
  exact agree' coordinate (hsub coordinate chosen)

/-- A smaller selected family enlarges the unselected coordinates, so an
event that ignored the original selected family still ignores the
smaller one. -/
theorem DependsOnUnselected.subset (n : Nat) (Value : Fin n -> Type u)
    {selected selected' : Fin n -> Bool}
    (event : Assignment n Value -> Bool)
    (hsub : forall coordinate, selected' coordinate = true ->
      selected coordinate = true)
    (depends : DependsOnUnselected n Value selected event) :
    DependsOnUnselected n Value selected' event := by
  intro left right agree'
  apply depends
  intro coordinate unselected
  have unselected' : selected' coordinate = false := by
    cases hsel : selected' coordinate with
    | false =>
        rfl
    | true =>
        have : selected coordinate = true := hsub coordinate hsel
        rw [unselected] at this
        cases this
  exact agree' coordinate unselected'

/-- Constant events depend on no coordinates. -/
theorem DependsOnSelected.const (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (value : Bool) :
    DependsOnSelected n Value selected (fun _ => value) := by
  intro _left _right _agree
  rfl

theorem DependsOnUnselected.const (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (value : Bool) :
    DependsOnUnselected n Value selected (fun _ => value) := by
  intro _left _right _agree
  rfl

/-- Depending only on the complement is the unselected judgement for the
original family. -/
theorem DependsOnUnselected.of_compl_selected (n : Nat)
    (Value : Fin n -> Type u) (selected : Fin n -> Bool)
    (event : Assignment n Value -> Bool)
    (depends : DependsOnSelected n Value (fun coordinate =>
      !selected coordinate) event) :
    DependsOnUnselected n Value selected event := by
  intro left right agree
  apply depends
  intro coordinate hcompl
  have unselected : selected coordinate = false := by
    cases hsel : selected coordinate with
    | false =>
        rfl
    | true =>
        simp [hsel] at hcompl
  exact agree coordinate unselected

/-- Depending only on a family is the unselected judgement for its
complement. -/
theorem DependsOnUnselected.of_selected_compl (n : Nat)
    (Value : Fin n -> Type u) (selected : Fin n -> Bool)
    (event : Assignment n Value -> Bool)
    (depends : DependsOnSelected n Value selected event) :
    DependsOnUnselected n Value (fun coordinate => !selected coordinate)
      event := by
  intro left right agree
  apply depends
  intro coordinate chosen
  have unselected : (!selected coordinate) = false := by
    simp [chosen]
  exact agree coordinate unselected

theorem dependsOnSelected_splice (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool)
    (depends : DependsOnSelected n Value selected event)
    (left right : Assignment n Value) :
    event (spliceAssignment n Value selected left right) = event left := by
  apply depends
  intro coordinate chosen
  exact spliceAssignment_selected n Value selected left right coordinate chosen

theorem dependsOnUnselected_splice (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool)
    (depends : DependsOnUnselected n Value selected event)
    (left right : Assignment n Value) :
    event (spliceAssignment n Value selected left right) = event right := by
  apply depends
  intro coordinate chosen
  exact spliceAssignment_unselected n Value selected left right coordinate chosen

/-- Swap the selected coordinates of a pair of assignments. -/
def swapPair (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool)
    (pair : Assignment n Value × Assignment n Value) :
    Assignment n Value × Assignment n Value :=
  (spliceAssignment n Value selected pair.1 pair.2,
    spliceAssignment n Value selected pair.2 pair.1)

theorem swapPair_involutive (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool)
    (pair : Assignment n Value × Assignment n Value) :
    swapPair n Value selected (swapPair n Value selected pair) = pair := by
  apply Prod.ext
  · exact spliceAssignment_exchange n Value selected pair.1 pair.2
  · exact spliceAssignment_exchange n Value selected pair.2 pair.1

/-- A map with an explicit left inverse preserves duplicate-freeness. -/
theorem nodup_map_of_leftInverse {A : Type u} {B : Type v} (forward : A -> B)
    (backward : B -> A) (leftInverse : forall value,
      backward (forward value) = value) (values : List A)
    (nodup : values.Nodup) : (values.map forward).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons value values ih =>
      rw [List.map_cons, List.nodup_cons]
      have parts := List.nodup_cons.mp nodup
      constructor
      · intro occurs
        obtain ⟨other, otherMem, same⟩ := List.mem_map.mp occurs
        apply parts.1
        have sameValue : other = value := by
          rw [← leftInverse other, ← leftInverse value, same]
        simpa [sameValue] using otherMem
      · exact ih parts.2

/-- Cartesian-product enumeration, with the right coordinate varying fastest. -/
def pairList {A : Type u} {B : Type v} (left : List A) (right : List B) :
    List (A × B) :=
  left.flatMap (fun first => right.map (fun second => (first, second)))

@[simp] theorem mem_pairList {A : Type u} {B : Type v}
    [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (first : A) (second : B)
    (left : List A) (right : List B) :
    (first, second) ∈ pairList left right <->
      first ∈ left ∧ second ∈ right := by
  simp [pairList]

theorem pairList_nodup {A : Type u} {B : Type v}
    [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (left : List A) (right : List B)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (pairList left right).Nodup := by
  induction left with
  | nil => exact List.nodup_nil
  | cons first left ih =>
      have parts := List.nodup_cons.mp leftNodup
      rw [pairList, List.flatMap_cons, List.nodup_append]
      constructor
      · exact nodup_map_of_leftInverse (fun second => (first, second))
          Prod.snd (fun _ => rfl) right rightNodup
      · constructor
        · exact ih parts.2
        · intro rowPair rowMem tailPair tailMem same
          apply parts.1
          have rowFirst : rowPair.1 = first := by
            obtain ⟨second, _, rowEq⟩ := List.mem_map.mp rowMem
            rw [← rowEq]
          have tailFirst : tailPair.1 ∈ left :=
            (mem_pairList tailPair.1 tailPair.2 left right).mp tailMem |>.1
          rw [← rowFirst, same]
          exact tailFirst

/-- Duplicate-free finite enumerations with the same members differ only by a
permutation. -/
theorem perm_of_nodup_mem_iff {A : Type u} [BEq A] [LawfulBEq A]
    (left right : List A) (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : forall value, value ∈ left <-> value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Perm.refl []
      | cons head tail =>
          have impossible : head ∈ ([] : List A) :=
            (sameMembers head).mpr (by simp)
          simp at impossible
  | cons head tail ih =>
      have leftParts := List.nodup_cons.mp leftNodup
      have headMemRight := (sameMembers head).mp (by simp)
      obtain ⟨before, suffix, rightEq⟩ := List.append_of_mem headMemRight
      subst right
      have rightParts := List.nodup_append.mp rightNodup
      have suffixParts := List.nodup_cons.mp rightParts.2.1
      have removedNodup : (before ++ suffix).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨rightParts.1, suffixParts.2, ?_⟩
        intro first firstMem second secondMem same
        exact rightParts.2.2 first firstMem second (by simp [secondMem]) same
      have headNotRemoved : head ∉ before ++ suffix := by
        intro occurs
        simp only [List.mem_append] at occurs
        rcases occurs with inPrefix | inSuffix
        · exact rightParts.2.2 head inPrefix head (by simp) rfl
        · exact suffixParts.1 inSuffix
      have tailMembers : forall value,
          value ∈ tail <-> value ∈ before ++ suffix := by
        intro value
        constructor
        · intro tailMem
          have different : value ≠ head := by
            intro same
            subst value
            exact leftParts.1 tailMem
          have rightMem := (sameMembers value).mp (by simp [tailMem])
          simp only [List.mem_append, List.mem_cons] at rightMem ⊢
          rcases rightMem with inPrefix | same | inSuffix
          · exact Or.inl inPrefix
          · exact (different same).elim
          · exact Or.inr inSuffix
        · intro removedMem
          have rightMem : value ∈ before ++ head :: suffix := by
            simp only [List.mem_append, List.mem_cons] at removedMem ⊢
            rcases removedMem with inPrefix | inSuffix
            · exact Or.inl inPrefix
            · exact Or.inr (Or.inr inSuffix)
          have leftMem := (sameMembers value).mpr rightMem
          simp only [List.mem_cons] at leftMem
          rcases leftMem with same | inTail
          · subst value
            exact (headNotRemoved removedMem).elim
          · exact inTail
      have tailPerm := ih (before ++ suffix) leftParts.2 removedNodup
        tailMembers
      exact (tailPerm.cons head).trans List.perm_middle.symm

/-- Splicing is a constructive bijection between pairs satisfying separate
selected/unselected events and pairs whose first component satisfies their
intersection.  The second component is unrestricted. -/
theorem swapPair_eventPairs_perm (n : Nat) (Value : Fin n -> Type u)
    [DecidableEq (Assignment n Value)]
    (selected : Fin n -> Bool) (values : List (Assignment n Value))
    (valuesNodup : values.Nodup)
    (valuesComplete : forall value, value ∈ values)
    (selectedEvent unselectedEvent : Assignment n Value -> Bool)
    (selectedDepends : DependsOnSelected n Value selected selectedEvent)
    (unselectedDepends : DependsOnUnselected n Value selected
      unselectedEvent) :
    (pairList (values.filter selectedEvent)
      (values.filter unselectedEvent)).map (swapPair n Value selected) |>.Perm
        (pairList (values.filter
          (Probability.inter selectedEvent unselectedEvent)) values) := by
  let source := pairList (values.filter selectedEvent)
    (values.filter unselectedEvent)
  let target := pairList (values.filter
    (Probability.inter selectedEvent unselectedEvent)) values
  have sourceNodup : source.Nodup := by
    exact pairList_nodup _ _
      (List.Sublist.nodup List.filter_sublist valuesNodup)
      (List.Sublist.nodup List.filter_sublist valuesNodup)
  have targetNodup : target.Nodup := by
    exact pairList_nodup _ _
      (List.Sublist.nodup List.filter_sublist valuesNodup) valuesNodup
  have mappedNodup :
      (source.map (swapPair n Value selected)).Nodup :=
    nodup_map_of_leftInverse (swapPair n Value selected)
      (swapPair n Value selected)
      (swapPair_involutive n Value selected) source sourceNodup
  apply perm_of_nodup_mem_iff _ _ mappedNodup targetNodup
  intro targetPair
  constructor
  · intro occurs
    obtain ⟨sourcePair, sourceMem, swapped⟩ := List.mem_map.mp occurs
    have sourceParts :=
      (mem_pairList sourcePair.1 sourcePair.2
        (values.filter selectedEvent)
        (values.filter unselectedEvent)).mp sourceMem
    have firstParts := List.mem_filter.mp sourceParts.1
    have secondParts := List.mem_filter.mp sourceParts.2
    rw [← swapped]
    apply (mem_pairList _ _
      (values.filter (Probability.inter selectedEvent unselectedEvent))
      values).mpr
    constructor
    · apply List.mem_filter.mpr
      constructor
      · exact valuesComplete _
      · have selectedPreserved := dependsOnSelected_splice n Value selected
          selectedEvent selectedDepends sourcePair.1 sourcePair.2
        have unselectedPreserved := dependsOnUnselected_splice n Value selected
          unselectedEvent unselectedDepends sourcePair.1 sourcePair.2
        simp [Probability.inter, selectedPreserved, unselectedPreserved,
          firstParts.2, secondParts.2]
    · exact valuesComplete _
  · intro occurs
    have targetParts :=
      (mem_pairList targetPair.1 targetPair.2
        (values.filter (Probability.inter selectedEvent unselectedEvent))
        values).mp occurs
    have firstParts := List.mem_filter.mp targetParts.1
    have eventParts : selectedEvent targetPair.1 = true ∧
        unselectedEvent targetPair.1 = true := by
      simpa [Probability.inter] using firstParts.2
    apply List.mem_map.mpr
    refine ⟨swapPair n Value selected targetPair, ?_,
      swapPair_involutive n Value selected targetPair⟩
    apply (mem_pairList _ _ (values.filter selectedEvent)
      (values.filter unselectedEvent)).mpr
    constructor
    · apply List.mem_filter.mpr
      constructor
      · exact valuesComplete _
      · have preserved := dependsOnSelected_splice n Value selected
          selectedEvent selectedDepends targetPair.1 targetPair.2
        simpa [swapPair, preserved] using eventParts.1
    · apply List.mem_filter.mpr
      constructor
      · exact valuesComplete _
      · have preserved := dependsOnUnselected_splice n Value selected
          unselectedEvent unselectedDepends targetPair.2 targetPair.1
        simpa [swapPair, preserved] using eventParts.2

end CanonicalFactorization

namespace ProbabilityTerm

private theorem unionList_event_true_of_mem
    {events : List (Probability.Event X)} {event : Probability.Event X}
    (member : event ∈ events) (value : X) (holds : event value = true) :
    Probability.unionList events value = true := by
  induction events with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst event
        simp [Probability.unionList, Probability.union, holds]
      · simp [Probability.unionList, Probability.union, ih later]

private theorem exists_event_of_unionList_true
    (events : List (Probability.Event X)) (value : X)
    (holds : Probability.unionList events value = true) :
    ∃ event, event ∈ events ∧ event value = true := by
  induction events with
  | nil => simp [Probability.unionList, Probability.bottomEvent] at holds
  | cons head tail ih =>
      simp only [Probability.unionList, Probability.union,
        Bool.or_eq_true] at holds
      rcases holds with headHolds | tailHolds
      · exact ⟨head, by simp, headHolds⟩
      · rcases ih tailHolds with ⟨event, member, eventHolds⟩
        exact ⟨event, by simp [member], eventHolds⟩

theorem marginal_numerator_events_pairwise
    (y z action w : NodeSet S) (reference : S.Assignment) :
    ((marginalAssignments S z reference).map (fun variant =>
      (Kernel.mk (NodeSet.union y z) action w).numeratorEvent variant)).Pairwise
      Probability.disjoint := by
  apply (List.pairwise_map).mpr
  apply List.Pairwise.imp_of_mem
    (p := marginalAssignments_nodup S z reference)
  intro first second firstMember secondMember different
  intro sample firstHolds secondHolds
  apply different
  have firstZ : Kernel.agreesOn z first sample = true := by
    have parts : Kernel.agreesOn y first sample = true ∧
        Kernel.agreesOn z first sample = true ∧
          Kernel.agreesOn w first sample = true := by
      simpa [Kernel.numeratorEvent, Kernel.agreesOn_union, Bool.and_assoc] using
        firstHolds
    exact parts.2.1
  have secondZ : Kernel.agreesOn z second sample = true := by
    have parts : Kernel.agreesOn y second sample = true ∧
        Kernel.agreesOn z second sample = true ∧
          Kernel.agreesOn w second sample = true := by
      simpa [Kernel.numeratorEvent, Kernel.agreesOn_union, Bool.and_assoc] using
        secondHolds
    exact parts.2.1
  have firstProjected := (Kernel.agreesOn_iff_project_eq z first sample).mp firstZ
  have secondProjected := (Kernel.agreesOn_iff_project_eq z second sample).mp secondZ
  funext i
  cases selected : z i with
  | false =>
      exact (marginal_member_agrees_outside firstMember selected).trans
        (marginal_member_agrees_outside secondMember selected).symm
  | true =>
      have projected : S.project z first i = S.project z second i := by
        rw [← firstProjected, ← secondProjected]
      simpa [ObservedSignature.project, selected] using projected

theorem marginal_numerator_union
    (y z action w : NodeSet S) (reference : S.Assignment)
    (yz : NodeSet.Disjoint y z) (wz : NodeSet.Disjoint w z) :
    Probability.unionList
        ((marginalAssignments S z reference).map (fun variant =>
          (Kernel.mk (NodeSet.union y z) action w).numeratorEvent variant)) =
      (Kernel.mk y action w).numeratorEvent reference := by
  funext sample
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro unionHolds
    rcases exists_event_of_unionList_true _ sample unionHolds with
      ⟨event, eventMember, eventHolds⟩
    simp only [List.mem_map] at eventMember
    rcases eventMember with ⟨variant, variantMember, eventEq⟩
    subst event
    have variantY : ∀ i, y i = true -> variant i = reference i := by
      intro i selected
      exact marginal_member_agrees_outside variantMember (yz i selected)
    have variantW : ∀ i, w i = true -> variant i = reference i := by
      intro i selected
      exact marginal_member_agrees_outside variantMember (wz i selected)
    have yAgreement := Kernel.agreesOn_reference_congr y variant reference sample variantY
    have wAgreement := Kernel.agreesOn_reference_congr w variant reference sample variantW
    have parts : Kernel.agreesOn y reference sample = true ∧
        Kernel.agreesOn z variant sample = true ∧
          Kernel.agreesOn w reference sample = true := by
      simpa [Kernel.numeratorEvent, Kernel.agreesOn_union, Bool.and_assoc,
        yAgreement, wAgreement] using eventHolds
    simpa [Kernel.numeratorEvent] using And.intro parts.1 parts.2.2
  · intro targetHolds
    let variant := marginalVariant S z reference sample
    have variantMember := marginalVariant_mem S z reference sample
    apply unionList_event_true_of_mem
      (List.mem_map.mpr ⟨variant, variantMember, rfl⟩) sample
    have variantY : ∀ i, y i = true -> variant i = reference i := by
      intro i selected
      have notZ := yz i selected
      simp [variant, marginalVariant, notZ]
    have variantW : ∀ i, w i = true -> variant i = reference i := by
      intro i selected
      have notZ := wz i selected
      simp [variant, marginalVariant, notZ]
    have variantZ : ∀ i, z i = true -> variant i = sample i := by
      intro i selected
      simp [variant, marginalVariant, selected]
    have yAgreement := Kernel.agreesOn_reference_congr y variant reference sample variantY
    have wAgreement := Kernel.agreesOn_reference_congr w variant reference sample variantW
    have zAgreement := Kernel.agreesOn_reference_congr z variant sample sample variantZ
    have targetParts : Kernel.agreesOn y reference sample = true ∧
        Kernel.agreesOn w reference sample = true := by
      simpa [Kernel.numeratorEvent] using targetHolds
    have yTrue : Kernel.agreesOn y variant sample = true := by
      rw [yAgreement]
      exact targetParts.1
    have wTrue : Kernel.agreesOn w variant sample = true := by
      rw [wAgreement]
      exact targetParts.2
    have zTrue : Kernel.agreesOn z variant sample = true := by
      rw [zAgreement]
      apply (finAll_eq_true_iff _).mpr
      intro i
      cases z i <;> simp
    simp [Kernel.numeratorEvent, Kernel.agreesOn_union, yTrue, zTrue, wTrue]

/--
Finite marginalization partitions a joint cylinder over its marginalized
values.  Support of the source kernel alone is sufficient: the proof rewrites
the source numerator as a finite sum with a common positive denominator, so
definedness of the marginal endpoint is a consequence rather than a premise.
-/
noncomputable def marginalization_equivalentAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (leftSupported : SupportedAt model (.kernel ⟨y, x, w⟩) assignment) :
    EquivalentAt model
      (.kernel ⟨y, x, w⟩)
      (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment := by
  let variants := marginalAssignments S z assignment
  let leftKernel : Kernel S := ⟨y, x, w⟩
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let distribution := leftKernel.distribution model assignment
  let denominator := distribution.probVal (leftKernel.conditionEvent assignment)
  let total := distribution.probVal (leftKernel.numeratorEvent assignment)
  let numerator : S.Assignment -> QProb := fun variant =>
    distribution.probVal (jointKernel.numeratorEvent variant)
  have pairwise :
      (variants.map (fun variant => jointKernel.numeratorEvent variant)).Pairwise
        Probability.disjoint := by
    simpa only [variants, jointKernel] using
      marginal_numerator_events_pairwise y z x w assignment
  have union : Probability.unionList
      (variants.map (fun variant => jointKernel.numeratorEvent variant)) =
        leftKernel.numeratorEvent assignment := by
    simpa only [variants, jointKernel, leftKernel] using
      marginal_numerator_union y z x w assignment disjoint.yz
        disjoint.zw.symm
  have numeratorSum : QProb.Equiv total
      (QProb.listSum (variants.map numerator)) := by
    have additive := distribution.finite_additivity_family
      (variants.map (fun variant => jointKernel.numeratorEvent variant)) pairwise
    rw [union] at additive
    simpa only [total, numerator, List.map_map, Function.comp_apply] using additive
  have leftCanonical : ProbabilityResult.Equivalent
      (leftKernel.denote model assignment)
      (ProbabilityResult.divide (some total) (some denominator)) := by
    exact ProbabilityResult.divide_congr
      (.value (QProb.equiv_refl _)) (.value (QProb.equiv_refl _))
  have variantCanonical : ∀ variant, variant ∈ variants ->
      ProbabilityResult.Equivalent
        (jointKernel.denote model variant)
        (ProbabilityResult.divide (some (numerator variant)) (some denominator)) := by
    intro variant member
    have outside := (mem_marginalAssignments_iff S z assignment variant).mp
      (by simpa only [variants] using member)
    have actionAgreement : ∀ i, x i = true -> variant i = assignment i := by
      intro i selected
      exact outside i (disjoint.xz i selected)
    have conditionAgreement : ∀ i, w i = true -> variant i = assignment i := by
      intro i selected
      exact outside i (disjoint.zw.symm i selected)
    have distributionEq : jointKernel.distribution model variant = distribution := by
      simpa only [jointKernel, leftKernel, distribution] using
        Kernel.distribution_eq_of_action_reference model
          (NodeSet.union y z) y x w w variant assignment actionAgreement
    have denominatorEq : QProb.Equiv
        ((jointKernel.distribution model variant).probVal
          (jointKernel.conditionEvent variant)) denominator := by
      rw [distributionEq]
      apply FiniteProbRecord.probVal_congr
      intro sample
      exact Kernel.agreesOn_reference_congr w variant assignment sample
        conditionAgreement
    have numeratorEq : QProb.Equiv
        ((jointKernel.distribution model variant).probVal
          (jointKernel.numeratorEvent variant)) (numerator variant) := by
      rw [distributionEq]
      exact QProb.equiv_refl _
    simpa only [Kernel.denote] using
      ProbabilityResult.divide_congr (.value numeratorEq) (.value denominatorEq)
  have rightCanonical : ProbabilityResult.Equivalent
      ((ProbabilityTerm.marginalize z (.kernel jointKernel)).denote model assignment)
      (ProbabilityResult.sum (variants.map (fun variant =>
        ProbabilityResult.divide (some (numerator variant)) (some denominator)))) := by
    simpa only [ProbabilityTerm.denote, variants] using
      ProbabilityResult.sum_map_congr_mem variants
        (fun variant => jointKernel.denote model variant)
        (fun variant =>
          ProbabilityResult.divide (some (numerator variant)) (some denominator))
        variantCanonical
  let leftListCanonical : ProbabilityResult.Equivalent
      (leftKernel.denote model assignment)
      (ProbabilityResult.divide
        (some (QProb.listSum (variants.map numerator))) (some denominator)) :=
    ProbabilityResult.trans leftCanonical
      (ProbabilityResult.divide_congr (.value numeratorSum)
        (.value (QProb.equiv_refl _)))
  have listSupported : ProbabilityResult.Supported
      (ProbabilityResult.divide
        (some (QProb.listSum (variants.map numerator))) (some denominator)) :=
    ProbabilityResult.Supported.transport leftListCanonical (by
      simpa only [leftKernel, SupportedAt, denote] using leftSupported)
  exact ProbabilityResult.trans leftListCanonical
    (ProbabilityResult.trans
      (ProbabilityResult.divide_listSum_same_denominator
        (variants.map numerator) denominator listSupported)
      (by
        simpa only [List.map_map, Function.comp_apply] using
          ProbabilityResult.symm rightCanonical))

/-- Source support transports across finite marginalization. -/
noncomputable def marginalization_supportedAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (leftSupported : SupportedAt model (.kernel ⟨y, x, w⟩) assignment) :
    SupportedAt model
      (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment :=
  SupportedAt.of_equivalent
    (marginalization_equivalentAt model x y z w assignment disjoint
      leftSupported)
    leftSupported

/--
Compatibility wrapper for the primitive-soundness signature, which supplies
support at both endpoints.  The second witness is intentionally unnecessary:
`marginalization_supportedAt` can reconstruct it from the source.
-/
noncomputable def marginalization_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (leftSupported : SupportedAt model (.kernel ⟨y, x, w⟩) assignment)
    (_rightSupported : SupportedAt model
      (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment) :
    EquivalentAt model
      (.kernel ⟨y, x, w⟩)
      (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment :=
  marginalization_equivalentAt model x y z w assignment disjoint leftSupported

/-- Conditioning is the quotient of a joint kernel by its conditioning kernel. -/
noncomputable def conditioning_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment)
    (leftSupported : SupportedAt model
      (.kernel ⟨y, x, NodeSet.union z w⟩) assignment)
    (rightSupported : SupportedAt model
      (.divide
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.kernel ⟨z, x, w⟩)) assignment) :
    EquivalentAt model
      (.kernel ⟨y, x, NodeSet.union z w⟩)
      (.divide
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.kernel ⟨z, x, w⟩)) assignment := by
  let leftKernel : Kernel S := ⟨y, x, NodeSet.union z w⟩
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let conditionKernel : Kernel S := ⟨z, x, w⟩
  let distribution := leftKernel.distribution model assignment
  let jointEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn y assignment sample &&
      Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let conditionEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let baseEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn w assignment sample
  let numerator := distribution.probVal jointEvent
  let middle := distribution.probVal conditionEvent
  let denominator := distribution.probVal baseEvent
  have jointDistribution :
      jointKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      (NodeSet.union y z) y x w (NodeSet.union z w) assignment
  have conditionDistribution :
      conditionKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      z y x w (NodeSet.union z w) assignment
  have leftNumerator : QProb.Equiv
      ((leftKernel.distribution model assignment).probVal
        (leftKernel.numeratorEvent assignment)) numerator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [leftKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have leftDenominator : QProb.Equiv
      ((leftKernel.distribution model assignment).probVal
        (leftKernel.conditionEvent assignment)) middle := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [leftKernel, conditionEvent, Kernel.conditionEvent,
      Kernel.agreesOn_union]
  have jointNumerator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.numeratorEvent assignment)) numerator := by
    rw [jointDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [jointKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have jointDenominator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.conditionEvent assignment)) denominator := by
    rw [jointDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionNumerator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.numeratorEvent assignment)) middle := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionDenominator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.conditionEvent assignment)) denominator := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  let leftCanonical : ProbabilityResult.Equivalent
      (leftKernel.denote model assignment)
      (ProbabilityResult.divide (some numerator) (some middle)) := by
    simpa only [Kernel.denote] using ProbabilityResult.divide_congr
      (.value leftNumerator) (.value leftDenominator)
  let rightCanonical : ProbabilityResult.Equivalent
      (ProbabilityResult.divide
        (jointKernel.denote model assignment)
        (conditionKernel.denote model assignment))
      (ProbabilityResult.divide
        (ProbabilityResult.divide (some numerator) (some denominator))
        (ProbabilityResult.divide (some middle) (some denominator))) := by
    apply ProbabilityResult.divide_congr
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value jointNumerator) (.value jointDenominator)
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value conditionNumerator) (.value conditionDenominator)
  have leftSupported' : ProbabilityResult.Supported
      (ProbabilityResult.divide (some numerator) (some middle)) :=
    ProbabilityResult.Supported.transport leftCanonical (by
      simpa only [leftKernel, SupportedAt, denote] using leftSupported)
  have rightSupported' : ProbabilityResult.Supported
      (ProbabilityResult.divide
        (ProbabilityResult.divide (some numerator) (some denominator))
        (ProbabilityResult.divide (some middle) (some denominator))) :=
    ProbabilityResult.Supported.transport rightCanonical (by
      simpa only [jointKernel, conditionKernel, SupportedAt, denote] using
        rightSupported)
  exact ProbabilityResult.trans leftCanonical
    (ProbabilityResult.trans
      (ProbabilityResult.divide_divide_cancel numerator middle denominator
        leftSupported' rightSupported')
      (ProbabilityResult.symm rightCanonical))

/-- The product of adjacent conditional kernels is their joint kernel. -/
noncomputable def chain_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment)
    (leftSupported : SupportedAt model
      (.kernel ⟨NodeSet.union y z, x, w⟩) assignment)
    (rightSupported : SupportedAt model
      (.multiply
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.kernel ⟨z, x, w⟩)) assignment) :
    EquivalentAt model
      (.kernel ⟨NodeSet.union y z, x, w⟩)
      (.multiply
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.kernel ⟨z, x, w⟩)) assignment := by
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let conditionalKernel : Kernel S := ⟨y, x, NodeSet.union z w⟩
  let conditionKernel : Kernel S := ⟨z, x, w⟩
  let distribution := jointKernel.distribution model assignment
  let jointEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn y assignment sample &&
      Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let middleEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let baseEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn w assignment sample
  let numerator := distribution.probVal jointEvent
  let middle := distribution.probVal middleEvent
  let denominator := distribution.probVal baseEvent
  have conditionalDistribution :
      conditionalKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      y (NodeSet.union y z) x (NodeSet.union z w) w assignment
  have conditionDistribution :
      conditionKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      z (NodeSet.union y z) x w w assignment
  have jointNumerator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.numeratorEvent assignment)) numerator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [jointKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have jointDenominator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.conditionEvent assignment)) denominator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionalNumerator : QProb.Equiv
      ((conditionalKernel.distribution model assignment).probVal
        (conditionalKernel.numeratorEvent assignment)) numerator := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have conditionalDenominator : QProb.Equiv
      ((conditionalKernel.distribution model assignment).probVal
        (conditionalKernel.conditionEvent assignment)) middle := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, middleEvent, Kernel.conditionEvent,
      Kernel.agreesOn_union]
  have conditionNumerator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.numeratorEvent assignment)) middle := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionDenominator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.conditionEvent assignment)) denominator := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  let leftCanonical : ProbabilityResult.Equivalent
      (jointKernel.denote model assignment)
      (ProbabilityResult.divide (some numerator) (some denominator)) := by
    simpa only [Kernel.denote] using ProbabilityResult.divide_congr
      (.value jointNumerator) (.value jointDenominator)
  let rightCanonical : ProbabilityResult.Equivalent
      (ProbabilityResult.multiply
        (conditionalKernel.denote model assignment)
        (conditionKernel.denote model assignment))
      (ProbabilityResult.multiply
        (ProbabilityResult.divide (some numerator) (some middle))
        (ProbabilityResult.divide (some middle) (some denominator))) := by
    apply ProbabilityResult.multiply_congr
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value conditionalNumerator) (.value conditionalDenominator)
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value conditionNumerator) (.value conditionDenominator)
  have leftSupported' : ProbabilityResult.Supported
      (ProbabilityResult.divide (some numerator) (some denominator)) :=
    ProbabilityResult.Supported.transport leftCanonical (by
      simpa only [jointKernel, SupportedAt, denote] using leftSupported)
  have rightSupported' : ProbabilityResult.Supported
      (ProbabilityResult.multiply
        (ProbabilityResult.divide (some numerator) (some middle))
        (ProbabilityResult.divide (some middle) (some denominator))) :=
    ProbabilityResult.Supported.transport rightCanonical (by
      simpa only [conditionalKernel, conditionKernel, SupportedAt, denote] using
        rightSupported)
  exact ProbabilityResult.trans leftCanonical
    (ProbabilityResult.trans
      (ProbabilityResult.divide_multiply_chain numerator middle denominator
        leftSupported' rightSupported')
      (ProbabilityResult.symm rightCanonical))

end ProbabilityTerm

/--
Equality of a joint interventional kernel descends to every sub-outcome.
The proof is deliberately constructive despite `ValueEquivalent` hiding each
pointwise witness behind `Nonempty`: `sum_map_congr_nonempty` opens those
witnesses one finite marginal cell at a time and returns only an inhabited
equivalence.  No function selecting evidence for all assignments is formed.
-/
theorem JointKernelQuery.valueEquivalent_restrictOutcome
    (q : JointKernelQuery S) (left right : ExactModel S)
    (equivalent : q.ValueEquivalent left right)
    (outcome : NodeSet S) (subset : NodeSet.Subset outcome q.outcome) :
    (q.restrictOutcome outcome subset).ValueEquivalent left right := by
  intro assignment
  let rest := NodeSet.diff q.outcome outcome
  have unionEq : NodeSet.union outcome rest = q.outcome := by
    simpa [rest] using NodeSet.union_diff_eq subset
  let disjoint : FourWayDisjoint q.action outcome rest NodeSet.empty :=
    { xy := NodeSet.disjoint_of_subset_right q.action_outcome_disjoint subset
      xz := NodeSet.disjoint_of_subset_right q.action_outcome_disjoint
        (NodeSet.diff_subset_left q.outcome outcome)
      xw := NodeSet.disjoint_empty_right q.action
      yz := by simpa [rest] using NodeSet.disjoint_diff q.outcome outcome
      yw := NodeSet.disjoint_empty_right outcome
      zw := NodeSet.disjoint_empty_right rest }
  have leftMarginal :=
    ProbabilityTerm.marginalization_equivalentAt left q.action outcome rest
      NodeSet.empty assignment disjoint
      ((q.restrictOutcome outcome subset).supportedAt left assignment)
  have rightMarginal :=
    ProbabilityTerm.marginalization_equivalentAt right q.action outcome rest
      NodeSet.empty assignment disjoint
      ((q.restrictOutcome outcome subset).supportedAt right assignment)
  have leftMarginal' :
      ProbabilityResult.Equivalent
        ((q.restrictOutcome outcome subset).sourceTerm.denote left assignment)
        ((ProbabilityTerm.marginalize rest q.sourceTerm).denote left
          assignment) := by
    simpa only [JointKernelQuery.restrictOutcome_sourceTerm,
      JointKernelQuery.sourceTerm, unionEq] using leftMarginal
  have rightMarginal' :
      ProbabilityResult.Equivalent
        ((q.restrictOutcome outcome subset).sourceTerm.denote right assignment)
        ((ProbabilityTerm.marginalize rest q.sourceTerm).denote right
          assignment) := by
    simpa only [JointKernelQuery.restrictOutcome_sourceTerm,
      JointKernelQuery.sourceTerm, unionEq] using rightMarginal
  have middle :
      Nonempty
        (ProbabilityResult.Equivalent
          ((ProbabilityTerm.marginalize rest q.sourceTerm).denote left
            assignment)
          ((ProbabilityTerm.marginalize rest q.sourceTerm).denote right
            assignment)) := by
    simpa only [ProbabilityTerm.denote] using
      ProbabilityResult.sum_map_congr_nonempty
        (ProbabilityTerm.marginalAssignments S rest assignment)
        (fun variant => q.sourceTerm.denote left variant)
        (fun variant => q.sourceTerm.denote right variant)
        equivalent
  rcases middle with ⟨middleEq⟩
  exact ⟨ProbabilityResult.trans leftMarginal'
    (ProbabilityResult.trans middleEq
      (ProbabilityResult.symm rightMarginal'))⟩

namespace Kernel

def productRecord (model : FiniteLatentSCM S) :
    FiniteProbRecord model.latent.Assignment :=
  FiniteProduct.record model.latent.count model.latent.Value model.factor

def productMass (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) : QProb :=
  (productRecord model).probVal
    (fun roots => event
      (model.evalUnder (kernel.intervention reference) roots))

/-- The latent event whose canonical-product mass is `productMass`. -/
def productPreimage (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    model.latent.Assignment -> Bool :=
  fun roots => event
    (model.evalUnder (kernel.intervention reference) roots)

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

theorem productRecord_singleton_qProduct (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    QProb.Equiv
      ((productRecord model).probVal
        (FiniteProbRecord.singletonEvent assignment))
      (FiniteProduct.qProduct model.latent.count (fun root =>
        (model.factor root).probVal
          (FiniteProbRecord.singletonEvent (assignment root)))) := by
  let events := FiniteLatentSCM.assignmentEvents model assignment
  have rectangular := FiniteProduct.record_rectangular_probVal
    model.latent.count model.latent.Value model.factor events
  have eventEq : FiniteProduct.rectangularEvent model.latent.count
      model.latent.Value events =
        FiniteProbRecord.singletonEvent assignment := by
    simpa [events, LatentExtension.rectangularEvent] using
      FiniteLatentSCM.rectangular_assignmentEvents model assignment
  rw [eventEq] at rectangular
  simpa [productRecord, events, FiniteLatentSCM.assignmentEvents] using
    rectangular

/-- Point-mass products in the canonical latent record are invariant under
coordinate splicing. -/
theorem productRecord_singleton_splice_mul (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (left right : model.latent.Assignment) :
    QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal
          (FiniteProbRecord.singletonEvent left))
        ((productRecord model).probVal
          (FiniteProbRecord.singletonEvent right)))
      (QProb.mul
        ((productRecord model).probVal (FiniteProbRecord.singletonEvent
          (CanonicalFactorization.spliceAssignment model.latent.count
            model.latent.Value selected left right)))
        ((productRecord model).probVal (FiniteProbRecord.singletonEvent
          (CanonicalFactorization.spliceAssignment model.latent.count
            model.latent.Value selected right left)))) := by
  let weight := fun (root : Fin model.latent.count)
      (value : model.latent.Value root) =>
    (model.factor root).probVal (FiniteProbRecord.singletonEvent value)
  have leftPoint := productRecord_singleton_qProduct model left
  have rightPoint := productRecord_singleton_qProduct model right
  have firstSplicePoint := productRecord_singleton_qProduct model
    (CanonicalFactorization.spliceAssignment model.latent.count
      model.latent.Value selected left right)
  have secondSplicePoint := productRecord_singleton_qProduct model
    (CanonicalFactorization.spliceAssignment model.latent.count
      model.latent.Value selected right left)
  have swap := CanonicalFactorization.qProduct_splice_mul
    model.latent.count model.latent.Value weight selected left right
  exact QProb.equiv_trans (QProb.mul_congr leftPoint rightPoint)
    (QProb.equiv_trans (by simpa [weight] using swap)
      (QProb.equiv_symm
        (QProb.mul_congr firstSplicePoint secondSplicePoint)))

/-- Events depending on complementary families of independent latent roots
satisfy the denominator-free independence identity.  The factor
`P(topEvent)` is retained so the statement is valid for the unreduced
rational presentations used by `QProb`. -/
theorem productRecord_complementary_independence
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedEvent unselectedEvent : model.latent.Assignment -> Bool)
    (selectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedEvent)
    (unselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedEvent) :
    QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal selectedEvent)
        ((productRecord model).probVal unselectedEvent))
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter selectedEvent unselectedEvent))
        ((productRecord model).probVal Probability.topEvent)) := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  let values := FiniteLatentSCM.factorizationAssignments model
  let pointMass := fun assignment : model.latent.Assignment =>
    (productRecord model).probVal
      (FiniteProbRecord.singletonEvent assignment)
  let pairMass := fun pair :
      model.latent.Assignment × model.latent.Assignment =>
    QProb.mul (pointMass pair.1) (pointMass pair.2)
  let source := CanonicalFactorization.pairList
    (values.filter selectedEvent) (values.filter unselectedEvent)
  let target := CanonicalFactorization.pairList
    (values.filter (Probability.inter selectedEvent unselectedEvent)) values
  have valuesNodup : values.Nodup := by
    exact FiniteLatentSCM.factorizationAssignments_nodup model
  have valuesComplete : forall value, value ∈ values := by
    exact FiniteLatentSCM.factorizationAssignments_complete model
  have expand (event : model.latent.Assignment -> Bool) :=
    FiniteProbRecord.probVal_equiv_listSum_singletons
      (productRecord model) values valuesNodup valuesComplete event
  have sourceExpansion : QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal selectedEvent)
        ((productRecord model).probVal unselectedEvent))
      (QProb.listSum (source.map pairMass)) := by
    have multiplyExpanded := QProb.listSum_mul_listSum
      ((values.filter selectedEvent).map pointMass)
      ((values.filter unselectedEvent).map pointMass)
    have flattenExpanded := QProb.listSum_flatMap
      (values.filter selectedEvent) (fun first =>
        (values.filter unselectedEvent).map (fun second =>
          pairMass (first, second)))
    exact QProb.equiv_trans
      (QProb.mul_congr (expand selectedEvent) (expand unselectedEvent))
      (QProb.equiv_trans multiplyExpanded (by
        simpa [source, CanonicalFactorization.pairList, pairMass,
          pointMass, List.map_map, List.map_flatMap,
          Function.comp_apply] using QProb.equiv_symm flattenExpanded))
  have targetExpansion : QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter selectedEvent unselectedEvent))
        ((productRecord model).probVal Probability.topEvent))
      (QProb.listSum (target.map pairMass)) := by
    have topFilter : values.filter Probability.topEvent = values := by
      induction values with
      | nil => rfl
      | cons value values ih =>
          simp [Probability.topEvent, ih]
    have expandTop : QProb.Equiv
        ((productRecord model).probVal Probability.topEvent)
        (QProb.listSum (values.map pointMass)) := by
      have expanded := expand Probability.topEvent
      rw [topFilter] at expanded
      exact expanded
    have multiplyExpanded := QProb.listSum_mul_listSum
      ((values.filter
        (Probability.inter selectedEvent unselectedEvent)).map pointMass)
      (values.map pointMass)
    have flattenExpanded := QProb.listSum_flatMap
      (values.filter (Probability.inter selectedEvent unselectedEvent))
      (fun first => values.map (fun second => pairMass (first, second)))
    exact QProb.equiv_trans
      (QProb.mul_congr
        (expand (Probability.inter selectedEvent unselectedEvent))
        expandTop)
      (QProb.equiv_trans multiplyExpanded (by
        simpa [target, CanonicalFactorization.pairList, pairMass,
          pointMass, Probability.topEvent, List.map_map, List.map_flatMap,
          Function.comp_apply, Function.comp_def] using
            QProb.equiv_symm flattenExpanded))
  have pairPermutation := CanonicalFactorization.swapPair_eventPairs_perm
    model.latent.count model.latent.Value selected values valuesNodup
    valuesComplete selectedEvent unselectedEvent selectedDepends
    unselectedDepends
  have pointwise : forall pair :
      model.latent.Assignment × model.latent.Assignment,
      QProb.Equiv (pairMass pair)
        (pairMass (CanonicalFactorization.swapPair model.latent.count
          model.latent.Value selected pair)) := by
    intro pair
    simpa [pairMass, pointMass, CanonicalFactorization.swapPair] using
      productRecord_singleton_splice_mul model selected pair.1 pair.2
  have reindexed : QProb.Equiv
      (QProb.listSum (source.map pairMass))
      (QProb.listSum (target.map pairMass)) := by
    exact QProb.equiv_trans
      (QProb.listSum_map_congr source pairMass
        (fun pair => pairMass
          (CanonicalFactorization.swapPair model.latent.count
            model.latent.Value selected pair)) pointwise)
      (by
        have mappedPermutation := pairPermutation.map pairMass
        simpa [source, target, List.map_map] using
          QProb.listSum_perm mappedPermutation)
  exact QProb.equiv_trans sourceExpansion
    (QProb.equiv_trans reindexed (QProb.equiv_symm targetExpansion))

/-- Normalization removes the explicit `P(topEvent)` factor from the
denominator-free product identity. -/
theorem productRecord_inter_equiv_mul
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedEvent unselectedEvent : model.latent.Assignment -> Bool)
    (selectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedEvent)
    (unselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedEvent) :
    QProb.Equiv
      ((productRecord model).probVal
        (Probability.inter selectedEvent unselectedEvent))
      (QProb.mul
        ((productRecord model).probVal selectedEvent)
        ((productRecord model).probVal unselectedEvent)) := by
  let intersection := (productRecord model).probVal
    (Probability.inter selectedEvent unselectedEvent)
  let whole := (productRecord model).probVal Probability.topEvent
  have independent := productRecord_complementary_independence model selected
    selectedEvent unselectedEvent selectedDepends unselectedDepends
  have normalized : QProb.Equiv whole QProb.one :=
    (productRecord model).normalization
  exact QProb.equiv_trans (QProb.equiv_symm (QProb.mul_one intersection))
    (QProb.equiv_trans
      (QProb.mul_congr (QProb.equiv_refl intersection)
        (QProb.equiv_symm normalized))
      (by simpa [intersection, whole] using QProb.equiv_symm independent))

/-- Conditional independence in cross-product form.  A common conditioning
event may have one component on each side of the latent-root partition. -/
theorem productRecord_conditional_independence_cross
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedOutcome selectedCondition unselectedOutcome
      unselectedCondition : model.latent.Assignment -> Bool)
    (selectedOutcomeDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedOutcome)
    (selectedConditionDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedCondition)
    (unselectedOutcomeDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedOutcome)
    (unselectedConditionDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedCondition) :
    QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter
            (Probability.inter selectedOutcome selectedCondition)
            unselectedCondition))
        ((productRecord model).probVal
          (Probability.inter selectedCondition
            (Probability.inter unselectedOutcome unselectedCondition))))
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter
            (Probability.inter selectedOutcome selectedCondition)
            (Probability.inter unselectedOutcome unselectedCondition)))
        ((productRecord model).probVal
          (Probability.inter selectedCondition unselectedCondition))) := by
  let selectedJoint := Probability.inter selectedOutcome selectedCondition
  let unselectedJoint := Probability.inter unselectedOutcome unselectedCondition
  have selectedJointDepends := CanonicalFactorization.DependsOnSelected.inter
    model.latent.count model.latent.Value selected
      selectedOutcome selectedCondition selectedOutcomeDepends
      selectedConditionDepends
  have unselectedJointDepends :=
    CanonicalFactorization.DependsOnUnselected.inter model.latent.count
      model.latent.Value selected unselectedOutcome unselectedCondition
      unselectedOutcomeDepends unselectedConditionDepends
  have leftFactor := productRecord_inter_equiv_mul model selected
    selectedJoint unselectedCondition selectedJointDepends
    unselectedConditionDepends
  have rightFactor := productRecord_inter_equiv_mul model selected
    selectedCondition unselectedJoint selectedConditionDepends
    unselectedJointDepends
  have jointFactor := productRecord_inter_equiv_mul model selected
    selectedJoint unselectedJoint selectedJointDepends unselectedJointDepends
  have conditionFactor := productRecord_inter_equiv_mul model selected
    selectedCondition unselectedCondition selectedConditionDepends
    unselectedConditionDepends
  exact QProb.equiv_trans (QProb.mul_congr leftFactor rightFactor)
    (QProb.equiv_trans (by
      simp only [QProb.Equiv, QProb.mul]
      ac_rfl)
      (QProb.equiv_symm (QProb.mul_congr jointFactor conditionFactor)))

/-- Every kernel distribution is a pushforward of the canonical independent
latent product, including the action-free branch. -/
theorem distribution_probVal_productRecord
    (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    QProb.Equiv ((kernel.distribution model reference).probVal event)
      (productMass model kernel reference event) := by
  unfold productMass productRecord
  cases actionValue : kernel.hasAction with
  | true =>
      simpa [Kernel.distribution, actionValue,
        FiniteLatentSCM.interventionalValue] using
        model.interventionalValue_productRecord
          (kernel.intervention reference) event
  | false =>
      have noAction : forall node, kernel.action node = false :=
        (finAny_eq_false_iff kernel.action).mp (by
          simpa [Kernel.hasAction] using actionValue)
      have noIntervention : kernel.intervention reference =
          FiniteLatentSCM.noIntervention S := by
        funext node
        simp [Kernel.intervention, FiniteLatentSCM.noIntervention,
          noAction node]
      rw [noIntervention]
      simpa [Kernel.distribution, actionValue,
        FiniteLatentSCM.observationalValue,
        FiniteLatentSCM.evalUnder_noIntervention, productMass,
        productRecord] using
        model.observationalValue_productRecord event

/-- The denominator-free cross-product obligation for two conditional kernels. -/
structure CrossProductEquivalentAt (model : FiniteLatentSCM S)
    (left right : Kernel S) (assignment : S.Assignment) : Prop where
  cross : QProb.Equiv
    (QProb.mul
      ((left.distribution model assignment).probVal
        (left.numeratorEvent assignment))
      ((right.distribution model assignment).probVal
        (right.conditionEvent assignment)))
    (QProb.mul
      ((right.distribution model assignment).probVal
        (right.numeratorEvent assignment))
      ((left.distribution model assignment).probVal
        (left.conditionEvent assignment)))

/-- The same cross-product obligation after replacing the supplied latent
prior by its canonical independent product record. -/
structure ProductCrossProductEquivalentAt (model : FiniteLatentSCM S)
    (left right : Kernel S) (assignment : S.Assignment) : Prop where
  cross : QProb.Equiv
    (QProb.mul
      (productMass model left assignment (left.numeratorEvent assignment))
      (productMass model right assignment (right.conditionEvent assignment)))
    (QProb.mul
      (productMass model right assignment (right.numeratorEvent assignment))
      (productMass model left assignment (left.conditionEvent assignment)))

theorem ProductCrossProductEquivalentAt.symm
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : ProductCrossProductEquivalentAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model right left assignment :=
  ⟨QProb.equiv_symm equivalent.cross⟩

/-- A concrete latent partition witnessing the conditional-independence
identity required by a pair of kernels.  The four equalities isolate the
intervention/structural-equation work; the four dependence fields isolate the
graph-separation work. -/
structure ProductConditionalIndependenceWitnessAt
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  selectedOutcome : model.latent.Assignment -> Bool
  selectedCondition : model.latent.Assignment -> Bool
  unselectedOutcome : model.latent.Assignment -> Bool
  unselectedCondition : model.latent.Assignment -> Bool
  selectedOutcomeDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedOutcome
  selectedConditionDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedCondition
  unselectedOutcomeDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedOutcome
  unselectedConditionDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedCondition
  leftNumerator :
    productPreimage model left assignment (left.numeratorEvent assignment) =
      Probability.inter
        (Probability.inter selectedOutcome selectedCondition)
        (Probability.inter unselectedOutcome unselectedCondition)
  rightCondition :
    productPreimage model right assignment (right.conditionEvent assignment) =
      Probability.inter selectedCondition unselectedCondition
  rightNumerator :
    productPreimage model right assignment (right.numeratorEvent assignment) =
      Probability.inter selectedCondition
        (Probability.inter unselectedOutcome unselectedCondition)
  leftCondition :
    productPreimage model left assignment (left.conditionEvent assignment) =
      Probability.inter
        (Probability.inter selectedOutcome selectedCondition)
        unselectedCondition

/-- Build the latent conditional-independence witness for rule 1 from two
backward-closed, latent-separated regions and a partition of the common
conditioning nodes. -/
def rule1PartitionWitness (model : FiniteLatentSCM S)
    (x y z w wSelected wUnselected leftRelevant rightRelevant : NodeSet S)
    (assignment : S.Assignment)
    (wSplit : w = NodeSet.union wSelected wUnselected)
    (leftClosed : model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment) leftRelevant)
    (rightClosed : model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment) rightRelevant)
    (zContained : NodeSet.Subset z leftRelevant)
    (wSelectedContained : NodeSet.Subset wSelected leftRelevant)
    (yContained : NodeSet.Subset y rightRelevant)
    (wUnselectedContained : NodeSet.Subset wUnselected rightRelevant)
    (separated : model.LatentSeparatedUnder
      ((rule1Right x y z w).intervention assignment)
      leftRelevant rightRelevant) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let intervention := (rule1Right x y z w).intervention assignment
  let evaluated := fun roots : model.latent.Assignment =>
    model.evalUnder intervention roots
  let cylinder := fun nodes : NodeSet S => fun roots : model.latent.Assignment =>
    Kernel.agreesOn nodes assignment (evaluated roots)
  refine
    { selected := model.latentRelevantUnder intervention leftRelevant
      selectedOutcome := cylinder z
      selectedCondition := cylinder wSelected
      unselectedOutcome := cylinder y
      unselectedCondition := cylinder wUnselected
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnSelected model intervention leftRelevant z
        assignment leftClosed zContained
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnSelected model intervention leftRelevant
        wSelected assignment leftClosed wSelectedContained
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnUnselected model intervention leftRelevant
        rightRelevant y assignment rightClosed yContained separated
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnUnselected model intervention leftRelevant
        rightRelevant wUnselected assignment rightClosed
        wUnselectedContained separated
  · funext roots
    simp only [productPreimage, rule1Left, Kernel.numeratorEvent,
      cylinder, evaluated]
    change
      (Kernel.agreesOn y assignment (model.evalUnder intervention roots) &&
        Kernel.agreesOn (NodeSet.union z w) assignment
          (model.evalUnder intervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union z,
      Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule1Right, Kernel.conditionEvent,
      cylinder, evaluated]
    change Kernel.agreesOn w assignment
      (model.evalUnder intervention roots) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
  · funext roots
    simp only [productPreimage, rule1Right, Kernel.numeratorEvent,
      cylinder, evaluated]
    change
      (Kernel.agreesOn y assignment (model.evalUnder intervention roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder intervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule1Left, Kernel.conditionEvent,
      cylinder, evaluated]
    change Kernel.agreesOn (NodeSet.union z w) assignment
      (model.evalUnder intervention roots) = _
    rw [wSplit, Kernel.agreesOn_union z,
      Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl

/--
Rule 1 when `W` shares no latent with the open `Z` core: `Z` is selected,
`Y` and `W` are unselected, and the common condition is the whole of `W`.
-/
def rule1PartitionWitness_of_w_avoids_z_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (havoid : rule1WMeetsUnionAncestral model G x w assignment z = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  refine
    { selected := model.latentRelevantUnder Iu
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
      selectedOutcome := zEv
      selectedCondition := Probability.topEvent
      unselectedOutcome := yEv
      unselectedCondition := wEv
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [Iu, zEv] using
      agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment
  · exact CanonicalFactorization.DependsOnSelected.const _ _ _ true
  · simpa [Iu, yEv] using
      agreesOn_rule1Y_dependsOnUnselected_union model G projected x y z w
        assignment separated
  · simpa [wEv] using
      agreesOn_rule1W_dependsOnUnselected_of_avoids_z model G x y z w
        assignment havoid
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, zEv, yEv, wEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew]
    simp only [Bool.and_true]
    ac_rfl
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, wEv]
    rw [show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.true_and]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, yEv, wEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.true_and]
    rw [hR, Bool.and_comm]
    exact hy.trans (Bool.and_comm _ _)
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, zEv, wEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union]
    simp only [Bool.and_true]
    rw [hR, Bool.and_comm]
    exact hz.trans (Bool.and_comm _ _)

/--
Rule 1 when `W` shares no latent with the open `Y` core: selected
coordinates are everything except that core, `W` sits with `Z` on the
selected side, and `Y` is unselected.
-/
def rule1PartitionWitness_of_w_avoids_y_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (havoid : rule1WMeetsUnionAncestral model G x w assignment y = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let zCore := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z
  let yCore := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have hsep :=
    FiniteLatentSCM.rule1Ancestral_latentSeparated_union model G projected
      x y z w assignment separated
  have zCore_subset_not_y :
      forall root, model.latentRelevantUnder Iu zCore root = true ->
        (!model.latentRelevantUnder Iu yCore root) = true := by
    intro root hz
    have hy := hsep root (by simpa [Iu, zCore] using hz)
    cases hy' : model.latentRelevantUnder Iu yCore root with
    | false =>
        rfl
    | true =>
        simp [Iu, yCore, hy'] at hy
  refine
    { selected := fun root => !model.latentRelevantUnder Iu yCore root
      selectedOutcome := zEv
      selectedCondition := wEv
      unselectedOutcome := yEv
      unselectedCondition := Probability.topEvent
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value zEv zCore_subset_not_y
      (by simpa [Iu, zEv, zCore] using
        agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment)
  · simpa [wEv, Iu, yCore] using
      agreesOn_rule1W_dependsOnSelected_of_avoids_y model G x y z w
        assignment havoid
  · simpa [Iu, yEv, yCore] using
      CanonicalFactorization.DependsOnUnselected.of_selected_compl
        model.latent.count model.latent.Value
        (model.latentRelevantUnder Iu yCore) yEv
        (by simpa [Iu, yEv, yCore] using
          agreesOn_rule1Y_dependsOnSelected_union model G x y z w assignment)
  · exact CanonicalFactorization.DependsOnUnselected.const _ _ _ true
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, zEv, yEv, wEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew]
    simp only [Bool.and_true]
    ac_rfl
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, wEv]
    rw [show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.and_true]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, yEv, wEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.and_true]
    rw [hR]
    exact Bool.and_comm _ _ ▸ hy
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, zEv, wEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union]
    simp only [Bool.and_true]
    rw [hR, Bool.and_comm]
    exact hz.trans (Bool.and_comm _ _)

/--
Rule 1 from the two one-sided core-avoidance witnesses, once `W` is known
not to meet both open cores.
-/
def rule1PartitionWitness_of_not_both_meet
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hnot :
      (rule1WMeetsUnionAncestral model G x w assignment z &&
        rule1WMeetsUnionAncestral model G x w assignment y) = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  cases hZ : rule1WMeetsUnionAncestral model G x w assignment z with
  | false =>
      exact rule1PartitionWitness_of_w_avoids_z_core model G projected
        x y z w assignment separated hZ
  | true =>
      cases hY : rule1WMeetsUnionAncestral model G x w assignment y with
      | false =>
          exact rule1PartitionWitness_of_w_avoids_y_core model G projected
            x y z w assignment separated hY
      | true =>
          simp [hZ, hY] at hnot

/--
Rule 1 with empty given-set `W`.  The both-meet obligation is vacuous, so
path d-separation and the projected graph already supply the partition
witness.  This is the empty-conditioner special case of
`PathDoRulePartitionWitnesses.rule1`.
-/
def rule1PartitionWitness_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hw : NodeSet.isEmpty w = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment :=
  rule1PartitionWitness_of_not_both_meet model G projected
    x y z w assignment separated (by
      have hZ :=
        rule1WMeetsUnionAncestral_of_empty_w model G x w assignment z hw
      simp [hZ])

/-- Boolean `&&` is associative and commutative; these rearrangements
avoid relying on the AC tactic at four-factor cylinders. -/
private theorem bool_and_four_pairs (a b c d : Bool) :
    ((a && b) && (c && d)) = ((d && a) && (c && b)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem bool_and_mid_swap (a b c : Bool) :
    ((a && b) && c) = (a && (c && b)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem bool_and_rot_left (a b c : Bool) :
    ((a && b) && c) = ((c && a) && b) := by
  cases a <;> cases b <;> cases c <;> rfl

/--
Rule 1 when `W` meets both open cores, but the two-block split of `W`
still factorizes. Selected coordinates are the complement of the `Y`
block: the open `Y` core together with ancestral latents of the
`Y`-meeting slice. The remaining obligations are that the complementary
slice avoids that block, and that the `Y`-meeting slice avoids the
open `Z` core.
-/
def rule1PartitionWitness_of_w_split
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hSelAvoids :
      rule1WSplitSelectedMeetsYCore model G x y z w assignment = false)
    (hOverlap :
      rule1WSplitAncestralLatentsOverlap model G x y z w assignment = false)
    (hUnselAvoidsZ :
      rule1WSplitUnselectedMeetsZCore model G x y z w assignment = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let wSel := rule1WSplitSelected model G x w assignment y
  let wUnsel := rule1WSplitUnselected model G x w assignment y
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wSelEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wSel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  let wUnselEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wUnsel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have wEq : forall roots,
      Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots) =
        (wSelEv roots && wUnselEv roots) := by
    intro roots
    have hnodes :=
      congrArg
        (fun nodes =>
          Kernel.agreesOn nodes assignment
            (model.evalUnder
              ((rule1Right x y z w).intervention assignment) roots))
        (rule1WSplit_union model G x w assignment y)
    simpa [wSelEv, wUnselEv, wSel, wUnsel, Kernel.agreesOn_union] using
      hnodes.symm
  refine
    { selected := fun root =>
        !(rule1WSplitYBlockLatents model G x y z w assignment root)
      selectedOutcome := zEv
      selectedCondition := wSelEv
      unselectedOutcome := yEv
      unselectedCondition := wUnselEv
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [zEv, Iu] using
      (agreesOn_rule1Z_dependsOnNotYBlock model G projected x y z w
        assignment separated hUnselAvoidsZ)
  · simpa [wSelEv, wSel] using
      (agreesOn_rule1WSplitSelected_dependsOnNotYBlock model G x y z w
        assignment hSelAvoids hOverlap)
  · simpa [yEv, Iu] using
      agreesOn_rule1Y_dependsOnYBlock model G x y z w assignment
  · simpa [wUnselEv, wUnsel] using
      agreesOn_rule1WSplitUnselected_dependsOnYBlock model G x y z w
        assignment
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      zEv, yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew, wEq roots]
    exact bool_and_four_pairs (wSelEv roots) (wUnselEv roots)
      (yEv roots) (zEv roots)
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      wSelEv, wUnselEv]
    rw [show (rule1Right x y z w).condition = w from rfl, wEq roots]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl, hR,
      Bool.and_comm, hy, ← hR, wEq roots]
    exact bool_and_mid_swap (wSelEv roots) (wUnselEv roots) (yEv roots)
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      zEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hR, Bool.and_comm, hz, ← hR, wEq roots]
    exact bool_and_rot_left (wSelEv roots) (wUnselEv roots) (zEv roots)

/-- The closed selected slice depends only on the complement of the closed
`Y` block. -/
theorem agreesOn_rule1WSplitClosedSelected_dependsOnNotYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hY :
      rule1WSplitClosedSelectedMeetsYCore model G x y z w assignment =
        false)
    (hOverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
        false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitSelectedClosed model G x w assignment y) assignment
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
            (rule1WSplitSelectedClosed model G x w assignment y))
          root)).mp
      (by simpa [rule1WSplitClosedSelectedMeetsYCore] using hY)
  have hallO :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelectedClosed model G x w assignment y)) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselectedClosed model G x w assignment y))
          root)).mp
      (by simpa [rule1WSplitClosedAncestralLatentsOverlap] using hOverlap)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitSelectedClosed model G x w assignment y))
            root = true ->
          (!(rule1WSplitClosedYBlockLatents model G x y z w assignment
              root)) = true := by
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
                (rule1WSplitUnselectedClosed model G x w assignment y))
              root with
        | true =>
            simp [hr, hu] at hOroot
        | false =>
            simp [rule1WSplitClosedYBlockLatents, hy, hu]
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitSelectedClosed model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    hsub
    (agreesOn_rule1WSplitClosedSelected_dependsOnAncestral model G x y z w
      assignment)

/-- Under `do(X ∪ W)`, `Z` depends only on the complement of the closed
`Y` block once that block shares no latent with the open `Z` core. -/
theorem agreesOn_rule1Z_dependsOnNotClosedYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hUnselZ :
      rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment =
        false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
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
            (rule1WSplitUnselectedClosed model G x w assignment y))
          root)).mp
      (by simpa [rule1WSplitClosedUnselectedMeetsZCore] using hUnselZ)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
            root = true ->
          (!(rule1WSplitClosedYBlockLatents model G x y z w assignment
              root)) = true := by
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
                (rule1WSplitUnselectedClosed model G x w assignment y))
              root with
        | true =>
            simp [hz, hu] at hZroot
        | false =>
            simp [rule1WSplitClosedYBlockLatents, hy', hu]
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn z assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots))
    hsub
    (agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment)

/-- `Y` ignores the complement of the closed `Y` block. -/
theorem agreesOn_rule1Y_dependsOnClosedYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
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
          rule1WSplitClosedYBlockLatents model G x y z w assignment root =
            true := by
    intro root hr
    simp [rule1WSplitClosedYBlockLatents, hr]
  exact CanonicalFactorization.DependsOnUnselected.of_selected_compl
    model.latent.count model.latent.Value
    (rule1WSplitClosedYBlockLatents model G x y z w assignment)
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

/-- The closed `Y` block of `W` ignores the complement of that block. -/
theorem agreesOn_rule1WSplitClosedUnselected_dependsOnYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselectedClosed model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitUnselectedClosed model G x w assignment y))
            root = true ->
          rule1WSplitClosedYBlockLatents model G x y z w assignment root =
            true := by
    intro root hr
    simp [rule1WSplitClosedYBlockLatents, hr]
  exact CanonicalFactorization.DependsOnUnselected.of_selected_compl
    model.latent.count model.latent.Value
    (rule1WSplitClosedYBlockLatents model G x y z w assignment)
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitUnselectedClosed model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    (CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselectedClosed model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots))
      hsub
      (agreesOn_rule1WSplitClosedUnselected_dependsOnAncestral model G x y
        z w assignment))

/--
Rule 1 when `W` meets both open cores, using the descendant-closed
`Y` block. Directed `W_Y → W'` and extra `do(X)`-free `Y`-core ancestors
outside `W` are absorbed as `Y`-side seeds, so the complementary slice
avoids the closed `Y` block by construction. The remaining obligations
are that the two slices share no ancestral latent, and that the closed
`Y` block avoids the open `Z` core.
-/
def rule1PartitionWitness_of_w_split_closed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hOverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
        false)
    (hUnselAvoidsZ :
      rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment =
        false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  have hSelAvoids :
      rule1WSplitClosedSelectedMeetsYCore model G x y z w assignment =
        false :=
    rule1WSplitClosedSelectedMeetsYCore_eq_false model G x y z w assignment
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let wSel := rule1WSplitSelectedClosed model G x w assignment y
  let wUnsel := rule1WSplitUnselectedClosed model G x w assignment y
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wSelEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wSel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  let wUnselEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wUnsel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have wEq : forall roots,
      Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots) =
        (wSelEv roots && wUnselEv roots) := by
    intro roots
    have hnodes :=
      congrArg
        (fun nodes =>
          Kernel.agreesOn nodes assignment
            (model.evalUnder
              ((rule1Right x y z w).intervention assignment) roots))
        (rule1WSplitClosed_union model G x w assignment y)
    simpa [wSelEv, wUnselEv, wSel, wUnsel, Kernel.agreesOn_union] using
      hnodes.symm
  refine
    { selected := fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root)
      selectedOutcome := zEv
      selectedCondition := wSelEv
      unselectedOutcome := yEv
      unselectedCondition := wUnselEv
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [zEv, Iu] using
      (agreesOn_rule1Z_dependsOnNotClosedYBlock model G projected x y z w
        assignment separated hUnselAvoidsZ)
  · simpa [wSelEv, wSel] using
      (agreesOn_rule1WSplitClosedSelected_dependsOnNotYBlock model G x y z w
        assignment hSelAvoids hOverlap)
  · simpa [yEv, Iu] using
      agreesOn_rule1Y_dependsOnClosedYBlock model G x y z w assignment
  · simpa [wUnselEv, wUnsel] using
      agreesOn_rule1WSplitClosedUnselected_dependsOnYBlock model G x y z w
        assignment
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      zEv, yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew, wEq roots]
    exact bool_and_four_pairs (wSelEv roots) (wUnselEv roots)
      (yEv roots) (zEv roots)
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      wSelEv, wUnselEv]
    rw [show (rule1Right x y z w).condition = w from rfl, wEq roots]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl, hR,
      Bool.and_comm, hy, ← hR, wEq roots]
    exact bool_and_mid_swap (wSelEv roots) (wUnselEv roots) (yEv roots)
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      zEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hR, Bool.and_comm, hz, ← hR, wEq roots]
    exact bool_and_rot_left (wSelEv roots) (wUnselEv roots) (zEv roots)

/--
Rule 1 from path d-separation.  If `W` misses at least one open core, the
one-sided witnesses suffice.  If it meets both, the descendant-closed
split still factorizes once the two slices share no ancestral latent and
the closed `Y` block misses the open `Z` core.
-/
def rule1PartitionWitness_of_path
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hOverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
        false)
    (hUnselAvoidsZ :
      rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment =
        false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  cases hboth :
      (rule1WMeetsUnionAncestral model G x w assignment z &&
        rule1WMeetsUnionAncestral model G x w assignment y) with
  | false =>
      exact rule1PartitionWitness_of_not_both_meet model G projected
        x y z w assignment separated hboth
  | true =>
      exact rule1PartitionWitness_of_w_split_closed model G projected
        x y z w assignment separated hOverlap hUnselAvoidsZ

/--
Rule 1 from path d-separation, with the remaining both-meet obligations
stated as graph-theoretic conditions on the closed split rather than as
raw Bools.
-/
def rule1PartitionWitness_of_closed_split
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
              true)
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
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment :=
  rule1PartitionWitness_of_path model G projected x y z w assignment
    separated
    (rule1WSplitClosedAncestralLatentsOverlap_eq_false_of model G projected
      x y z w assignment separated hSame hDistinct)
    (rule1WSplitClosedUnselectedMeetsZCore_eq_false_of model G projected
      x y z w assignment separated hSeed)

/-- Build the rule-2 witness once the four cylinders have been assigned to a
common latent partition.  The cross-world event equalities are discharged by
SCM composition; only the dependence proofs remain graph-specific. -/
def rule2PartitionWitness (model : FiniteLatentSCM S)
    (x y z w wSelected wUnselected : NodeSet S)
    (assignment : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (wSplit : w = NodeSet.union wSelected wUnselected)
    (zDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule2Right x y z w).intervention assignment) roots)))
    (wSelectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn wSelected assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)))
    (yDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)))
    (wUnselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn wUnselected assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots))) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  let baseIntervention := (rule2Right x y z w).intervention assignment
  let extendedIntervention := (rule2Left x y z w).intervention assignment
  let baseCylinder := fun nodes : NodeSet S =>
    fun roots : model.latent.Assignment => Kernel.agreesOn nodes assignment
      (model.evalUnder baseIntervention roots)
  let extendedCylinder := fun nodes : NodeSet S =>
    fun roots : model.latent.Assignment => Kernel.agreesOn nodes assignment
      (model.evalUnder extendedIntervention roots)
  refine
    { selected := selected
      selectedOutcome := baseCylinder z
      selectedCondition := extendedCylinder wSelected
      unselectedOutcome := extendedCylinder y
      unselectedCondition := extendedCylinder wUnselected
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [baseCylinder, baseIntervention] using zDepends
  · simpa [extendedCylinder, extendedIntervention] using wSelectedDepends
  · simpa [extendedCylinder, extendedIntervention] using yDepends
  · simpa [extendedCylinder, extendedIntervention] using wUnselectedDepends
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.numeratorEvent,
      baseCylinder, extendedCylinder]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder baseIntervention roots) &&
        Kernel.agreesOn (NodeSet.union z w) assignment
          (model.evalUnder baseIntervention roots)) = _
    rw [Kernel.agreesOn_union z w]
    cases zHolds : Kernel.agreesOn z assignment
        (model.evalUnder baseIntervention roots) with
    | false => simp [Probability.inter, zHolds]
    | true =>
        have evaluationsEqual :
            model.evalUnder extendedIntervention roots =
              model.evalUnder baseIntervention roots := by
          simpa [baseIntervention, extendedIntervention, rule2Left,
            rule2Right] using
            evalUnder_union_intervention_eq_of_agreesOn model x z assignment
              roots zHolds
        simp only [Probability.inter]
        rw [evaluationsEqual]
        rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
        simp [zHolds]
        ac_rfl
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.conditionEvent,
      extendedCylinder]
    change Kernel.agreesOn w assignment
      (model.evalUnder extendedIntervention roots) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.numeratorEvent,
      extendedCylinder]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder extendedIntervention roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder extendedIntervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.conditionEvent,
      baseCylinder, extendedCylinder]
    change Kernel.agreesOn (NodeSet.union z w) assignment
      (model.evalUnder baseIntervention roots) = _
    rw [Kernel.agreesOn_union z w]
    cases zHolds : Kernel.agreesOn z assignment
        (model.evalUnder baseIntervention roots) with
    | false => simp [Probability.inter, zHolds]
    | true =>
        have evaluationsEqual :
            model.evalUnder extendedIntervention roots =
              model.evalUnder baseIntervention roots := by
          simpa [baseIntervention, extendedIntervention, rule2Left,
            rule2Right] using
            evalUnder_union_intervention_eq_of_agreesOn model x z assignment
              roots zHolds
        simp only [Probability.inter]
        rw [evaluationsEqual]
        rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
        simp [zHolds]

/-- Empty-cylinder events are constant, so they depend on no coordinates. -/
theorem agreesOn_empty_eq_true
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (assignment : S.Assignment) (roots : model.latent.Assignment) :
    Kernel.agreesOn NodeSet.empty assignment
      (model.evalUnder intervention roots) = true := by
  unfold Kernel.agreesOn NodeSet.empty
  refine (finAll_eq_true_iff _).mpr ?_
  intro _i
  simp

/-- A latent is shared between `An(Z)` under `do(X)` and `An(W)` under
`do(X ∪ Z)`.  When this is false, the whole of `W` can sit with `Y` on
the unselected side of the rule-2 partition. -/
def rule2WMeetsZAncestral (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z) root &&
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root)

/-- Ancestral overlap with `W` is vacuous when `W` is empty. -/
theorem rule2WMeetsZAncestral_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true) :
    rule2WMeetsZAncestral model G x z w assignment = false := by
  have hw' : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  subst hw'
  refine (finAny_eq_false_iff _).mpr ?_
  intro root
  have hrel :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            NodeSet.empty) root = false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      model.latentRelevantUnder_empty
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        root
  simp [hrel]

/-- The displayed meet is exactly a shared latent of the two ancestral
families. -/
theorem rule2WMeetsZAncestral_eq_true_iff
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment) :
    rule2WMeetsZAncestral model G x z w assignment = true ↔
      Exists fun root : Fin model.latent.count =>
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true ∧
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root =
              true := by
  constructor
  · intro hmeet
    rcases (finAny_eq_true_iff _).mp (by
      simpa [rule2WMeetsZAncestral] using hmeet) with ⟨root, hroot⟩
    exact ⟨root, Bool.and_eq_true_iff.mp hroot⟩
  · rintro ⟨root, hZ, hW⟩
    apply (finAny_eq_true_iff _).mpr
    refine ⟨root, ?_⟩
    exact Bool.and_eq_true_iff.mpr ⟨hZ, hW⟩

/-- Rule 2 when `W` shares no latent with `An(Z)`: `W` under `do(X ∪ Z)`
depends only on coordinates complementary to those `An(Z)` latents. -/
theorem agreesOn_rule2W_dependsOnUnselected_of_avoids_z
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) w assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) w assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) w w
      (fun _i hi => hi))
    left right
  intro root hrelW
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hmeet :
          rule2WMeetsZAncestral model G x z w assignment = true := by
        refine (rule2WMeetsZAncestral_eq_true_iff model G x z w
            assignment).mpr ⟨root, ?_, ?_⟩
        · simpa [selected, rule2Right, Kernel.intervention] using hsel
        · simpa [heavier, rule2Left, Kernel.intervention] using hrelW
      rw [hmeet] at havoid
      cases havoid

/-- A `do(X)`-relevant `An(Z)` latent is already relevant to the rule-2
open `Z` core when `W` shares no such latent: its free incident child is
open given `X ∪ W`, and a shortest walk into `Z` never meets `W`. -/
theorem latentRelevantUnder_rule2ZOpenCore_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    {root : Fin model.latent.count}
    (hrel : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z) root = true) :
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.rule2ZOpenCore G x z w) root = true := by
  let doX :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  let doXZ :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z) NodeSet.empty).intervention
      assignment
  rcases (model.latentRelevantUnder_eq_true_iff doX
      (FiniteLatentSCM.ancestralInBar G x z) root).mp hrel with
    ⟨child, hsel, hnone, hinc⟩
  have hx : x child = false := by
    dsimp [doX, Kernel.intervention] at hnone
    cases hx : x child with
    | false =>
        rfl
    | true =>
        simp [hx] at hnone
  have hwChild : w child = false := by
    cases hw : w child with
    | false =>
        rfl
    | true =>
        have hz : z child = false := by
          cases hz : z child with
          | false =>
              rfl
          | true =>
              have hfalse := disjoint.zw child hz
              rw [hw] at hfalse
              cases hfalse
        have hfreeXZ : doXZ child = none := by
          simp [doXZ, Kernel.intervention, NodeSet.union, hx, hz]
        have hancW :
            FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w child =
              true :=
          FiniteLatentSCM.observedAncestorOf_self G
            (GraphMutilation.bar (NodeSet.union x z)) w hw
        have hW :=
          model.latentRelevantUnder_of_incident doXZ
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
            root child hancW hfreeXZ hinc
        have hmeet :
            rule2WMeetsZAncestral model G x z w assignment = true :=
          (rule2WMeetsZAncestral_eq_true_iff model G x z w assignment).mpr
            ⟨root, hrel, hW⟩
        rw [hmeet] at havoid
        cases havoid
  have hunion : NodeSet.union x w child = false :=
    Bool.or_eq_false_iff.mpr ⟨hx, hwChild⟩
  have hbar :=
    FiniteLatentSCM.observedAncestorOf_barUnderline_z_of_bar G x z child hsel
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.barUnderline x z) z child hbar with
    ⟨target, htarget, length, walk, simple, minimal⟩
  have hopen :
      forall n, n ∈ walk.nodes -> NodeSet.union x w n = false := by
    intro n hn
    have hxN : x n = false := by
      by_cases hsrc : n = child
      · subst n
        exact hx
      · have hin :=
          PathSpecification.directed_walk_mem_not_removeIncoming G
            (GraphMutilation.barUnderline x z) walk hn hsrc
        simpa [GraphMutilation.barUnderline] using hin
    have hwN : w n = false := by
      cases hw : w n with
      | false =>
          rfl
      | true =>
          have hzN : z n = false := by
            cases hz : z n with
            | false =>
                rfl
            | true =>
                have hfalse := disjoint.zw n hz
                rw [hw] at hfalse
                cases hfalse
          by_cases hsrc : n = child
          · subst n
            exact (Bool.false_ne_true (hwChild.symm.trans hw)).elim
          · rcases FiniteReachability.ExactWalk.exists_prefix_with_subset
                walk hn with
              ⟨_plen, preWalk, _bound, subset, rest, hsplit⟩
            have hnotZ :
                forall m, m ∈ preWalk.nodes -> z m = false := by
              intro m hm
              have hmWalk := subset m hm
              by_cases hmeq : m = target
              · subst m
                have hneN : n ≠ target := by
                  intro eq
                  subst n
                  exact Bool.false_ne_true (hzN.symm.trans htarget)
                cases hrest : rest with
                | nil =>
                    have heq : walk.nodes = preWalk.nodes := by
                      simpa [hrest] using hsplit
                    have wlast := walk.nodes_getLast
                    have plast := preWalk.nodes_getLast
                    have : n = target := by
                      simpa [heq, plast] using wlast
                    exact (hneN this).elim
                | cons head tail =>
                    have hwalkNodup := simple
                    rw [hsplit, hrest] at hwalkNodup
                    have hrestMem : target ∈ head :: tail := by
                      have wlast := walk.nodes_getLast
                      have hrestLast :
                          (head :: tail).getLast? = some target := by
                        rw [hsplit, hrest] at wlast
                        simpa [List.getLast?_append] using wlast
                      exact List.mem_of_mem_getLast? (by
                        simp [hrestLast])
                    have hne :=
                      (List.nodup_append.mp hwalkNodup).2.2 target hm target
                        hrestMem
                    exact (hne rfl).elim
              · have hfalse :=
                  FiniteReachability.ExactWalk.not_mem_targets_of_minimal_internal
                    walk minimal hmWalk hmeq
                cases hzm : z m with
                | false =>
                    rfl
                | true =>
                    rw [hzm] at hfalse
                    cases hfalse
            have hancW :
                FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w
                    child = true :=
              FiniteLatentSCM.observedAncestorOf_barUnion_of_barUnderline_walk
                G x z w preWalk hw hnotZ
            have hzChild : z child = false :=
              hnotZ child preWalk.mem_source
            have hfreeXZ : doXZ child = none := by
              simp [doXZ, Kernel.intervention, NodeSet.union, hx, hzChild]
            have hW :=
              model.latentRelevantUnder_of_incident doXZ
                (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
                root child hancW hfreeXZ hinc
            have hmeet :
                rule2WMeetsZAncestral model G x z w assignment = true :=
              (rule2WMeetsZAncestral_eq_true_iff model G x z w
                  assignment).mpr ⟨root, hrel, hW⟩
            rw [hmeet] at havoid
            cases havoid
    exact Bool.or_eq_false_iff.mpr ⟨hxN, hwN⟩
  have hancU :=
    FiniteLatentSCM.observedAncestorOf_unionBarUnderline_of_open_walk G x w z
      z walk htarget hopen
  have hblocked :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed child) =
        false := by
    simpa [ObservedGraph.blockedBy] using hunion
  have hcore : FiniteLatentSCM.rule2ZOpenCore G x z w child = true := by
    simp [FiniteLatentSCM.rule2ZOpenCore,
      FiniteLatentSCM.openAncestralInGraph, hblocked, hancU]
  exact model.latentRelevantUnder_of_incident doX
    (FiniteLatentSCM.rule2ZOpenCore G x z w) root child hcore hnone hinc

/-- A `do(X ∪ Z)`-relevant `An(Y)` latent that is also `do(X)`-relevant to
`An(Z)` is already relevant to the rule-2 open `Y` core when `W` shares
no `An(Z)` latent: its free incident child is open given `X ∪ W`, and a
shortest walk into `Y` in `G_{\overline{X}\underline{Z}}` never meets
`W`. -/
theorem latentRelevantUnder_rule2YOpenCore_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    {root : Fin model.latent.count}
    (hrelZ : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z) root = true)
    (hrelY : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root =
        true) :
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.rule2YOpenCore G x y z w) root = true := by
  let doX :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  let doXZ :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z) NodeSet.empty).intervention
      assignment
  rcases (model.latentRelevantUnder_eq_true_iff doXZ
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root).mp
      hrelY with
    ⟨child, hsel, hnone, hinc⟩
  have hfreeXZ : NodeSet.union x z child = false := by
    dsimp [doXZ, Kernel.intervention] at hnone
    cases hunion : NodeSet.union x z child with
    | false =>
        rfl
    | true =>
        simp [hunion] at hnone
  have hx : x child = false := (Bool.or_eq_false_iff.mp hfreeXZ).1
  have hzChild : z child = false := (Bool.or_eq_false_iff.mp hfreeXZ).2
  have hwChild : w child = false := by
    cases hw : w child with
    | false =>
        rfl
    | true =>
        have hancW :
            FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w child =
              true :=
          FiniteLatentSCM.observedAncestorOf_self G
            (GraphMutilation.bar (NodeSet.union x z)) w hw
        have hW :=
          model.latentRelevantUnder_of_incident doXZ
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
            root child hancW hnone hinc
        have hmeet :
            rule2WMeetsZAncestral model G x z w assignment = true :=
          (rule2WMeetsZAncestral_eq_true_iff model G x z w assignment).mpr
            ⟨root, hrelZ, hW⟩
        rw [hmeet] at havoid
        cases havoid
  have hunion : NodeSet.union x w child = false :=
    Bool.or_eq_false_iff.mpr ⟨hx, hwChild⟩
  have hbar :=
    FiniteLatentSCM.observedAncestorOf_barUnderline_y_of_barUnion G x y z
      child hsel hfreeXZ
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.barUnderline x z) y child hbar with
    ⟨target, htarget, length, walk, simple, minimal⟩
  have hnotZWalk :
      forall m, m ∈ walk.nodes -> z m = false := by
    intro m hm
    by_cases hsrc : m = child
    · subst m
      exact hzChild
    · by_cases hmt : m = target
      · subst m
        have hyfalse := disjoint.yz target htarget
        cases hz : z target with
        | false =>
            rfl
        | true =>
            rw [hz] at hyfalse
            cases hyfalse
      · rcases FiniteReachability.ExactWalk.exists_simple_suffix_of_mem
            walk simple hm with
          ⟨_slen, suffix, _ss, _pre, _hsplit⟩
        cases suffix with
        | refl =>
            exact (hmt rfl).elim
        | step first rest =>
            have hzParent : z m = false := by
              simp [ObservedGraph.observedDirectedEdge,
                GraphMutilation.barUnderline] at first
              exact first.1.2
            exact hzParent
  have hopen :
      forall n, n ∈ walk.nodes -> NodeSet.union x w n = false := by
    intro n hn
    have hxN : x n = false := by
      by_cases hsrc : n = child
      · subst n
        exact hx
      · have hin :=
          PathSpecification.directed_walk_mem_not_removeIncoming G
            (GraphMutilation.barUnderline x z) walk hn hsrc
        simpa [GraphMutilation.barUnderline] using hin
    have hwN : w n = false := by
      cases hw : w n with
      | false =>
          rfl
      | true =>
          by_cases hsrc : n = child
          · subst n
            exact (Bool.false_ne_true (hwChild.symm.trans hw)).elim
          · rcases FiniteReachability.ExactWalk.exists_prefix_with_subset
                walk hn with
              ⟨_plen, preWalk, _bound, subset, _rest, _hsplit⟩
            have hnotZ :
                forall m, m ∈ preWalk.nodes -> z m = false :=
              fun m hm => hnotZWalk m (subset m hm)
            have hancW :
                FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w
                    child = true :=
              FiniteLatentSCM.observedAncestorOf_barUnion_of_barUnderline_walk
                G x z w preWalk hw hnotZ
            have hW :=
              model.latentRelevantUnder_of_incident doXZ
                (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
                root child hancW hnone hinc
            have hmeet :
                rule2WMeetsZAncestral model G x z w assignment = true :=
              (rule2WMeetsZAncestral_eq_true_iff model G x z w
                  assignment).mpr ⟨root, hrelZ, hW⟩
            rw [hmeet] at havoid
            cases havoid
    exact Bool.or_eq_false_iff.mpr ⟨hxN, hwN⟩
  have hancU :=
    FiniteLatentSCM.observedAncestorOf_unionBarUnderline_of_open_walk G x w z
      y walk htarget hopen
  have hblocked :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed child) =
        false := by
    simpa [ObservedGraph.blockedBy] using hunion
  have hcore : FiniteLatentSCM.rule2YOpenCore G x y z w child = true := by
    simp [FiniteLatentSCM.rule2YOpenCore,
      FiniteLatentSCM.openAncestralInGraph, hblocked, hancU]
  have hnoneX : doX child = none := by
    simp [doX, Kernel.intervention, hx]
  exact model.latentRelevantUnder_of_incident doX
    (FiniteLatentSCM.rule2YOpenCore G x y z w) root child hcore hnoneX hinc

/-- Rule 2 with empty `W`: `Z` under `do(X)` depends only on latents of
`An(Z)` in `G_{\overline{X}}`. -/
theorem agreesOn_rule2Z_dependsOnSelected_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x _y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule2Right x y z w).intervention assignment) roots)) :=
  agreesOn_evalUnder_dependsOnSelected model
    ((rule2Right x y z w).intervention assignment)
    (FiniteLatentSCM.ancestralInBar G x z) z assignment
    (by
      have hact :
          (rule2Right x y z w).intervention assignment =
            (fun i => if x i then some (assignment i) else none) := by
        funext i
        simp [rule2Right, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          x z assignment)
    (FiniteLatentSCM.subset_ancestralInBar G x z z (fun _i hi => hi))

/-- Rule 2 with empty `W`: `Y` under `do(X ∪ Z)` is independent of the
selected `An(Z)` latents, because those latents are separated from the
open `Y` core in `G_{\overline{X}\underline{Z}}`. -/
theorem agreesOn_rule2Y_dependsOnUnselected_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) y assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) y y
      (fun _i hi => hi))
    left right
  intro root hrelY
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hZopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2ZOpenCore G x z w) root = true := by
        have hrelZ : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true := by
          simpa [selected, rule2Right, Kernel.intervention] using hsel
        exact FiniteLatentSCM.latentRelevantUnder_rule2ZOpenCore_of_ancestral_of_empty_w
          model G x z w assignment hw hrelZ
      have hYopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2YOpenCore G x y z w) root = true := by
        have hrelY' : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root =
              true := by
          simpa [heavier, rule2Left, Kernel.intervention] using hrelY
        exact FiniteLatentSCM.latentRelevantUnder_rule2YOpenCore_of_barUnion_of_empty_w
          model G x y z w assignment hw hrelY'
      have hsep :=
        FiniteLatentSCM.rule2OpenCores_latentSeparated_of_empty_w model G
          projected x y z w assignment hw separated root hZopen
      rw [hYopen] at hsep
      cases hsep

/-- Rule 2 when `W` shares no `An(Z)` latent: `Y` under `do(X ∪ Z)` is
independent of the selected `An(Z)` latents, because those latents are
separated from the open `Y` core in `G_{\overline{X}\underline{Z}}`. -/
theorem agreesOn_rule2Y_dependsOnUnselected_of_avoids_z
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) y assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) y y
      (fun _i hi => hi))
    left right
  intro root hrelY
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hZopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2ZOpenCore G x z w) root = true := by
        have hrelZ : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true := by
          simpa [selected, rule2Right, Kernel.intervention] using hsel
        exact latentRelevantUnder_rule2ZOpenCore_of_avoids
          model G x y z w assignment disjoint havoid hrelZ
      have hYopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2YOpenCore G x y z w) root = true := by
        have hrelZ : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true := by
          simpa [selected, rule2Right, Kernel.intervention] using hsel
        have hrelY' : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root =
              true := by
          simpa [heavier, rule2Left, Kernel.intervention] using hrelY
        exact latentRelevantUnder_rule2YOpenCore_of_avoids
          model G x y z w assignment disjoint havoid hrelZ hrelY'
      have hsep :=
        FiniteLatentSCM.rule2OpenCores_latentSeparated model G
          projected x y z w assignment separated root hZopen
      rw [hYopen] at hsep
      cases hsep

/-- Empty `W` supplies the four cylinder-dependence hypotheses of
`rule2PartitionWitness`: both `W` blocks are empty, `Z` depends on
`An(Z)` under `do(X)`, and `Y` is independent of those latents under
`do(X ∪ Z)`. -/
def rule2PartitionWitness_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    (hw : NodeSet.isEmpty w = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  have hact : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  have wSplit : w = NodeSet.union NodeSet.empty NodeSet.empty := by
    simp [hact, NodeSet.union_empty_right]
  exact rule2PartitionWitness model x y z w
    NodeSet.empty NodeSet.empty assignment
    (model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z))
    wSplit
    (agreesOn_rule2Z_dependsOnSelected_of_empty_w model G x y z w assignment)
    (by
      intro left right _agree
      have hL :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment left
      have hR :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment right
      simp [hL, hR])
    (agreesOn_rule2Y_dependsOnUnselected_of_empty_w model G projected
      x y z w assignment hw separated)
    (by
      intro left right _agree
      have hL :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment left
      have hR :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment right
      simp [hL, hR])

/-- When `W` shares no `An(Z)` latent, the whole of `W` is unselected:
`wSelected` is empty, `wUnselected` is `W`, `Z` depends on `An(Z)` under
`do(X)`, and `Y` is independent of those latents under `do(X ∪ Z)`. -/
def rule2PartitionWitness_of_w_avoids_z
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  have wSplit : w = NodeSet.union NodeSet.empty w :=
    (NodeSet.union_empty_left w).symm
  exact rule2PartitionWitness model x y z w
    NodeSet.empty w assignment
    (model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z))
    wSplit
    (agreesOn_rule2Z_dependsOnSelected_of_empty_w model G x y z w assignment)
    (by
      intro left right _agree
      have hL :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment left
      have hR :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment right
      simp [hL, hR])
    (agreesOn_rule2Y_dependsOnUnselected_of_avoids_z model G projected
      x y z w assignment disjoint havoid separated)
    (agreesOn_rule2W_dependsOnUnselected_of_avoids_z model G
      x y z w assignment havoid)

/-- A `W` vertex that is free under `do(X ∪ Z)` and incident to a
`do(X)`-relevant `An(Z)` latent.  These are the observed children of the
rule-2 meet. -/
def rule2WVertexMeetsZ (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    (w i &&
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root &&
        model.latent.incident root i)

theorem rule2WVertexMeetsZ_subset_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.Subset (rule2WVertexMeetsZ model G x z w assignment) w := by
  intro i hi
  have hparts :
      (w i &&
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root &&
            model.latent.incident root i) = true := by
    simpa [rule2WVertexMeetsZ] using hi
  exact (Bool.and_eq_true_iff.mp hparts.1).1

/-- A `do(X ∪ Z)`-free ancestor of `W` incident to a `do(X)`-relevant
`An(Z)` latent.  Meeting `W` vertices are included, as are extra free
ancestors outside `W` that still feed the meet. -/
def rule2WZSideSeed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i &&
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root &&
        model.latent.incident root i)

theorem rule2WZSideSeed_of_vertex_meet
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {i : Fin S.count}
    (hi : rule2WVertexMeetsZ model G x z w assignment i = true) :
    rule2WZSideSeed model G x z w assignment i = true := by
  have hparts :
      (w i &&
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root &&
            model.latent.incident root i) = true := by
    simpa [rule2WVertexMeetsZ] using hi
  have hw : w i = true := (Bool.and_eq_true_iff.mp hparts.1).1
  have hself :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i = true :=
    FiniteLatentSCM.observedAncestorOf_self G
      (GraphMutilation.bar (NodeSet.union x z)) w hw
  refine Bool.and_eq_true_iff.mpr ⟨?_, hparts.2⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hself, (Bool.and_eq_true_iff.mp hparts.1).2⟩

/-- A `Z`-side seed already witnesses `rule2WMeetsZAncestral`. -/
theorem rule2WMeetsZAncestral_of_seed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {i : Fin S.count}
    (hi : rule2WZSideSeed model G x z w assignment i = true) :
    rule2WMeetsZAncestral model G x z w assignment = true := by
  have hparts :
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i &&
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root &&
            model.latent.incident root i) = true := by
    simpa [rule2WZSideSeed] using hi
  have hancW :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i = true :=
    (Bool.and_eq_true_iff.mp hparts.1).1
  have hfree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i) = none :=
    Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hparts.1).2
  rcases (finAny_eq_true_iff _).mp hparts.2 with ⟨root, hroot⟩
  rcases Bool.and_eq_true_iff.mp hroot with ⟨hrelZ, hinc⟩
  have hW :=
    model.latentRelevantUnder_of_incident
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
      root i hancW hfree hinc
  exact (rule2WMeetsZAncestral_eq_true_iff model G x z w assignment).mpr
    ⟨root, hrelZ, hW⟩

/-- Avoiding the `An(Z)` meet empties the `Z`-side seed set. -/
theorem rule2WZSideSeed_eq_false_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (i : Fin S.count) :
    rule2WZSideSeed model G x z w assignment i = false := by
  cases hseed : rule2WZSideSeed model G x z w assignment i with
  | false =>
      rfl
  | true =>
      have hmeet :=
        rule2WMeetsZAncestral_of_seed model G x z w assignment hseed
      rw [hmeet] at havoid
      cases havoid

/--
`W` vertices that are directed descendants of a `Z`-side seed in
`G_{\overline{X ∪ Z}}`, including every `Z`-meeting `W` vertex.  Directed
`W_Z → W'` is absorbed into the selected block.
-/
def rule2WSplitSelectedClosed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    w i &&
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (NodeSet.singleton i))
        (rule2WZSideSeed model G x z w assignment)

def rule2WSplitUnselectedClosed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  NodeSet.diff w (rule2WSplitSelectedClosed model G x z w assignment)

theorem rule2WSplitClosed_disjoint (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.Disjoint
      (rule2WSplitSelectedClosed model G x z w assignment)
      (rule2WSplitUnselectedClosed model G x z w assignment) :=
  NodeSet.Disjoint.diff_left w
    (rule2WSplitSelectedClosed model G x z w assignment)

theorem rule2WSplitClosed_union (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.union
      (rule2WSplitSelectedClosed model G x z w assignment)
      (rule2WSplitUnselectedClosed model G x z w assignment) = w := by
  funext i
  simp [rule2WSplitSelectedClosed, rule2WSplitUnselectedClosed,
    NodeSet.union, NodeSet.diff]
  cases hw : w i with
  | false =>
      simp
  | true =>
      cases hm :
          NodeSet.meetsBool
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (NodeSet.singleton i))
            (rule2WZSideSeed model G x z w assignment) with
      | false =>
          simp
      | true =>
          simp

/-- Every `Z`-meeting `W` vertex is a descendant of itself, hence sits
in the closed selected block. -/
theorem rule2WSplitClosed_contains_meets
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {i : Fin S.count}
    (hi : rule2WVertexMeetsZ model G x z w assignment i = true) :
    rule2WSplitSelectedClosed model G x z w assignment i = true := by
  have hw : w i = true :=
    rule2WVertexMeetsZ_subset_w model G x z w assignment i hi
  have hseed :
      rule2WZSideSeed model G x z w assignment i = true :=
    rule2WZSideSeed_of_vertex_meet model G x z w assignment hi
  have hself :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (NodeSet.singleton i) i = true :=
    FiniteLatentSCM.observedAncestorOf_self G
      (GraphMutilation.bar (NodeSet.union x z)) (NodeSet.singleton i)
      ((NodeSet.singleton_eq_true_iff i i).mpr rfl)
  have hmeets :
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (NodeSet.singleton i))
        (rule2WZSideSeed model G x z w assignment) = true :=
    (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨i, hself, hseed⟩
  simp [rule2WSplitSelectedClosed, hw, hmeets]

/-- Avoiding the `An(Z)` meet empties the closed selected block. -/
theorem rule2WSplitSelectedClosed_eq_false_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (i : Fin S.count) :
    rule2WSplitSelectedClosed model G x z w assignment i = false := by
  simp [rule2WSplitSelectedClosed]
  cases hw : w i with
  | false =>
      simp
  | true =>
      cases hm :
          NodeSet.meetsBool
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (NodeSet.singleton i))
            (rule2WZSideSeed model G x z w assignment) with
      | false =>
          simp
      | true =>
          rcases (NodeSet.meetsBool_eq_true_iff _ _).mp hm with
            ⟨seed, _hanc, hseed⟩
          have hfalse :=
            rule2WZSideSeed_eq_false_of_avoids model G x z w assignment
              havoid seed
          rw [hfalse] at hseed
          cases hseed

/-- A `do(X ∪ Z)`-free ancestor of `W` incident to a `do(X ∪ Z)`-relevant
`An(Y)` latent.  This is the rule-2 analogue of a `Y`-side seed. -/
def rule2WYSideSeed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i &&
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root &&
        model.latent.incident root i)

/-- A `Z`-side seed cannot ancestor an unselected `W` vertex: that
vertex would itself be a descendant of the seed, hence selected. -/
theorem rule2WSplitClosed_no_seed_in_unselected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {seed : Fin S.count}
    (hseed : rule2WZSideSeed model G x z w assignment seed = true)
    (hanc : FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment) seed =
          true) :
    False := by
  have hany :
      (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
        rule2WSplitUnselectedClosed model G x z w assignment target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun k : Fin S.count => k))
            (G.observedDirectedEdge
              (GraphMutilation.bar (NodeSet.union x z)))
            (List.ofFn (fun k : Fin S.count => k)).length seed target) =
        true := by
    simpa [FiniteLatentSCM.ancestralInBar, ObservedGraph.observedAncestorOf]
      using hanc
  rcases List.any_eq_true.mp hany with ⟨t, tMem, ht⟩
  have htParts := Bool.and_eq_true_iff.mp ht
  have hunsel :
      rule2WSplitUnselectedClosed model G x z w assignment t = true :=
    htParts.1
  have hseedT :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (NodeSet.singleton t) seed = true := by
    have hanyT :
        (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
          NodeSet.singleton t target &&
            FiniteReachability.within finBeq
              (List.ofFn (fun k : Fin S.count => k))
              (G.observedDirectedEdge
                (GraphMutilation.bar (NodeSet.union x z)))
              (List.ofFn (fun k : Fin S.count => k)).length seed target) =
          true :=
      List.any_eq_true.mpr
        ⟨t, tMem,
          Bool.and_eq_true_iff.mpr
            ⟨(NodeSet.singleton_eq_true_iff t t).mpr rfl, htParts.2⟩⟩
    simpa [FiniteLatentSCM.ancestralInBar, ObservedGraph.observedAncestorOf]
      using hanyT
  have hwT : w t = true :=
    NodeSet.diff_subset_left w
      (rule2WSplitSelectedClosed model G x z w assignment) t hunsel
  have hsel :
      rule2WSplitSelectedClosed model G x z w assignment t = true := by
    have hmeetsT :
        NodeSet.meetsBool
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (NodeSet.singleton t))
          (rule2WZSideSeed model G x z w assignment) = true :=
      (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨seed, hseedT, hseed⟩
    simp [rule2WSplitSelectedClosed, hwT, hmeetsT]
  have hfalse :
      rule2WSplitUnselectedClosed model G x z w assignment t = false :=
    rule2WSplitClosed_disjoint model G x z w assignment t hsel
  exact Bool.false_ne_true (hfalse.symm.trans hunsel)

/-- The closed unselected slice of `W` observes only latents complementary
to the `do(X)`-relevant `An(Z)` family: a selected latent incident to an
unselected ancestor would be a `Z`-side seed in that ancestral set. -/
theorem agreesOn_rule2WSplitUnselectedClosed_dependsOnNotZ
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn
        (rule2WSplitUnselectedClosed model G x z w assignment) assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
      (rule2WSplitUnselectedClosed model G x z w assignment))
    (rule2WSplitUnselectedClosed model G x z w assignment) assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z)
          (rule2WSplitUnselectedClosed model G x z w assignment)
          assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z)
      (rule2WSplitUnselectedClosed model G x z w assignment)
      (rule2WSplitUnselectedClosed model G x z w assignment)
      (fun _i hi => hi))
    left right
  intro root hrelW
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hrelZ : model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root = true := by
        simpa [selected, rule2Right, Kernel.intervention] using hsel
      rcases (model.latentRelevantUnder_eq_true_iff heavier
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule2WSplitUnselectedClosed model G x z w assignment))
          root).mp (by
            simpa [heavier, rule2Left, Kernel.intervention] using hrelW) with
        ⟨child, hancU, hnone, hinc⟩
      have hancW :
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w child =
            true :=
        FiniteLatentSCM.ancestralInBar_mono G (NodeSet.union x z)
          (NodeSet.diff_subset_left w
            (rule2WSplitSelectedClosed model G x z w assignment))
          hancU
      have hseed :
          rule2WZSideSeed model G x z w assignment child = true := by
        have hfree :
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment child).isNone =
              true := by
          have hact :
              heavier =
                (Kernel.mk NodeSet.empty (NodeSet.union x z)
                  NodeSet.empty).intervention assignment := by
            funext i
            simp [heavier, rule2Left, Kernel.intervention]
          have : heavier child = none := hnone
          rw [hact] at this
          exact Option.isNone_iff_eq_none.mpr this
        have hincZ :
            finAny model.latent.count (fun r =>
              model.latentRelevantUnder
                  ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                    assignment)
                  (FiniteLatentSCM.ancestralInBar G x z) r &&
                model.latent.incident r child) = true :=
          (finAny_eq_true_iff _).mpr ⟨root,
            Bool.and_eq_true_iff.mpr ⟨hrelZ, hinc⟩⟩
        refine Bool.and_eq_true_iff.mpr ⟨?_, hincZ⟩
        exact Bool.and_eq_true_iff.mpr ⟨hancW, hfree⟩
      exact (rule2WSplitClosed_no_seed_in_unselected model G x z w
        assignment hseed hancU).elim

/-- The closed selected slice of `W` observes only latents of its own
ancestors in `G_{\overline{X ∪ Z}}`. -/
theorem agreesOn_rule2WSplitSelectedClosed_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Left x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule2WSplitSelectedClosed model G x z w assignment)))
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitSelectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((rule2Left x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule2Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule2Left, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule2WSplitSelectedClosed model G x z w assignment))
      (rule2WSplitSelectedClosed model G x z w assignment) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
        (NodeSet.union x z)
        (rule2WSplitSelectedClosed model G x z w assignment) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z)
        (rule2WSplitSelectedClosed model G x z w assignment)
        (rule2WSplitSelectedClosed model G x z w assignment)
        (fun _i hi => hi))

/-- The closed unselected slice of `W` observes only latents of its own
ancestors in `G_{\overline{X ∪ Z}}`. -/
theorem agreesOn_rule2WSplitUnselectedClosed_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Left x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule2WSplitUnselectedClosed model G x z w assignment)))
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitUnselectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((rule2Left x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule2Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule2Left, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment))
      (rule2WSplitUnselectedClosed model G x z w assignment) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
        (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment)
        (rule2WSplitUnselectedClosed model G x z w assignment)
        (fun _i hi => hi))

/-- A selected-`W` ancestral latent under `do(X ∪ Z)` that is missing from
`An(Z)` under `do(X)`.  This is the extra-latent gap: the closed selected
block can see coordinates outside the rule-2 `An(Z)` mask. -/
def rule2WSplitSelectedClosedExtraLatent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule2WSplitSelectedClosed model G x z w assignment)) root &&
      !(model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root))

/-- Avoiding the `An(Z)` meet empties the selected block, so it contributes
no extra ancestral latents. -/
theorem rule2WSplitSelectedClosedExtraLatent_eq_false_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false) :
    rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
      false := by
  have hsel :
      rule2WSplitSelectedClosed model G x z w assignment = NodeSet.empty := by
    funext i
    exact rule2WSplitSelectedClosed_eq_false_of_avoids model G x z w
      assignment havoid i
  refine (finAny_eq_false_iff _).mpr ?_
  intro root
  have hrel :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule2WSplitSelectedClosed model G x z w assignment))
          root = false := by
    rw [hsel, FiniteLatentSCM.ancestralInBar_eq_empty]
    exact model.latentRelevantUnder_empty
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      root
  simp [hrel]

/-- When the extra-latent gap is empty, the closed selected slice of `W`
observes only the `do(X)`-relevant `An(Z)` latents. -/
theorem agreesOn_rule2WSplitSelectedClosed_dependsOnZ
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hextra :
      rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
        false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitSelectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((rule2Left x y z w).intervention assignment) roots)) := by
  have hall :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule2WSplitSelectedClosed model G x z w assignment)) root &&
        !(model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root))).mp
      (by simpa [rule2WSplitSelectedClosedExtraLatent] using hextra)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (rule2WSplitSelectedClosed model G x z w assignment))
            root = true ->
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root = true := by
    intro root hr
    have hroot := hall root
    cases hz :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root with
    | true =>
        rfl
    | false =>
        simp [hr, hz] at hroot
  have hinterL :
      (rule2Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule2Left, Kernel.intervention]
  have hinterR :
      (rule2Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment :=
      by
    funext i
    simp [rule2Right, Kernel.intervention]
  simpa [hinterL, hinterR] using
    CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitSelectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment) roots))
      hsub
      (by
        simpa [hinterL] using
          agreesOn_rule2WSplitSelectedClosed_dependsOnAncestral model G
            x y z w assignment)

/-- A `do(X)`-relevant `An(Z)` latent that is also `do(X ∪ Z)`-relevant to
`An(Y)`.  When this is false, `Y` ignores the rule-2 selected mask. -/
def rule2SelectedMeetsYAncestral (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z _w : NodeSet S)
    (assignment : S.Assignment) :
    Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z) root &&
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root)

/-- `Y` under `do(X ∪ Z)` is independent of the selected `An(Z)` latents
once those latents are not relevant to `An(Y)`. -/
theorem agreesOn_rule2Y_dependsOnUnselected_of_avoids_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (havoidY :
      rule2SelectedMeetsYAncestral model G x y z w assignment = false) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) y assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) y y
      (fun _i hi => hi))
    left right
  intro root hrelY
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hmeet :
          rule2SelectedMeetsYAncestral model G x y z w assignment = true := by
        refine (finAny_eq_true_iff _).mpr ⟨root, ?_⟩
        refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
        · simpa [selected, rule2Right, Kernel.intervention] using hsel
        · simpa [heavier, rule2Left, Kernel.intervention] using hrelY
      rw [hmeet] at havoidY
      cases havoidY

/-- When the extra-latent gap is empty and `Y` ignores the selected
`An(Z)` mask, the closed `Z`-side split inhabits the rule-2 partition. -/
def rule2PartitionWitness_of_w_split_closed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hextra :
      rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
        false)
    (havoidY :
      rule2SelectedMeetsYAncestral model G x y z w assignment = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment :=
  rule2PartitionWitness model x y z w
    (rule2WSplitSelectedClosed model G x z w assignment)
    (rule2WSplitUnselectedClosed model G x z w assignment) assignment
    (model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z))
    (rule2WSplitClosed_union model G x z w assignment).symm
    (agreesOn_rule2Z_dependsOnSelected_of_empty_w model G x y z w assignment)
    (agreesOn_rule2WSplitSelectedClosed_dependsOnZ model G x y z w
      assignment hextra)
    (agreesOn_rule2Y_dependsOnUnselected_of_avoids_y model G x y z w
      assignment havoidY)
    (agreesOn_rule2WSplitUnselectedClosed_dependsOnNotZ model G x y z w
      assignment)

/-- A checked latent partition discharges the canonical-product cross-product
obligation. -/
theorem ProductConditionalIndependenceWitnessAt.toCrossProduct
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (witness : ProductConditionalIndependenceWitnessAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model left right assignment := by
  have conditional := productRecord_conditional_independence_cross model
    witness.selected witness.selectedOutcome witness.selectedCondition
    witness.unselectedOutcome witness.unselectedCondition
    witness.selectedOutcomeDepends witness.selectedConditionDepends
    witness.unselectedOutcomeDepends witness.unselectedConditionDepends
  constructor
  unfold productMass
  change QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.conditionEvent assignment))))
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.conditionEvent assignment))))
  rw [witness.leftNumerator, witness.rightCondition,
    witness.rightNumerator, witness.leftCondition]
  exact QProb.equiv_trans (QProb.equiv_symm conditional)
    (QProb.mul_comm _ _)

/-- A latent event factored across a selected/unselected partition of the
independent roots.  Unlike `ProductConditionalIndependenceWitnessAt`, this
does not require the four kernel events to share any of their two factors. -/
structure ProductEventRectangle (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (event : model.latent.Assignment -> Bool) where
  selectedPart : model.latent.Assignment -> Bool
  unselectedPart : model.latent.Assignment -> Bool
  selectedDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedPart
  unselectedDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedPart
  factorization : event = Probability.inter selectedPart unselectedPart

theorem ProductEventRectangle.probVal
    {model : FiniteLatentSCM S}
    {selected : Fin model.latent.count -> Bool}
    {event : model.latent.Assignment -> Bool}
    (rectangle : ProductEventRectangle model selected event) :
    QProb.Equiv ((productRecord model).probVal event)
      (QProb.mul
        ((productRecord model).probVal rectangle.selectedPart)
        ((productRecord model).probVal rectangle.unselectedPart)) := by
  cases rectangle with
  | mk selectedPart unselectedPart selectedDepends unselectedDepends
      factorization =>
      subst event
      exact productRecord_inter_equiv_mul model selected
        selectedPart unselectedPart selectedDepends unselectedDepends

/-- A general rectangular factorization of a kernel cross product.

The selected and unselected factors may differ in all four kernel events.
The two component cross identities are therefore expressive enough for
cross-world intervention arguments such as do-calculus Rule 3, without
imposing a pointwise inclusion between the two conditioning events. -/
structure ProductRectangularCrossProductWitnessAt
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  leftNumerator : ProductEventRectangle model selected
    (productPreimage model left assignment (left.numeratorEvent assignment))
  rightCondition : ProductEventRectangle model selected
    (productPreimage model right assignment (right.conditionEvent assignment))
  rightNumerator : ProductEventRectangle model selected
    (productPreimage model right assignment (right.numeratorEvent assignment))
  leftCondition : ProductEventRectangle model selected
    (productPreimage model left assignment (left.conditionEvent assignment))
  selectedCross : QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal leftNumerator.selectedPart)
      ((productRecord model).probVal rightCondition.selectedPart))
    (QProb.mul
      ((productRecord model).probVal rightNumerator.selectedPart)
      ((productRecord model).probVal leftCondition.selectedPart))
  unselectedCross : QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal leftNumerator.unselectedPart)
      ((productRecord model).probVal rightCondition.unselectedPart))
    (QProb.mul
      ((productRecord model).probVal rightNumerator.unselectedPart)
      ((productRecord model).probVal leftCondition.unselectedPart))

/--
Assemble a rectangular cross-product from factors shared in the only places
where the cross identity requires them to agree.

The two numerator events have the same selected-coordinate factor, and the
two conditioning events have the same selected-coordinate factor.  Their
unselected factors may differ between the left and right interventions.  The
selected cross identity is therefore reflexive, while the unselected identity
is commutativity of multiplication.

This shape is strictly more general than putting an entire conditioning
cylinder on the unselected side.  In particular, a rule-3 conditioner `W`
may legitimately share latent roots with `Y`: that common part belongs in
`selectedCondition`, while only the intervention-sensitive residuals need to
lie on the complementary coordinates.
-/
def ProductRectangularCrossProductWitnessAt.of_shared_factors
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (selectedNumerator selectedCondition leftResidual rightResidual :
      model.latent.Assignment -> Bool)
    (selectedNumeratorDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedNumerator)
    (selectedConditionDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedCondition)
    (leftResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected leftResidual)
    (rightResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected rightResidual)
    (leftNumerator :
      productPreimage model left assignment (left.numeratorEvent assignment) =
        Probability.inter selectedNumerator leftResidual)
    (rightCondition :
      productPreimage model right assignment (right.conditionEvent assignment) =
        Probability.inter selectedCondition rightResidual)
    (rightNumerator :
      productPreimage model right assignment
          (right.numeratorEvent assignment) =
        Probability.inter selectedNumerator rightResidual)
    (leftCondition :
      productPreimage model left assignment (left.conditionEvent assignment) =
        Probability.inter selectedCondition leftResidual) :
    ProductRectangularCrossProductWitnessAt model left right assignment where
  selected := selected
  leftNumerator :=
    { selectedPart := selectedNumerator
      unselectedPart := leftResidual
      selectedDepends := selectedNumeratorDepends
      unselectedDepends := leftResidualDepends
      factorization := leftNumerator }
  rightCondition :=
    { selectedPart := selectedCondition
      unselectedPart := rightResidual
      selectedDepends := selectedConditionDepends
      unselectedDepends := rightResidualDepends
      factorization := rightCondition }
  rightNumerator :=
    { selectedPart := selectedNumerator
      unselectedPart := rightResidual
      selectedDepends := selectedNumeratorDepends
      unselectedDepends := rightResidualDepends
      factorization := rightNumerator }
  leftCondition :=
    { selectedPart := selectedCondition
      unselectedPart := leftResidual
      selectedDepends := selectedConditionDepends
      unselectedDepends := leftResidualDepends
      factorization := leftCondition }
  selectedCross := QProb.equiv_refl _
  unselectedCross := QProb.mul_comm _ _

/-- Componentwise rectangular cross identities imply the kernel-level
canonical-product cross identity. -/
theorem ProductRectangularCrossProductWitnessAt.toCrossProduct
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (witness : ProductRectangularCrossProductWitnessAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model left right assignment := by
  have leftNumeratorFactor := witness.leftNumerator.probVal
  have rightConditionFactor := witness.rightCondition.probVal
  have rightNumeratorFactor := witness.rightNumerator.probVal
  have leftConditionFactor := witness.leftCondition.probVal
  constructor
  unfold productMass
  change QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.conditionEvent assignment))))
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.conditionEvent assignment))))
  exact QProb.equiv_trans
    (QProb.mul_congr leftNumeratorFactor rightConditionFactor)
    (QProb.equiv_trans (by
      simp only [QProb.Equiv, QProb.mul]
      ac_rfl)
      (QProb.equiv_trans
        (QProb.mul_congr witness.selectedCross witness.unselectedCross)
        (QProb.equiv_trans (by
          simp only [QProb.Equiv, QProb.mul]
          ac_rfl)
          (QProb.equiv_symm
            (QProb.mul_congr rightNumeratorFactor
              leftConditionFactor)))))

/-- A fully unselected mask makes every event a rectangle with constant
selected factor `true`. -/
def ProductEventRectangle.of_all_unselected (model : FiniteLatentSCM S)
    (event : model.latent.Assignment -> Bool) :
    ProductEventRectangle model (fun _ => false) event where
  selectedPart := fun _ => true
  unselectedPart := event
  selectedDepends :=
    CanonicalFactorization.DependsOnSelected.const _ _ _ true
  unselectedDepends := by
    intro left right agree
    have heq : left = right := funext fun i => agree i rfl
    subst heq
    rfl
  factorization := by
    funext roots
    simp [Probability.inter]

/-- Identical kernels have a rectangular cross-product: both sides share
the same numerator and condition, and a fully unselected mask makes the
two cross identities reflexive. -/
def ProductRectangularCrossProductWitnessAt.of_kernel_eq
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) (heq : left = right) :
    ProductRectangularCrossProductWitnessAt model left right assignment := by
  subst heq
  exact
    { selected := fun _ => false
      leftNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.numeratorEvent assignment))
      rightCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.conditionEvent assignment))
      rightNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.numeratorEvent assignment))
      leftCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.conditionEvent assignment))
      selectedCross := QProb.equiv_refl _
      unselectedCross := QProb.equiv_refl _ }

/-- Identical kernels also inhabit the stronger CI shape: the selected
factors are constantly true, the unselected factors are the shared
numerator and condition, and `P(Y, W)` already implies `W`. -/
def ProductConditionalIndependenceWitnessAt.of_kernel_eq
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) (heq : left = right) :
    ProductConditionalIndependenceWitnessAt model left right assignment := by
  subst heq
  let num :=
    productPreimage model left assignment (left.numeratorEvent assignment)
  let cond :=
    productPreimage model left assignment (left.conditionEvent assignment)
  let numRect := ProductEventRectangle.of_all_unselected model num
  let condRect := ProductEventRectangle.of_all_unselected model cond
  refine
    { selected := fun _ => false
      selectedOutcome := fun _ => true
      selectedCondition := fun _ => true
      unselectedOutcome := num
      unselectedCondition := cond
      selectedOutcomeDepends :=
        CanonicalFactorization.DependsOnSelected.const _ _ _ true
      selectedConditionDepends :=
        CanonicalFactorization.DependsOnSelected.const _ _ _ true
      unselectedOutcomeDepends := numRect.unselectedDepends
      unselectedConditionDepends := condRect.unselectedDepends
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · funext roots
    simp [num, cond, productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter]
  · funext roots
    simp [cond, productPreimage, Probability.inter]
  · funext roots
    simp [num, cond, productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter]
  · funext roots
    simp [cond, productPreimage, Probability.inter]

/-- Empty `Z` makes rule 1 an identity of kernels.  The side condition
`Y ⊥ ∅ | X ∪ W` in `G_{\overline{X}}` is vacuous. -/
def rule1PartitionWitness_of_empty_z
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hz : NodeSet.isEmpty z = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment :=
  ProductConditionalIndependenceWitnessAt.of_kernel_eq model
    (rule1Left x y z w) (rule1Right x y z w) assignment
    (rule1Left_eq_rule1Right_of_empty_z x y z w hz)

/-- Empty `Z` makes rule 2 an identity of kernels, oriented as the
partition witness `(right, left)`. -/
def rule2PartitionWitness_of_empty_z
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hz : NodeSet.isEmpty z = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment :=
  ProductConditionalIndependenceWitnessAt.of_kernel_eq model
    (rule2Right x y z w) (rule2Left x y z w) assignment
    (rule2Left_eq_rule2Right_of_empty_z x y z w hz).symm

/--
Rule 2 from path d-separation.  Empty `Z` is a kernel identity; empty
`W` or a `W` that misses `An(Z)` uses the one-sided witnesses.  If `W`
meets `An(Z)`, the closed split still factorizes once the extra-latent
gap is empty and `Y` ignores the selected `An(Z)` mask.
-/
def rule2PartitionWitness_of_path
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    (hextra :
      rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
        false)
    (havoidY :
      rule2SelectedMeetsYAncestral model G x y z w assignment = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  cases hz : NodeSet.isEmpty z with
  | true =>
      exact rule2PartitionWitness_of_empty_z model x y z w assignment hz
  | false =>
      cases hw : NodeSet.isEmpty w with
      | true =>
          exact rule2PartitionWitness_of_empty_w model G projected
            x y z w assignment separated hw
      | false =>
          cases havoid :
              rule2WMeetsZAncestral model G x z w assignment with
          | false =>
              exact rule2PartitionWitness_of_w_avoids_z model G projected
                x y z w assignment disjoint havoid separated
          | true =>
              exact rule2PartitionWitness_of_w_split_closed model G
                x y z w assignment hextra havoidY

/-- Empty `Z` makes rule 3 an identity of kernels. -/
def rule3RectangularWitness_of_empty_z
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hz : NodeSet.isEmpty z = true) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  ProductRectangularCrossProductWitnessAt.of_kernel_eq model
    (rule3Left x y z w) (rule3Right x y z w) assignment
    (rule3Left_eq_rule3Right_of_empty_z x y z w hz)

/-- When `Z(W) = Z`, `Y` is evaluated the same under `do(X)` and
`do(X ∪ Z)`, because d-separation in `G_{\overline{X ∪ Z}}` forbids `Z`
from ancestoring `Y`. -/
theorem agreesOn_rule3Y_eq_of_z_avoids_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases hy : y child with
  | false =>
      rfl
  | true =>
      have hanc :
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y child =
            true :=
        FiniteLatentSCM.observedAncestorOf_self G
          (GraphMutilation.bar (NodeSet.union x z)) y hy
      have hclosed :=
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment
      have hagree :
          forall i, FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y i =
              true ->
            ((rule3Left x y z w).intervention assignment i) =
              ((rule3Right x y z w).intervention assignment i) := by
        intro i hi
        have hz : z i = false := by
          cases hzi : z i with
          | false =>
              rfl
          | true =>
              have hfalse :=
                FiniteLatentSCM.rule3_z_not_ancestral_of_z_avoids_w G x y z w
                  disjoint hrem separated hzi
              simpa [FiniteLatentSCM.ancestralInBar] using
                (hfalse.symm.trans hi)
        have hinterL :
            (rule3Left x y z w).intervention assignment i =
              (if NodeSet.union x z i then some (assignment i)
                else none) := by
          simp [rule3Left, Kernel.intervention]
        have hinterR :
            (rule3Right x y z w).intervention assignment i =
              (if x i then some (assignment i) else none) := by
          simp [rule3Right, Kernel.intervention]
        have hxZ : NodeSet.union x z i = x i := by
          simp [NodeSet.union, hz]
        simp [hinterL, hinterR, hxZ]
      have heval :=
        FiniteLatentSCM.evalUnder_eq_on_of_intervention_agree_on_closed
          model
          ((rule3Left x y z w).intervention assignment)
          ((rule3Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y)
          roots hclosed hagree child hanc
      simp [heval]

theorem agreesOn_rule3Y_eq_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) :=
  agreesOn_rule3Y_eq_of_z_avoids_w model G x y z w assignment disjoint
    (ObservedGraph.nonAncestorsOf_of_isEmpty G (GraphMutilation.bar x) z w hw)
    separated roots

/--
A cylinder is invariant under adding `do(Z)` whenever no `Z` vertex reaches
its nodes in `G_{\overline{X ∪ Z}}`.

The ancestral set is backward-closed for the heavier intervention.  On that
set the two interventions agree, because a selected `Z` coordinate would
contradict the supplied non-ancestry fact.  This lemma is stated independently
of rule 3 so a future common block of `W` can use it directly.
-/
theorem agreesOn_evalUnder_bar_union_eq_of_z_not_ancestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z nodes : NodeSet S) (assignment : S.Assignment)
    (zAvoids : forall i, z i = true ->
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes i = false)
    (roots : model.latent.Assignment) :
    Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment) roots) =
      Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          roots) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases hnodes : nodes child with
  | false =>
      rfl
  | true =>
      have hanc :
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes child =
            true :=
        FiniteLatentSCM.observedAncestorOf_self G
          (GraphMutilation.bar (NodeSet.union x z)) nodes hnodes
      have hclosed :=
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) nodes assignment
      have hagree :
          forall i,
            FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes i =
                true ->
              ((Kernel.mk NodeSet.empty (NodeSet.union x z)
                NodeSet.empty).intervention assignment i) =
                ((Kernel.mk NodeSet.empty x
                  NodeSet.empty).intervention assignment i) := by
        intro i hi
        have hz : z i = false := by
          cases hzi : z i with
          | false =>
              rfl
          | true =>
              have hfalse := zAvoids i hzi
              rw [hi] at hfalse
              contradiction
        have hinterL :
            (Kernel.mk NodeSet.empty (NodeSet.union x z)
                NodeSet.empty).intervention assignment i =
              (if NodeSet.union x z i then some (assignment i)
                else none) := by
          simp [Kernel.intervention]
        have hinterR :
            (Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment i =
              (if x i then some (assignment i) else none) := by
          simp [Kernel.intervention]
        have hxZ : NodeSet.union x z i = x i := by
          simp [NodeSet.union, hz]
        simp [hinterL, hinterR, hxZ]
      have heval :=
        FiniteLatentSCM.evalUnder_eq_on_of_intervention_agree_on_closed
          model
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes)
          roots hclosed hagree child hanc
      simp [heval]

/--
The conditioned `W` vertices that can be reached from `Z` in
`G_{\overline{X ∪ Z}}`.  These are exactly the vertices whose agreement
cylinder may change when `do(Z)` is added; they form the residual block of the
rule-3 node split.
-/
def rule3WInterventionSensitive (G : ObservedGraph S)
    (x z w : NodeSet S) : NodeSet S :=
  fun child =>
    w child &&
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (NodeSet.singleton child)) z

/-- The complementary `W` block is pointwise invariant under adding
`do(Z)`. -/
def rule3WInterventionInvariant (G : ObservedGraph S)
    (x z w : NodeSet S) : NodeSet S :=
  NodeSet.diff w (rule3WInterventionSensitive G x z w)

/--
Latent coordinates used by the common side of the rule-3 factorization: the
ancestors of `Y` after fixing `X ∪ W`, together with the ancestors of the
intervention-invariant `W` block under `do(X ∪ Z)`.
-/
def rule3YInvariantLatentMask (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) : Fin model.latent.count -> Bool :=
  fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root ||
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule3WInterventionInvariant G x z w)) root

theorem rule3WInterventionSensitive_subset_w (G : ObservedGraph S)
    (x z w : NodeSet S) :
    NodeSet.Subset (rule3WInterventionSensitive G x z w) w := by
  intro child selected
  exact (Bool.and_eq_true_iff.mp selected).1

/-- The invariant and sensitive blocks are disjoint by construction. -/
theorem rule3WInterventionSplit_disjoint (G : ObservedGraph S)
    (x z w : NodeSet S) :
    NodeSet.Disjoint (rule3WInterventionInvariant G x z w)
      (rule3WInterventionSensitive G x z w) :=
  NodeSet.Disjoint.diff_right w (rule3WInterventionSensitive G x z w)

/-- The invariant and sensitive blocks cover all conditioned vertices. -/
theorem rule3WInterventionSplit_union (G : ObservedGraph S)
    (x z w : NodeSet S) :
    NodeSet.union (rule3WInterventionInvariant G x z w)
      (rule3WInterventionSensitive G x z w) = w := by
  funext child
  have subset := rule3WInterventionSensitive_subset_w G x z w child
  simp [rule3WInterventionInvariant, NodeSet.union, NodeSet.diff]
  cases hw : w child with
  | false =>
      cases hs : rule3WInterventionSensitive G x z w child with
      | false => simp
      | true => exact (Bool.false_ne_true (hw.symm.trans (subset hs))).elim
  | true =>
      cases hs : rule3WInterventionSensitive G x z w child <;> simp

/-- No `Z` vertex ancestors the invariant block: any such walk would make
its endpoint intervention-sensitive by definition. -/
theorem rule3_z_not_ancestral_invariant_w
    (G : ObservedGraph S) (x z w : NodeSet S)
    {source : Fin S.count} (sourceInZ : z source = true) :
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
      (rule3WInterventionInvariant G x z w) source = false := by
  cases hanc :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule3WInterventionInvariant G x z w) source with
  | false => rfl
  | true =>
      rcases (G.observedAncestorOf_eq_true_iff
          (GraphMutilation.bar (NodeSet.union x z))
          (rule3WInterventionInvariant G x z w) source).mp hanc with
        ⟨target, targetInvariant, walk⟩
      have targetInW : w target = true :=
        NodeSet.diff_subset_left w
          (rule3WInterventionSensitive G x z w) target targetInvariant
      have targetNotSensitive :
          rule3WInterventionSensitive G x z w target = false := by
        have disjoint := rule3WInterventionSplit_disjoint G x z w
          target targetInvariant
        exact disjoint
      have sourceAncestorsTarget :
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (NodeSet.singleton target) source = true :=
        (G.observedAncestorOf_eq_true_iff
          (GraphMutilation.bar (NodeSet.union x z))
          (NodeSet.singleton target) source).mpr
          ⟨target, (NodeSet.singleton_eq_true_iff target target).mpr rfl,
            walk⟩
      have meetsZ :
          NodeSet.meetsBool
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (NodeSet.singleton target)) z = true :=
        (NodeSet.meetsBool_eq_true_iff _ _).mpr
          ⟨source, sourceAncestorsTarget, sourceInZ⟩
      have targetSensitive :
          rule3WInterventionSensitive G x z w target = true :=
        Bool.and_eq_true_iff.mpr ⟨targetInW, meetsZ⟩
      rw [targetSensitive] at targetNotSensitive
      contradiction

/-- The invariant `W` block has the same agreement cylinder under
`do(X ∪ Z)` and `do(X)`. -/
theorem agreesOn_rule3WInterventionInvariant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (roots : model.latent.Assignment) :
    Kernel.agreesOn (rule3WInterventionInvariant G x z w) assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn (rule3WInterventionInvariant G x z w) assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) := by
  have invariant :=
    agreesOn_evalUnder_bar_union_eq_of_z_not_ancestral model G x z
      (rule3WInterventionInvariant G x z w) assignment
      (fun source sourceInZ =>
        rule3_z_not_ancestral_invariant_w G x z w sourceInZ)
      roots
  simpa [rule3Left, rule3Right, Kernel.intervention] using invariant

/-- When no `Z` vertex ancestors `W` in `G_{\overline{X}}`, the `W`
cylinders under `do(X ∪ Z)` and `do(X)` coincide: intervening on `Z`
cannot reach `W`. -/
theorem agreesOn_rule3W_eq_of_z_avoids_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    (roots : model.latent.Assignment) :
    Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) := by
  have invariant :=
    agreesOn_evalUnder_bar_union_eq_of_z_not_ancestral model G x z w
      assignment
      (fun i hzi =>
        FiniteLatentSCM.rule3_z_not_ancestral_w_of_z_avoids_w G x z w
          hrem hzi)
      roots
  simpa [rule3Left, rule3Right, Kernel.intervention] using invariant

/-- `Y` under `do(X ∪ W ∪ Z)` equals `Y` under `do(X ∪ W)`: d-separation
in the rule-3 side graph forbids `Z` from ancestoring `Y` after incoming
arrows to `W` are cut. -/
theorem agreesOn_rule3Y_eq_of_union_xw
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty
            (NodeSet.union (NodeSet.union x w) z)
            NodeSet.empty).intervention assignment) roots) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases hy : y child with
  | false =>
      rfl
  | true =>
      have hanc :
          FiniteLatentSCM.ancestralInBar G
            (NodeSet.union (NodeSet.union x w) z) y child = true :=
        FiniteLatentSCM.observedAncestorOf_self G
          (GraphMutilation.bar (NodeSet.union (NodeSet.union x w) z)) y hy
      have hclosed :=
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union (NodeSet.union x w) z) y assignment
      have hagree :
          forall i,
            FiniteLatentSCM.ancestralInBar G
                (NodeSet.union (NodeSet.union x w) z) y i = true ->
              ((Kernel.mk NodeSet.empty
                  (NodeSet.union (NodeSet.union x w) z)
                  NodeSet.empty).intervention assignment i) =
                ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                  NodeSet.empty).intervention assignment i) := by
        intro i hi
        have hz : z i = false := by
          cases hzi : z i with
          | false =>
              rfl
          | true =>
              have hfalse :=
                FiniteLatentSCM.rule3_z_not_ancestral_of_union_xw G x y z w
                  disjoint separated hzi
              simpa [FiniteLatentSCM.ancestralInBar] using
                (hfalse.symm.trans hi)
        have hinterL :
            (Kernel.mk NodeSet.empty
                (NodeSet.union (NodeSet.union x w) z)
                NodeSet.empty).intervention assignment i =
              (if NodeSet.union (NodeSet.union x w) z i
                then some (assignment i) else none) := by
          simp [Kernel.intervention]
        have hinterR :
            (Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment i =
              (if NodeSet.union x w i then some (assignment i)
                else none) := by
          simp [Kernel.intervention]
        have hxZ : NodeSet.union (NodeSet.union x w) z i =
            NodeSet.union x w i := by
          simp [NodeSet.union, hz]
        simp [hinterL, hinterR, hxZ]
      have heval :=
        FiniteLatentSCM.evalUnder_eq_on_of_intervention_agree_on_closed
          model
          ((Kernel.mk NodeSet.empty
            (NodeSet.union (NodeSet.union x w) z)
            NodeSet.empty).intervention assignment)
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G
            (NodeSet.union (NodeSet.union x w) z) y)
          roots hclosed hagree child hanc
      simp [heval]

/-- Rule-3 left numerator `Y ∧ W` under `do(X ∪ Z)` rewrites as the `W`
cylinder times `Y` under `do(X ∪ Z ∪ W)`. -/
theorem agreesOn_rule3Left_evalUnder_union_eq
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (roots : model.latent.Assignment) :
    (Kernel.agreesOn y assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots)) =
      (Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty
            (NodeSet.union (NodeSet.union x z) w)
            NodeSet.empty).intervention assignment) roots)) := by
  have hinter :
      (rule3Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule3Left, Kernel.intervention]
  rw [hinter]
  conv =>
    lhs
    rw [Bool.and_comm]
  exact agreesOn_and_evalUnder_union_eq model (NodeSet.union x z) w y
    assignment roots

/-- Rule-3 right numerator `Y ∧ W` under `do(X)` rewrites as the `W`
cylinder times `Y` under `do(X ∪ W)`. -/
theorem agreesOn_rule3Right_evalUnder_union_eq
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (roots : model.latent.Assignment) :
    (Kernel.agreesOn y assignment
        (model.evalUnder ((rule3Right x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Right x y z w).intervention assignment)
          roots)) =
      (Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Right x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots)) := by
  have hinter :
      (rule3Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment := by
    funext i
    simp [rule3Right, Kernel.intervention]
  rw [hinter]
  conv =>
    lhs
    rw [Bool.and_comm]
  exact agreesOn_and_evalUnder_union_eq model x w y assignment roots

/-- Combined given-`W` rewrite of the rule-3 left numerator onto
`Y` under `do(X ∪ W)`. -/
theorem agreesOn_rule3Left_numerator_eq_given_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    (Kernel.agreesOn y assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots)) =
      (Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots)) := by
  have hunion :
      NodeSet.union (NodeSet.union x z) w =
        NodeSet.union (NodeSet.union x w) z := by
    rw [NodeSet.union_assoc, NodeSet.union_comm z w, ← NodeSet.union_assoc]
  rw [agreesOn_rule3Left_evalUnder_union_eq]
  rw [hunion]
  have hy :=
    agreesOn_rule3Y_eq_of_union_xw model G x y z w assignment disjoint
      separated roots
  rw [hy]

/-- A `do(X ∪ W)`-relevant ancestor of `Y` that is also relevant to `W`
under `do(X ∪ Z)` or `do(X)`.  When this is false, the given-`W` cylinders
factor across the `Y` mask. -/
def rule3YWLatentOverlap (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
      (model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root ||
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x w) root))

/-- Empty `W` has no ancestral latents, so it cannot overlap the `Y` mask. -/
theorem rule3YWLatentOverlap_eq_false_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true) :
    rule3YWLatentOverlap model G x y z w assignment = false := by
  have hw' : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  subst hw'
  refine (finAny_eq_false_iff _).mpr fun root => ?_
  have hL :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            NodeSet.empty) root = false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      FiniteLatentSCM.latentRelevantUnder_empty model
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment) root
  have hR :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x NodeSet.empty) root =
            false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      FiniteLatentSCM.latentRelevantUnder_empty model
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment) root
  simp [hL, hR]

/-- Empty `Y` has no ancestral latents, so the given-`W` overlap is false. -/
theorem rule3YWLatentOverlap_eq_false_of_empty_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hy : NodeSet.isEmpty y = true) :
    rule3YWLatentOverlap model G x y z w assignment = false := by
  have hy' : y = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hy
  subst hy'
  refine (finAny_eq_false_iff _).mpr fun root => ?_
  have hY :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w)
            NodeSet.empty) root = false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      FiniteLatentSCM.latentRelevantUnder_empty model
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment) root
  simp [hY]

theorem rule3YWLatentSeparatedAcross_left_of_overlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    model.LatentSeparatedAcross
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) := by
  intro root hyRel
  have hall := (finAny_eq_false_iff _).mp hoverlap root
  cases hL :
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root with
  | false =>
      rfl
  | true =>
      simp [hyRel, hL] at hall

theorem rule3YWLatentSeparatedAcross_right_of_overlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    model.LatentSeparatedAcross
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x w) := by
  intro root hyRel
  have hall := (finAny_eq_false_iff _).mp hoverlap root
  cases hR :
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x w) root with
  | false =>
      rfl
  | true =>
      simp [hyRel, hR] at hall

/--
The factorization actually needed by the nontrivial given-`W` case of rule 3.

After conditioning is rewritten as intervention on `W`, the `Y` cylinder is
the same on both sides by the rule-3 path condition.  The two original `W`
cylinders may nevertheless share latent roots with that common `Y` cylinder.
Such shared dependence is represented by `commonCondition`, while the parts
of `W` that differ between `do(X ∪ Z)` and `do(X)` are kept in the two
residual events on unselected roots.

Unlike `rule3YWLatentOverlap = false`, this interface does not demand that
`Y` and `W` be independent.  It records only the common/residual decomposition
needed for cancellation in the conditional cross product.
-/
structure Rule3GivenWFactorization
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  commonCondition : model.latent.Assignment -> Bool
  leftResidual : model.latent.Assignment -> Bool
  rightResidual : model.latent.Assignment -> Bool
  yDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected
    (fun roots =>
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots))
  commonConditionDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected commonCondition
  leftResidualDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected leftResidual
  rightResidualDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected rightResidual
  leftCondition :
    productPreimage model (rule3Left x y z w) assignment
        ((rule3Left x y z w).conditionEvent assignment) =
      Probability.inter commonCondition leftResidual
  rightCondition :
    productPreimage model (rule3Right x y z w) assignment
        ((rule3Right x y z w).conditionEvent assignment) =
      Probability.inter commonCondition rightResidual

/--
Build the rule-3 common/residual event factorization from an actual split of
the conditioned vertices.

The `common` block may depend on the same selected latent roots as `Y`, but
its agreement cylinder must be unchanged by adding the `Z` intervention.
The complementary `residual` block may have different cylinders on the two
sides, provided both depend only on unselected roots.  This is the graph-level
shape expected from a moral separator: dependence shared by `Y` and `W` is
retained and cancelled, rather than incorrectly ruled out.
-/
def Rule3GivenWFactorization.of_node_split
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (common residual : NodeSet S)
    (covers : NodeSet.union common residual = w)
    (commonInvariant : forall roots,
      Kernel.agreesOn common assignment
          (model.evalUnder
            ((rule3Left x y z w).intervention assignment) roots) =
        Kernel.agreesOn common assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots))
    (yDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)))
    (commonDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn common assignment
          (model.evalUnder
            ((rule3Left x y z w).intervention assignment) roots)))
    (leftResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn residual assignment
          (model.evalUnder
            ((rule3Left x y z w).intervention assignment) roots)))
    (rightResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn residual assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots))) :
    Rule3GivenWFactorization model G x y z w assignment where
  selected := selected
  commonCondition := fun roots =>
    Kernel.agreesOn common assignment
      (model.evalUnder
        ((rule3Left x y z w).intervention assignment) roots)
  leftResidual := fun roots =>
    Kernel.agreesOn residual assignment
      (model.evalUnder
        ((rule3Left x y z w).intervention assignment) roots)
  rightResidual := fun roots =>
    Kernel.agreesOn residual assignment
      (model.evalUnder
        ((rule3Right x y z w).intervention assignment) roots)
  yDepends := yDepends
  commonConditionDepends := commonDepends
  leftResidualDepends := leftResidualDepends
  rightResidualDepends := rightResidualDepends
  leftCondition := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter]
    rw [show (rule3Left x y z w).condition = w from rfl]
    have split := congrArg
      (fun nodes => Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots)) covers
    have split' :
        Kernel.agreesOn (NodeSet.union common residual) assignment
            (model.evalUnder
              ((rule3Left x y z w).intervention assignment) roots) =
          Kernel.agreesOn w assignment
            (model.evalUnder
              ((rule3Left x y z w).intervention assignment) roots) := by
      simpa using split
    rw [← split', Kernel.agreesOn_union]
  rightCondition := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter]
    rw [show (rule3Right x y z w).condition = w from rfl]
    have split := congrArg
      (fun nodes => Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots)) covers
    have split' :
        Kernel.agreesOn (NodeSet.union common residual) assignment
            (model.evalUnder
              ((rule3Right x y z w).intervention assignment) roots) =
          Kernel.agreesOn w assignment
            (model.evalUnder
              ((rule3Right x y z w).intervention assignment) roots) := by
      simpa using split
    rw [← split', Kernel.agreesOn_union, ← commonInvariant roots]

/--
Instantiate the rule-3 node split with the part of `W` that is pointwise
invariant under adding `do(Z)` and its intervention-sensitive complement.

The selected latent mask contains every coordinate needed by `Y` under
`do(X ∪ W)` and by the invariant `W` cylinder under `do(X ∪ Z)`.
Consequently all dependency and intervention-invariance fields of
`Rule3GivenWFactorization` are automatic.  The only remaining hypotheses say
that the sensitive `W` cylinder, under each of its two interventions, avoids
that selected mask.

These two avoidance statements are deliberately explicit.  They are valid
in an important rule-3 subcase, but path d-separation alone need not put *all*
intervention-invariant `W` vertices on the `Y` side of the moral separator.
The fully general construction must refine the invariant block by moral side
rather than silently treating these hypotheses as universal consequences.
-/
def Rule3GivenWFactorization.of_intervention_split
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (leftResidualAvoids : forall root,
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule3WInterventionSensitive G x z w)) root = true ->
        rule3YInvariantLatentMask model G x y z w assignment root = false)
    (rightResidualAvoids : forall root,
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule3WInterventionSensitive G x z w)) root = true ->
        rule3YInvariantLatentMask model G x y z w assignment root = false) :
    Rule3GivenWFactorization model G x y z w assignment := by
  let yInt :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let leftInt :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z)
      NodeSet.empty).intervention assignment
  let rightInt :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  let yRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  let common := rule3WInterventionInvariant G x z w
  let residual := rule3WInterventionSensitive G x z w
  let commonRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) common
  let leftResidualRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) residual
  let rightResidualRelevant :=
    FiniteLatentSCM.ancestralInBar G x residual
  let selected := rule3YInvariantLatentMask model G x y z w assignment
  have yDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder yInt yRelevant)
      (selected' := selected)
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) ?_ ?_
    · intro root relevantRoot
      simp [selected, rule3YInvariantLatentMask, yInt, yRelevant,
        relevantRoot]
    · exact agreesOn_evalUnder_dependsOnSelected model yInt yRelevant y
        assignment
        (by
          dsimp [yInt, yRelevant]
          exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
            model G (NodeSet.union x w) y assignment)
        (by
          dsimp [yRelevant]
          exact FiniteLatentSCM.ancestralInBar_contains_targets G
            (NodeSet.union x w) y)
  have commonDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn common assignment
        (model.evalUnder leftInt roots)) := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder leftInt commonRelevant)
      (selected' := selected)
      (fun roots => Kernel.agreesOn common assignment
        (model.evalUnder leftInt roots)) ?_ ?_
    · intro root relevantRoot
      simp [selected, rule3YInvariantLatentMask, leftInt, common,
        commonRelevant, relevantRoot]
    · exact agreesOn_evalUnder_dependsOnSelected model leftInt
        commonRelevant common assignment
        (by
          dsimp [leftInt, commonRelevant, common]
          exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
            model G (NodeSet.union x z)
              (rule3WInterventionInvariant G x z w) assignment)
        (by
          dsimp [commonRelevant, common]
          exact FiniteLatentSCM.ancestralInBar_contains_targets G
            (NodeSet.union x z)
              (rule3WInterventionInvariant G x z w))
  have leftResidualDepends :
      CanonicalFactorization.DependsOnUnselected
        model.latent.count model.latent.Value selected
        (fun roots => Kernel.agreesOn residual assignment
          (model.evalUnder leftInt roots)) :=
    agreesOn_evalUnder_dependsOnUnselected_of_relevance_avoids model
      selected leftInt leftResidualRelevant residual assignment
      (by
        dsimp [leftInt, leftResidualRelevant, residual]
        exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
          model G (NodeSet.union x z)
            (rule3WInterventionSensitive G x z w) assignment)
      (by
        dsimp [leftResidualRelevant, residual]
        exact FiniteLatentSCM.ancestralInBar_contains_targets G
          (NodeSet.union x z)
            (rule3WInterventionSensitive G x z w))
      (by
        intro root relevantRoot
        exact leftResidualAvoids root (by
          simpa [leftInt, leftResidualRelevant, residual] using relevantRoot))
  have rightResidualDepends :
      CanonicalFactorization.DependsOnUnselected
        model.latent.count model.latent.Value selected
        (fun roots => Kernel.agreesOn residual assignment
          (model.evalUnder rightInt roots)) :=
    agreesOn_evalUnder_dependsOnUnselected_of_relevance_avoids model
      selected rightInt rightResidualRelevant residual assignment
      (by
        dsimp [rightInt, rightResidualRelevant, residual]
        exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
          model G x (rule3WInterventionSensitive G x z w) assignment)
      (by
        dsimp [rightResidualRelevant, residual]
        exact FiniteLatentSCM.ancestralInBar_contains_targets G x
          (rule3WInterventionSensitive G x z w))
      (by
        intro root relevantRoot
        exact rightResidualAvoids root (by
          simpa [rightInt, rightResidualRelevant, residual]
            using relevantRoot))
  apply Rule3GivenWFactorization.of_node_split model G x y z w assignment
    selected common residual
    (by
      dsimp [common, residual]
      exact rule3WInterventionSplit_union G x z w)
    (by
      intro roots
      dsimp [common]
      exact agreesOn_rule3WInterventionInvariant model G x y z w assignment
        roots)
  · simpa [yInt] using yDepends
  · simpa [leftInt, rule3Left, Kernel.intervention] using commonDepends
  · simpa [leftInt, rule3Left, Kernel.intervention]
      using leftResidualDepends
  · simpa [rightInt, rule3Right, Kernel.intervention]
      using rightResidualDepends

/--
Compile the common/residual `W` decomposition into the rectangular rule-3
cross product.  The proof uses the path condition only to rewrite both
numerators onto the same `Y`-under-`do(X ∪ W)` cylinder; factor independence
then follows from the supplied coordinate dependencies.
-/
def rule3RectangularWitness_of_given_w_factorization
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (factorization : Rule3GivenWFactorization model G x y z w assignment) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment := by
  let yCyl : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment
      (model.evalUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment) roots)
  let leftCondition :=
    productPreimage model (rule3Left x y z w) assignment
      ((rule3Left x y z w).conditionEvent assignment)
  let rightCondition :=
    productPreimage model (rule3Right x y z w) assignment
      ((rule3Right x y z w).conditionEvent assignment)
  have leftConditionFactor :
      leftCondition = Probability.inter factorization.commonCondition
        factorization.leftResidual := by
    simpa [leftCondition] using factorization.leftCondition
  have rightConditionFactor :
      rightCondition = Probability.inter factorization.commonCondition
        factorization.rightResidual := by
    simpa [rightCondition] using factorization.rightCondition
  have leftNumeratorGivenW :
      productPreimage model (rule3Left x y z w) assignment
          ((rule3Left x y z w).numeratorEvent assignment) =
        Probability.inter leftCondition yCyl := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter, leftCondition, yCyl]
    exact agreesOn_rule3Left_numerator_eq_given_w model G x y z w
      assignment disjoint separated roots
  have rightNumeratorGivenW :
      productPreimage model (rule3Right x y z w) assignment
          ((rule3Right x y z w).numeratorEvent assignment) =
        Probability.inter rightCondition yCyl := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter, rightCondition, yCyl]
    exact agreesOn_rule3Right_evalUnder_union_eq model x y z w assignment
      roots
  apply ProductRectangularCrossProductWitnessAt.of_shared_factors model
    (rule3Left x y z w) (rule3Right x y z w) assignment
    factorization.selected
    (Probability.inter yCyl factorization.commonCondition)
    factorization.commonCondition factorization.leftResidual
    factorization.rightResidual
  · exact CanonicalFactorization.DependsOnSelected.inter
      model.latent.count model.latent.Value factorization.selected
      yCyl factorization.commonCondition (by
        simpa [yCyl] using factorization.yDepends)
      factorization.commonConditionDepends
  · exact factorization.commonConditionDepends
  · exact factorization.leftResidualDepends
  · exact factorization.rightResidualDepends
  · rw [leftNumeratorGivenW, leftConditionFactor]
    funext roots
    exact bool_and_rot_left (factorization.commonCondition roots)
      (factorization.leftResidual roots) (yCyl roots)
  · exact rightConditionFactor
  · rw [rightNumeratorGivenW, rightConditionFactor]
    funext roots
    exact bool_and_rot_left (factorization.commonCondition roots)
      (factorization.rightResidual roots) (yCyl roots)
  · exact leftConditionFactor

/--
The earlier no-overlap argument is the degenerate common/residual
factorization whose common `W` factor is `true`.  Keeping it as an explicit
constructor both preserves the useful special case and documents precisely
what the stronger hypothesis buys: every left and right `W` cylinder can be
placed wholly on the coordinates complementary to the `Y` mask.
-/
def Rule3GivenWFactorization.of_no_overlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    Rule3GivenWFactorization model G x y z w assignment := by
  let yInt :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let yMask :=
    model.latentRelevantUnder yInt
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
  let wLeft : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule3Left x y z w).intervention assignment) roots)
  let wRight : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule3Right x y z w).intervention assignment) roots)
  have hinterL :
      (rule3Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule3Left, Kernel.intervention]
  have hinterR :
      (rule3Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment := by
    funext i
    simp [rule3Right, Kernel.intervention]
  have yClosed :=
    FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x w) y assignment
  have yContained :=
    FiniteLatentSCM.ancestralInBar_contains_targets G (NodeSet.union x w) y
  have wContainedL :=
    FiniteLatentSCM.ancestralInBar_contains_targets G (NodeSet.union x z) w
  have wContainedR :=
    FiniteLatentSCM.ancestralInBar_contains_targets G x w
  have wClosedL :=
    FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x z) w assignment
  have wClosedR :=
    FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G x w
      assignment
  have yDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value yMask
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) :=
    agreesOn_evalUnder_dependsOnSelected model yInt
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) y
      assignment yClosed yContained
  have wLeftDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value yMask wLeft := by
    simpa [wLeft, hinterL] using
      agreesOn_evalUnder_dependsOnUnselected_across model yInt
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) w
        assignment wClosedL wContainedL
        (rule3YWLatentSeparatedAcross_left_of_overlap model G x y z w
          assignment hoverlap)
  have wRightDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value yMask wRight := by
    simpa [wRight, hinterR] using
      agreesOn_evalUnder_dependsOnUnselected_across model yInt
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
        (FiniteLatentSCM.ancestralInBar G x w) w assignment wClosedR
        wContainedR
        (rule3YWLatentSeparatedAcross_right_of_overlap model G x y z w
          assignment hoverlap)
  exact
    { selected := yMask
      commonCondition := fun _ => true
      leftResidual := wLeft
      rightResidual := wRight
      yDepends := by simpa [yInt] using yDepends
      commonConditionDepends :=
        CanonicalFactorization.DependsOnSelected.const _ _ _ true
      leftResidualDepends := wLeftDepends
      rightResidualDepends := wRightDepends
      leftCondition := by
        funext roots
        simp [productPreimage, Kernel.conditionEvent, rule3Left, wLeft,
          Probability.inter]
      rightCondition := by
        funext roots
        simp [productPreimage, Kernel.conditionEvent, rule3Right, wRight,
          Probability.inter] }

/-- Given-`W` rule 3: if the `Y` mask under `do(X ∪ W)` shares no latent
with `W` under either kernel intervention, the four events are rectangles
on that mask.  The extra overlap Bool is not a theorem of path
d-separation (`U → Y` and `U → W` remain). -/
def rule3RectangularWitness_of_given_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_given_w_factorization model G x y z w assignment
    disjoint separated
    (Rule3GivenWFactorization.of_no_overlap model G x y z w assignment
      hoverlap)

/-- Empty-outcome rule 3: the `Y` mask is vacant, so given-`W` overlap
is false and the rectangle inhabits. -/
def rule3RectangularWitness_of_empty_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (hy : NodeSet.isEmpty y = true) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_given_w model G x y z w assignment disjoint
    separated
    (rule3YWLatentOverlap_eq_false_of_empty_y model G x y z w assignment
      hy)

/-- When no `Z` vertex ancestors `W` in `G_{\overline{X}}`, and path
d-separation forbids `Z` from ancestoring `Y` in `G_{\overline{X ∪ Z}}`,
the two rule-3 kernels share `Y` and `W` cylinders.  The selected mask is
vacuous: intervening on `Z` is invisible to both families. -/
def rule3RectangularWitness_of_z_avoids_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w)) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment := by
  let yLeft : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment
      (model.evalUnder ((rule3Left x y z w).intervention assignment) roots)
  let wLeft : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule3Left x y z w).intervention assignment) roots)
  have yEq : forall roots,
      yLeft roots =
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots) :=
    fun roots =>
      agreesOn_rule3Y_eq_of_z_avoids_w model G x y z w assignment
        disjoint hrem separated roots
  have wEq : forall roots,
      wLeft roots =
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots) :=
    fun roots =>
      agreesOn_rule3W_eq_of_z_avoids_w model G x y z w assignment hrem roots
  have hnumL :
      productPreimage model (rule3Left x y z w) assignment
          ((rule3Left x y z w).numeratorEvent assignment) =
        fun roots => yLeft roots && wLeft roots := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent, rule3Left]
    simp [yLeft, wLeft, rule3Left]
  have hnumR :
      productPreimage model (rule3Right x y z w) assignment
          ((rule3Right x y z w).numeratorEvent assignment) =
        fun roots => yLeft roots && wLeft roots := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent]
    have hout : (rule3Right x y z w).outcome = y := rfl
    have hcondn : (rule3Right x y z w).condition = w := rfl
    rw [hout, hcondn]
    rw [← yEq roots, ← wEq roots]
  have hcondL :
      productPreimage model (rule3Left x y z w) assignment
          ((rule3Left x y z w).conditionEvent assignment) =
        wLeft := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent, rule3Left]
    simp [wLeft, rule3Left]
  have hcondR :
      productPreimage model (rule3Right x y z w) assignment
          ((rule3Right x y z w).conditionEvent assignment) =
        wLeft := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent]
    have hcondn : (rule3Right x y z w).condition = w := rfl
    rw [hcondn]
    rw [← wEq roots]
  exact
    { selected := fun _ => false
      leftNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Left x y z w) assignment
            ((rule3Left x y z w).numeratorEvent assignment))
      rightCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Right x y z w) assignment
            ((rule3Right x y z w).conditionEvent assignment))
      rightNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Right x y z w) assignment
            ((rule3Right x y z w).numeratorEvent assignment))
      leftCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Left x y z w) assignment
            ((rule3Left x y z w).conditionEvent assignment))
      selectedCross := QProb.equiv_refl _
      unselectedCross := by
        change QProb.Equiv
          (QProb.mul
            ((productRecord model).probVal
              (productPreimage model (rule3Left x y z w)
                assignment
                ((rule3Left x y z w).numeratorEvent assignment)))
            ((productRecord model).probVal
              (productPreimage model (rule3Right x y z w)
                assignment
                ((rule3Right x y z w).conditionEvent assignment))))
          (QProb.mul
            ((productRecord model).probVal
              (productPreimage model (rule3Right x y z w)
                assignment
                ((rule3Right x y z w).numeratorEvent assignment)))
            ((productRecord model).probVal
              (productPreimage model (rule3Left x y z w)
                assignment
                ((rule3Left x y z w).conditionEvent assignment))))
        rw [hnumL, hnumR, hcondL, hcondR]
        exact QProb.equiv_refl _ }

/-- Empty `W` is given-`W` rule 3 with a vacuous overlap: `W` has no
ancestral latents. -/
def rule3RectangularWitness_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w)) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_given_w model G x y z w assignment disjoint
    separated
    (rule3YWLatentOverlap_eq_false_of_empty_w model G x y z w assignment hw)

/--
Rule 3 from path d-separation and the common/residual factorization of its
genuinely cross-interventional case.  Empty `Z`, empty `Y`, empty `W`, and
`Z(W) = Z` retain their direct constructions; only the remaining branch uses
the supplied factorization.
-/
def rule3RectangularWitness_of_path_factorization
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (factorization : Rule3GivenWFactorization model G x y z w assignment) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment := by
  cases hz : NodeSet.isEmpty z with
  | true =>
      exact rule3RectangularWitness_of_empty_z model x y z w assignment hz
  | false =>
      cases hy : NodeSet.isEmpty y with
      | true =>
          exact rule3RectangularWitness_of_empty_y model G x y z w
            assignment disjoint separated hy
      | false =>
          cases hw : NodeSet.isEmpty w with
          | true =>
              exact rule3RectangularWitness_of_empty_w model G x y z w
                assignment disjoint hw separated
          | false =>
              cases hrem :
                  NodeSet.equal
                    (G.nonAncestorsOf (GraphMutilation.bar x) z w) z with
              | true =>
                  exact rule3RectangularWitness_of_z_avoids_w model G
                    x y z w assignment disjoint
                    ((NodeSet.equal_eq_true_iff _ _).mp hrem)
                    separated
              | false =>
                  exact rule3RectangularWitness_of_given_w_factorization
                    model G x y z w assignment disjoint separated
                    factorization

/--
Backward-compatible rule-3 assembler for the stronger no-overlap premise.
The premise is first embedded into the general common/residual
factorization; downstream cross-product algebra no longer relies on the
misleading idea that all valid rule-3 queries must satisfy it.
-/
def rule3RectangularWitness_of_path
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (hoverlap :
      rule3YWLatentOverlap model G x y z w assignment = false) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_path_factorization model G x y z w assignment
    disjoint separated
    (Rule3GivenWFactorization.of_no_overlap model G x y z w assignment
      hoverlap)

theorem ProductCrossProductEquivalentAt.toDistribution
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : ProductCrossProductEquivalentAt
      model left right assignment) :
    CrossProductEquivalentAt model left right assignment := by
  let leftNumerator := left.distribution_probVal_productRecord model assignment
    (left.numeratorEvent assignment)
  let leftDenominator := left.distribution_probVal_productRecord model assignment
    (left.conditionEvent assignment)
  let rightNumerator := right.distribution_probVal_productRecord model assignment
    (right.numeratorEvent assignment)
  let rightDenominator := right.distribution_probVal_productRecord model assignment
    (right.conditionEvent assignment)
  refine ⟨QProb.equiv_trans
    (QProb.mul_congr leftNumerator rightDenominator)
    (QProb.equiv_trans equivalent.cross
      (QProb.equiv_symm
        (QProb.mul_congr rightNumerator leftDenominator)))⟩

/-- A cross-product identity yields equality of both supported partial ratios. -/
noncomputable def CrossProductEquivalentAt.denote
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : CrossProductEquivalentAt model left right assignment)
    (leftSupported : ProbabilityTerm.SupportedAt model (.kernel left) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model (.kernel right) assignment) :
    ProbabilityResult.Equivalent
      (left.denote model assignment) (right.denote model assignment) := by
  let leftNumerator := (left.distribution model assignment).probVal
    (left.numeratorEvent assignment)
  let leftDenominator := (left.distribution model assignment).probVal
    (left.conditionEvent assignment)
  let rightNumerator := (right.distribution model assignment).probVal
    (right.numeratorEvent assignment)
  let rightDenominator := (right.distribution model assignment).probVal
    (right.conditionEvent assignment)
  have leftPositive : 0 < leftDenominator.num := by
    by_cases positive : 0 < leftDenominator.num
    · exact positive
    · change ProbabilityResult.Supported (left.denote model assignment)
        at leftSupported
      simp only [Kernel.denote, leftDenominator,
        ProbabilityResult.divide, dif_neg positive] at leftSupported
      rcases leftSupported with ⟨_, impossible⟩
      cases impossible
  have rightPositive : 0 < rightDenominator.num := by
    by_cases positive : 0 < rightDenominator.num
    · exact positive
    · change ProbabilityResult.Supported (right.denote model assignment)
        at rightSupported
      simp only [Kernel.denote, rightDenominator,
        ProbabilityResult.divide, dif_neg positive] at rightSupported
      rcases rightSupported with ⟨_, impossible⟩
      cases impossible
  simp only [Kernel.denote, leftDenominator, rightDenominator,
    ProbabilityResult.divide,
    dif_pos leftPositive, dif_pos rightPositive]
  exact .value (QProb.div_equiv_of_cross leftPositive rightPositive
    equivalent.cross)

end Kernel

/--
All graph-dependent work for primitive soundness, stated before ratio algebra.
This is the target of the finite global-Markov/do-calculus proof.
-/
structure PathDoRuleCrossProductSoundness (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  crossProduct : forall {left right} (assignment : S.Assignment),
    PathDoRuleApplication G left right ->
      Kernel.CrossProductEquivalentAt model left right assignment

/-- Separate cross-product obligations for the three do-calculus rules. -/
structure PathDoRuleCrossProductLaws (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.CrossProductEquivalentAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.CrossProductEquivalentAt model
      (rule2Left x y z w) (rule2Right x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.CrossProductEquivalentAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment

/-- The three graph-dependent laws reduced to the canonical independent
latent product.  This is the input expected from the finite factor-graph
separation proof. -/
structure PathDoRuleProductCrossProductLaws (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule2Left x y z w) (rule2Right x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment

/-- The remaining graph layer may provide explicit latent partitions rather
than opaque kernel-level mass equalities.  Rules 1 and 2 use the stronger
conditional-independence shape.  Rule 3 uses general rectangular factors,
because its two conditioning cylinders live under different interventions
and need not be pointwise nested.  Rule 2 is oriented in reverse because its
composition proof naturally identifies the observational-action kernel as
the joint side of conditional independence. -/
structure PathDoRulePartitionWitnesses (G : ObservedGraph S)
    (model : FiniteLatentSCM S) where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment
  -- `rule3RectangularWitness_of_path_factorization` cases empty
  -- `Z`/`Y`/`W` and `Z(W) = Z` before using the common/residual `W`
  -- decomposition.  Unlike the older no-overlap leaf, this decomposition
  -- permits the ordinary latent dependence of nonempty `Y` and `W`.
  -- `rule2PartitionWitness_of_path` cases empty `Z`/`W` and the
  -- `An(Z)`-avoiding split before asking for the extra-latent gap and
  -- the mixed `An(Z)`–`An(Y)` meet.

/--
Assemble the three path-do-rule partition witnesses from path d-separation,
a projected graph, the remaining rule-1/rule-2 Bools, and the rule-3
common/residual factorization.

The rule-1/rule-2 Bools and the rule-3 factorization are required only on
queries that survive the cheap empty or one-sided branches inside the local
assemblers.  They are stated uniformly here so this package does not hide a
case split from its caller.
-/
def PathDoRulePartitionWitnesses.ofPathFactorizedRule3
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G)
    (hRule1Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedAncestralLatentsOverlap
        model G x y z w assignment = false)
    (hRule1Unsel : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedUnselectedMeetsZCore
        model G x y z w assignment = false)
    (hRule2Extra : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2WSplitSelectedClosedExtraLatent
        model G x z w assignment = false)
    (hRule2MeetsY : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2SelectedMeetsYAncestral
        model G x y z w assignment = false)
    (hRule3Factorization : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated G
        { removeIncoming :=
            NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
          removeOutgoing := NodeSet.empty }
        y z (NodeSet.union x w) →
      Kernel.Rule3GivenWFactorization model G x y z w assignment) :
    PathDoRulePartitionWitnesses G model where
  rule1 := fun x y z w assignment _disjoint separated =>
    Kernel.rule1PartitionWitness_of_path model G projected
      x y z w assignment separated
      (hRule1Overlap x y z w assignment separated)
      (hRule1Unsel x y z w assignment separated)
  rule2 := fun x y z w assignment disjoint separated =>
    Kernel.rule2PartitionWitness_of_path model G projected
      x y z w assignment disjoint separated
      (hRule2Extra x y z w assignment separated)
      (hRule2MeetsY x y z w assignment separated)
  rule3 := fun x y z w assignment disjoint separated =>
    Kernel.rule3RectangularWitness_of_path_factorization model G
      x y z w assignment disjoint separated
      (hRule3Factorization x y z w assignment separated)

/--
Compatibility assembler for the former rule-3 no-overlap premise.  New
global-Markov work should target `ofPathFactorizedRule3`: path separation
does not in general imply that `Y` and conditioned `W` share no latent root.
-/
def PathDoRulePartitionWitnesses.ofPath
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G)
    (hRule1Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedAncestralLatentsOverlap
        model G x y z w assignment = false)
    (hRule1Unsel : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedUnselectedMeetsZCore
        model G x y z w assignment = false)
    (hRule2Extra : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2WSplitSelectedClosedExtraLatent
        model G x z w assignment = false)
    (hRule2MeetsY : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2SelectedMeetsYAncestral
        model G x y z w assignment = false)
    (hRule3Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated G
        { removeIncoming :=
            NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
          removeOutgoing := NodeSet.empty }
        y z (NodeSet.union x w) →
      Kernel.rule3YWLatentOverlap model G x y z w assignment = false) :
    PathDoRulePartitionWitnesses G model :=
  PathDoRulePartitionWitnesses.ofPathFactorizedRule3 G model projected
    hRule1Overlap hRule1Unsel hRule2Extra hRule2MeetsY
    (fun x y z w assignment separated =>
      Kernel.Rule3GivenWFactorization.of_no_overlap model G x y z w
        assignment (hRule3Overlap x y z w assignment separated))

def PathDoRulePartitionWitnesses.toProductCrossProductLaws
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (witnesses : PathDoRulePartitionWitnesses G model) :
    PathDoRuleProductCrossProductLaws G model where
  rule1 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule1 x y z w assignment disjoint separated).toCrossProduct
  rule2 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule2 x y z w assignment disjoint separated).toCrossProduct.symm
  rule3 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule3 x y z w assignment disjoint separated).toCrossProduct

def PathDoRuleProductCrossProductLaws.toDistributionLaws
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (laws : PathDoRuleProductCrossProductLaws G model) :
    PathDoRuleCrossProductLaws G model where
  rule1 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule1 x y z w assignment disjoint separated).toDistribution
  rule2 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule2 x y z w assignment disjoint separated).toDistribution
  rule3 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule3 x y z w assignment disjoint separated).toDistribution

/-- Package the three independently checkable laws as application soundness. -/
def PathDoRuleCrossProductLaws.toCrossProductSoundness
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (laws : PathDoRuleCrossProductLaws G model) :
    PathDoRuleCrossProductSoundness G model where
  crossProduct := by
    intro left right assignment application
    cases application with
    | rule1 x y z w disjoint sideCondition =>
        exact laws.rule1 x y z w assignment disjoint sideCondition
    | rule2 x y z w disjoint sideCondition =>
        exact laws.rule2 x y z w assignment disjoint sideCondition
    | rule3 x y z w disjoint sideCondition =>
        exact laws.rule3 x y z w assignment disjoint sideCondition

/-- Cross-product do-rule laws supply the semantic do-rule leaf. -/
noncomputable def PathDoRuleCrossProductSoundness.toDoRule
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (sound : PathDoRuleCrossProductSoundness G model)
    {left right : Kernel S} (assignment : S.Assignment)
    (application : PathDoRuleApplication G left right)
    (_leftSupported : ProbabilityTerm.SupportedAt model (.kernel left) assignment)
    (_rightSupported : ProbabilityTerm.SupportedAt model (.kernel right) assignment) :
    ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
      assignment := by
  simpa only [ProbabilityTerm.denote] using
    (sound.crossProduct assignment application).denote
      _leftSupported _rightSupported

/-- Assemble all primitive laws once the graph-dependent do-rule leaf is supplied. -/
noncomputable def PathPrimitiveSoundness.ofDoRule
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (doRuleSound : ∀ {left right} (assignment : S.Assignment),
      PathDoRuleApplication G left right ->
        ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
        ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
        ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
          assignment) :
    PathPrimitiveSoundness G model where
  doRule := doRuleSound
  marginalization := by
    intro x y z w assignment disjoint leftSupported rightSupported
    exact ProbabilityTerm.marginalization_soundAt model x y z w assignment
      disjoint leftSupported rightSupported
  conditioning := by
    intro x y z w assignment _ leftSupported rightSupported
    exact ProbabilityTerm.conditioning_soundAt model x y z w assignment
      leftSupported rightSupported
  chain := by
    intro x y z w assignment _ leftSupported rightSupported
    exact ProbabilityTerm.chain_soundAt model x y z w assignment
      leftSupported rightSupported

/-- Compile path-based primitive semantics to executable rule syntax using the
proved algorithm-to-path implication.  The converse (path to algorithm) is
inhabited as `ObservedGraph.dSeparationCorrectness` and is used by
`PublishedSoundness`, not by semantic soundness of an executable derivation.
-/
def PathPrimitiveSoundness.compileChecked
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (semantics : PathPrimitiveSoundness G model) :
    LocalPrimitiveSoundness G model where
  doRule := by
    intro left right assignment application leftSupported rightSupported
    exact semantics.doRule assignment application.toPathChecked
      leftSupported rightSupported
  marginalization := semantics.marginalization
  conditioning := semantics.conditioning
  chain := semantics.chain

/-- Assemble executable primitive soundness directly from the three path
cross-product laws, without assuming full d-separation completeness. -/
noncomputable def LocalPrimitiveSoundness.ofPathCrossProductLaws
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (laws : PathDoRuleCrossProductLaws G model) :
    LocalPrimitiveSoundness G model :=
  (PathPrimitiveSoundness.ofDoRule model G
    laws.toCrossProductSoundness.toDoRule).compileChecked

/--
Soundness package for executable derivations.  Unlike `PublishedSoundness`,
this needs only the proved algorithm-to-path implication; the reverse
direction remains relevant to compiling published path certificates, not to
semantic soundness of an executable derivation.
-/
structure CheckedSoundness (S : ObservedSignature)
    (G : ObservedGraph S) where
  pathPrimitive : forall model : ExactModel S,
    Compatible model G -> PathPrimitiveSoundness G model

def CheckedSoundness.primitive (sound : CheckedSoundness S G)
    (model : ExactModel S) (compatible : Compatible model G) :
    LocalPrimitiveSoundness G model :=
  (sound.pathPrimitive model compatible).compileChecked

/-- Construct the executable package from the remaining global-Markov
cross-product laws. -/
noncomputable def CheckedSoundness.ofCrossProductLaws
    (G : ObservedGraph S)
    (laws : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductLaws G model) :
    CheckedSoundness S G where
  pathPrimitive := by
    intro model compatible
    exact PathPrimitiveSoundness.ofDoRule model G
      (laws model compatible).toCrossProductSoundness.toDoRule

/-- Assemble executable soundness from explicit graph-derived latent
partition witnesses. -/
noncomputable def CheckedSoundness.ofPartitionWitnesses
    (G : ObservedGraph S)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    CheckedSoundness S G :=
  CheckedSoundness.ofCrossProductLaws G (fun model compatible =>
    (witnesses model compatible).toProductCrossProductLaws.toDistributionLaws)

/-- Transport target primitive soundness back to the finite source semantics. -/
noncomputable def PathPrimitiveSoundness.toFiniteSource
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {model : FiniteTableSCM T}
    (semantics : PathPrimitiveSoundness G.interpret model.interpret) :
    FiniteSourcePathPrimitiveSoundness G model where
  doRule := by
    intro left right assignment application leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.doRule assignment application
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  marginalization := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.marginalization x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  conditioning := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.conditioning x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  chain := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.chain x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)

/--
The checked constructor isolates the two remaining graph-dependent obligations:
correctness of executable d-separation and semantic validity of a path do-rule.
-/
noncomputable def PublishedSoundness.ofDSeparationDoRule
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (doRuleSound : ∀ (model : ExactModel S), Compatible model G ->
      ∀ {left right} (assignment : S.Assignment),
        PathDoRuleApplication G left right ->
          ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
          ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
          ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
            assignment) :
    PublishedSoundness S G where
  dseparation := correct
  pathPrimitive := by
    intro model compatible
    exact PathPrimitiveSoundness.ofDoRule model G
      (doRuleSound model compatible)

/-- Assemble published soundness from raw global-Markov cylinder equalities. -/
noncomputable def PublishedSoundness.ofDSeparationCrossProduct
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (crossProductSound : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductSoundness G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationDoRule G correct (by
    intro model compatible left right assignment application
      leftSupported rightSupported
    exact (crossProductSound model compatible).toDoRule assignment application
      leftSupported rightSupported)

/-- Published soundness assembled from three separately proved cross-product laws. -/
noncomputable def PublishedSoundness.ofDSeparationCrossProductLaws
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (laws : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductLaws G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationCrossProduct G correct
    (fun model compatible =>
      (laws model compatible).toCrossProductSoundness)

/-- Assemble published soundness from explicit graph-derived latent
partitions plus the complete d-separation correctness theorem. -/
noncomputable def PublishedSoundness.ofDSeparationPartitionWitnesses
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationCrossProductLaws G correct
    (fun model compatible =>
      (witnesses model compatible).toProductCrossProductLaws.toDistributionLaws)

/--
Published soundness from a path do-rule, using the inhabited d-separation
correctness theorem.  The remaining obligation is global-Markov soundness
of the three rules on compatible models.
-/
noncomputable def PublishedSoundness.ofDoRule
    (G : ObservedGraph S)
    (doRuleSound : ∀ (model : ExactModel S), Compatible model G ->
      ∀ {left right} (assignment : S.Assignment),
        PathDoRuleApplication G left right ->
          ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
          ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
          ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
            assignment) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationDoRule G G.dSeparationCorrectness doRuleSound

/--
Published soundness from graph-derived latent partitions, using the
inhabited d-separation correctness theorem.  The remaining obligation is
the three do-rule partition witnesses on compatible models.
-/
noncomputable def PublishedSoundness.ofPartitionWitnesses
    (G : ObservedGraph S)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationPartitionWitnesses G
    G.dSeparationCorrectness witnesses

/-- A generic soundness package specializes constructively to finite source tables. -/
noncomputable def PublishedSoundness.toFiniteSource
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (sound : PublishedSoundness T.toObserved G.interpret) :
    PublishedFiniteSourceSoundness T G where
  dseparation := sound.dseparation
  pathPrimitive := by
    intro model compatible
    apply PathPrimitiveSoundness.toFiniteSource
    exact sound.pathPrimitive model.interpret
      ((finiteSourceCompatible_iff model G).mp compatible)

/-- Finite-source package assembled from the three target mass laws. -/
noncomputable def PublishedFiniteSourceSoundness.ofDSeparationCrossProductLaws
    {T : FiniteTableSignature} (G : FiniteTableGraph T)
    (correct : DSeparationCorrectness G.interpret)
    (laws : forall (model : ExactModel T.toObserved),
      Compatible model G.interpret ->
        PathDoRuleCrossProductLaws G.interpret model) :
    PublishedFiniteSourceSoundness T G :=
  (PublishedSoundness.ofDSeparationCrossProductLaws
    G.interpret correct laws).toFiniteSource

end Causality
end Thesis
