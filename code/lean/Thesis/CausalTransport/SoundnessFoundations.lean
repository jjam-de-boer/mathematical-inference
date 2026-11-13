import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.DSeparationCorrectness
import Thesis.Probability.Reindexing

namespace Thesis
namespace Causality

open Probability

/-!
# Finite soundness foundations and independent-product identities

This layer owns the finite-source probability bridge, ancestry and separation
foundations, canonical assignment splicing, ordinary probability operations,
and the basic independent latent-product kernel identities. The three
point-mass/product lemmas are placed with their private enumeration helpers,
so those helpers remain private rather than becoming a new public interface.

Every extracted declaration keeps its original namespace, statement and proof
body. These independent product lemmas now precede the kernel-region arguments
that do not occur in their proofs. The import boundary allows later graph and
rule proofs to reuse a completed artifact instead of retaining this layer's
elaboration state. Published soundness is still assembled by importing
Soundness; this foundation adds no replacement premise or assumed law.
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

/-- Evaluation at `child` is insensitive to intervention differences strictly
after `child` in the signature's fixed topological order.

The prefix through `child` is backward-closed because every directed parent
has a smaller index.  This small generic lemma is the semantic reason that a
rule-2 local factor may intervene on *all* vertices of the opposite
conditioning block: vertices later than the factor being read cannot affect
its structural equation. -/
theorem evalNodeUnder_eq_of_intervention_agree_through
    (model : FiniteLatentSCM S)
    (left right : (i : Fin S.count) -> Option (S.Value i))
    (roots : model.latent.Assignment) (child : Fin S.count)
    (agree : forall node, node.val <= child.val -> left node = right node) :
    model.evalNodeUnder left roots child =
      model.evalNodeUnder right roots child := by
  let through : NodeSet S := fun node => decide (node.val <= child.val)
  have closed : model.BackwardClosedUnder left through := by
    intro parent current currentThrough _currentFree edge
    have currentLe : current.val <= child.val :=
      of_decide_eq_true (by simpa [through] using currentThrough)
    have parentLt : parent.val < current.val := S.directed_earlier edge
    have parentLe : parent.val <= child.val :=
      Nat.le_trans (Nat.le_of_lt parentLt) currentLe
    simpa [through] using decide_eq_true parentLe
  exact model.evalNodeUnder_eq_of_intervention_agree_on_closed
    left right through roots closed (by
      intro node nodeThrough
      exact agree node (of_decide_eq_true (by
        simpa [through] using nodeThrough))) child (by simp [through])

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

@[simp] theorem remapMinimalBarWalkToBarUnderline_nodes
    (G : ObservedGraph S) (x z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge (GraphMutilation.bar x)) length source target)
    (simple : walk.nodes.Nodup)
    (havoid : forall n, n ∈ walk.nodes -> n ≠ target -> z n = false) :
    (remapMinimalBarWalkToBarUnderline G x z walk simple havoid).nodes =
      walk.nodes := by
  induction walk with
  | refl => rfl
  | @step length source middle target first rest ih =>
      simp only [remapMinimalBarWalkToBarUnderline,
        FiniteReachability.ExactWalk.nodes]
      rw [ih _ _]

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

@[simp] theorem remapBarUnionWalkToBarUnderline_nodes
    (G : ObservedGraph S) (x z : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge
        (GraphMutilation.bar (NodeSet.union x z))) length source target)
    (hnotZ : forall n, n ∈ walk.nodes -> z n = false) :
    (remapBarUnionWalkToBarUnderline G x z walk hnotZ).nodes = walk.nodes := by
  induction walk with
  | refl => rfl
  | @step length source middle target first rest ih =>
      simp only [remapBarUnionWalkToBarUnderline,
        FiniteReachability.ExactWalk.nodes]
      rw [ih _]

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


end Kernel
end Causality
end Thesis
