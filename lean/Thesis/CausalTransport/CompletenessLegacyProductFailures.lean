import Thesis.CausalTransport.CompletenessLegacyShrinkFailures

namespace Thesis
namespace Causality

open Probability

/-!
# Historical product failures and trace-compilation interfaces

Retains the original trace-compilation boundary and the existing product-branch
failure cases. These legacy facts do not certify unsafe identified formulas.

Every extracted declaration keeps its original namespace, statement, proof
script and order. The new boundary only lets later work import a completed
artifact instead of retaining this section's elaboration state. Existing
clients may still import Completeness for the entire historical interface.
No theorem is dropped, weakened or replaced by an assumption.

Historical branch-specific unpackers remain historical facts: their quantity
is not evidence that a published semantic completeness theorem has been
inhabited. Current-engine compilation and hedge semantics retain their
existing independently checked assembly boundaries.
-/

/-!
### Reducing joint completeness to trace compilation and hedge semantics

The totality and failure-to-hedge results above remove all control-flow
uncertainty from the public joint theorem.  What remains is represented below
as a structural compiler: every successful trace must produce a certificate
whose displayed formula is exactly the engine result.  Keeping that equality
as data prevents a future implementation from satisfying the interface with
an unrelated action-free expression.
-/

/-- A published joint certificate aligned with the result indexed by a
successful structural ID trace. -/
structure PublishedJointSuccessCompilation
    {S : ObservedSignature} {G : ObservedGraph S}
    (C : GraphModelClass G) (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) (term : ProbabilityTerm S) where
  certificate : PublishedJointCertificate C correct q
  formula_eq : certificate.formula = term

/-!
### Terminal constructors of the structural success compiler

The public trace begins at `remaining = V` and `current = P(V)`.  Its two
nonrecursive terminal constructors therefore line up exactly with certificates
already proved above:

* `emptyAction` is the ordinary observational marginal of `P(V)`;
* `emptyFree` forces `V \ X = ∅`, hence the disjoint outcome is empty and ID
  returns the full marginal `∑_V P(V)`.

Packaging these cases at the trace boundary is deliberately different from a
front-end query heuristic: the returned `formula_eq` is indexed by the actual
term stored in the success trace.
-/

/-- Compile the top-level empty-action trace target. -/
noncomputable def PublishedJointSuccessCompilation.ofEmptyAction
    {S : ObservedSignature} {G : ObservedGraph S}
    {C : GraphModelClass G} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PublishedJointSuccessCompilation C correct q
      (.marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S)) where
  certificate := emptyActionIdentifiedPublishedCertificate correct q emptyAction
  formula_eq := rfl

/-- Compile the top-level no-free-component trace target. -/
noncomputable def PublishedJointSuccessCompilation.ofEmptyFree
    {S : ObservedSignature} {G : ObservedGraph S}
    {C : GraphModelClass G} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (noFreeComponents :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = []) :
    PublishedJointSuccessCompilation C correct q
      (.marginalize NodeSet.full (observationalJointTerm S)) where
  certificate :=
    let emptyOutcome := outcome_isEmpty_of_empty_free G q noFreeComponents
    emptyOutcomeIdentifiedPublishedCertificate correct q emptyOutcome
  formula_eq := by
    exact emptyOutcomeIdentifiedTerm_eq q
      (outcome_isEmpty_of_empty_free G q noFreeComponents)

/--
Compile exactly the two terminal constructors of a public structural success
trace.  Recursive shrink/restriction/product traces and the nonrecursive
maximal-component chain remain `none`; callers can inspect this option without
asserting that those branches have already been solved.
-/
noncomputable def publishedJointSuccessLeafCompilation?
    {S : ObservedSignature} {G : ObservedGraph S}
    {C : GraphModelClass G} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) (term : ProbabilityTerm S)
    (trace : JointIdentificationSuccessTrace G q term) :
    Option (PublishedJointSuccessCompilation C correct q term) := by
  cases trace with
  | emptyAction _fuel _remaining _outcome _action _current actionEmpty =>
      have emptyAction : NodeSet.isEmpty q.action = true := by
        simpa [NodeSet.inter_full_right] using actionEmpty
      exact some (by
        simpa [NodeSet.inter_full_right] using
          PublishedJointSuccessCompilation.ofEmptyAction correct q emptyAction)
  | emptyFree _fuel _remaining _outcome _action _current _actionNonempty
      _ancestral noFreeComponents =>
      have noFreeComponents' :
          G.cComponents (NodeSet.diff NodeSet.full q.action) = [] := by
        simpa [NodeSet.inter_full_right] using noFreeComponents
      exact some (by
        simpa using
          PublishedJointSuccessCompilation.ofEmptyFree correct q
            noFreeComponents')
  | chain => exact none
  | shrink => exact none
  | restrict => exact none
  | product => exact none

/-- The intended branch-generic program for successful public joint ID.

This record indexes the legacy `Legacy.identifyJoint` trace, not the replacement
`identifyJointKernel` program.  The exact-output requirement is substantive:
`Examples.FrontDoorIdentification` proves that the legacy engine makes this
record uninhabitable on a front-door graph.  The continuing compiler must
target the current-kernel recursion instead; this legacy field must not be
assumed as an axiom or filled by more branch unpackers. -/
structure Legacy.PublishedJointTraceCompiler
    {S : ObservedSignature} (G : ObservedGraph S)
    (C : GraphModelClass G) (correct : DSeparationCorrectness G) where
  compile : forall (q : JointKernelQuery S) (term : ProbabilityTerm S),
    JointIdentificationSuccessTrace G q term ->
      PublishedJointSuccessCompilation C correct q term

/--
A structural trace compiler and a countermodel for every extracted hedge
already imply semantic joint completeness.  The failed branch contradicts
identifiability; the successful branch returns the compiler's inspectable
certificate.  No unfinished branch exists by the rank theorem.
-/
noncomputable def Legacy.PublishedJointTraceCompiler.certificateOfIdentifiable
    {S : ObservedSignature.{0}} {G : ObservedGraph S}
    {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    (compiler : Legacy.PublishedJointTraceCompiler G C correct)
    (hedgeCounterexample : forall q,
      HedgeWitness G q -> CounterexampleIn C q)
    (q : JointKernelQuery S) (identifiable : C.identifiable q) :
    PublishedJointCertificate C correct q := by
  cases identifyJoint_terminalTrace G q with
  | identified term trace =>
      exact (compiler.compile q term trace).certificate
  | failed fail trace =>
      let extracted := trace.extractedHedge G q
      exact False.elim
        ((hedgeCounterexample q extracted.witness).not_identifiable
          identifiable)

/--
A free c-component of `G \ X` avoids the original action.
-/
theorem product_piece_avoids_action
    (G : ObservedGraph S) (q : JointKernelQuery S) {piece : NodeSet S}
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action)) :
    NodeSet.disjointBool piece q.action = true := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff NodeSet.full
          (NodeSet.inter q.action NodeSet.full)) := by
    simpa [hinter] using hmem
  exact product_piece_avoids_action_of G NodeSet.full q.action hmem'

/--
The full vertex set meets a nonempty action.
-/
theorem full_meets_action
    {S : ObservedSignature} (action : NodeSet S)
    (hex : NodeSet.isEmpty action = false) :
    NodeSet.meetsBool NodeSet.full action = true := by
  rcases (NodeSet.isEmpty_eq_false_iff action).mp hex with ⟨i, hi⟩
  exact (NodeSet.meetsBool_eq_true_iff _ _).mpr
    ⟨i, by simp [NodeSet.full], hi⟩

/--
A first product split whose nested fail has free side the failing piece
yields a hedge for the original query, once the recorded remaining set
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.  Remaining need
not be the full vertex set: nested ancestral restriction is the typical
smaller remaining set, and is covered as soon as those two Boolean facts
hold.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_of
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    have hmem' :
        piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
      simpa [hfc] using hmem
    simpa [failedHedgeSelection, hpiece] using
      product_piece_avoids_action G q hmem'
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
Unshrunk nested remaining is the special case of
`hedgeWitness?_eq_some_of_failed_after_product_of` in which the nested
call never left the full graph: the full vertex set meets a nonempty
action, and outer `hkept` is ancestry of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining NodeSet.full = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    simpa [failedHedgeSelection, heqR] using full_meets_action q.action hex
  have hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true := by
    have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
      NodeSet.inter_full_right _
    have hanc :
        G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome NodeSet.full) = NodeSet.full := by
      simpa [hy] using (NodeSet.equal_eq_true_iff _ _).mp hkept
    simpa [heqR, hy] using (NodeSet.equal_eq_true_iff _ _).mpr hanc
  exact hedgeWitness?_eq_some_of_failed_after_product_of G q hex hkept hfc
    hmem hfail hfreeEq hancFree hmeets hancY

/--
Unshrunk product failure whose recorded free side is one of the listed
free c-components.  The free-equality hypothesis of
`hedgeWitness?_eq_some_of_failed_after_product` is then reflexivity.
-/
theorem hedgeWitness?_eq_some_of_failed_after_first_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining NodeSet.full = true)
    (hfreeMem :
      fail.free ∈ component :: component2 :: rest)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed_after_product G q hex hkept hfc
    hfreeMem hfail heq
    ((NodeSet.equal_eq_true_iff fail.free fail.free).mpr rfl) hancFree

/--
The nested product action `remaining \ piece` is nonempty on `remaining`
whenever `piece` is a free c-component of `remaining \ (X ∩ remaining)`
and that nested original action is nonempty.  Extra vertices of
`remaining` that avoid `X` do not fill the cut.
-/
theorem product_piece_nested_action_nonempty_of
    (G : ObservedGraph S) (remaining action : NodeSet S)
    {piece : NodeSet S}
    (hex :
      NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hmem : piece ∈ G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining))) :
    NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff remaining piece) remaining) =
      false := by
  rcases (NodeSet.isEmpty_eq_false_iff _).mp hex with ⟨i, hi⟩
  have hpair : action i = true ∧ remaining i = true :=
    Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
  have hdisj :=
    (NodeSet.disjointBool_eq_true_iff _ _).mp
      (product_piece_avoids_action_of G remaining action hmem)
  have hnot : piece i = false := by
    cases hp : piece i with
    | false =>
        rfl
    | true =>
        exact (Bool.false_ne_true ((hdisj i hp).symm.trans hpair.1)).elim
  exact (NodeSet.isEmpty_eq_false_iff _).mpr
    ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩

/--
The nested product action `V \ piece` is nonempty whenever the original
action is nonempty and `piece` is a free c-component of `G \ X`.
-/
theorem product_piece_nested_action_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S) {piece : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action)) :
    NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
      false := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff NodeSet.full
          (NodeSet.inter q.action NodeSet.full)) := by
    simpa [hinter] using hmem
  simpa [NodeSet.inter_full_right] using
    product_piece_nested_action_nonempty_of G NodeSet.full q.action
      hex' hmem'

/--
Every vertex of a free product piece is a self-ancestor in
`G_{\overline{V \ piece}}`, so the nested ancestral remaining set still
contains that piece.
-/
theorem product_piece_subset_nested_ancestral
    (G : ObservedGraph S) (piece : NodeSet S) :
    NodeSet.Subset piece
      (G.ancestralSet NodeSet.full
        (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
        (NodeSet.inter piece NodeSet.full)) := by
  intro i hi
  have hinterNodes :
      NodeSet.inter (NodeSet.inter piece NodeSet.full) NodeSet.full i =
        true := by
    simp [NodeSet.inter, NodeSet.full, hi]
  have hmem :
      i ∈ NodeSet.members
        (NodeSet.inter (NodeSet.inter piece NodeSet.full) NodeSet.full) :=
    (NodeSet.mem_members_iff _ i).mpr hinterNodes
  have hself :
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (G.directedEdgeWithin NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece)))
        S.count i i = true :=
    FiniteReachability.within_self finBeq (NodeSet.enumerated S)
      (G.directedEdgeWithin NodeSet.full
        (GraphMutilation.bar (NodeSet.diff NodeSet.full piece)))
      S.count i (NodeSet.mem_enumerated S i) (natBeq_refl i.val)
  have hany :
      (NodeSet.members
          (NodeSet.inter (NodeSet.inter piece NodeSet.full)
            NodeSet.full)).any
        (fun target =>
          FiniteReachability.within finBeq (NodeSet.enumerated S)
            (G.directedEdgeWithin NodeSet.full
              (GraphMutilation.bar (NodeSet.diff NodeSet.full piece)))
            S.count i target) = true :=
    List.any_eq_true.mpr ⟨i, hmem, hself⟩
  simpa [ObservedGraph.ancestralSet, ObservedGraph.ancestorOfWithin,
    NodeSet.full] using
    Bool.and_eq_true_iff.mpr ⟨rfl, hany⟩

/--
On the nested ancestral remaining set of a product piece, the local
`remaining \ X` cut is exactly that piece: vertices outside the piece
that still ancestor it sit in the nested action `V \ piece`.
-/
theorem product_nested_shrink_free_eq_piece
    (G : ObservedGraph S) (piece remaining : NodeSet S)
    (heq :
      remaining =
        G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full)) :
    NodeSet.diff remaining
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) remaining) =
      piece := by
  have hsub := product_piece_subset_nested_ancestral G piece
  funext i
  have hAn : remaining i = G.ancestralSet NodeSet.full
      (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
      (NodeSet.inter piece NodeSet.full) i := by
    rw [heq]
  cases hp : piece i with
  | true =>
      have hrem : remaining i = true := by
        rw [hAn]
        exact hsub i hp
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full, hp, hrem]
  | false =>
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full, hp, hAn]

/--
A first product split whose nested call is an immediate 4.1 fail on that
piece: the failure record is the full graph with free side `piece`, and
the original query has a hedge.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_immediate
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hsingle : G.isSingleCComponent NodeSet.full = true)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (hnestedFc : G.cComponents piece = [piece])
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hexN :
      NodeSet.isEmpty
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        false :=
    product_piece_nested_action_nonempty G q hex hmem'
  have hact :
      NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full =
        NodeSet.diff NodeSet.full piece :=
    NodeSet.inter_full_right _
  have hkeptN :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true := by
    simpa [hact] using hnestedKept
  have hfreeN :
      NodeSet.diff NodeSet.full
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        piece := by
    rw [hact, NodeSet.diff_diff]
    funext i
    simp [NodeSet.inter, NodeSet.full]
  have hfcN :
      G.cComponents
          (NodeSet.diff NodeSet.full
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)) =
        [piece] := by
    simpa [hfreeN] using hnestedFc
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero : Legacy.identifyFuel 0 G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc : Legacy.identifyFuel (n + 1) G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have parts :=
        identifyFuel_eq_failed_immediate_query_site n G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S)
          hexN hkeptN hfcN hsingle hsucc
      have heq :
          NodeSet.equal fail.remaining NodeSet.full = true :=
        (NodeSet.equal_eq_true_iff _ _).mpr parts.1
      have hfreeEq :
          NodeSet.equal fail.free piece = true :=
        (NodeSet.equal_eq_true_iff _ _).mpr parts.2.1
      have hancFree :
          NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter fail.free fail.remaining))
            fail.remaining = true := by
        have hanc := parts.2.2.2
        have hr : fail.remaining = NodeSet.full := parts.1
        have hf : fail.free = piece := parts.2.1
        simpa [hr, hf, NodeSet.inter_full_right] using hanc
      exact hedgeWitness?_eq_some_of_failed_after_product G q hex hkept hfc
        hmem hfail heq hfreeEq hancFree

/--
A nested product call whose remaining set is not ancestral of the piece
first restricts to that ancestral set.  The original query's hedge tests
then need that smaller remaining set to meet `X` and to be ancestral of
`Y` in `G_{\overline{X}}`.
-/
theorem identifyFuel_eq_failed_of_product_nested_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action))
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          piece (NodeSet.diff NodeSet.full piece)
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full)))
            (observationalJointTerm S)) =
        IdentificationOutcome.failed fail := by
  have hexN :
      NodeSet.isEmpty
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        false :=
    product_piece_nested_action_nonempty G q hex hmem
  have hact :
      NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full =
        NodeSet.diff NodeSet.full piece :=
    NodeSet.inter_full_right _
  have hkeptN :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false := by
    simpa [hact] using hnestedKept
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero : Legacy.identifyFuel 0 G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc : Legacy.identifyFuel (n + 1) G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      exact ⟨n,
        identifyFuel_eq_failed_of_shrink n G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S)
          hexN hkeptN hsucc⟩

/--
After a nested ancestral shrink of a product piece, a further product
split unpacks as an ID run on one free c-component of that nested
`An(piece)`, with action `kept \ subpiece`.
-/
theorem identifyFuel_eq_failed_of_product_nested_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action))
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff NodeSet.full piece)
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))) = false)
    (hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))))
          (NodeSet.inter piece
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full))))
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        component :: component2 :: rest)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full))
            subpiece
            (NodeSet.diff
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))
              subpiece)
            (.marginalize
              (NodeSet.diff NodeSet.full
                (G.ancestralSet NodeSet.full
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full))
                  (NodeSet.inter piece NodeSet.full)))
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
      (NodeSet.inter piece NodeSet.full)
  rcases identifyFuel_eq_failed_of_product_nested_shrink G q hex hmem
      hnestedKept hnested with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G kept piece (NodeSet.diff NodeSet.full piece)
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        simpa [kept] using hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G kept piece
            (NodeSet.diff NodeSet.full piece)
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        simpa [kept] using hm
      have hexK' :
          NodeSet.isEmpty
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept) =
            false := by
        simpa [kept] using hexK
      have hkeptK' :
          NodeSet.equal
            (G.ancestralSet kept
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept))
              (NodeSet.inter piece kept))
            kept = true := by
        simpa [kept] using hkeptK
      have hfcK' :
          G.cComponents
            (NodeSet.diff kept
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) =
            component :: component2 :: rest := by
        simpa [kept] using hfcK
      have hprod :=
        identifyFuel_eq_failed_of_product n G kept piece
          (NodeSet.diff NodeSet.full piece)
          (.marginalize
            (NodeSet.diff NodeSet.full kept)
            (observationalJointTerm S))
          hexK' hkeptK' hfcK' hsucc
      rcases hprod with ⟨subpiece, hmemS, hEq⟩
      exact ⟨subpiece, hmemS, ⟨n, by simpa [kept] using hEq⟩⟩

/--
A first product split, nested ancestral shrink, then a further product
split on that ancestral remaining set, with free side the failing
subpiece, yields a hedge for the original query once that remaining set
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false)
    (_hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff NodeSet.full piece)
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))) = false)
    (_hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))))
          (NodeSet.inter piece
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full))))
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
      (NodeSet.inter piece NodeSet.full)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) := by
    have hfcK' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcK
    rw [hfcK']
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept) i =
          true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hk : kept i with
          | false =>
              simp [hp, hk] at hcut
          | true =>
              simp [hp, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, and nested product
split, a further 4.3 restriction unpacks as the ID run on the containing
c-component of the failing subpiece inside that ancestral remaining set,
with action `(kept \ subpiece) ∩ larger`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_product_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept subpiece larger : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept subpiece) kept) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet kept
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff kept subpiece) kept))
          (NodeSet.inter subpiece kept))
        kept = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff kept subpiece) kept)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent kept = false)
    (hany2 :
      (G.cComponents kept).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 :
      G.containingCComponent kept subpiece = some larger)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G kept subpiece (NodeSet.diff kept subpiece)
          (.marginalize
            (NodeSet.diff NodeSet.full kept) (observationalJointTerm S)) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff kept subpiece) kept) larger)
        (chainProduct kept larger) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G kept subpiece
    (.marginalize
      (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
    hexP2 hnestedKept2 hnestedFc2 hsingle2 hany2 hcont2 hinner

/--
A first product split, nested ancestral shrink, nested product split,
then 4.3 onto the containing c-component of the failing subpiece, with
remaining that inner host and free side the subpiece, yields a hedge
for the original query once that host meets `X` and is ancestral of `Y`
in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece subpiece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
      (NodeSet.inter piece NodeSet.full)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) := by
    have hfcK' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcK
    rw [hfcK']
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept) i =
          true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hk : kept i with
          | false =>
              simp [hp, hk] at hcut
          | true =>
              simp [hp, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, and nested product
split, a further ancestral shrink unpacks as the ID run on `An(subpiece)`
inside that ancestral remaining set, with action `kept \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept subpiece : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept subpiece) kept) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet kept
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff kept subpiece) kept))
          (NodeSet.inter subpiece kept))
        kept = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G kept subpiece (NodeSet.diff kept subpiece)
          (.marginalize
            (NodeSet.diff NodeSet.full kept) (observationalJointTerm S)) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet kept
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff kept subpiece) kept))
          (NodeSet.inter subpiece kept))
        subpiece (NodeSet.diff kept subpiece)
        (.marginalize
          (NodeSet.diff kept
            (G.ancestralSet kept
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff kept subpiece) kept))
              (NodeSet.inter subpiece kept)))
          (.marginalize
            (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G kept subpiece
    (.marginalize
      (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
    hexP2 hnestedKept2 hinner

/--
A first product split, nested ancestral shrink, nested product split,
then ancestral shrink of that subpiece, with remaining `An(subpiece)`
inside the first ancestral remaining set and free side the subpiece,
yields a hedge for the original query once that smaller remaining set
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet NodeSet.full
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full))
                  (NodeSet.inter piece NodeSet.full))
                subpiece)
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))))
          (NodeSet.inter subpiece
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
      (NodeSet.inter piece NodeSet.full)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) := by
    have hfcK' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcK
    rw [hfcK']
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept) i =
          true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hk : kept i with
          | false =>
              simp [hp, hk] at hcut
          | true =>
              simp [hp, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a nested ancestral shrink of a product piece, a further 4.3
restriction unpacks as the ID run on the containing c-component of that
ancestral remaining set, with action `(V \ piece) ∩ host`.
-/
theorem identifyFuel_eq_failed_of_product_nested_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece host seed : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action))
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff NodeSet.full piece)
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))) = false)
    (hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))))
          (NodeSet.inter piece
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full))))
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        [seed])
    (hsingleK :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = false)
    (hanyK :
      (G.cComponents
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))).any
        (fun c => NodeSet.equal c seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        seed = some host)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))
          host)
        (chainProduct
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          host) =
        IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
      (NodeSet.inter piece NodeSet.full)
  rcases identifyFuel_eq_failed_of_product_nested_shrink G q hex hmem
      hnestedKept hnested with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G kept piece (NodeSet.diff NodeSet.full piece)
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        simpa [kept] using hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G kept piece
            (NodeSet.diff NodeSet.full piece)
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        simpa [kept] using hm
      have hexK' :
          NodeSet.isEmpty
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept) =
            false := by
        simpa [kept] using hexK
      have hkeptK' :
          NodeSet.equal
            (G.ancestralSet kept
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept))
              (NodeSet.inter piece kept))
            kept = true := by
        simpa [kept] using hkeptK
      have hfcK' :
          G.cComponents
            (NodeSet.diff kept
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) =
            [seed] := by
        simpa [kept] using hfcK
      have hsingleK' : G.isSingleCComponent kept = false := by
        simpa [kept] using hsingleK
      have hanyK' :
          (G.cComponents kept).any
            (fun c => NodeSet.equal c seed) = false := by
        simpa [kept] using hanyK
      have hcont' : G.containingCComponent kept seed = some host := by
        simpa [kept] using hcont
      refine ⟨n, ?_⟩
      simpa [kept] using
        identifyFuel_eq_failed_of_restrict n G kept piece
          (NodeSet.diff NodeSet.full piece)
          (.marginalize
            (NodeSet.diff NodeSet.full kept)
            (observationalJointTerm S))
          hexK' hkeptK' hfcK' hsingleK' hanyK' hcont' hsucc

/--
A first product split, nested ancestral shrink, then 4.3 restriction,
with remaining the containing host and free side `host \ (V \ piece)`,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece host seed : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false)
    (_hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff NodeSet.full piece)
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))) = false)
    (_hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))))
          (NodeSet.inter piece
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full))))
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (_hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        [seed])
    (_hsingleK :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = false)
    (_hanyK :
      (G.cComponents
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        seed = some host)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            fail.remaining)) = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut : fail.free i = true := by
      simpa [failedHedgeSelection] using hi
    have hp : piece i = true := by
      have hi' : NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            fail.remaining) i = true := by
        simpa [hfreeR] using hcut
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hi'
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hr : fail.remaining i with
          | false =>
              simp [hp, hr] at hi'
          | true =>
              simp [hp, hr] at hi'
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
A first product split whose nested call shrinks, then fails with the
recorded remaining set equal to that ancestral set and free side the
local `remaining \ X`, yields a hedge for the original query once the
smaller remaining set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.  Immediate 4.1 on the shrunk remaining set is the
special case in which those remaining/free equations come from the
nested 4.1 site.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            fail.remaining)) = true)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hexN :
      NodeSet.isEmpty
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        false :=
    product_piece_nested_action_nonempty G q hex hmem'
  have hact :
      NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full =
        NodeSet.diff NodeSet.full piece :=
    NodeSet.inter_full_right _
  have hkeptN :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false := by
    simpa [hact] using hnestedKept
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hAn :
      fail.remaining =
        G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full) := by
    simpa [hact] using heqR
  have hfreeEq :
      NodeSet.equal fail.free piece = true := by
    have hcut :
        NodeSet.diff fail.remaining
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              fail.remaining) =
          piece :=
      product_nested_shrink_free_eq_piece G piece fail.remaining hAn
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
    exact (NodeSet.equal_eq_true_iff _ _).mpr (hfreeR.trans hcut)
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero : Legacy.identifyFuel 0 G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc : Legacy.identifyFuel (n + 1) G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have hshrunk :=
        identifyFuel_eq_failed_of_shrink n G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S)
          hexN hkeptN hsucc
      have hancFree :
          NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter fail.free fail.remaining))
            fail.remaining = true := by
        have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
        simpa [hfreeR] using
          (identifyFuel_eq_failed_query_of_remaining_eq n G
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full))
            piece (NodeSet.diff NodeSet.full piece)
            (.marginalize
              (NodeSet.diff NodeSet.full
                (G.ancestralSet NodeSet.full
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full))
                  (NodeSet.inter piece NodeSet.full)))
              (observationalJointTerm S))
            hshrunk heq hfree)
      exact hedgeWitness?_eq_some_of_failed_after_product_of G q hex
        hkept hfc hmem hfail hfreeEq hancFree hmeets hancY

/--
A first product split whose nested call shrinks, then fails as an
immediate 4.1 hedge on that ancestral remaining set, yields a hedge for
the original query once the smaller remaining set meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_immediate
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false)
    (hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (hexKept :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff NodeSet.full piece)
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))) = false)
    (hnestedKeptImm :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))))
          (NodeSet.inter piece
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full))))
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
          (NodeSet.inter piece NodeSet.full)) = true)
    (hnestedFcKept :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) = [piece])
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hexN :
      NodeSet.isEmpty
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        false :=
    product_piece_nested_action_nonempty G q hex hmem'
  have hact :
      NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full =
        NodeSet.diff NodeSet.full piece :=
    NodeSet.inter_full_right _
  have hkeptN :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = false := by
    simpa [hact] using hnestedKept
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero : Legacy.identifyFuel 0 G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc : Legacy.identifyFuel (n + 1) G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have hshrunk :=
        identifyFuel_eq_failed_of_shrink n G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S)
          hexN hkeptN hsucc
      cases n with
      | zero =>
          simp [Legacy.identifyFuel] at hshrunk
      | succ n' =>
          have parts :=
            identifyFuel_eq_failed_immediate_query_site n' G
              (G.ancestralSet NodeSet.full
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full))
                (NodeSet.inter piece NodeSet.full))
              piece (NodeSet.diff NodeSet.full piece)
              (.marginalize
                (NodeSet.diff NodeSet.full
                  (G.ancestralSet NodeSet.full
                    (GraphMutilation.bar
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        NodeSet.full))
                    (NodeSet.inter piece NodeSet.full)))
                (observationalJointTerm S))
              hexKept hnestedKeptImm hnestedFcKept hsingle hshrunk
          have hfreeEq :
              NodeSet.equal fail.free piece = true :=
            (NodeSet.equal_eq_true_iff _ _).mpr parts.2.1
          have hancFree :
              NodeSet.equal
                (G.ancestralSet fail.remaining
                  (GraphMutilation.bar
                    (NodeSet.diff fail.remaining fail.free))
                  (NodeSet.inter fail.free fail.remaining))
                fail.remaining = true := by
            have hanc := parts.2.2.2
            have hr := parts.1
            have hf : fail.free = piece := parts.2.1
            simpa [hr, hf] using hanc
          exact hedgeWitness?_eq_some_of_failed_after_product_of G q hex
            hkept hfc hmem hfail hfreeEq hancFree hmeets hancY

/--
A first product split whose nested call is a 4.3 restriction onto a
containing c-component of the piece, then fails with remaining/free the
local remaining-eq equations on that host, yields a hedge for the
original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (hnestedFc : G.cComponents piece = [piece])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            fail.remaining)) = true)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hexN :
      NodeSet.isEmpty
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        false :=
    product_piece_nested_action_nonempty G q hex hmem'
  have hact :
      NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full =
        NodeSet.diff NodeSet.full piece :=
    NodeSet.inter_full_right _
  have hkeptN :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true := by
    simpa [hact] using hnestedKept
  have hfreeN :
      NodeSet.diff NodeSet.full
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        piece := by
    rw [hact, NodeSet.diff_diff]
    funext i
    simp [NodeSet.inter, NodeSet.full]
  have hfcN :
      G.cComponents
          (NodeSet.diff NodeSet.full
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)) =
        [piece] := by
    simpa [hfreeN] using hnestedFc
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hsub : NodeSet.Subset piece larger :=
    (containingCComponent_spec G NodeSet.full piece hcont).2
  have hfreeEq :
      NodeSet.equal fail.free piece = true := by
    have hcut :
        NodeSet.diff larger
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger) =
          piece := by
      funext i
      cases hp : piece i with
      | true =>
          have hl : larger i = true := hsub i hp
          simp [NodeSet.diff, NodeSet.inter, NodeSet.full, hp, hl]
      | false =>
          simp [NodeSet.diff, NodeSet.inter, NodeSet.full, hp]
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
    exact (NodeSet.equal_eq_true_iff _ _).mpr
      (hfreeR.trans (by simpa [heqR] using hcut))
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            fail.remaining)) = true := by
    have hsame :
        NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            fail.remaining =
          NodeSet.inter (NodeSet.diff NodeSet.full piece)
            fail.remaining := by
      rw [hact, heqR]
      funext i
      simp [NodeSet.inter]
    simpa [hsame] using hfree
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero : Legacy.identifyFuel 0 G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc : Legacy.identifyFuel (n + 1) G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have hrestricted :=
        identifyFuel_eq_failed_of_restrict n G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S)
          hexN hkeptN hfcN hsingle hany hcont hsucc
      have hancFree :=
        identifyFuel_eq_failed_query_of_remaining_eq n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)
          (chainProduct NodeSet.full larger) hrestricted heq hfree'
      have hancFree' :
          NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter fail.free fail.remaining))
            fail.remaining = true := by
        have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
        simpa [hfreeR] using hancFree
      exact hedgeWitness?_eq_some_of_failed_after_product_of G q hex
        hkept hfc hmem hfail hfreeEq hancFree' hmeets hancY

/--
A first product split whose nested call is a 4.3 restriction, then an
immediate 4.1 fail on that containing c-component, yields a hedge for
the original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_immediate
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (hnestedFc : G.cComponents piece = [piece])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger) = false)
    (hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) = [piece])
    (hsingleL : G.isSingleCComponent larger = true)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hexN :
      NodeSet.isEmpty
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        false :=
    product_piece_nested_action_nonempty G q hex hmem'
  have hact :
      NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full =
        NodeSet.diff NodeSet.full piece :=
    NodeSet.inter_full_right _
  have hkeptN :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true := by
    simpa [hact] using hnestedKept
  have hfreeN :
      NodeSet.diff NodeSet.full
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        piece := by
    rw [hact, NodeSet.diff_diff]
    funext i
    simp [NodeSet.inter, NodeSet.full]
  have hfcN :
      G.cComponents
          (NodeSet.diff NodeSet.full
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)) =
        [piece] := by
    simpa [hfreeN] using hnestedFc
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero : Legacy.identifyFuel 0 G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc : Legacy.identifyFuel (n + 1) G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have hrestricted :=
        identifyFuel_eq_failed_of_restrict n G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S)
          hexN hkeptN hfcN hsingle hany hcont hsucc
      cases n with
      | zero =>
          simp [Legacy.identifyFuel] at hrestricted
      | succ n' =>
          have hactL :
              NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger)
                  larger =
                NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger := by
            funext i
            simp [NodeSet.inter]
          have hexL' :
              NodeSet.isEmpty
                  (NodeSet.inter
                    (NodeSet.inter
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        NodeSet.full)
                      larger)
                    larger) = false := by
            simpa [hactL] using hexL
          have hkeptL' :
              NodeSet.equal
                (G.ancestralSet larger
                  (GraphMutilation.bar
                    (NodeSet.inter
                      (NodeSet.inter
                        (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                          NodeSet.full)
                        larger)
                      larger))
                  (NodeSet.inter piece larger))
                larger = true := by
            simpa [hactL] using hkeptL
          have hfcL' :
              G.cComponents
                (NodeSet.diff larger
                  (NodeSet.inter
                    (NodeSet.inter
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        NodeSet.full)
                      larger)
                    larger)) = [piece] := by
            simpa [hactL] using hfcL
          have parts :=
            identifyFuel_eq_failed_immediate_query_site n' G larger piece
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              (chainProduct NodeSet.full larger) hexL' hkeptL' hfcL'
              hsingleL hrestricted
          have hfreeEq :
              NodeSet.equal fail.free piece = true :=
            (NodeSet.equal_eq_true_iff _ _).mpr parts.2.1
          have hancFree :
              NodeSet.equal
                (G.ancestralSet fail.remaining
                  (GraphMutilation.bar
                    (NodeSet.diff fail.remaining fail.free))
                  (NodeSet.inter fail.free fail.remaining))
                fail.remaining = true := by
            have hanc := parts.2.2.2
            have hr := parts.1
            have hf : fail.free = piece := parts.2.1
            simpa [hr, hf] using hanc
          exact hedgeWitness?_eq_some_of_failed_after_product_of G q hex
            hkept hfc hmem hfail hfreeEq hancFree hmeets hancY

/--
A nested product call whose remaining set is a single c-component of
`G \ (V \ piece)` but not of `G` unpacks as the ID run on the containing
host, with action `(V \ piece) ∩ host`.
-/
theorem identifyFuel_eq_failed_of_product_nested_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action))
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (hnestedFc : G.cComponents piece = [piece])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger)
        (chainProduct NodeSet.full larger) =
        IdentificationOutcome.failed fail := by
  have hexN :
      NodeSet.isEmpty
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        false :=
    product_piece_nested_action_nonempty G q hex hmem
  have hact :
      NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full =
        NodeSet.diff NodeSet.full piece :=
    NodeSet.inter_full_right _
  have hkeptN :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true := by
    simpa [hact] using hnestedKept
  have hfreeN :
      NodeSet.diff NodeSet.full
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full) =
        piece := by
    rw [hact, NodeSet.diff_diff]
    funext i
    simp [NodeSet.inter, NodeSet.full]
  have hfcN :
      G.cComponents
          (NodeSet.diff NodeSet.full
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)) =
        [piece] := by
    simpa [hfreeN] using hnestedFc
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero : Legacy.identifyFuel 0 G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc : Legacy.identifyFuel (n + 1) G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      exact ⟨n,
        identifyFuel_eq_failed_of_restrict n G NodeSet.full piece
          (NodeSet.diff NodeSet.full piece) (observationalJointTerm S)
          hexN hkeptN hfcN hsingle hany hcont hsucc⟩

/--
After a nested 4.3 restriction of a product piece, a further product
split unpacks as an ID run on one free c-component of the containing
host, with action `host \ subpiece`.
-/
theorem identifyFuel_eq_failed_of_product_nested_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece larger : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action))
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (hnestedFc : G.cComponents piece = [piece])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger) = false)
    (hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        component :: component2 :: rest)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
            (chainProduct NodeSet.full larger) =
            IdentificationOutcome.failed fail := by
  rcases identifyFuel_eq_failed_of_product_nested_restrict G q hex hmem
      hnestedKept hnestedFc hsingle hany hcont hnested with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G larger piece
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (chainProduct NodeSet.full larger) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G larger piece
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (chainProduct NodeSet.full larger) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      have hactL :
          NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              larger =
            NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger := by
        funext i
        simp [NodeSet.inter]
      have hexL' :
          NodeSet.isEmpty
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              larger) = false := by
        simpa [hactL] using hexL
      have hkeptL' :
          NodeSet.equal
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger)
                  larger))
              (NodeSet.inter piece larger))
            larger = true := by
        simpa [hactL] using hkeptL
      have hfcL' :
          G.cComponents
            (NodeSet.diff larger
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger)
                larger)) =
            component :: component2 :: rest := by
        simpa [hactL] using hfcL
      have hprod :=
        identifyFuel_eq_failed_of_product n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)
          (chainProduct NodeSet.full larger) hexL' hkeptL' hfcL' hsucc
      rcases hprod with ⟨subpiece, hmemS, hEq⟩
      exact ⟨subpiece, hmemS, ⟨n, hEq⟩⟩

/--
A first product split, nested 4.3 restriction, then a further product
split on that host, with remaining the containing c-component and free
side the failing subpiece, yields a hedge for the original query once
that host meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (_hnestedFc : G.cComponents piece = [piece])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (_hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (_hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger) = false)
    (_hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, and nested product
split, a further 4.3 restriction unpacks as the ID run on the containing
c-component of the failing subpiece inside that nested host, with action
`(larger \ subpiece) ∩ larger2`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece larger2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action))
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (_hnestedFc : G.cComponents piece = [piece])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (_hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (_hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger) = false)
    (_hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (_hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (_hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) larger) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        larger = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter (NodeSet.diff larger subpiece) larger)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent larger = false)
    (hany2 :
      (G.cComponents larger).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 :
      G.containingCComponent larger subpiece = some larger2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
          (chainProduct NodeSet.full larger) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff larger subpiece) larger) larger2)
        (chainProduct larger larger2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G larger subpiece
    (chainProduct NodeSet.full larger) hexP2 hnestedKept2 hnestedFc2
    hsingle2 hany2 hcont2 hinner

/--
A first product split, nested 4.3 restriction, nested product split,
then 4.3 onto the containing c-component of the failing subpiece, with
remaining that inner host and free side the subpiece, yields a hedge
for the original query once that host meets `X` and is ancestral of `Y`
in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece larger2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (_hnestedFc : G.cComponents piece = [piece])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (_hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (_hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger) = false)
    (_hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (_hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) larger) = false)
    (_hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        larger = true)
    (_hnestedFc2 :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter (NodeSet.diff larger subpiece) larger)) =
        [subpiece])
    (_hsingle2 : G.isSingleCComponent larger = false)
    (_hany2 :
      (G.cComponents larger).any
        (fun c => NodeSet.equal c subpiece) = false)
    (_hcont2 :
      G.containingCComponent larger subpiece = some larger2)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining larger2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, and nested product
split, a further ancestral shrink unpacks as the ID run on `An(subpiece)`
inside that nested host, with action `larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {_piece larger subpiece : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) larger) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        larger = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
          (chainProduct NodeSet.full larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        subpiece (NodeSet.diff larger subpiece)
        (.marginalize
          (NodeSet.diff larger
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff larger subpiece) larger))
              (NodeSet.inter subpiece larger)))
          (chainProduct NodeSet.full larger)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G larger subpiece
    (chainProduct NodeSet.full larger) hexP2 hnestedKept2 hinner

/--
A first product split, nested 4.3 restriction, nested product split,
then ancestral shrink of that subpiece, with remaining `An(subpiece)`
inside the nested host and free side the subpiece, yields a hedge for
the original query once that ancestral set meets `X` and is ancestral
of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a nested 4.3 restriction of a product piece, a further ancestral
shrink unpacks as the ID run on `An(piece)` inside the containing host,
with action `(V \ piece) ∩ host`.
-/
theorem identifyFuel_eq_failed_of_product_nested_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hmem : piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action))
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (hnestedFc : G.cComponents piece = [piece])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger) = false)
    (hnestedKeptH :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        larger = false)
    (hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G
          NodeSet.full piece (NodeSet.diff NodeSet.full piece)
          (observationalJointTerm S) =
        IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger)
        (.marginalize
          (NodeSet.diff larger
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger)))
          (chainProduct NodeSet.full larger)) =
        IdentificationOutcome.failed fail := by
  rcases identifyFuel_eq_failed_of_product_nested_restrict G q hex hmem
      hnestedKept hnestedFc hsingle hany hcont hnested with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G larger piece
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (chainProduct NodeSet.full larger) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G larger piece
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (chainProduct NodeSet.full larger) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      have hinter :
          NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              larger =
            NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger := by
        funext i
        simp [NodeSet.inter]
      have hexL' :
          NodeSet.isEmpty
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              larger) = false := by
        simpa [hinter] using hexL
      have hkeptH' :
          NodeSet.equal
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger)
                  larger))
              (NodeSet.inter piece larger))
            larger = false := by
        simpa [hinter] using hnestedKeptH
      refine ⟨n, ?_⟩
      have hshrunk :=
        identifyFuel_eq_failed_of_shrink n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)
          (chainProduct NodeSet.full larger) hexL' hkeptH' hsucc
      simpa [hinter] using hshrunk

/--
A first product split, nested 4.3 restriction, then ancestral shrink,
with remaining that nested `An(piece)` and free side
`remaining \ (V \ piece)`, yields a hedge for the original query once
that remaining set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.diff NodeSet.full piece))
          (NodeSet.inter piece NodeSet.full))
        NodeSet.full = true)
    (_hnestedFc : G.cComponents piece = [piece])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c piece) = false)
    (_hcont :
      G.containingCComponent NodeSet.full piece = some larger)
    (_hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger) = false)
    (_hnestedKeptH :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        larger = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger)) = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            fail.remaining)) = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut : fail.free i = true := by
      simpa [failedHedgeSelection] using hi
    have hp : piece i = true := by
      have hi' : NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            fail.remaining) i = true := by
        simpa [hfreeR] using hcut
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hi'
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hr : fail.remaining i with
          | false =>
              simp [hp, hr] at hi'
          | true =>
              simp [hp, hr] at hi'
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, and nested ancestral
shrink, a further product split unpacks as an ID run on one free
c-component of `An(piece)` inside that 4.3 host, with action
`An(piece) \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_shrink_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece larger : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
            larger)
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              (G.ancestralSet larger
                (GraphMutilation.bar
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger))
                (NodeSet.inter piece larger))))
          (NodeSet.inter piece
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger))))
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger)) = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger)))) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
            larger)
          (.marginalize
            (NodeSet.diff larger
              (G.ancestralSet larger
                (GraphMutilation.bar
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger))
                (NodeSet.inter piece larger)))
            (chainProduct NodeSet.full larger)) =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger))
            subpiece
            (NodeSet.diff
              (G.ancestralSet larger
                (GraphMutilation.bar
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger))
                (NodeSet.inter piece larger))
              subpiece)
            (.marginalize
              (NodeSet.diff larger
                (G.ancestralSet larger
                  (GraphMutilation.bar
                    (NodeSet.inter
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        NodeSet.full)
                      larger))
                  (NodeSet.inter piece larger)))
              (chainProduct NodeSet.full larger)) =
            IdentificationOutcome.failed fail := by
  let nestedAn :=
    G.ancestralSet larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  exact identifyFuel_eq_failed_of_product_of G nestedAn piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
      larger)
    (.marginalize
      (NodeSet.diff larger nestedAn) (chainProduct NodeSet.full larger))
    (by simpa [nestedAn] using hexN)
    (by simpa [nestedAn] using hkeptN)
    (by simpa [nestedAn] using hfcN)
    (by simpa [nestedAn] using hinner)

/--
A first product split, nested 4.3 restriction, nested ancestral shrink,
then a product split, with remaining `An(piece)` inside the 4.3 host
and free side the failing subpiece, yields a hedge for the original
query once that ancestral set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let nestedAn :=
    G.ancestralSet larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            nestedAn)) := by
    have hfcN' :
        G.cComponents
          (NodeSet.diff nestedAn
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              nestedAn)) =
          inner :: inner2 :: innerRest := by
      simpa [nestedAn] using hfcN
    rw [hfcN']
    exact hmemS
  have hhost : NodeSet.Subset nestedAn larger :=
    ancestralSet_subset G larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hn : nestedAn i with
          | false =>
              simp [hp, hn] at hcut
          | true =>
              have hl : larger i = true := hhost i hn
              simp [hp, hn, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, and nested ancestral
shrink, a further 4.3 restriction unpacks as the ID run on the containing
c-component of `piece` inside `An(piece)`, with action
`((V \ piece) ∩ larger ∩ An(piece)) ∩ host`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_shrink_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S} {piece larger host : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
            larger)
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              (G.ancestralSet larger
                (GraphMutilation.bar
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger))
                (NodeSet.inter piece larger))))
          (NodeSet.inter piece
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger))))
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger)) = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger)))) =
        [piece])
    (hsingleN :
      G.isSingleCComponent
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger)) = false)
    (hanyN :
      (G.cComponents
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontN :
      G.containingCComponent
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger))
          (NodeSet.inter piece larger))
        piece = some host)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
            larger)
          (.marginalize
            (NodeSet.diff larger
              (G.ancestralSet larger
                (GraphMutilation.bar
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      NodeSet.full)
                    larger))
                (NodeSet.inter piece larger)))
            (chainProduct NodeSet.full larger)) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
              larger)
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger)))
          host)
        (chainProduct
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          host) =
        IdentificationOutcome.failed fail := by
  let nestedAn :=
    G.ancestralSet larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  exact identifyFuel_eq_failed_of_restrict_of G nestedAn piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
      larger)
    (.marginalize
      (NodeSet.diff larger nestedAn) (chainProduct NodeSet.full larger))
    (by simpa [nestedAn] using hexN)
    (by simpa [nestedAn] using hkeptN)
    (by simpa [nestedAn] using hfcN)
    (by simpa [nestedAn] using hsingleN)
    (by simpa [nestedAn] using hanyN)
    (by simpa [nestedAn] using hcontN)
    (by simpa [nestedAn] using hinner)

/--
A first product split, nested 4.3 restriction, nested ancestral shrink,
then 4.3 onto the containing c-component of `piece` inside `An(piece)`,
with remaining that inner host and free side `piece`, yields a hedge
for the original query once that host meets `X` and is ancestral of `Y`
in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece _larger host : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, and nested 4.3
restriction, a further product split unpacks as an ID run on one free
c-component of that 4.3 host, with action `host \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host piece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          host) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host))
          (NodeSet.inter piece host))
        host = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          (chainProduct kept host) =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G host subpiece
            (NodeSet.diff host subpiece)
            (chainProduct kept host) =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G host piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
      host)
    (chainProduct kept host) hexN hkeptN hfcN hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
then a product split, with remaining that 4.3 host and free side the
failing subpiece, yields a hedge for the original query once that host
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece kept host subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hhost : NodeSet.Subset host kept)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hh : host i with
          | false =>
              simp [hp, hh] at hcut
          | true =>
              have hk : kept i = true := hhost i hh
              simp [hp, hh, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, and nested 4.3
restriction, a further 4.3 restriction unpacks as the ID run on the
containing c-component of the free singleton inside that host, with
action `((V \ piece) ∩ kept ∩ host) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host piece seed host2 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          host) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host))
          (NodeSet.inter piece host))
        host = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) =
        [seed])
    (hsingleN : G.isSingleCComponent host = false)
    (hanyN :
      (G.cComponents host).any
        (fun c => NodeSet.equal c seed) = false)
    (hcontN : G.containingCComponent host seed = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          (chainProduct kept host) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)
          host2)
        (chainProduct host host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G host piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
      host)
    (chainProduct kept host) hexN hkeptN hfcN hsingleN hanyN hcontN hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
then 4.3 onto the containing c-component of the free singleton, with
remaining that inner host and free side `piece`, yields a hedge for the
original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, and nested 4.3
restriction, a further ancestral shrink unpacks as the ID run on
`An(piece)` inside that 4.3 host, with action `(V \ piece) ∩ kept ∩ host`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host piece : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          host) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host))
          (NodeSet.inter piece host))
        host = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          (chainProduct kept host) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host))
          (NodeSet.inter piece host))
        piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
          host)
        (.marginalize
          (NodeSet.diff host
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                      kept)
                    host)
                  host))
              (NodeSet.inter piece host)))
          (chainProduct kept host)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G host piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
      host)
    (chainProduct kept host) hexN hkeptN hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
then a nested ancestral shrink, with remaining `An(piece)` inside that
4.3 host and free side `piece`, yields a hedge for the original query
once that ancestral set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece nestedAn : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested 4.3
restriction, and nested ancestral shrink, a further product split
unpacks as an ID run on one free c-component of `An(piece)` inside that
4.3 host, with action `An(piece) \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_shrink_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host nestedAn piece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            nestedAn)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          (.marginalize
            (NodeSet.diff host nestedAn) (chainProduct kept host)) =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G nestedAn subpiece
            (NodeSet.diff nestedAn subpiece)
            (.marginalize
              (NodeSet.diff host nestedAn) (chainProduct kept host)) =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G nestedAn piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
      host)
    (.marginalize
      (NodeSet.diff host nestedAn) (chainProduct kept host))
    hexN hkeptN hfcN hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
nested ancestral shrink, then a product split, with remaining
`An(piece)` inside that 4.3 host and free side the failing subpiece,
yields a hedge for the original query once that ancestral set meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece kept host nestedAn subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            nestedAn)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hAn : NodeSet.Subset nestedAn host)
    (hhost : NodeSet.Subset host kept)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            nestedAn)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hn : nestedAn i with
          | false =>
              simp [hp, hn] at hcut
          | true =>
              have hh : host i = true := hAn i hn
              have hk : kept i = true := hhost i hh
              simp [hp, hn, hh, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested 4.3
restriction, and nested ancestral shrink, a further 4.3 restriction
unpacks as the ID run on the containing c-component of the free
singleton inside `An(piece)`, with action
`((V \ piece) ∩ kept ∩ host ∩ An(piece)) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_shrink_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host nestedAn piece seed host2 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            nestedAn)) =
        [seed])
    (hsingleN : G.isSingleCComponent nestedAn = false)
    (hanyN :
      (G.cComponents nestedAn).any
        (fun c => NodeSet.equal c seed) = false)
    (hcontN : G.containingCComponent nestedAn seed = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          (.marginalize
            (NodeSet.diff host nestedAn) (chainProduct kept host)) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            nestedAn)
          host2)
        (chainProduct nestedAn host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G nestedAn piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
      host)
    (.marginalize
      (NodeSet.diff host nestedAn) (chainProduct kept host))
    hexN hkeptN hfcN hsingleN hanyN hcontN hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
nested ancestral shrink, then 4.3 onto the containing c-component of
the free singleton inside `An(piece)`, with remaining that inner host
and free side `piece`, yields a hedge for the original query once that
host meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested 4.3
restriction, and nested product split, a further 4.3 restriction unpacks
as the ID run on the containing c-component of the failing subpiece,
with action `(host \ subpiece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_product_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host subpiece host2 : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host subpiece) host) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host subpiece) host))
          (NodeSet.inter subpiece host))
        host = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.diff host subpiece) host)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent host = false)
    (hany2 :
      (G.cComponents host).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 : G.containingCComponent host subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host subpiece (NodeSet.diff host subpiece)
          (chainProduct kept host) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff host subpiece) host) host2)
        (chainProduct host host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G host subpiece
    (chainProduct kept host) hexP2 hnestedKept2 hnestedFc2 hsingle2 hany2
    hcont2 hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
nested product split, then 4.3 onto the containing c-component of the
failing subpiece, with remaining that inner host and free side the
subpiece, yields a hedge for the original query once that host meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece kept host subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hhost : NodeSet.Subset host kept)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hh : host i with
          | false =>
              simp [hp, hh] at hcut
          | true =>
              have hk : kept i = true := hhost i hh
              simp [hp, hh, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested 4.3
restriction, and nested product split, a further ancestral shrink
unpacks as the ID run on `An(subpiece)` inside that 4.3 host, with
action `host \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host subpiece : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host subpiece) host) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host subpiece) host))
          (NodeSet.inter subpiece host))
        host = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host subpiece (NodeSet.diff host subpiece)
          (chainProduct kept host) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host subpiece) host))
          (NodeSet.inter subpiece host))
        subpiece (NodeSet.diff host subpiece)
        (.marginalize
          (NodeSet.diff host
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host subpiece) host))
              (NodeSet.inter subpiece host)))
          (chainProduct kept host)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G host subpiece
    (chainProduct kept host) hexP2 hnestedKept2 hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
nested product split, then a nested ancestral shrink, with remaining
`An(subpiece)` inside that 4.3 host and free side the subpiece, yields a
hedge for the original query once that ancestral set meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece kept host subpiece nestedAn : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hhost : NodeSet.Subset host kept)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hh : host i with
          | false =>
              simp [hp, hh] at hcut
          | true =>
              have hk : kept i = true := hhost i hh
              simp [hp, hh, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested ancestral
shrink, and nested product split, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the failing subpiece inside
`An(piece)`, with action `(An(piece) \ subpiece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_shrink_product_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn subpiece host2 : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent nestedAn = false)
    (hany2 :
      (G.cComponents nestedAn).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 : G.containingCComponent nestedAn subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff nestedAn subpiece)
          (.marginalize
            (NodeSet.diff larger nestedAn) (chainProduct NodeSet.full larger)) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) host2)
        (chainProduct nestedAn host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G nestedAn subpiece
    (.marginalize
      (NodeSet.diff larger nestedAn) (chainProduct NodeSet.full larger))
    hexP2 hnestedKept2 hnestedFc2 hsingle2 hany2 hcont2 hinner

/--
A first product split, nested 4.3 restriction, nested ancestral shrink,
nested product split, then 4.3 onto the containing c-component of the
failing subpiece, with remaining that inner host and free side the
subpiece, yields a hedge for the original query once that host meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let nestedAn :=
    G.ancestralSet larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            nestedAn)) := by
    have hfcN' :
        G.cComponents
          (NodeSet.diff nestedAn
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              nestedAn)) =
          inner :: inner2 :: innerRest := by
      simpa [nestedAn] using hfcN
    rw [hfcN']
    exact hmemS
  have hhost : NodeSet.Subset nestedAn larger :=
    ancestralSet_subset G larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hn : nestedAn i with
          | false =>
              simp [hp, hn] at hcut
          | true =>
              have hl : larger i = true := hhost i hn
              simp [hp, hn, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested ancestral
shrink, and nested product split, a further ancestral shrink unpacks as
the ID run on `An(subpiece)` inside `An(piece)`, with action
`An(piece) \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_shrink_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn subpiece : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff nestedAn subpiece)
          (.marginalize
            (NodeSet.diff larger nestedAn) (chainProduct NodeSet.full larger)) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        subpiece (NodeSet.diff nestedAn subpiece)
        (.marginalize
          (NodeSet.diff nestedAn
            (G.ancestralSet nestedAn
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
              (NodeSet.inter subpiece nestedAn)))
          (.marginalize
            (NodeSet.diff larger nestedAn) (chainProduct NodeSet.full larger))) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G nestedAn subpiece
    (.marginalize
      (NodeSet.diff larger nestedAn) (chainProduct NodeSet.full larger))
    hexP2 hnestedKept2 hinner

/--
A first product split, nested 4.3 restriction, nested ancestral shrink,
nested product split, then a nested ancestral shrink, with remaining
`An(subpiece)` inside `An(piece)` and free side the subpiece, yields a
hedge for the original query once that ancestral set meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece nestedAn2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet larger
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger))
            (NodeSet.inter piece larger))
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                    NodeSet.full)
                  larger))
              (NodeSet.inter piece larger)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let nestedAn :=
    G.ancestralSet larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            nestedAn)) := by
    have hfcN' :
        G.cComponents
          (NodeSet.diff nestedAn
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full)
                larger)
              nestedAn)) =
          inner :: inner2 :: innerRest := by
      simpa [nestedAn] using hfcN
    rw [hfcN']
    exact hmemS
  have hhost : NodeSet.Subset nestedAn larger :=
    ancestralSet_subset G larger
      (GraphMutilation.bar
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full)
          larger))
      (NodeSet.inter piece larger)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full)
              larger)
            nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hn : nestedAn i with
          | false =>
              simp [hp, hn] at hcut
          | true =>
              have hl : larger i = true := hhost i hn
              simp [hp, hn, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested ancestral
shrink, and nested 4.3 restriction, a further product split unpacks as
an ID run on one free c-component of that inner host, with action
`host \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_shrink_restrict_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn host piece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
              nestedAn)
            host)
          host) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                  nestedAn)
                host)
              host))
          (NodeSet.inter piece host))
        host = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                nestedAn)
              host)
            host)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
              nestedAn)
            host)
          (chainProduct nestedAn host) =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G host subpiece
            (NodeSet.diff host subpiece)
            (chainProduct nestedAn host) =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G host piece
    (NodeSet.inter
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
        nestedAn)
      host)
    (chainProduct nestedAn host) hexN hkeptN hfcN hinner

/--
A first product split, nested 4.3 restriction, nested ancestral shrink,
nested 4.3 restriction, then a product split, with remaining that inner
host and free side the failing subpiece, yields a hedge for the original
query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger nestedAn host subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                nestedAn)
              host)
            host)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hinner : NodeSet.Subset host nestedAn)
    (hAn : NodeSet.Subset nestedAn larger)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                nestedAn)
              host)
            host)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                nestedAn)
              host)
            host) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hh : host i with
          | false =>
              simp [hp, hh] at hcut
          | true =>
              have hn : nestedAn i = true := hinner i hh
              have hl : larger i = true := hAn i hn
              simp [hp, hh, hn, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested ancestral
shrink, and nested 4.3 restriction, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the free singleton inside
that inner host, with action
`((V \ piece) ∩ larger ∩ An(piece) ∩ host) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_shrink_restrict_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn host piece seed host2 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
              nestedAn)
            host)
          host) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                  nestedAn)
                host)
              host))
          (NodeSet.inter piece host))
        host = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                nestedAn)
              host)
            host)) =
        [seed])
    (hsingleN : G.isSingleCComponent host = false)
    (hanyN :
      (G.cComponents host).any
        (fun c => NodeSet.equal c seed) = false)
    (hcontN : G.containingCComponent host seed = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
              nestedAn)
            host)
          (chainProduct nestedAn host) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                nestedAn)
              host)
            host)
          host2)
        (chainProduct host host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G host piece
    (NodeSet.inter
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
        nestedAn)
      host)
    (chainProduct nestedAn host) hexN hkeptN hfcN hsingleN hanyN hcontN
    hinner

/--
A first product split, nested 4.3 restriction, nested ancestral shrink,
nested 4.3 restriction, then 4.3 onto the containing c-component of the
free singleton, with remaining that inner host and free side `piece`,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink_restrict_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested ancestral
shrink, and nested 4.3 restriction, a further ancestral shrink unpacks
as the ID run on `An(piece)` inside that inner host, with action
`(V \ piece) ∩ larger ∩ An(piece) ∩ host`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_shrink_restrict_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn host piece : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
              nestedAn)
            host)
          host) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                  nestedAn)
                host)
              host))
          (NodeSet.inter piece host))
        host = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
              nestedAn)
            host)
          (chainProduct nestedAn host) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
                  nestedAn)
                host)
              host))
          (NodeSet.inter piece host))
        piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
            nestedAn)
          host)
        (.marginalize
          (NodeSet.diff host
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        larger)
                      nestedAn)
                    host)
                  host))
              (NodeSet.inter piece host)))
          (chainProduct nestedAn host)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G host piece
    (NodeSet.inter
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) larger)
        nestedAn)
      host)
    (chainProduct nestedAn host) hexN hkeptN hinner

/--
A first product split, nested 4.3 restriction, nested ancestral shrink,
nested 4.3 restriction, then a nested ancestral shrink, with remaining
`An(piece)` inside that inner host and free side `piece`, yields a hedge
for the original query once that ancestral set meets `X` and is ancestral
of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_shrink_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece nestedAn2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested 4.3
restriction, and nested 4.3 restriction, a further product split unpacks
as an ID run on one free c-component of that inner host, with action
`host2 \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_restrict_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host host2 piece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host2)
          host2) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                  host)
                host2)
              host2))
          (NodeSet.inter piece host2))
        host2 = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff host2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host2)
            host2)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host2 piece
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host2)
          (chainProduct host host2) =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G host2 subpiece
            (NodeSet.diff host2 subpiece)
            (chainProduct host host2) =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G host2 piece
    (NodeSet.inter
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
        host)
      host2)
    (chainProduct host host2) hexN hkeptN hfcN hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
nested 4.3 restriction, then a product split, with remaining that inner
host and free side the failing subpiece, yields a hedge for the original
query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece kept host host2 subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff host2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host2)
            host2)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hinner : NodeSet.Subset host2 host)
    (hAn : NodeSet.Subset host kept)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff host2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host2)
            host2)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff host2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host2)
            host2) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hh : host2 i with
          | false =>
              simp [hp, hh] at hcut
          | true =>
              have hn : host i = true := hinner i hh
              have hk : kept i = true := hAn i hn
              simp [hp, hh, hn, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested 4.3
restriction, and nested 4.3 restriction, a further 4.3 restriction
unpacks as the ID run on the containing c-component of the free
singleton inside that inner host, with action
`((V \ piece) ∩ kept ∩ host ∩ host2) ∩ host3`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_restrict_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host host2 piece seed host3 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host2)
          host2) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                  host)
                host2)
              host2))
          (NodeSet.inter piece host2))
        host2 = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff host2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host2)
            host2)) =
        [seed])
    (hsingleN : G.isSingleCComponent host2 = false)
    (hanyN :
      (G.cComponents host2).any
        (fun c => NodeSet.equal c seed) = false)
    (hcontN : G.containingCComponent host2 seed = some host3)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host2 piece
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host2)
          (chainProduct host host2) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host3 piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                host)
              host2)
            host2)
          host3)
        (chainProduct host2 host3) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G host2 piece
    (NodeSet.inter
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
        host)
      host2)
    (chainProduct host host2) hexN hkeptN hfcN hsingleN hanyN hcontN
    hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
nested 4.3 restriction, then 4.3 onto the containing c-component of the
free singleton, with remaining that inner host and free side `piece`,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_restrict_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece host3 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host3 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested 4.3
restriction, and nested 4.3 restriction, a further ancestral shrink
unpacks as the ID run on `An(piece)` inside that inner host, with
action `(V \ piece) ∩ kept ∩ host ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_restrict_restrict_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept host host2 piece : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host2)
          host2) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                  host)
                host2)
              host2))
          (NodeSet.inter piece host2))
        host2 = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host2 piece
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
              host)
            host2)
          (chainProduct host host2) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet host2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
                  host)
                host2)
              host2))
          (NodeSet.inter piece host2))
        piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
            host)
          host2)
        (.marginalize
          (NodeSet.diff host2
            (G.ancestralSet host2
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        kept)
                      host)
                    host2)
                  host2))
              (NodeSet.inter piece host2)))
          (chainProduct host host2)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G host2 piece
    (NodeSet.inter
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)
        host)
      host2)
    (chainProduct host host2) hexN hkeptN hinner

/--
A first product split, nested ancestral shrink, nested 4.3 restriction,
nested 4.3 restriction, then a nested ancestral shrink, with remaining
`An(piece)` inside that inner host and free side `piece`, yields a hedge
for the original query once that ancestral set meets `X` and is ancestral
of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_restrict_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece nestedAn2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hp : piece i = true := by
      simpa [failedHedgeSelection, hsub] using hi
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY


end Causality
end Thesis
