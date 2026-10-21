import Thesis.CausalTransport.CompletenessCertificates
import Thesis.CausalTransport.Hedge.ReadoutGeometry

namespace Thesis
namespace Causality

open Probability

/-!
# Failure records and finite hedge extraction

Retains the original finite failure records, graph tests and failure-to-hedge
transport lemmas. No new engine failure case is added by this extraction.

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

/-! ## Failure records and finite hedge extraction -/

theorem failedHedgeSelection_small_single
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    G.isSingleCComponent (failedHedgeSelection fail).small = true := by
  rcases (identifyJoint_eq_failed_free G q hfail).2 with ⟨root, hroot, hEq⟩
  exact isSingleCComponent_of_self G fail.free hroot hEq

theorem failedHedgeSelection_small_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty (failedHedgeSelection fail).small = false :=
  isSingleCComponent_nonempty G _
    (failedHedgeSelection_small_single G q hfail)

theorem failedHedgeSelection_small_subset
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.subsetBool (failedHedgeSelection fail).small
      (failedHedgeSelection fail).large = true :=
  (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (identifyJoint_eq_failed_free G q hfail).1

theorem failedHedgeSelection_child_wellFormed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    childWellFormedBool (failedHedgeSelection fail).large
      (failedHedgeSelection fail).child = true :=
  closedForestChild_wellFormed fail.remaining fail.free
    (identifyJoint_eq_failed_free G q hfail).1

theorem failedHedgeSelection_childClosed
    (fail : IdentificationFail S) :
    childClosedBool (failedHedgeSelection fail).small
      (failedHedgeSelection fail).child = true :=
  closedForestChild_childClosed fail.remaining fail.free

theorem failedHedgeSelection_large_single
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    G.isSingleCComponent (failedHedgeSelection fail).large = true :=
  identifyJoint_eq_failed G q hfail

theorem failedHedgeSelection_large_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty (failedHedgeSelection fail).large = false :=
  isSingleCComponent_nonempty G _
    (failedHedgeSelection_large_single G q hfail)

/--
Vertex tests of the failure-record selection, once the remaining set
still meets the original action.
-/
theorem failedHedgeSelection_largeVerticesReady
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true) :
    largeVerticesReady G q (failedHedgeSelection fail).large = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, hmeets⟩
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · have hempty := failedHedgeSelection_large_nonempty G q hfail
    cases h : NodeSet.isEmpty (failedHedgeSelection fail).large
    · rfl
    · exact False.elim (Bool.false_ne_true (hempty.symm.trans h))
  · exact failedHedgeSelection_large_single G q hfail

/--
Small-side tests of the failure-record selection that do not mention the
original action or kept-sink inclusion.  Child-closure is by construction
of `closedForestChild`.
-/
theorem failedHedgeSelection_smallForestCore
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    ((!NodeSet.isEmpty (failedHedgeSelection fail).small) &&
      G.isSingleCComponent (failedHedgeSelection fail).small &&
      NodeSet.subsetBool (failedHedgeSelection fail).small
        (failedHedgeSelection fail).large &&
      childClosedBool (failedHedgeSelection fail).small
        (failedHedgeSelection fail).child) = true := by
  have hempty := failedHedgeSelection_small_nonempty G q hfail
  have hneg : (!NodeSet.isEmpty (failedHedgeSelection fail).small) = true := by
    cases h : NodeSet.isEmpty (failedHedgeSelection fail).small
    · rfl
    · exact False.elim (Bool.false_ne_true (hempty.symm.trans h))
  refine Bool.and_eq_true_iff.mpr ⟨?_, failedHedgeSelection_childClosed fail⟩
  refine Bool.and_eq_true_iff.mpr ⟨?_,
    failedHedgeSelection_small_subset G q hfail⟩
  exact Bool.and_eq_true_iff.mpr ⟨hneg,
    failedHedgeSelection_small_single G q hfail⟩


/--
Kept sinks of the failure-record forest lie in the free side once the
remaining set is ancestral of the outcome in `G_{\overline{cut}}` and
the cut avoids the outcome.  Every cut vertex then has a directed
successor in the remaining set.
-/
theorem failedHedgeSelection_keptSinks_of_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true)
    (hnotY :
      NodeSet.Disjoint (NodeSet.diff fail.remaining fail.free)
        (NodeSet.inter q.outcome fail.remaining)) :
    NodeSet.subsetBool
      (keptSinks (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child)
      (failedHedgeSelection fail).small = true :=
  (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (closedForestChild_keptSinks_subset fail.remaining fail.free
      (fun parent hL hS => by
        have hcut :
            NodeSet.diff fail.remaining fail.free parent = true :=
          Bool.and_eq_true_iff.mpr ⟨hL, by simp [hS]⟩
        have hancP :
            G.ancestorOfWithin fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter q.outcome fail.remaining) parent = true :=
          ancestorOfWithin_of_ancestralSet G fail.remaining _ _ hanc hL
        have hnot : NodeSet.inter q.outcome fail.remaining parent = false :=
          hnotY parent hcut
        rcases ancestorOfWithin_first_successor G fail.remaining
            (GraphMutilation.bar
              (NodeSet.diff fail.remaining fail.free))
            (NodeSet.inter q.outcome fail.remaining) hancP hnot with
          ⟨child, hchild, hedge, _⟩
        have hdir : S.directed parent child = true :=
          ((observedDirectedEdge_bar G
              (NodeSet.diff fail.remaining fail.free)).mp hedge).1
        exact ⟨child,
          (mem_directedChildren_iff fail.remaining parent child).mpr
            ⟨hchild, hdir⟩⟩))

/--
Kept sinks lie in the free component once the remaining set is ancestral
of that component in `G_{\overline{cut}}`.  The cut is disjoint from
`free` by construction, so this does not need `cut ⊆ X`.
-/
theorem failedHedgeSelection_keptSinks_of_free_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true) :
    NodeSet.subsetBool
      (keptSinks (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child)
      (failedHedgeSelection fail).small = true :=
  (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (closedForestChild_keptSinks_subset fail.remaining fail.free
      (fun parent hL hS => by
        have hcut :
            NodeSet.diff fail.remaining fail.free parent = true :=
          Bool.and_eq_true_iff.mpr ⟨hL, by simp [hS]⟩
        have hancP :
            G.ancestorOfWithin fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter fail.free fail.remaining) parent = true :=
          ancestorOfWithin_of_ancestralSet G fail.remaining _ _ hanc hL
        have hnotP :
            NodeSet.inter fail.free fail.remaining parent = false := by
          have hfreeF : fail.free parent = false :=
            NodeSet.Disjoint.diff_right fail.remaining fail.free parent hcut
          simp [NodeSet.inter, hfreeF]
        rcases ancestorOfWithin_first_successor G fail.remaining
            (GraphMutilation.bar
              (NodeSet.diff fail.remaining fail.free))
            (NodeSet.inter fail.free fail.remaining) hancP hnotP with
          ⟨child, hchild, hedge, _⟩
        have hdir : S.directed parent child = true :=
          ((observedDirectedEdge_bar G
              (NodeSet.diff fail.remaining fail.free)).mp hedge).1
        exact ⟨child,
          (mem_directedChildren_iff fail.remaining parent child).mpr
            ⟨hchild, hdir⟩⟩))

/--
The remaining small-side Boolean tests, once the original action avoids
the free component and the kept sinks lie in that component.
-/
theorem failedHedgeSelection_smallForestReady_of
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true)
    (hkept :
      NodeSet.subsetBool
        (keptSinks (failedHedgeSelection fail).large
          (failedHedgeSelection fail).child)
        (failedHedgeSelection fail).small = true) :
    smallForestReady G q (failedHedgeSelection fail).large
      (failedHedgeSelection fail).child
      (failedHedgeSelection fail).small = true := by
  have core := failedHedgeSelection_smallForestCore G q hfail
  have hABCD := Bool.and_eq_true_iff.mp core
  have hABC := Bool.and_eq_true_iff.mp hABCD.1
  have hAB := Bool.and_eq_true_iff.mp hABC.1
  simp [smallForestReady, hAB.1, hAB.2, hABC.2, hdisj, hABCD.2, hkept]


theorem failedHedgeSelection_rootsReach_of_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    rootsReachOutcomeBool q
      (keptSinks (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child) = true :=
  rootsReachOutcomeBool_of_ancestralSet G q fail.remaining
    (keptSinks fail.remaining (closedForestChild fail.remaining fail.free))
    hanc
    (keptSinks_subset _ _)

/--
Boolean hedge tests of the failure-record selection, once the remaining
set meets the original action, kept roots reach the outcome, and the
small-side forest tests pass.
-/
theorem failedHedgeSelection_tests_of
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hreach :
      rootsReachOutcomeBool q
        (keptSinks (failedHedgeSelection fail).large
          (failedHedgeSelection fail).child) = true)
    (hsmall :
      smallForestReady G q (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child
        (failedHedgeSelection fail).small = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true := by
  have hverts :=
    failedHedgeSelection_largeVerticesReady G q hfail hmeets
  have hwell := failedHedgeSelection_child_wellFormed G q hfail
  have hchild : largeChildReady G q (failedHedgeSelection fail).large
      (failedHedgeSelection fail).child = true := by
    simp [largeChildReady, hwell, hreach]
  simp [hedgeTestsHold, hverts, hchild, hsmall]

/--
When the recorded free side is `remaining \ (remaining ∩ X)`, the cut
is exactly the original action inside the remaining set.
-/
theorem failedHedgeSelection_cut_eq_of_free
    (fail : IdentificationFail S) (action : NodeSet S)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter action fail.remaining)) = true) :
    NodeSet.diff fail.remaining fail.free =
      NodeSet.inter action fail.remaining := by
  have eq := (NodeSet.equal_eq_true_iff _ _).mp hfree
  rw [eq, NodeSet.diff_diff]
  exact NodeSet.inter_eq_of_subset
    (NodeSet.inter_subset_right action fail.remaining)

/--
A cut inside the original action is disjoint from the original
outcome, hence from remaining outcome vertices.
-/
theorem failedHedgeSelection_notY_of_cut
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hsub :
      NodeSet.Subset (NodeSet.diff fail.remaining fail.free) q.action) :
    NodeSet.Disjoint (NodeSet.diff fail.remaining fail.free)
      (NodeSet.inter q.outcome fail.remaining) :=
  fun i hi => by
    have hact : q.action i = true := hsub i hi
    have hout : q.outcome i = false := q.action_outcome_disjoint i hact
    simp [NodeSet.inter, hout]

/--
Boolean hedge tests of the failure-record selection, when the cut is the
original action inside the remaining set and that remaining set is
ancestral of the original outcome in `G_{\overline{cut}}`.
-/
theorem failedHedgeSelection_tests_of_local_action
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true := by
  have hcut := failedHedgeSelection_cut_eq_of_free fail q.action hfree
  have hsub : NodeSet.Subset (NodeSet.diff fail.remaining fail.free)
      q.action := by
    intro i hi
    have hi' : NodeSet.inter q.action fail.remaining i = true := by
      simpa [hcut] using hi
    exact NodeSet.inter_subset_left q.action fail.remaining i hi'
  have hcutIncl :
      NodeSet.Subset (NodeSet.inter q.action fail.remaining)
        (NodeSet.diff fail.remaining fail.free) := by
    intro i hi
    simpa [hcut] using hi
  have hmeets := failedHedgeSelection_meets_action_of_cut G q hfail hsub
  have hdisj := failedHedgeSelection_avoids_action_of_cut G q hfail hcutIncl
  have hnotY := failedHedgeSelection_notY_of_cut G q hfail hsub
  have hkept :=
    failedHedgeSelection_keptSinks_of_ancestral G q hfail hanc hnotY
  have hsmall :=
    failedHedgeSelection_smallForestReady_of G q hfail hdisj hkept
  have hancBar :
      G.ancestralSet fail.remaining
        (GraphMutilation.bar (NodeSet.inter q.action fail.remaining))
        (NodeSet.inter q.outcome fail.remaining) =
        fail.remaining := by
    have heq := (NodeSet.equal_eq_true_iff _ _).mp hanc
    simpa [hcut] using heq
  have hancAction :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true := by
    have heq :
        G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining) = fail.remaining := by
      rw [← ancestralSet_bar_inter]
      exact hancBar
    exact (NodeSet.equal_eq_true_iff _ _).mpr heq
  have hreach :=
    failedHedgeSelection_rootsReach_of_ancestral G q hfail hancAction
  exact failedHedgeSelection_tests_of G q hfail hmeets hreach hsmall


/-- Unpack the Boolean hedge tests into the `HedgeWitness` fields. -/
def hedgeWitness_of_sets
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (sel : HedgeSelection S)
    (h : hedgeTestsHold G q sel = true) :
    HedgeWitness G q :=
  let hABC := Bool.and_eq_true_iff.mp h
  let hAB := Bool.and_eq_true_iff.mp hABC.1
  let hverts := hAB.1
  let hchildReady := hAB.2
  let hsmall := hABC.2
  let hverts_b := Bool.and_eq_true_iff.mp hverts
  let hverts_a := Bool.and_eq_true_iff.mp hverts_b.1
  let hsingleL := hverts_a.2
  let hmeets := hverts_b.2
  let hwell := (Bool.and_eq_true_iff.mp hchildReady).1
  let hreach := (Bool.and_eq_true_iff.mp hchildReady).2
  let small_e := Bool.and_eq_true_iff.mp hsmall
  let small_d := Bool.and_eq_true_iff.mp small_e.1
  let small_c := Bool.and_eq_true_iff.mp small_d.1
  let small_b := Bool.and_eq_true_iff.mp small_c.1
  let small_a := Bool.and_eq_true_iff.mp small_b.1
  let hsingleS := small_a.2
  let hsubset := small_b.2
  let havoids := small_c.2
  let hclosed := small_d.2
  let hrootsIn := small_e.2
  let large := sel.large
  let small := sel.small
  let child := sel.child
  let hsubP := (NodeSet.subsetBool_eq_true_iff small large).mp hsubset
  let hwellS := childWellFormed_restrict large small child hwell hsubP hclosed
  let sameRoots :
      keptSinks small (restrictChild small child) =
        keptSinks large child :=
    keptSinks_restrict_eq large small child hsubP hclosed
      ((NodeSet.subsetBool_eq_true_iff (keptSinks large child) small).mp
        hrootsIn)
  let actionSeed := NodeSet.getMeeting large q.action hmeets
  let hstart := NodeSet.getMeeting_left hmeets
  let sink := forestSink large child hwell actionSeed hstart
  let hroot : keptSinks large child sink = true :=
    forestSink_kept large child hwell actionSeed hstart
  let rootMem : sink ∈ NodeSet.members (keptSinks large child) :=
    (NodeSet.mem_members_iff (keptSinks large child) sink).mpr hroot
  let anyY :
      (NodeSet.members q.outcome).any (fun y =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S q.action) S.count sink y) = true :=
    (List.all_eq_true.mp hreach) sink rootMem
  let outcomeSeed :=
    listFirstAny (NodeSet.members q.outcome)
      (fun y =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S q.action) S.count sink y)
      anyY
  {
    large := large
    small := small
    roots := keptSinks large child
    child := child
    large_forest := cForest_of_child G large child hsingleL hwell
    small_forest := by
      have F := cForest_of_child G small (restrictChild small child)
        hsingleS hwellS
      exact sameRoots ▸ F
    small_subset_large := hsubP
    large_meets_intervention :=
      (NodeSet.meetsBool_eq_true_iff large q.action).mp hmeets
    small_avoids_intervention :=
      (NodeSet.disjointBool_eq_true_iff small q.action).mp havoids
    roots_reach_outcome :=
      rootsReachOutcome_of_bool q (keptSinks large child) hreach
    actionSeed := actionSeed
    actionSeed_in_large := hstart
    actionSeed_in_action := NodeSet.getMeeting_right hmeets
    outcomeSeed := outcomeSeed
    outcomeSeed_in_outcome :=
      (NodeSet.mem_members_iff q.outcome outcomeSeed).mp
        (listFirstAny_mem (NodeSet.members q.outcome)
          (fun y =>
            FiniteReachability.within finBeq (NodeSet.enumerated S)
              (mutilatedDirected S q.action) S.count sink y)
          anyY)
  }

/--
Executable extraction of a hedge from ID-failure data by finite search over
vertex selections and kept directed children.  Greedy thinning remains
available as lemmas; it is not the extractor.  Returning `none` means no
enumerated selection passed the Boolean tests — search completeness, not
an absence of hedges in the abstract.
-/
def hedgeWitness? (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) : Option (HedgeWitness G q) :=
  match hfound : findHedgeWitnessSets G q fail with
  | none => none
  | some sel =>
      some (hedgeWitness_of_sets G q sel
        (findHedgeWitnessSets_tests G q fail hfound))

/--
The extractor returns a witness exactly when the finite search returns a
selection.  Named-pattern matching in `hedgeWitness?` is definitionally
`Option.map` of that search, so `isSome` is preserved.
-/
theorem hedgeWitness?_isSome_iff_sets
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    (hedgeWitness? G q fail).isSome =
      (findHedgeWitnessSets G q fail).isSome := by
  dsimp [hedgeWitness?]
  split
  · next heq =>
      change false = (findHedgeWitnessSets G q fail).isSome
      rw [heq]
      rfl
  · next _sel heq =>
      change true = (findHedgeWitnessSets G q fail).isSome
      rw [heq]
      rfl

/--
The extractor inhabits a `HedgeWitness` as soon as any enumerated
selection inside `fail.remaining` passes the Boolean tests.  Combined
with search completeness, the remaining ID-failure leaf is to exhibit
such a selection.
-/
theorem hedgeWitness?_eq_some_of_selection
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) (sel : HedgeSelection S)
    (hlarge : NodeSet.Subset sel.large fail.remaining)
    (htests : hedgeTestsHold G q sel = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  rcases findHedgeWitnessSets_eq_some_of_selection G q fail sel hlarge
      htests with ⟨found, hf⟩
  have hsome : (hedgeWitness? G q fail).isSome = true := by
    rw [hedgeWitness?_isSome_iff_sets, hf]
    rfl
  match h : hedgeWitness? G q fail with
  | none =>
      simp [h] at hsome
  | some witness =>
      exact ⟨witness, rfl⟩

theorem hedgeWitness?_eq_some_of_thinned
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S)
    (htests :
      hedgeTestsHold G q (thinnedHedgeSelection G q fail) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_selection G q fail
    (thinnedHedgeSelection G q fail)
    (thinnedHedgeSelection_subset_remaining G q fail) htests

theorem hedgeWitness?_eq_some_of_failed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S)
    (htests : hedgeTestsHold G q (failedHedgeSelection fail) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_selection G q fail
    (failedHedgeSelection fail)
    (failedHedgeSelection_subset_remaining fail) htests

/--
Top-level ID failure with a remaining-local original action yields a
`HedgeWitness` by search completeness.
-/
theorem hedgeWitness?_eq_some_of_failed_local_action
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed G q fail
    (failedHedgeSelection_tests_of_local_action G q hfail hfree hanc)

/--
When the failing site's local outcome and action agree with the original
query on the recorded remaining vertices, the local-action hedge tests
apply to `q` itself.  Product-nested sites typically fail this agreement;
shrink and 4.3 restriction keep it.
-/
theorem failedHedgeSelection_tests_of_site_agrees
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (localOutcome localAction : NodeSet S)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter localAction fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter localOutcome fail.remaining))
        fail.remaining = true)
    (hYeq :
      NodeSet.equal
        (NodeSet.inter localOutcome fail.remaining)
        (NodeSet.inter q.outcome fail.remaining) = true)
    (hXeq :
      NodeSet.equal
        (NodeSet.inter localAction fail.remaining)
        (NodeSet.inter q.action fail.remaining) = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true := by
  have hX :
      NodeSet.inter localAction fail.remaining =
        NodeSet.inter q.action fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp hXeq
  have hY :
      NodeSet.inter localOutcome fail.remaining =
        NodeSet.inter q.outcome fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp hYeq
  have hfreeQ :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true := by
    simpa [hX] using hfree
  have hancQ :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true := by
    simpa [hY] using hanc
  exact failedHedgeSelection_tests_of_local_action G q hfail hfreeQ hancQ

theorem hedgeWitness?_eq_some_of_failed_site_agrees
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (localOutcome localAction : NodeSet S)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter localAction fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter localOutcome fail.remaining))
        fail.remaining = true)
    (hYeq :
      NodeSet.equal
        (NodeSet.inter localOutcome fail.remaining)
        (NodeSet.inter q.outcome fail.remaining) = true)
    (hXeq :
      NodeSet.equal
        (NodeSet.inter localAction fail.remaining)
        (NodeSet.inter q.action fail.remaining) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed G q fail
    (failedHedgeSelection_tests_of_site_agrees G q hfail localOutcome
      localAction hfree hanc hYeq hXeq)

/--
A product-free structural failure trace yields a hedge for the original
top-level query, regardless of how many ancestral-shrink and 4.3-restriction
frames precede its terminal 4.1 failure.

The trace induction in `IdentificationInduction` proves that those two frame
kinds preserve the outcome and action after restriction to `fail.remaining`.
The terminal site's generic 4.1 facts can therefore be transported directly
to `q` and discharged by the common hedge-search theorem above.  Product
frames are excluded explicitly: they replace the local query by a factor and
require the separate free-component ancestry argument developed below.
-/
theorem hedgeWitness?_eq_some_of_productFree_failureTrace
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (trace : JointIdentificationFailureTrace G q fail)
    (productFree : trace.hasNoProductFrame = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hfail :
      Legacy.identifyJoint G q = IdentificationOutcome.failed fail := by
    simpa [Legacy.identifyJoint, JointIdentificationFailureTrace] using
      trace.eq_failed
  let site : IdentificationImmediateFailureSite G fail := trace.immediateSite
  have localFacts := site.local_query_site
  have queryAgreement :=
    trace.immediateSite_query_agrees_of_hasNoProductFrame productFree
  exact hedgeWitness?_eq_some_of_failed_site_agrees G q hfail site.outcome
    site.action localFacts.1 localFacts.2 queryAgreement.1 queryAgreement.2

/--
Hedge tests for the original query when the failure-record forest points
at the recorded free component (the nested 4.1 target) rather than at
`Y` itself.  The remaining set still has to meet `X`, the free side has
to avoid `X`, and vertices of the remaining set still have to reach `Y`
in `G_{\overline{X}}`.  Product-nested 4.1 fails inhabit the free-side
ancestry from `identifyJoint_eq_failed_site` once the local outcome is
that free component.
-/
theorem failedHedgeSelection_tests_of_free_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true :=
  failedHedgeSelection_tests_of G q hfail hmeets
    (failedHedgeSelection_rootsReach_of_ancestral G q hfail hancY)
    (failedHedgeSelection_smallForestReady_of G q hfail hdisj
      (failedHedgeSelection_keptSinks_of_free_ancestral G q hfail
        hancFree))

theorem hedgeWitness?_eq_some_of_failed_free_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed G q fail
    (failedHedgeSelection_tests_of_free_ancestral G q hfail hmeets hdisj
      hancFree hancY)

/--
When the failing site's local outcome is the recorded free component,
site ancestry is free-component ancestry.
-/
theorem failedHedgeSelection_free_ancestral_of_site
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (localOutcome _localAction : NodeSet S)
    (_hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter _localAction fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter localOutcome fail.remaining))
        fail.remaining = true)
    (hEq :
      NodeSet.equal (NodeSet.inter localOutcome fail.remaining)
        (NodeSet.inter fail.free fail.remaining) = true) :
    NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true := by
  have heq :
      NodeSet.inter localOutcome fail.remaining =
        NodeSet.inter fail.free fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp hEq
  simpa [heq] using hanc

/--
Top-level ID failure whose recorded remaining set is still the full
graph, with free side `V \ X`, is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem identifyJoint_eq_failed_query_of_full
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining NodeSet.full = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true :=
  identifyFuel_eq_failed_query_of_remaining_eq (identificationFuel S) G
    NodeSet.full q.outcome q.action (observationalJointTerm S) hfail heq
    hfree

theorem hedgeWitness?_eq_some_of_failed_remaining_eq
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining NodeSet.full = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed_local_action G q hfail hfree
    (identifyJoint_eq_failed_query_of_full G q hfail heq hfree)


end Causality
end Thesis
