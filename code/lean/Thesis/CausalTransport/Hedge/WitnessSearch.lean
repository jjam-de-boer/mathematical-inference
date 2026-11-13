import Thesis.CausalTransport.Hedge.ReadoutGeometry
import Thesis.Causality.CForestConstruction

namespace Thesis
namespace Causality

open Probability

/-!
# Constructing hedge witnesses from actual finite search data

Successful Boolean tests supply the complete fields of a `HedgeWitness`:
two connected forests, their common roots, the original action/outcome
coordinates and constructive root-to-outcome reachability. The executable
search retains its supplied failure record and enumerates actual selections;
a returned witness is never chosen from a bare proposition.

The search wrapper and its recognition/completeness lemmas are independent
of which identification recursion produced that record. They do not assert
that every failure supplies passing tests, nor that a hedge by itself already
comes with semantic countermodels. Those are separate extractor and semantic
theorems, supplied by current recursive failure extraction and countermodel
construction.
-/

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

end Causality
end Thesis
