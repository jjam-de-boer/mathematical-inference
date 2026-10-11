import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

open Probability

/-!
# Quarantined legacy identification recursion

This module intentionally preserves a refuted algorithm, its exact branch
equations, and its action-free-output invariant.  The positive front-door
fixture in `Examples.IdentificationRegression` proves that one successful
output has the wrong causal value.  These definitions must therefore never
be used as the ordinary joint or conditional identification interface.

Only the explicitly qualified `Legacy.identifyFuel`,
`Legacy.identifyJoint`, and `Legacy.identifyConditional` names are provided.
There are no aliases restoring their former public names and no global
`open Legacy`.  Modern clients import the shared `IdentificationSearch`
module and the corrected current-kernel programs without importing this
historical implementation.

The surrounding theorem names are retained to avoid silently changing the
meaning of existing historical traces and certified special cases.  Their
statements now visibly refer to `Legacy` programs.  They certify exactly
the property stated, such as control flow or syntactic action-freedom; they
do not assert the legacy algorithm's general semantic soundness.
-/

/--
One fuel-bounded syntactic ID step on a current remaining vertex set and a
recursive input expression `current`.  After c-component restriction, that
input need not be the host's ordinary observational marginal.

The intended branch skeleton follows Shpitser–Pearl 2006, function ID;
the present semantic limitations are recorded after the list:

1. empty action — marginalize to the outcome;
2. discard non-ancestors of `Y` in `G_{\overline{X}}`;
3. `C(G \ X)` has two or more pieces — product of subproblems, then
   marginalize `V \ (Y ∪ X)`;
4. unique free c-component `S`:
   4.1 `C(G) = {G}` — fail (hedge);
   4.2 `S` is already a c-component of `G` — chain-rule expression;
   4.3 `S ⊂ S' ∈ C(G)` — recurse on `G_{S'}` with the restricted action
       `X ∩ S'` and the chain-rule joint on `S'`.

The finite control flow is proved total in `Completeness`, but this is not
yet a generally certified implementation of the published ID algorithm.
`Examples.FrontDoorIdentification` in `IdentificationRegression` proves a
positive compatible counterexample to one returned formula.  Ancestral
shrinking in the incoming-cut graph and extraction of factors independently
of `current` must be revisited before an exact-output success compiler can
be inhabited.  An `identified` constructor alone is not a semantic
identification certificate.
-/
def Legacy.identifyFuel (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S) : IdentificationOutcome S :=
  match fuel with
  | 0 => .unfinished
  | fuel + 1 =>
      let identifyNext := Legacy.identifyFuel fuel
      let y := NodeSet.inter outcome remaining
      let x := NodeSet.inter action remaining
      if NodeSet.isEmpty x then
        .identified (.marginalize (NodeSet.diff remaining y) current)
      else
        let kept := G.ancestralSet remaining (GraphMutilation.bar x) y
        if NodeSet.equal kept remaining then
          let free := NodeSet.diff remaining x
          let freeComponents := G.cComponents free
          match freeComponents with
          | [] =>
              .identified (.marginalize remaining current)
          | [component] =>
              if G.isSingleCComponent remaining then
                .failed ⟨remaining, component⟩
              else if (G.cComponents remaining).any (fun piece =>
                  NodeSet.equal piece component) then
                .identified
                  (.marginalize (NodeSet.diff component y)
                    (chainProduct remaining component))
              else
                match G.containingCComponent remaining component with
                | some larger =>
                    identifyNext G larger outcome (NodeSet.inter x larger)
                      (chainProduct remaining larger)
                | none =>
                    .unfinished
          | _ :: _ :: _ =>
              IdentificationOutcome.combine
                (freeComponents.map (fun component =>
                  identifyNext G remaining component
                    (NodeSet.diff remaining component) current))
                (fun terms =>
                  .marginalize
                    (NodeSet.diff remaining (NodeSet.union y x))
                    (productTerms terms))
        else
          identifyNext G kept outcome action
            (.marginalize (NodeSet.diff remaining kept) current)

/-- Legacy top-level ID on the full observed graph.  Its general output
correctness is refuted by the positive front-door regression; the continuing
completeness development uses `identifyJointKernel` from
`IdentificationKernel` instead.  This entry point remains for the checked
legacy trace library and its already certified special cases. -/
def Legacy.identifyJoint (G : ObservedGraph S) (q : JointKernelQuery S) :
    IdentificationOutcome S :=
  Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome q.action
    (observationalJointTerm S)

/--
Historical Bayes-only fallback: run the legacy joint recursion on the
numerator and denominator, then divide.  It inherits the legacy joint
engine's refuted general correctness and is not a sound general IDC API.
The empty-action theorem below remains a checked special case.  The actual
conditional engine is `identifyConditionalKernel`, with recursive rule-2
exchanges and a denominator marginalized from its identified numerator.
-/
def Legacy.identifyConditional (G : ObservedGraph S)
    (q : ConditionalKernelQuery S) : IdentificationOutcome S :=
  match Legacy.identifyJoint G q.jointNumerator, Legacy.identifyJoint G q.jointDenominator with
  | .identified numerator, .identified denominator =>
      .identified (.divide numerator denominator)
  | .failed seed, _ => .failed seed
  | _, .failed seed => .failed seed
  | _, _ => .unfinished

/--
Empty-action queries reduce in one step to an observational marginal of
`P(V)`.  Completeness of this branch is the trivial ID base case.
-/
theorem identifyJoint_of_empty_action (G : ObservedGraph S)
    (q : JointKernelQuery S) (emptyAction : NodeSet.isEmpty q.action = true) :
    Legacy.identifyJoint G q =
      .identified
        (.marginalize (NodeSet.diff NodeSet.full q.outcome)
          (observationalJointTerm S)) := by
  simp [Legacy.identifyJoint, identificationFuel, Legacy.identifyFuel, emptyAction,
    NodeSet.inter_full_right]

/--
Empty-action conditional queries reduce by IDC's Bayes step: identify
the two joints `P(Y, Z)` and `P(Z)`, then divide.  Completeness of this
branch is the empty-action base case of IDC.
-/
theorem identifyConditional_of_empty_action (G : ObservedGraph S)
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    Legacy.identifyConditional G q =
      IdentificationOutcome.identified
        (.divide
          (.marginalize
            (NodeSet.diff NodeSet.full
              (NodeSet.union q.outcome q.condition))
            (observationalJointTerm S))
          (.marginalize
            (NodeSet.diff NodeSet.full q.condition)
            (observationalJointTerm S))) := by
  have hnum :=
    identifyJoint_of_empty_action G q.jointNumerator emptyAction
  have hden :=
    identifyJoint_of_empty_action G q.jointDenominator emptyAction
  simp only [Legacy.identifyConditional]
  rw [hnum, hden]
  simp [ConditionalKernelQuery.jointNumerator,
    ConditionalKernelQuery.jointDenominator]

/--
The empty-local-action ID step, at any remaining set.  Top-level
`identifyJoint_of_empty_action` is the instance `remaining = V`.
-/
theorem identifyFuel_eq_identified_of_empty_action
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = true) :
    Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff remaining (NodeSet.inter outcome remaining))
          current) := by
  simp [Legacy.identifyFuel, hex]

/--
No free c-component means the working remaining set lies inside the
local action, so ID returns the current expression marginalized off
every remaining vertex.
-/
theorem identifyFuel_eq_identified_of_empty_free
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) = []) :
    Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize remaining current) := by
  simp [Legacy.identifyFuel, hex, hkept, hfc]

/--
Every successful ID formula is action-free: the recursion starts from `P(V)`
and only composes observational kernels, products, quotients, and
marginals.  That is the syntactic half of a published joint certificate.
-/
theorem identifyFuel_identified_actionFree
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hcur : current.ActionFree)
    {term : ProbabilityTerm S}
    (h : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.identified term) :
    term.ActionFree := by
  induction fuel generalizing remaining outcome action current term with
  | zero =>
      simp [Legacy.identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, hex] at h
          subst h
          exact hcur
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [Legacy.identifyFuel, hex, hkept] at h
              exact ih
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                outcome action
                (.marginalize
                  (NodeSet.diff remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)))
                  current)
                hcur h
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [Legacy.identifyFuel, hex, hkept, hfc] at h
                  subst h
                  exact hcur
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle] at h
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                              subst h
                              exact chainProduct_actionFree remaining
                                component
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  exact ih larger outcome
                                    (NodeSet.inter
                                      (NodeSet.inter action remaining)
                                      larger)
                                    (chainProduct remaining larger)
                                    (chainProduct_actionFree remaining larger)
                                    h
                  | cons component2 rest2 =>
                      simp [Legacy.identifyFuel, hex, hkept, hfc] at h
                      refine IdentificationOutcome.combine_identified_actionFree
                        _ _ ?_ ?_ h
                      · intro terms hterms
                        exact productTerms_actionFree terms hterms
                      · intro t ht
                        simp [List.mem_cons] at ht
                        rcases ht with h1 | hrest
                        · exact ih remaining component
                            (NodeSet.diff remaining component) current hcur
                            h1.symm
                        · rcases hrest with h2 | ⟨piece, _, hEq⟩
                          · exact ih remaining component2
                              (NodeSet.diff remaining component2) current
                              hcur h2.symm
                          · exact ih remaining piece
                              (NodeSet.diff remaining piece) current hcur hEq

/--
ID failure always occurs on a remaining set that is a single c-component
of the working graph.  The failed remaining set is contained in the
remaining set of the call that produced it.
-/
theorem identifyFuel_eq_failed
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    G.isSingleCComponent fail.remaining = true ∧
      NodeSet.Subset fail.remaining remaining := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [Legacy.identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [Legacy.identifyFuel, hex, hkept] at h
              have nested :=
                ih
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  h
              exact ⟨nested.1, NodeSet.Subset.trans nested.2
                (ancestralSet_subset G remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))⟩
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [Legacy.identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          exact ⟨hsingle, fun _i hi => hi⟩
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  have nested :=
                                    ih larger outcome
                                      (NodeSet.inter
                                        (NodeSet.inter action remaining)
                                        larger)
                                      (chainProduct remaining larger) h
                                  exact ⟨nested.1, NodeSet.Subset.trans nested.2
                                    (containingCComponent_subset_host G
                                      remaining component hcont)⟩
                  | cons component2 rest2 =>
                      simp [Legacy.identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                Legacy.identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

/--
The free side recorded at a hedge failure is a listed c-component of some
host still inside the working remaining set.  That host is `remaining \ X`
at an immediate 4.1 fail, and is preserved by ancestral restriction, 4.3
c-component restriction, and product recursion.
-/
theorem identifyFuel_eq_failed_free
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    NodeSet.Subset fail.free fail.remaining ∧
      Exists fun host =>
        Exists fun root =>
          host root = true ∧
            fail.free = G.cComponentOf host root ∧
              NodeSet.Subset host remaining := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [Legacy.identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [Legacy.identifyFuel, hex, hkept] at h
              have nested :=
                ih
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  h
              constructor
              · exact nested.1
              · rcases nested.2 with ⟨host, root, hroot, hdef, hsub⟩
                exact ⟨host, root, hroot, hdef,
                  NodeSet.Subset.trans hsub
                    (ancestralSet_subset G remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining))⟩
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [Legacy.identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          constructor
                          · intro i hi
                            have hmem :
                                component ∈
                                  G.cComponents
                                    (NodeSet.diff remaining
                                      (NodeSet.inter action remaining)) := by
                              simp [hfc]
                            rcases cComponents_mem G _ hmem with
                              ⟨root, _, hdef⟩
                            have hi' :
                                G.cComponentOf
                                  (NodeSet.diff remaining
                                    (NodeSet.inter action remaining))
                                  root i = true := by
                              simpa [hdef] using hi
                            exact NodeSet.diff_subset_left _ _ i
                              (cComponentOf_subset G _ hi')
                          · have hmem :
                                component ∈
                                  G.cComponents
                                    (NodeSet.diff remaining
                                      (NodeSet.inter action remaining)) := by
                              simp [hfc]
                            rcases cComponents_mem G _ hmem with
                              ⟨root, hroot, hdef⟩
                            exact ⟨NodeSet.diff remaining
                                (NodeSet.inter action remaining),
                              root, hroot, hdef, NodeSet.diff_subset_left _ _⟩
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  have nested :=
                                    ih larger outcome
                                      (NodeSet.inter
                                        (NodeSet.inter action remaining)
                                        larger)
                                      (chainProduct remaining larger) h
                                  constructor
                                  · exact nested.1
                                  · rcases nested.2 with
                                      ⟨host, root, hroot, hdef, hsub⟩
                                    exact ⟨host, root, hroot, hdef,
                                      NodeSet.Subset.trans hsub
                                        (containingCComponent_subset_host G
                                          remaining component hcont)⟩
                  | cons component2 rest2 =>
                      simp [Legacy.identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                Legacy.identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

/--
A 4.1 failure always records a nonempty cut `remaining \ free`.  The local
action of that call is nonempty and lives in the cut, because the free
side is a c-component of `remaining \ X`.
-/
theorem identifyFuel_eq_failed_cut_nonempty
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    NodeSet.isEmpty
      (NodeSet.diff fail.remaining fail.free) = false := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [Legacy.identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [Legacy.identifyFuel, hex, hkept] at h
              exact ih
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                outcome action
                (.marginalize
                  (NodeSet.diff remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)))
                  current)
                h
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [Legacy.identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          rcases (NodeSet.isEmpty_eq_false_iff
                              (NodeSet.inter action remaining)).mp hex with
                            ⟨i, hi⟩
                          have hrem : remaining i = true :=
                            NodeSet.inter_subset_right action remaining i hi
                          have hhost :
                              NodeSet.diff remaining
                                (NodeSet.inter action remaining) i = false := by
                            simp [NodeSet.diff, hi]
                          have hfree : component i = false := by
                            cases hf : component i with
                            | false => rfl
                            | true =>
                                have hmem :
                                    component ∈
                                      G.cComponents
                                        (NodeSet.diff remaining
                                          (NodeSet.inter action remaining)) :=
                                  by simp [hfc]
                                rcases cComponents_mem G _ hmem with
                                  ⟨root, _, hdef⟩
                                have inHost :
                                    NodeSet.diff remaining
                                      (NodeSet.inter action remaining) i =
                                      true :=
                                  cComponentOf_subset G _
                                    (by simpa [hdef] using hf)
                                exact False.elim
                                  (Bool.false_ne_true
                                    (hhost.symm.trans inHost))
                          exact (NodeSet.isEmpty_eq_false_iff _).mpr
                            ⟨i, Bool.and_eq_true_iff.mpr
                              ⟨hrem, by simp [hfree]⟩⟩
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  exact ih larger outcome
                                    (NodeSet.inter
                                      (NodeSet.inter action remaining)
                                      larger)
                                    (chainProduct remaining larger) h
                  | cons component2 rest2 =>
                      simp [Legacy.identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                Legacy.identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

theorem identifyJoint_eq_failed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    G.isSingleCComponent fail.remaining = true :=
  (identifyFuel_eq_failed (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h).1

theorem identifyJoint_eq_failed_cut_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty (NodeSet.diff fail.remaining fail.free) = false :=
  identifyFuel_eq_failed_cut_nonempty (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h

theorem identifyJoint_identified_actionFree
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {term : ProbabilityTerm S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.identified term) :
    term.ActionFree :=
  identifyFuel_identified_actionFree (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S)
    (observationalJointTerm_actionFree S) h

theorem identifyConditional_identified_actionFree
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    {term : ProbabilityTerm S}
    (h : Legacy.identifyConditional G q = IdentificationOutcome.identified term) :
    term.ActionFree := by
  cases hnum : Legacy.identifyJoint G q.jointNumerator with
  | identified numerator =>
      cases hden : Legacy.identifyJoint G q.jointDenominator with
      | identified denominator =>
          simp [Legacy.identifyConditional, hnum, hden] at h
          subst h
          exact ⟨identifyJoint_identified_actionFree G q.jointNumerator hnum,
            identifyJoint_identified_actionFree G q.jointDenominator hden⟩
      | failed _ => simp [Legacy.identifyConditional, hnum, hden] at h
      | unfinished => simp [Legacy.identifyConditional, hnum, hden] at h
  | failed _ =>
      cases hden : Legacy.identifyJoint G q.jointDenominator <;>
        simp [Legacy.identifyConditional, hnum, hden] at h
  | unfinished =>
      cases hden : Legacy.identifyJoint G q.jointDenominator <;>
        simp [Legacy.identifyConditional, hnum, hden] at h

/--
Every ID failure is a 4.1 site for some local outcome and local action:
the recorded remaining set is ancestral of that local outcome in
`G_{\overline{remaining \ free}}`, and the free side is exactly
`remaining` minus the local cut.  Product recursion instantiates the
local query with a c-component of `G \ X` and action `V \ S_i`; ancestral
restriction and 4.3 keep the outer outcome.
-/
theorem identifyFuel_eq_failed_site
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    Exists fun localOutcome =>
      Exists fun localAction =>
        NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter localOutcome fail.remaining))
            fail.remaining = true ∧
          NodeSet.equal fail.free
              (NodeSet.diff fail.remaining
                (NodeSet.inter localAction fail.remaining)) = true := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [Legacy.identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [Legacy.identifyFuel, hex, hkept] at h
              exact ih
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                outcome action
                (.marginalize
                  (NodeSet.diff remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)))
                  current)
                h
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [Legacy.identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          have hcomp : component =
                              NodeSet.diff remaining
                                (NodeSet.inter action remaining) :=
                            cComponents_eq_of_singleton G _ hfc
                          refine ⟨outcome, action, ?_, ?_⟩
                          · have hcut :
                                NodeSet.diff remaining component =
                                  NodeSet.inter action remaining := by
                              rw [hcomp, NodeSet.diff_diff]
                              exact NodeSet.inter_eq_of_subset
                                (NodeSet.inter_subset_right action remaining)
                            have heq :=
                              (NodeSet.equal_eq_true_iff _ _).mp hkept
                            have heq' :
                                G.ancestralSet remaining
                                  (GraphMutilation.bar
                                    (NodeSet.diff remaining component))
                                  (NodeSet.inter outcome remaining) =
                                  remaining := by
                              simpa [hcut] using heq
                            exact (NodeSet.equal_eq_true_iff _ _).mpr heq'
                          · exact (NodeSet.equal_eq_true_iff _ _).mpr hcomp
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [Legacy.identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  exact ih larger outcome
                                    (NodeSet.inter
                                      (NodeSet.inter action remaining)
                                      larger)
                                    (chainProduct remaining larger) h
                  | cons component2 rest2 =>
                      simp [Legacy.identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                Legacy.identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

theorem identifyJoint_eq_failed_site
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun localOutcome =>
      Exists fun localAction =>
        NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter localOutcome fail.remaining))
            fail.remaining = true ∧
          NodeSet.equal fail.free
              (NodeSet.diff fail.remaining
                (NodeSet.inter localAction fail.remaining)) = true :=
  identifyFuel_eq_failed_site (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h

/--
An immediate 4.1 hedge: the working remaining set is already ancestral of
the local outcome in `G_{\overline{X}}`, that remaining set is a single
c-component, and `G \ X` has a unique free component.  The failure record
is exactly that remaining set together with `remaining \ X`.
-/
theorem identifyFuel_eq_failed_immediate_query_site
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S} {component : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = true)
    (h : Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    fail.remaining = remaining ∧
      fail.free = component ∧
        NodeSet.equal fail.free
            (NodeSet.diff fail.remaining
              (NodeSet.inter action fail.remaining)) = true ∧
          NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter outcome fail.remaining))
            fail.remaining = true := by
  simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle] at h
  cases h
  have hcomp : component =
      NodeSet.diff remaining (NodeSet.inter action remaining) :=
    cComponents_eq_of_singleton G _ hfc
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact (NodeSet.equal_eq_true_iff _ _).mpr hcomp
  · have hcut :
        NodeSet.diff remaining component =
          NodeSet.inter action remaining := by
      rw [hcomp, NodeSet.diff_diff]
      exact NodeSet.inter_eq_of_subset
        (NodeSet.inter_subset_right action remaining)
    have heq := (NodeSet.equal_eq_true_iff _ _).mp hkept
    have heq' :
        G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.diff remaining component))
          (NodeSet.inter outcome remaining) = remaining := by
      simpa [hcut] using heq
    exact (NodeSet.equal_eq_true_iff _ _).mpr heq'

/--
A failing ID call whose remaining set is not ancestral of the local
outcome first restricts to that ancestral set.  Product-nested 4.1 and
the top-level shrink branch both instantiate this unpacking.
-/
theorem identifyFuel_eq_failed_of_shrink
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false)
    (h : Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    Legacy.identifyFuel fuel G
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        outcome action
        (.marginalize
          (NodeSet.diff remaining
            (G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining)))
          current) =
      IdentificationOutcome.failed fail := by
  simp [Legacy.identifyFuel, hex, hkept] at h
  exact h

/--
A 4.3 restriction whose containing c-component is found unpacks as the
nested ID run on that host, with action `X ∩ remaining ∩ larger`.
Immediate 4.1 and the chain-product success branch are excluded by the
Boolean hypotheses.
-/
theorem identifyFuel_eq_failed_of_restrict
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S} {component larger : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent remaining component = some larger)
    (h : Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    Legacy.identifyFuel fuel G larger outcome
        (NodeSet.inter (NodeSet.inter action remaining) larger)
        (chainProduct remaining larger) =
      IdentificationOutcome.failed fail := by
  simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle, hany, hcont] at h
  exact h

/--
A product split with at least two free c-components unpacks as a nested
ID run on one of those pieces, with action `remaining \ piece`.
-/
theorem identifyFuel_eq_failed_of_product
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        component :: component2 :: rest)
    (h : Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        Legacy.identifyFuel fuel G remaining piece
            (NodeSet.diff remaining piece) current =
          IdentificationOutcome.failed fail := by
  simp [Legacy.identifyFuel, hex, hkept, hfc] at h
  have hin :
      IdentificationOutcome.failed fail ∈
        (component :: component2 :: rest).map (fun piece =>
          Legacy.identifyFuel fuel G remaining piece
            (NodeSet.diff remaining piece) current) :=
    IdentificationOutcome.combine_eq_failed _ _ h
  rcases List.mem_map.mp hin with ⟨piece, hmem, hEq⟩
  exact ⟨piece, hmem, hEq⟩

/--
A successful ID call whose remaining set is not ancestral of the local
outcome first restricts to that ancestral set.  Dual of
`identifyFuel_eq_failed_of_shrink`.
-/
theorem identifyFuel_eq_identified_of_shrink
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {term : ProbabilityTerm S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false)
    (h : Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified term) :
    Legacy.identifyFuel fuel G
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        outcome action
        (.marginalize
          (NodeSet.diff remaining
            (G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining)))
          current) =
      IdentificationOutcome.identified term := by
  simp [Legacy.identifyFuel, hex, hkept] at h
  exact h

/--
Ancestral restriction whose nested remaining set no longer meets the
action is the empty-action base case on that ancestral set: ID returns
the observational marginal of the already-shrunk current expression.
Needs two fuel units (one shrink, one empty-action step).
-/
theorem identifyFuel_eq_identified_of_shrink_empty
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false)
    (hexNested :
      NodeSet.isEmpty
        (NodeSet.inter action
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))) = true) :
    Legacy.identifyFuel (fuel + 2) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff
            (G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining))
            (NodeSet.inter outcome
              (G.ancestralSet remaining
                (GraphMutilation.bar (NodeSet.inter action remaining))
                (NodeSet.inter outcome remaining))))
          (.marginalize
            (NodeSet.diff remaining
              (G.ancestralSet remaining
                (GraphMutilation.bar (NodeSet.inter action remaining))
                (NodeSet.inter outcome remaining)))
            current)) := by
  have hshrink :
      Legacy.identifyFuel (fuel + 1 + 1) G remaining outcome action current =
        Legacy.identifyFuel (fuel + 1) G
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          outcome action
          (.marginalize
            (NodeSet.diff remaining
              (G.ancestralSet remaining
                (GraphMutilation.bar (NodeSet.inter action remaining))
                (NodeSet.inter outcome remaining)))
            current) := by
    simp [Legacy.identifyFuel, hex, hkept]
  have hempty :=
    identifyFuel_eq_identified_of_empty_action fuel G
      (G.ancestralSet remaining
        (GraphMutilation.bar (NodeSet.inter action remaining))
        (NodeSet.inter outcome remaining))
      outcome action
      (.marginalize
        (NodeSet.diff remaining
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining)))
        current)
      hexNested
  rw [show fuel + 2 = fuel + 1 + 1 from rfl, hshrink, hempty]

/--
ID step 4.2: the unique free c-component is already a c-component of the
working remaining graph, so the answer is the chain-rule factorization
`Q[S]` marginalized to the local outcome.
-/
theorem identifyFuel_eq_identified_of_chain
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {component : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = true) :
    Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff component (NodeSet.inter outcome remaining))
          (chainProduct remaining component)) := by
  simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle, hany]

/--
A 4.3 restriction whose containing c-component is found unpacks as the
nested ID run on that host.  Dual of `identifyFuel_eq_failed_of_restrict`.
-/
theorem identifyFuel_eq_identified_of_restrict
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {term : ProbabilityTerm S} {component larger : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent remaining component = some larger)
    (h : Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified term) :
    Legacy.identifyFuel fuel G larger outcome
        (NodeSet.inter (NodeSet.inter action remaining) larger)
        (chainProduct remaining larger) =
      IdentificationOutcome.identified term := by
  simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle, hany, hcont] at h
  exact h

/--
A 4.3 restriction whose nested remaining set misses the restricted
action is the empty-action base case on that host, with current
expression the chain-rule joint on the host.  Needs two fuel units.
-/
theorem identifyFuel_eq_identified_of_restrict_empty
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {component larger : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent remaining component = some larger)
    (hexNested :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter action remaining) larger) = true) :
    Legacy.identifyFuel (fuel + 2) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff larger (NodeSet.inter outcome larger))
          (chainProduct remaining larger)) := by
  have hrestrict :
      Legacy.identifyFuel (fuel + 1 + 1) G remaining outcome action current =
        Legacy.identifyFuel (fuel + 1) G larger outcome
          (NodeSet.inter (NodeSet.inter action remaining) larger)
          (chainProduct remaining larger) := by
    simp [Legacy.identifyFuel, hex, hkept, hfc, hsingle, hany, hcont]
  have hexNested' :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.inter action remaining) larger)
          larger) = true := by
    simpa [NodeSet.inter_idempotent_right] using hexNested
  have hempty :=
    identifyFuel_eq_identified_of_empty_action fuel G larger outcome
      (NodeSet.inter (NodeSet.inter action remaining) larger)
      (chainProduct remaining larger) hexNested'
  rw [show fuel + 2 = fuel + 1 + 1 from rfl, hrestrict, hempty]

/--
A product split with at least two free c-components unpacks as identified
runs on those pieces, assembled by `productTerms` and marginalized off
`V \ (Y ∪ X)` in the working remaining set.  Dual of
`identifyFuel_eq_failed_of_product`.
-/
theorem identifyFuel_eq_identified_of_product
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {term : ProbabilityTerm S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        component :: component2 :: rest)
    (h : Legacy.identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified term) :
    Exists fun terms =>
      term =
          ProbabilityTerm.marginalize
            (NodeSet.diff remaining
              (NodeSet.union (NodeSet.inter outcome remaining)
                (NodeSet.inter action remaining)))
            (productTerms terms) ∧
        (component :: component2 :: rest).map (fun piece =>
            Legacy.identifyFuel fuel G remaining piece
              (NodeSet.diff remaining piece) current) =
          terms.map IdentificationOutcome.identified := by
  simp [Legacy.identifyFuel, hex, hkept, hfc] at h
  rcases IdentificationOutcome.combine_eq_identified _ _ h with
    ⟨terms, hmap, hterm⟩
  exact ⟨terms, hterm, hmap⟩

/--
If the recorded remaining set is still the working remaining set of the
call that failed, and the free side is `remaining \ X` for that call's
action, then the remaining set is ancestral of the call's outcome in
`G_{\overline{cut}}`.  Ancestral restriction cannot produce this
situation: it strictly shrinks the working remaining set.  Immediate 4.1,
4.3 with `larger` restored to `remaining`, and product with an unshrunk
remaining set all have `hkept`, which is the required ancestry.
-/
theorem identifyFuel_eq_failed_query_of_remaining_eq
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining remaining = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter action fail.remaining)) = true) :
    NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter outcome fail.remaining))
        fail.remaining = true := by
  cases fuel with
  | zero =>
      simp [Legacy.identifyFuel] at h
  | succ fuel =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [Legacy.identifyFuel, hex, hkept] at h
              have nested :=
                identifyFuel_eq_failed fuel G
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  h
              have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
              have hsubset :
                  NodeSet.Subset remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)) := by
                intro i hi
                have hi' : fail.remaining i = true := by
                  rw [heqR]
                  exact hi
                exact nested.2 i hi'
              have hsubset' :=
                ancestralSet_subset G remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining)
              have hkeptTrue :
                  NodeSet.equal
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining))
                    remaining = true :=
                Bool.and_eq_true_iff.mpr
                  ⟨(NodeSet.subsetBool_eq_true_iff _ _).mpr hsubset',
                    (NodeSet.subsetBool_eq_true_iff _ _).mpr hsubset⟩
              exact False.elim (Bool.false_ne_true (hkept.symm.trans hkeptTrue))
          | true =>
              have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
              have hfreeEq := (NodeSet.equal_eq_true_iff _ _).mp hfree
              have hfreeEq' :
                  fail.free =
                    NodeSet.diff remaining
                      (NodeSet.inter action remaining) := by
                rw [hfreeEq, heqR]
              have hcut :
                  NodeSet.diff remaining fail.free =
                    NodeSet.inter action remaining := by
                rw [hfreeEq', NodeSet.diff_diff]
                exact NodeSet.inter_eq_of_subset
                  (NodeSet.inter_subset_right action remaining)
              have hkeptEq := (NodeSet.equal_eq_true_iff _ _).mp hkept
              have hanc :
                  G.ancestralSet fail.remaining
                    (GraphMutilation.bar
                      (NodeSet.diff fail.remaining fail.free))
                    (NodeSet.inter outcome fail.remaining) =
                    fail.remaining := by
                rw [heqR, hcut]
                exact hkeptEq
              exact (NodeSet.equal_eq_true_iff _ _).mpr hanc

theorem identifyJoint_eq_failed_free_subset
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.Subset fail.free fail.remaining :=
  (identifyFuel_eq_failed_free (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h).1

theorem failedHedgeSelection_cut_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty
      (NodeSet.diff (failedHedgeSelection fail).large
        (failedHedgeSelection fail).small) = false :=
  identifyJoint_eq_failed_cut_nonempty G q hfail

/--
If every original-action vertex in the remaining set lies in the cut,
the free side avoids the original action.
-/
theorem failedHedgeSelection_avoids_action_of_cut
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hcut :
      NodeSet.Subset (NodeSet.inter q.action fail.remaining)
        (NodeSet.diff fail.remaining fail.free)) :
    NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
      true :=
  (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun i hi => by
    have hrem : fail.remaining i = true :=
      identifyJoint_eq_failed_free_subset G q hfail i hi
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hinter : NodeSet.inter q.action fail.remaining i = true :=
          Bool.and_eq_true_iff.mpr ⟨ha, hrem⟩
        have hcuti := hcut i hinter
        have hfreeF : fail.free i = false := by
          have parts := Bool.and_eq_true_iff.mp hcuti
          cases hf : fail.free i with
          | false =>
              rfl
          | true =>
              have : (!fail.free i) = true := parts.2
              simp [hf] at this
        exact False.elim (Bool.false_ne_true (hfreeF.symm.trans hi)))

/--
If the nonempty cut sits inside the original action, the remaining set
meets that action.
-/
theorem failedHedgeSelection_meets_action_of_cut
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hsub :
      NodeSet.Subset (NodeSet.diff fail.remaining fail.free) q.action) :
    NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true := by
  rcases (NodeSet.isEmpty_eq_false_iff _).mp
      (failedHedgeSelection_cut_nonempty G q hfail) with ⟨i, hi⟩
  have hrem : fail.remaining i = true :=
    NodeSet.diff_subset_left fail.remaining fail.free i hi
  have hact : q.action i = true := hsub i hi
  exact (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨i, hrem, hact⟩

end Causality
end Thesis
