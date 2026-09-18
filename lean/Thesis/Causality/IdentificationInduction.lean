import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

open Probability

universe u

/-!
# Structural induction over executable ID searches

`identifyFuel` is structurally recursive on its fuel, but its definition contains
several nested Boolean decisions and a list-valued product branch.  Consequently,
proofs about a search result can easily turn into a manual enumeration of paths
such as “shrink, then product, then restrict, then fail”.  The number of such
path *shapes* grows with the available fuel even though every individual step
comes from the same small collection of ID branches.

This module packages the recursion in three exact trace families:

* `IdentificationFailureTrace` follows the unique path to a hedge failure;
* `IdentificationSuccessTrace` follows a successful path and, at a product
  split, retains aligned recursive traces for every factor; and
* `IdentificationUnfinishedTrace` follows the sentinel to exhausted fuel or a
  missing containing c-component.

Order-sensitive witnesses for `IdentificationOutcome.collect` ensure that a
product trace selects the first failure or sentinel only after all preceding
factors have identified.  Each trace family is proved equivalent to its
corresponding executable result.  Downstream proofs can therefore convert a
result equation into a trace and perform structural induction, proving one
preservation lemma per recursive branch instead of naming every finite stack.

Everything here is constructive.  All selected factors and aligned term lists
are obtained by recursion over concrete lists; no choice principle or excluded
middle is used.
-/

namespace IdentificationOutcome

/-!
## Ordered failures of product factors

Membership in a list of factor outcomes is not enough to explain the result of
`IdentificationOutcome.combine`: the collector stops at the *first* failure or
sentinel.  The relation below retains precisely the missing order information.
It says that `selected` reports `fail`, while every factor preceding `selected`
reports an identified term.  Factors after `selected` are intentionally
unconstrained because the collector never inspects them.
-/

/--
`FirstFailureAt run fail inputs selected` means that `selected` is the first
input in `inputs` whose `run` result prevents successful collection, and that
its result is exactly `failed fail`.

The relation is constructive: it stores the successful terms before the
failure and the failure equation at the selected input.  It does not require
decidable equality on inputs, probability terms, or failure records.
-/
inductive FirstFailureAt {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S)
    (fail : IdentificationFail S) : List α -> α -> Prop
  | here
      (item : α) (rest : List α)
      (result : run item = IdentificationOutcome.failed fail) :
      FirstFailureAt run fail (item :: rest) item
  | afterIdentified
      (item selected : α) (rest : List α)
      (term : ProbabilityTerm S)
      (result : run item = IdentificationOutcome.identified term)
      (tail : FirstFailureAt run fail rest selected) :
      FirstFailureAt run fail (item :: rest) selected

namespace FirstFailureAt

/-- The selected input really does evaluate to the recorded failure. -/
theorem selected_eq_failed {S : ObservedSignature} {α : Type u}
    {run : α -> IdentificationOutcome S} {fail : IdentificationFail S}
    {inputs : List α} {selected : α}
    (path : FirstFailureAt run fail inputs selected) :
    run selected = IdentificationOutcome.failed fail := by
  induction path with
  | here item rest result =>
      exact result
  | afterIdentified item selected rest term result tail tailResult =>
      exact tailResult

/-- The factor selected by an ordered failure path belongs to its input list. -/
theorem mem {S : ObservedSignature} {α : Type u}
    {run : α -> IdentificationOutcome S} {fail : IdentificationFail S}
    {inputs : List α} {selected : α}
    (path : FirstFailureAt run fail inputs selected) :
    selected ∈ inputs := by
  induction path with
  | here item rest result =>
      exact List.mem_cons.mpr (Or.inl rfl)
  | afterIdentified item selected rest term result tail tailMem =>
      exact List.mem_cons.mpr (Or.inr tailMem)

end FirstFailureAt

/--
A failed collection selects an ordered first-failure witness in the original
input list.  Generalizing the accumulator makes the result reusable both for
`combine` and for recursive proofs about `collect` itself.
-/
theorem firstFailureAt_of_collect_map_eq_failed
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (acc : List (ProbabilityTerm S)) {fail : IdentificationFail S}
    (result : collect assemble (inputs.map run) acc =
      IdentificationOutcome.failed fail) :
    Exists fun selected => FirstFailureAt run fail inputs selected := by
  induction inputs generalizing acc with
  | nil =>
      simp [collect] at result
  | cons head tail inductionHypothesis =>
      cases headResult : run head with
      | identified term =>
          have tailResult :
              collect assemble (tail.map run) (term :: acc) =
                IdentificationOutcome.failed fail := by
            simpa [collect, headResult] using result
          rcases inductionHypothesis (term :: acc) tailResult with
            ⟨selected, path⟩
          exact ⟨selected,
            .afterIdentified head selected tail term headResult path⟩
      | failed seed =>
          have seedEq : seed = fail := by
            simpa [collect, headResult] using result
          subst seed
          exact ⟨head, .here head tail headResult⟩
      | unfinished =>
          simp [collect, headResult] at result

/--
An ordered first-failure witness makes collection return that failure,
independently of both the accumulated successful terms and the assembly
function.
-/
theorem collect_map_eq_failed_of_firstFailureAt
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (acc : List (ProbabilityTerm S))
    {fail : IdentificationFail S} {inputs : List α} {selected : α}
    (path : FirstFailureAt run fail inputs selected) :
    collect assemble (inputs.map run) acc =
      IdentificationOutcome.failed fail := by
  induction path generalizing acc with
  | here item rest result =>
      simp [collect, result]
  | afterIdentified item selected rest term result tail tailResult =>
      simpa [collect, result] using tailResult (acc := term :: acc)

/-- `combine` exposes the first failing input, not merely an arbitrary member. -/
theorem firstFailureAt_of_combine_map_eq_failed
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    {fail : IdentificationFail S}
    (result : combine (inputs.map run) assemble =
      IdentificationOutcome.failed fail) :
    Exists fun selected => FirstFailureAt run fail inputs selected :=
  firstFailureAt_of_collect_map_eq_failed run inputs assemble [] result

/-- An ordered first-failure witness reconstructs the result of `combine`. -/
theorem combine_map_eq_failed_of_firstFailureAt
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    {fail : IdentificationFail S} {inputs : List α} {selected : α}
    (path : FirstFailureAt run fail inputs selected) :
    combine (inputs.map run) assemble = IdentificationOutcome.failed fail :=
  collect_map_eq_failed_of_firstFailureAt run assemble [] path

/--
Exact, order-sensitive characterization of a failed factor combination.
-/
theorem combine_map_eq_failed_iff_firstFailureAt
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (fail : IdentificationFail S) :
    combine (inputs.map run) assemble = IdentificationOutcome.failed fail ↔
      Exists fun selected => FirstFailureAt run fail inputs selected :=
  ⟨firstFailureAt_of_combine_map_eq_failed run inputs assemble,
    fun witness => by
      rcases witness with ⟨selected, path⟩
      exact combine_map_eq_failed_of_firstFailureAt run assemble path⟩

/--
Collecting an all-successful list preserves its order when it appends the
newly identified terms after the reverse accumulator.  This is the forward
counterpart of `collect_eq_identified` and is useful when constructing an
identified product result from recursive factor traces.
-/
theorem collect_map_identified
    {S : ObservedSignature}
    (terms acc : List (ProbabilityTerm S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S) :
    collect assemble (terms.map IdentificationOutcome.identified) acc =
      IdentificationOutcome.identified (assemble (acc.reverse ++ terms)) := by
  induction terms generalizing acc with
  | nil =>
      simp [collect]
  | cons head tail inductionHypothesis =>
      simp [collect, inductionHypothesis, List.reverse_cons,
        List.append_assoc]

/-- Combining identified factors applies the assembly function in list order. -/
theorem combine_map_identified
    {S : ObservedSignature}
    (terms : List (ProbabilityTerm S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S) :
    combine (terms.map IdentificationOutcome.identified) assemble =
      IdentificationOutcome.identified (assemble terms) := by
  simpa [combine] using collect_map_identified terms [] assemble

end IdentificationOutcome

/-!
## Ordered unfinished product factors

The `unfinished` sentinel is order-sensitive inside a product: it is returned
only when every preceding factor identified and the selected factor is
unfinished.  A preceding failure would make the product fail instead.  The
ordered witness below is the sentinel analogue of `FirstFailureAt`.
-/

namespace IdentificationOutcome

/-- The selected input is the first non-identified factor and is unfinished. -/
inductive FirstUnfinishedAt {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) : List α -> α -> Prop
  | here
      (item : α) (rest : List α)
      (result : run item = IdentificationOutcome.unfinished) :
      FirstUnfinishedAt run (item :: rest) item
  | afterIdentified
      (item selected : α) (rest : List α)
      (term : ProbabilityTerm S)
      (result : run item = IdentificationOutcome.identified term)
      (tail : FirstUnfinishedAt run rest selected) :
      FirstUnfinishedAt run (item :: rest) selected

namespace FirstUnfinishedAt

/-- The selected factor evaluates to the unfinished sentinel. -/
theorem selected_eq_unfinished {S : ObservedSignature} {α : Type u}
    {run : α -> IdentificationOutcome S}
    {inputs : List α} {selected : α}
    (path : FirstUnfinishedAt run inputs selected) :
    run selected = IdentificationOutcome.unfinished := by
  induction path with
  | here item rest result =>
      exact result
  | afterIdentified item selected rest term result tail tailResult =>
      exact tailResult

/-- The selected unfinished factor belongs to the input list. -/
theorem mem {S : ObservedSignature} {α : Type u}
    {run : α -> IdentificationOutcome S}
    {inputs : List α} {selected : α}
    (path : FirstUnfinishedAt run inputs selected) :
    selected ∈ inputs := by
  induction path with
  | here item rest result =>
      exact List.mem_cons.mpr (Or.inl rfl)
  | afterIdentified item selected rest term result tail tailMem =>
      exact List.mem_cons.mpr (Or.inr tailMem)

end FirstUnfinishedAt

/-- A sentinel result of `collect` exposes its first unfinished input. -/
theorem firstUnfinishedAt_of_collect_map_eq_unfinished
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (acc : List (ProbabilityTerm S))
    (result : collect assemble (inputs.map run) acc =
      IdentificationOutcome.unfinished) :
    Exists fun selected => FirstUnfinishedAt run inputs selected := by
  induction inputs generalizing acc with
  | nil =>
      simp [collect] at result
  | cons head tail inductionHypothesis =>
      cases headResult : run head with
      | identified term =>
          have tailResult :
              collect assemble (tail.map run) (term :: acc) =
                IdentificationOutcome.unfinished := by
            simpa [collect, headResult] using result
          rcases inductionHypothesis (term :: acc) tailResult with
            ⟨selected, path⟩
          exact ⟨selected,
            .afterIdentified head selected tail term headResult path⟩
      | failed fail =>
          simp [collect, headResult] at result
      | unfinished =>
          exact ⟨head, .here head tail headResult⟩

/-- An ordered unfinished input makes collection return the sentinel. -/
theorem collect_map_eq_unfinished_of_firstUnfinishedAt
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (acc : List (ProbabilityTerm S))
    {inputs : List α} {selected : α}
    (path : FirstUnfinishedAt run inputs selected) :
    collect assemble (inputs.map run) acc =
      IdentificationOutcome.unfinished := by
  induction path generalizing acc with
  | here item rest result =>
      simp [collect, result]
  | afterIdentified item selected rest term result tail tailResult =>
      simpa [collect, result] using tailResult (acc := term :: acc)

/-- A sentinel result of `combine` exposes its first unfinished input. -/
theorem firstUnfinishedAt_of_combine_map_eq_unfinished
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (result : combine (inputs.map run) assemble =
      IdentificationOutcome.unfinished) :
    Exists fun selected => FirstUnfinishedAt run inputs selected :=
  firstUnfinishedAt_of_collect_map_eq_unfinished run inputs assemble [] result

/-- An ordered unfinished factor reconstructs the sentinel product result. -/
theorem combine_map_eq_unfinished_of_firstUnfinishedAt
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    {inputs : List α} {selected : α}
    (path : FirstUnfinishedAt run inputs selected) :
    combine (inputs.map run) assemble = IdentificationOutcome.unfinished :=
  collect_map_eq_unfinished_of_firstUnfinishedAt run assemble [] path

/-- Exact, order-sensitive characterization of an unfinished combination. -/
theorem combine_map_eq_unfinished_iff_firstUnfinishedAt
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S) :
    combine (inputs.map run) assemble = IdentificationOutcome.unfinished ↔
      Exists fun selected => FirstUnfinishedAt run inputs selected :=
  ⟨firstUnfinishedAt_of_combine_map_eq_unfinished run inputs assemble,
    fun witness => by
      rcases witness with ⟨selected, path⟩
      exact combine_map_eq_unfinished_of_firstUnfinishedAt run assemble path⟩

end IdentificationOutcome

/--
A structural explanation of an `unfinished` ID result.

There are only two terminal causes: fuel is exhausted, or the unique free
c-component has no containing component in the current remaining graph.
The other constructors propagate one of those causes through ancestral
restriction, c-component restriction, or the first unfinished product factor.
-/
inductive IdentificationUnfinishedTrace {S : ObservedSignature}
    (G : ObservedGraph S) :
    (fuel : Nat) ->
    (remaining outcome action : NodeSet S) ->
    ProbabilityTerm S -> Prop
  | exhausted
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S) :
      IdentificationUnfinishedTrace G 0 remaining outcome action current
  | missingHost
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (component : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (oneFreeComponent :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          [component])
      (severalRemainingComponents :
        G.isSingleCComponent remaining = false)
      (componentNotMaximal :
        (G.cComponents remaining).any
          (fun piece => NodeSet.equal piece component) = false)
      (noContainingComponent :
        G.containingCComponent remaining component = none) :
      IdentificationUnfinishedTrace G (fuel + 1) remaining outcome action current
  | shrink
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (notAncestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = false)
      (nested :
        IdentificationUnfinishedTrace G fuel
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          outcome action
          (.marginalize
            (NodeSet.diff remaining
              (G.ancestralSet remaining
                (GraphMutilation.bar (NodeSet.inter action remaining))
                (NodeSet.inter outcome remaining)))
            current)) :
      IdentificationUnfinishedTrace G (fuel + 1) remaining outcome action current
  | restrict
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (component larger : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (oneFreeComponent :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          [component])
      (severalRemainingComponents :
        G.isSingleCComponent remaining = false)
      (componentNotMaximal :
        (G.cComponents remaining).any
          (fun piece => NodeSet.equal piece component) = false)
      (containingComponent :
        G.containingCComponent remaining component = some larger)
      (nested :
        IdentificationUnfinishedTrace G fuel larger outcome
          (NodeSet.inter (NodeSet.inter action remaining) larger)
          (chainProduct remaining larger)) :
      IdentificationUnfinishedTrace G (fuel + 1) remaining outcome action current
  | product
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (component component2 : NodeSet S)
      (rest : List (NodeSet S))
      (piece : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (freeComponents :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          component :: component2 :: rest)
      (firstUnfinishedFactor :
        IdentificationOutcome.FirstUnfinishedAt
          (fun factor =>
            identifyFuel fuel G remaining factor
              (NodeSet.diff remaining factor) current)
          (component :: component2 :: rest) piece)
      (nested :
        IdentificationUnfinishedTrace G fuel remaining piece
          (NodeSet.diff remaining piece) current) :
      IdentificationUnfinishedTrace G (fuel + 1) remaining outcome action current

namespace IdentificationUnfinishedTrace

/-- Every unfinished trace certifies the sentinel result at its root call. -/
theorem eq_unfinished {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S}
    (trace :
      IdentificationUnfinishedTrace G fuel remaining outcome action current) :
    identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.unfinished := by
  induction trace with
  | exhausted remaining outcome action current =>
      rfl
  | missingHost fuel remaining outcome action current component actionNonempty
      ancestral oneFreeComponent severalRemainingComponents componentNotMaximal
      noContainingComponent =>
      simp [identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        noContainingComponent]
  | shrink fuel remaining outcome action current actionNonempty notAncestral
      nested nestedResult =>
      simpa [identifyFuel, actionNonempty, notAncestral] using nestedResult
  | restrict fuel remaining outcome action current component larger
      actionNonempty ancestral oneFreeComponent severalRemainingComponents
      componentNotMaximal containingComponent nested nestedResult =>
      simpa [identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        containingComponent] using nestedResult
  | product fuel remaining outcome action current component component2 rest
      piece actionNonempty ancestral freeComponents firstUnfinishedFactor nested
      _nestedResult =>
      have combinedResult :=
        IdentificationOutcome.combine_map_eq_unfinished_of_firstUnfinishedAt
          (fun factor =>
            identifyFuel fuel G remaining factor
              (NodeSet.diff remaining factor) current)
          (fun terms =>
            .marginalize
              (NodeSet.diff remaining
                (NodeSet.union
                  (NodeSet.inter outcome remaining)
                  (NodeSet.inter action remaining)))
              (productTerms terms))
          firstUnfinishedFactor
      simpa [identifyFuel, actionNonempty, ancestral, freeComponents] using
        combinedResult

/-- Convert an unfinished executable result into its complete structural cause. -/
theorem of_eq_unfinished {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (result : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.unfinished) :
    IdentificationUnfinishedTrace G fuel remaining outcome action current := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      exact .exhausted remaining outcome action current
  | succ fuel inductionHypothesis =>
      cases actionEmpty :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, actionEmpty] at result
      | false =>
          cases ancestral :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              have nestedResult :
                  identifyFuel fuel G
                      (G.ancestralSet remaining
                        (GraphMutilation.bar
                          (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining))
                      outcome action
                      (.marginalize
                        (NodeSet.diff remaining
                          (G.ancestralSet remaining
                            (GraphMutilation.bar
                              (NodeSet.inter action remaining))
                            (NodeSet.inter outcome remaining)))
                        current) =
                    IdentificationOutcome.unfinished := by
                simpa [identifyFuel, actionEmpty, ancestral] using result
              exact .shrink fuel remaining outcome action current actionEmpty
                ancestral
                (inductionHypothesis
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar
                          (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  nestedResult)
          | true =>
              cases freeComponents :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, actionEmpty, ancestral,
                    freeComponents] at result
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases oneRemainingComponent :
                          G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, actionEmpty, ancestral,
                            freeComponents, oneRemainingComponent] at result
                      | false =>
                          cases componentMaximal :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, actionEmpty, ancestral,
                                freeComponents, oneRemainingComponent,
                                componentMaximal] at result
                          | false =>
                              cases containingComponent :
                                  G.containingCComponent remaining component with
                              | none =>
                                  exact .missingHost fuel remaining outcome action
                                    current component actionEmpty ancestral
                                    freeComponents oneRemainingComponent
                                    componentMaximal containingComponent
                              | some larger =>
                                  have nestedResult :
                                      identifyFuel fuel G larger outcome
                                          (NodeSet.inter
                                            (NodeSet.inter action remaining)
                                            larger)
                                          (chainProduct remaining larger) =
                                        IdentificationOutcome.unfinished := by
                                    simpa [identifyFuel, actionEmpty, ancestral,
                                      freeComponents, oneRemainingComponent,
                                      componentMaximal, containingComponent] using
                                      result
                                  exact .restrict fuel remaining outcome action
                                    current component larger actionEmpty ancestral
                                    freeComponents oneRemainingComponent
                                    componentMaximal containingComponent
                                    (inductionHypothesis larger outcome
                                      (NodeSet.inter
                                        (NodeSet.inter action remaining) larger)
                                      (chainProduct remaining larger)
                                      nestedResult)
                  | cons component2 rest =>
                      have combinedResult :
                          IdentificationOutcome.combine
                            ((component :: component2 :: rest).map
                              (fun factor =>
                                identifyFuel fuel G remaining factor
                                  (NodeSet.diff remaining factor) current))
                            (fun terms =>
                              .marginalize
                                (NodeSet.diff remaining
                                  (NodeSet.union
                                    (NodeSet.inter outcome remaining)
                                    (NodeSet.inter action remaining)))
                                (productTerms terms)) =
                            IdentificationOutcome.unfinished := by
                        simpa [identifyFuel, actionEmpty, ancestral,
                          freeComponents] using result
                      rcases
                          IdentificationOutcome.firstUnfinishedAt_of_combine_map_eq_unfinished
                            (fun factor =>
                              identifyFuel fuel G remaining factor
                                (NodeSet.diff remaining factor) current)
                            (component :: component2 :: rest)
                            (fun terms =>
                              .marginalize
                                (NodeSet.diff remaining
                                  (NodeSet.union
                                    (NodeSet.inter outcome remaining)
                                    (NodeSet.inter action remaining)))
                                (productTerms terms))
                            combinedResult with
                        ⟨piece, firstUnfinishedFactor⟩
                      have nestedResult :=
                        firstUnfinishedFactor.selected_eq_unfinished
                      exact .product fuel remaining outcome action current
                        component component2 rest piece actionEmpty ancestral
                        freeComponents firstUnfinishedFactor
                        (inductionHypothesis remaining piece
                          (NodeSet.diff remaining piece) current nestedResult)

end IdentificationUnfinishedTrace

/--
The executable unfinished sentinel and its two-terminal structural trace are
interchangeable.
-/
theorem identifyFuel_eq_unfinished_iff_unfinishedTrace
    {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S) :
    identifyFuel fuel G remaining outcome action current =
        IdentificationOutcome.unfinished ↔
      IdentificationUnfinishedTrace G fuel remaining outcome action current :=
  ⟨IdentificationUnfinishedTrace.of_eq_unfinished fuel G remaining outcome action
      current,
    IdentificationUnfinishedTrace.eq_unfinished⟩

/--
A structural path from an invocation of `identifyFuel` to its reported failure.

The indices deliberately retain the complete invocation, including `current`.
This makes the trace useful for semantic invariants whose statement changes
when the search marginalizes during `shrink` or replaces the current term by a
chain product during `restrict`.

The `product` case uses `IdentificationOutcome.FirstFailureAt` rather than mere
list membership.  This records that every earlier factor identified before the
selected factor failed, which is exactly the ordering information needed to
reconstruct the parent result.  Consequently, the trace is a self-contained
structural certificate: it does not retain the parent failure equation that it
is intended to certify.
-/
inductive IdentificationFailureTrace {S : ObservedSignature}
    (G : ObservedGraph S) :
    (fuel : Nat) ->
    (remaining outcome action : NodeSet S) ->
    ProbabilityTerm S ->
    IdentificationFail S -> Prop
  | immediate
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (component : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (oneFreeComponent :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          [component])
      (oneRemainingComponent : G.isSingleCComponent remaining = true) :
      IdentificationFailureTrace G (fuel + 1) remaining outcome action current
        ({ remaining := remaining, free := component } : IdentificationFail S)
  | shrink
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (fail : IdentificationFail S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (notAncestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = false)
      (nested :
        IdentificationFailureTrace G fuel
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
          fail) :
      IdentificationFailureTrace G (fuel + 1) remaining outcome action current
        fail
  | restrict
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (fail : IdentificationFail S)
      (component larger : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (oneFreeComponent :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          [component])
      (severalRemainingComponents :
        G.isSingleCComponent remaining = false)
      (componentNotMaximal :
        (G.cComponents remaining).any
          (fun piece => NodeSet.equal piece component) = false)
      (containingComponent :
        G.containingCComponent remaining component = some larger)
      (nested :
        IdentificationFailureTrace G fuel larger outcome
          (NodeSet.inter (NodeSet.inter action remaining) larger)
          (chainProduct remaining larger) fail) :
      IdentificationFailureTrace G (fuel + 1) remaining outcome action current
        fail
  | product
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (fail : IdentificationFail S)
      (component component2 : NodeSet S)
      (rest : List (NodeSet S))
      (piece : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (freeComponents :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          component :: component2 :: rest)
      (firstFailingFactor :
        IdentificationOutcome.FirstFailureAt
          (fun factor =>
            identifyFuel fuel G remaining factor
              (NodeSet.diff remaining factor) current)
          fail (component :: component2 :: rest) piece)
      (nested :
        IdentificationFailureTrace G fuel remaining piece
          (NodeSet.diff remaining piece) current fail) :
      IdentificationFailureTrace G (fuel + 1) remaining outcome action current
        fail

namespace IdentificationFailureTrace

/--
Every trace certifies the failed result named by its final index.

The three single-recursion cases compute directly from the branch hypotheses
and the recursively certified result.  The product case uses its stored parent
equation for the first-failing-factor reason documented on the constructor.
-/
theorem eq_failed {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S} {fail : IdentificationFail S}
    (trace :
      IdentificationFailureTrace G fuel remaining outcome action current fail) :
    identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail := by
  induction trace with
  | immediate fuel remaining outcome action current component
      actionNonempty ancestral oneFreeComponent oneRemainingComponent =>
      simp [identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        oneRemainingComponent]
  | shrink fuel remaining outcome action current fail actionNonempty
      notAncestral nested nestedResult =>
      simpa [identifyFuel, actionNonempty, notAncestral] using nestedResult
  | restrict fuel remaining outcome action current fail component larger
      actionNonempty ancestral oneFreeComponent severalRemainingComponents
      componentNotMaximal containingComponent nested nestedResult =>
      simpa [identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        containingComponent] using nestedResult
  | product fuel remaining outcome action current fail component component2 rest
      piece actionNonempty ancestral freeComponents firstFailingFactor nested
      _nestedResult =>
      have combinedResult :=
        IdentificationOutcome.combine_map_eq_failed_of_firstFailureAt
          (fun factor =>
            identifyFuel fuel G remaining factor
              (NodeSet.diff remaining factor) current)
          (fun terms =>
            .marginalize
              (NodeSet.diff remaining
                (NodeSet.union
                  (NodeSet.inter outcome remaining)
                  (NodeSet.inter action remaining)))
              (productTerms terms))
          firstFailingFactor
      simpa [identifyFuel, actionNonempty, ancestral, freeComponents] using
        combinedResult

/--
Turn a failed executable search into its finite structural failure path.

The proof follows the fuel recursion once.  Impossible success/sentinel
branches close by computation.  Recursive branches use the public one-step
inversion lemmas from `IdentificationSearch`; the product inversion supplies a
concrete member of the computed c-component list, so the construction remains
choice-free.
-/
theorem of_eq_failed {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (result : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    IdentificationFailureTrace G fuel remaining outcome action current fail := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [identifyFuel] at result
  | succ fuel inductionHypothesis =>
      cases actionNonempty :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, actionNonempty] at result
      | false =>
          cases ancestral :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              have nestedResult :=
                identifyFuel_eq_failed_of_shrink fuel G remaining outcome action
                  current actionNonempty ancestral result
              exact .shrink fuel remaining outcome action current fail
                actionNonempty ancestral
                (inductionHypothesis
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar
                          (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  nestedResult)
          | true =>
              cases freeComponents :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, actionNonempty, ancestral,
                    freeComponents] at result
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases oneRemainingComponent :
                          G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, actionNonempty, ancestral,
                            freeComponents, oneRemainingComponent] at result
                          cases result
                          exact .immediate fuel remaining outcome action current
                            component actionNonempty ancestral freeComponents
                            oneRemainingComponent
                      | false =>
                          cases componentMaximal :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, actionNonempty, ancestral,
                                freeComponents, oneRemainingComponent,
                                componentMaximal] at result
                          | false =>
                              cases containingComponent :
                                  G.containingCComponent remaining component with
                              | none =>
                                  simp [identifyFuel, actionNonempty, ancestral,
                                    freeComponents, oneRemainingComponent,
                                    componentMaximal, containingComponent] at result
                              | some larger =>
                                  have nestedResult :=
                                    identifyFuel_eq_failed_of_restrict fuel G
                                      remaining outcome action current
                                      actionNonempty ancestral freeComponents
                                      oneRemainingComponent componentMaximal
                                      containingComponent result
                                  exact .restrict fuel remaining outcome action
                                    current fail component larger actionNonempty
                                    ancestral freeComponents
                                    oneRemainingComponent componentMaximal
                                    containingComponent
                                    (inductionHypothesis larger outcome
                                      (NodeSet.inter
                                        (NodeSet.inter action remaining) larger)
                                      (chainProduct remaining larger)
                                      nestedResult)
                  | cons component2 rest =>
                      have combinedResult :
                          IdentificationOutcome.combine
                            ((component :: component2 :: rest).map
                              (fun factor =>
                                identifyFuel fuel G remaining factor
                                  (NodeSet.diff remaining factor) current))
                            (fun terms =>
                              .marginalize
                                (NodeSet.diff remaining
                                  (NodeSet.union
                                    (NodeSet.inter outcome remaining)
                                    (NodeSet.inter action remaining)))
                                (productTerms terms)) =
                            IdentificationOutcome.failed fail := by
                        simpa [identifyFuel, actionNonempty, ancestral,
                          freeComponents] using result
                      rcases
                          IdentificationOutcome.firstFailureAt_of_combine_map_eq_failed
                            (fun factor =>
                              identifyFuel fuel G remaining factor
                                (NodeSet.diff remaining factor) current)
                            (component :: component2 :: rest)
                            (fun terms =>
                              .marginalize
                                (NodeSet.diff remaining
                                  (NodeSet.union
                                    (NodeSet.inter outcome remaining)
                                    (NodeSet.inter action remaining)))
                                (productTerms terms))
                            combinedResult with
                        ⟨piece, firstFailingFactor⟩
                      have nestedResult :=
                        firstFailingFactor.selected_eq_failed
                      exact .product fuel remaining outcome action current fail
                        component component2 rest piece actionNonempty ancestral
                        freeComponents firstFailingFactor
                        (inductionHypothesis remaining piece
                          (NodeSet.diff remaining piece) current nestedResult)

end IdentificationFailureTrace

/--
Failed ID equations and structural failure traces are interchangeable.

Use the forward implication before an induction-heavy completeness argument;
use the reverse implication when a constructed path needs to be connected back
to the executable interface.
-/
theorem identifyFuel_eq_failed_iff_failureTrace
    {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (fail : IdentificationFail S) :
    identifyFuel fuel G remaining outcome action current =
        IdentificationOutcome.failed fail ↔
      IdentificationFailureTrace G fuel remaining outcome action current fail :=
  ⟨IdentificationFailureTrace.of_eq_failed fuel G remaining outcome action current,
    IdentificationFailureTrace.eq_failed⟩

/-!
## Structural traces for successful ID searches

Failure has a single selected path, whereas a successful product split must
certify *every* factor.  The following mutually inductive relations therefore
separate a successful invocation from an aligned list of successful factor
invocations.  Their generated mutual `rec`/`recOn` principle exposes induction
hypotheses both for a nested ID call and for every factor in a successful
product, which is the feature needed by semantic completeness proofs.  Because
the types are mutually inductive, downstream code should invoke that recursor
explicitly rather than the ordinary `induction` tactic.
-/

mutual

/--
A structural derivation of `identifyFuel ... = identified term`.

Each constructor mirrors one successful branch of the executable definition.
Recursive constructors retain their nested success traces, and the product
constructor retains an ordered, term-aligned trace for every c-component.
-/
inductive IdentificationSuccessTrace {S : ObservedSignature}
    (G : ObservedGraph S) :
    (fuel : Nat) ->
    (remaining outcome action : NodeSet S) ->
    ProbabilityTerm S ->
    ProbabilityTerm S -> Prop
  | emptyAction
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (actionEmpty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = true) :
      IdentificationSuccessTrace G (fuel + 1) remaining outcome action current
        (.marginalize
          (NodeSet.diff remaining (NodeSet.inter outcome remaining)) current)
  | emptyFree
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (noFreeComponents :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) = []) :
      IdentificationSuccessTrace G (fuel + 1) remaining outcome action current
        (.marginalize remaining current)
  | chain
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (component : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (oneFreeComponent :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          [component])
      (severalRemainingComponents :
        G.isSingleCComponent remaining = false)
      (componentMaximal :
        (G.cComponents remaining).any
          (fun piece => NodeSet.equal piece component) = true) :
      IdentificationSuccessTrace G (fuel + 1) remaining outcome action current
        (.marginalize
          (NodeSet.diff component (NodeSet.inter outcome remaining))
          (chainProduct remaining component))
  | shrink
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current term : ProbabilityTerm S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (notAncestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = false)
      (nested :
        IdentificationSuccessTrace G fuel
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
          term) :
      IdentificationSuccessTrace G (fuel + 1) remaining outcome action current
        term
  | restrict
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current term : ProbabilityTerm S)
      (component larger : NodeSet S)
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (oneFreeComponent :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          [component])
      (severalRemainingComponents :
        G.isSingleCComponent remaining = false)
      (componentNotMaximal :
        (G.cComponents remaining).any
          (fun piece => NodeSet.equal piece component) = false)
      (containingComponent :
        G.containingCComponent remaining component = some larger)
      (nested :
        IdentificationSuccessTrace G fuel larger outcome
          (NodeSet.inter (NodeSet.inter action remaining) larger)
          (chainProduct remaining larger) term) :
      IdentificationSuccessTrace G (fuel + 1) remaining outcome action current
        term
  | product
      (fuel : Nat)
      (remaining outcome action : NodeSet S)
      (current : ProbabilityTerm S)
      (component component2 : NodeSet S)
      (rest : List (NodeSet S))
      (terms : List (ProbabilityTerm S))
      (actionNonempty :
        NodeSet.isEmpty (NodeSet.inter action remaining) = false)
      (ancestral :
        NodeSet.equal
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          remaining = true)
      (freeComponents :
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) =
          component :: component2 :: rest)
      (factors :
        IdentificationProductSuccessTrace G fuel remaining current
          (component :: component2 :: rest) terms) :
      IdentificationSuccessTrace G (fuel + 1) remaining outcome action current
        (.marginalize
          (NodeSet.diff remaining
            (NodeSet.union
              (NodeSet.inter outcome remaining)
              (NodeSet.inter action remaining)))
          (productTerms terms))

/--
Successful recursive traces for a list of product factors, aligned with the
identified terms returned by those factors.

`headResult` is retained alongside `headTrace` so the alignment itself can be
reconstructed without a mutually recursive proof.  Unlike the former parent
equation in the failure trace, this is a local factor equation and the parent
product result is derived from the complete aligned list.
-/
inductive IdentificationProductSuccessTrace {S : ObservedSignature}
    (G : ObservedGraph S) :
    (fuel : Nat) -> (remaining : NodeSet S) ->
    (current : ProbabilityTerm S) ->
    List (NodeSet S) -> List (ProbabilityTerm S) -> Prop
  | nil :
      IdentificationProductSuccessTrace G fuel remaining current [] []
  | cons
      (component : NodeSet S) (term : ProbabilityTerm S)
      (rest : List (NodeSet S)) (terms : List (ProbabilityTerm S))
      (headResult :
        identifyFuel fuel G remaining component
            (NodeSet.diff remaining component) current =
          IdentificationOutcome.identified term)
      (headTrace :
        IdentificationSuccessTrace G fuel remaining component
          (NodeSet.diff remaining component) current term)
      (tail :
        IdentificationProductSuccessTrace G fuel remaining current rest terms) :
      IdentificationProductSuccessTrace G fuel remaining current
        (component :: rest) (term :: terms)

end

namespace IdentificationProductSuccessTrace

/-- The aligned factor traces reconstruct the complete list of factor results. -/
theorem results_eq {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining : NodeSet S} {current : ProbabilityTerm S}
    {components : List (NodeSet S)} {terms : List (ProbabilityTerm S)}
    (traces :
      IdentificationProductSuccessTrace G fuel remaining current
        components terms) :
    components.map (fun component =>
        identifyFuel fuel G remaining component
          (NodeSet.diff remaining component) current) =
      terms.map IdentificationOutcome.identified :=
  match traces with
  | .nil => rfl
  | .cons component term rest terms headResult _headTrace tail => by
      simp only [List.map_cons]
      rw [headResult, results_eq tail]

end IdentificationProductSuccessTrace

namespace IdentificationSuccessTrace

/-- Every structural success trace certifies its indexed identified result. -/
theorem eq_identified {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current term : ProbabilityTerm S}
    (trace :
      IdentificationSuccessTrace G fuel remaining outcome action current term) :
    identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.identified term :=
  match trace with
  | .emptyAction fuel remaining outcome action current actionEmpty => by
      simp [identifyFuel, actionEmpty]
  | .emptyFree fuel remaining outcome action current actionNonempty ancestral
      noFreeComponents => by
      simp [identifyFuel, actionNonempty, ancestral, noFreeComponents]
  | .chain fuel remaining outcome action current component actionNonempty
      ancestral oneFreeComponent severalRemainingComponents componentMaximal => by
      simp [identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentMaximal]
  | .shrink fuel remaining outcome action current term actionNonempty
      notAncestral nested => by
      simpa [identifyFuel, actionNonempty, notAncestral] using
        eq_identified nested
  | .restrict fuel remaining outcome action current term component larger
      actionNonempty ancestral oneFreeComponent severalRemainingComponents
      componentNotMaximal containingComponent nested => by
      simpa [identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        containingComponent] using eq_identified nested
  | .product fuel remaining outcome action current component component2 rest
      terms actionNonempty ancestral freeComponents factors => by
      let run := fun factor =>
        identifyFuel fuel G remaining factor
          (NodeSet.diff remaining factor) current
      let assemble := fun factorTerms =>
        ProbabilityTerm.marginalize
          (NodeSet.diff remaining
            (NodeSet.union
              (NodeSet.inter outcome remaining)
              (NodeSet.inter action remaining)))
          (productTerms factorTerms)
      have factorResults :
          (component :: component2 :: rest).map run =
            terms.map IdentificationOutcome.identified := by
        simpa [run] using factors.results_eq
      have combinedResult :
          IdentificationOutcome.combine
              ((component :: component2 :: rest).map run) assemble =
            IdentificationOutcome.identified (assemble terms) := by
        rw [factorResults]
        exact IdentificationOutcome.combine_map_identified terms assemble
      simpa [identifyFuel, actionNonempty, ancestral, freeComponents,
        run, assemble] using combinedResult

end IdentificationSuccessTrace

namespace IdentificationSuccessTrace

/--
Turn an identified executable search into its complete structural success
derivation.  Product success recursively constructs one aligned factor trace
per computed c-component; no factor is selected or discarded.
-/
theorem of_eq_identified {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current term : ProbabilityTerm S)
    (result : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.identified term) :
    IdentificationSuccessTrace G fuel remaining outcome action current term := by
  induction fuel generalizing remaining outcome action current term with
  | zero =>
      simp [identifyFuel] at result
  | succ fuel inductionHypothesis =>
      cases actionEmpty :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, actionEmpty] at result
          cases result
          exact .emptyAction fuel remaining outcome action current actionEmpty
      | false =>
          cases ancestral :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              have nestedResult :=
                identifyFuel_eq_identified_of_shrink fuel G remaining outcome
                  action current actionEmpty ancestral result
              exact .shrink fuel remaining outcome action current term
                actionEmpty ancestral
                (inductionHypothesis
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar
                          (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  term nestedResult)
          | true =>
              cases freeComponents :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, actionEmpty, ancestral,
                    freeComponents] at result
                  cases result
                  exact .emptyFree fuel remaining outcome action current
                    actionEmpty ancestral freeComponents
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases oneRemainingComponent :
                          G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, actionEmpty, ancestral,
                            freeComponents, oneRemainingComponent] at result
                      | false =>
                          cases componentMaximal :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, actionEmpty, ancestral,
                                freeComponents, oneRemainingComponent,
                                componentMaximal] at result
                              cases result
                              exact .chain fuel remaining outcome action current
                                component actionEmpty ancestral freeComponents
                                oneRemainingComponent componentMaximal
                          | false =>
                              cases containingComponent :
                                  G.containingCComponent remaining component with
                              | none =>
                                  simp [identifyFuel, actionEmpty, ancestral,
                                    freeComponents, oneRemainingComponent,
                                    componentMaximal, containingComponent] at result
                              | some larger =>
                                  have nestedResult :=
                                    identifyFuel_eq_identified_of_restrict fuel G
                                      remaining outcome action current
                                      actionEmpty ancestral freeComponents
                                      oneRemainingComponent componentMaximal
                                      containingComponent result
                                  exact .restrict fuel remaining outcome action
                                    current term component larger actionEmpty
                                    ancestral freeComponents
                                    oneRemainingComponent componentMaximal
                                    containingComponent
                                    (inductionHypothesis larger outcome
                                      (NodeSet.inter
                                        (NodeSet.inter action remaining) larger)
                                      (chainProduct remaining larger) term
                                      nestedResult)
                  | cons component2 rest =>
                      rcases identifyFuel_eq_identified_of_product fuel G
                          remaining outcome action current actionEmpty ancestral
                          freeComponents result with
                        ⟨terms, termEq, factorResults⟩
                      let run := fun factor =>
                        identifyFuel fuel G remaining factor
                          (NodeSet.diff remaining factor) current
                      have buildFactors :
                          forall (components : List (NodeSet S))
                            (factorTerms : List (ProbabilityTerm S)),
                            components.map run =
                                factorTerms.map
                                  IdentificationOutcome.identified ->
                              IdentificationProductSuccessTrace G fuel remaining
                                current components factorTerms := by
                        intro components
                        induction components with
                        | nil =>
                            intro factorTerms results
                            cases factorTerms with
                            | nil =>
                                exact .nil
                            | cons factorTerm factorTerms =>
                                simp at results
                        | cons factor factors factorInduction =>
                            intro factorTerms results
                            cases factorTerms with
                            | nil =>
                                simp at results
                            | cons factorTerm factorTerms =>
                                simp only [List.map_cons, List.cons.injEq] at results
                                have headResult :
                                    identifyFuel fuel G remaining factor
                                        (NodeSet.diff remaining factor) current =
                                      IdentificationOutcome.identified
                                        factorTerm := by
                                  simpa [run] using results.1
                                exact .cons factor factorTerm factors factorTerms
                                  headResult
                                  (inductionHypothesis remaining factor
                                    (NodeSet.diff remaining factor) current
                                    factorTerm headResult)
                                  (factorInduction factorTerms results.2)
                      have factors :
                          IdentificationProductSuccessTrace G fuel remaining
                            current (component :: component2 :: rest) terms :=
                        buildFactors (component :: component2 :: rest) terms
                          (by simpa [run] using factorResults)
                      subst term
                      exact .product fuel remaining outcome action current
                        component component2 rest terms actionEmpty ancestral
                        freeComponents factors

end IdentificationSuccessTrace

/--
Identified ID equations and structural success traces are interchangeable.
-/
theorem identifyFuel_eq_identified_iff_successTrace
    {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current term : ProbabilityTerm S) :
    identifyFuel fuel G remaining outcome action current =
        IdentificationOutcome.identified term ↔
      IdentificationSuccessTrace G fuel remaining outcome action current term :=
  ⟨IdentificationSuccessTrace.of_eq_identified fuel G remaining outcome action
      current term,
    IdentificationSuccessTrace.eq_identified⟩

end Causality
end Thesis
