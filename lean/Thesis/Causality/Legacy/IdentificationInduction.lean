import Thesis.Causality.Legacy.IdentificationSearch
import Thesis.Causality.IdentificationOutcomeTraces

namespace Thesis
namespace Causality

open Probability

universe u

/-!
# Exact structural traces for the quarantined legacy ID recursion

This module records the old program's executable control flow, not the
corrected engine's semantic certificates.  Every result equation below names
a `Legacy` program explicitly.  The current joint and conditional programs
have their own structural success compilers and failure extractors; importing
either current program does not import this module.

`Legacy.identifyFuel` is structurally recursive on its fuel, but its definition contains
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
    ProbabilityTerm S -> Type
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
            Legacy.identifyFuel fuel G remaining factor
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
    Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.unfinished := by
  induction trace with
  | exhausted remaining outcome action current =>
      rfl
  | missingHost fuel remaining outcome action current component actionNonempty
      ancestral oneFreeComponent severalRemainingComponents componentNotMaximal
      noContainingComponent =>
      simp [Legacy.identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        noContainingComponent]
  | shrink fuel remaining outcome action current actionNonempty notAncestral
      nested nestedResult =>
      simpa [Legacy.identifyFuel, actionNonempty, notAncestral] using nestedResult
  | restrict fuel remaining outcome action current component larger
      actionNonempty ancestral oneFreeComponent severalRemainingComponents
      componentNotMaximal containingComponent nested nestedResult =>
      simpa [Legacy.identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        containingComponent] using nestedResult
  | product fuel remaining outcome action current component component2 rest
      piece actionNonempty ancestral freeComponents firstUnfinishedFactor nested
      _nestedResult =>
      have combinedResult :=
        IdentificationOutcome.combine_map_eq_unfinished_of_firstUnfinishedAt
          (fun factor =>
            Legacy.identifyFuel fuel G remaining factor
              (NodeSet.diff remaining factor) current)
          (fun terms =>
            .marginalize
              (NodeSet.diff remaining
                (NodeSet.union
                  (NodeSet.inter outcome remaining)
                  (NodeSet.inter action remaining)))
              (productTerms terms))
          firstUnfinishedFactor
      simpa [Legacy.identifyFuel, actionNonempty, ancestral, freeComponents] using
        combinedResult

/--
Whether the selected unfinished path ends specifically by exhausting its
fuel.  The alternative terminal, `missingHost`, is represented explicitly so
downstream completeness code can prove it unreachable from the c-component
partition invariants rather than silently treating every sentinel as a depth
failure.
-/
def endsInExhaustion {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S}
    (trace :
      IdentificationUnfinishedTrace G fuel remaining outcome action current) :
    Bool :=
  match trace with
  | .exhausted .. => true
  | .missingHost .. => false
  | .shrink (nested := nested) .. => endsInExhaustion nested
  | .restrict (nested := nested) .. => endsInExhaustion nested
  | .product (nested := nested) .. => endsInExhaustion nested

/-- Convert an unfinished executable result into its complete structural cause. -/
noncomputable def of_eq_unfinished {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (result : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.unfinished) :
    IdentificationUnfinishedTrace G fuel remaining outcome action current := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      exact .exhausted remaining outcome action current
  | succ fuel inductionHypothesis =>
      cases actionEmpty :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, actionEmpty] at result
      | false =>
          cases ancestral :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              have nestedResult :
                  Legacy.identifyFuel fuel G
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
                simpa [Legacy.identifyFuel, actionEmpty, ancestral] using result
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
                  simp [Legacy.identifyFuel, actionEmpty, ancestral,
                    freeComponents] at result
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases oneRemainingComponent :
                          G.isSingleCComponent remaining with
                      | true =>
                          simp [Legacy.identifyFuel, actionEmpty, ancestral,
                            freeComponents, oneRemainingComponent] at result
                      | false =>
                          cases componentMaximal :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [Legacy.identifyFuel, actionEmpty, ancestral,
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
                                      Legacy.identifyFuel fuel G larger outcome
                                          (NodeSet.inter
                                            (NodeSet.inter action remaining)
                                            larger)
                                          (chainProduct remaining larger) =
                                        IdentificationOutcome.unfinished := by
                                    simpa [Legacy.identifyFuel, actionEmpty, ancestral,
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
                                Legacy.identifyFuel fuel G remaining factor
                                  (NodeSet.diff remaining factor) current))
                            (fun terms =>
                              .marginalize
                                (NodeSet.diff remaining
                                  (NodeSet.union
                                    (NodeSet.inter outcome remaining)
                                    (NodeSet.inter action remaining)))
                                (productTerms terms)) =
                            IdentificationOutcome.unfinished := by
                        simpa [Legacy.identifyFuel, actionEmpty, ancestral,
                          freeComponents] using result
                      rcases
                          IdentificationOutcome.firstUnfinishedAt_of_combine_map_eq_unfinished
                            (fun factor =>
                              Legacy.identifyFuel fuel G remaining factor
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
    Legacy.identifyFuel fuel G remaining outcome action current =
        IdentificationOutcome.unfinished ↔
      Nonempty
        (IdentificationUnfinishedTrace G fuel remaining outcome action current) :=
  ⟨fun result =>
      ⟨IdentificationUnfinishedTrace.of_eq_unfinished fuel G remaining outcome
        action current result⟩,
    fun ⟨trace⟩ => IdentificationUnfinishedTrace.eq_unfinished trace⟩

/--
A structural path from an invocation of `Legacy.identifyFuel` to its reported failure.

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
    IdentificationFail S -> Type
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
            Legacy.identifyFuel fuel G remaining factor
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
    Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail := by
  induction trace with
  | immediate fuel remaining outcome action current component
      actionNonempty ancestral oneFreeComponent oneRemainingComponent =>
      simp [Legacy.identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        oneRemainingComponent]
  | shrink fuel remaining outcome action current fail actionNonempty
      notAncestral nested nestedResult =>
      simpa [Legacy.identifyFuel, actionNonempty, notAncestral] using nestedResult
  | restrict fuel remaining outcome action current fail component larger
      actionNonempty ancestral oneFreeComponent severalRemainingComponents
      componentNotMaximal containingComponent nested nestedResult =>
      simpa [Legacy.identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        containingComponent] using nestedResult
  | product fuel remaining outcome action current fail component component2 rest
      piece actionNonempty ancestral freeComponents firstFailingFactor nested
      _nestedResult =>
      have combinedResult :=
        IdentificationOutcome.combine_map_eq_failed_of_firstFailureAt
          (fun factor =>
            Legacy.identifyFuel fuel G remaining factor
              (NodeSet.diff remaining factor) current)
          (fun terms =>
            .marginalize
              (NodeSet.diff remaining
                (NodeSet.union
                  (NodeSet.inter outcome remaining)
                  (NodeSet.inter action remaining)))
              (productTerms terms))
          firstFailingFactor
      simpa [Legacy.identifyFuel, actionNonempty, ancestral, freeComponents] using
        combinedResult

/--
Turn a failed executable search into its finite structural failure path.

The proof follows the fuel recursion once.  Impossible success/sentinel
branches close by computation.  Recursive branches use the public one-step
inversion lemmas from `IdentificationSearch`; the product inversion supplies a
concrete member of the computed c-component list, so the construction remains
choice-free.
-/
noncomputable def of_eq_failed {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (result : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    IdentificationFailureTrace G fuel remaining outcome action current fail := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [Legacy.identifyFuel] at result
  | succ fuel inductionHypothesis =>
      cases actionNonempty :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, actionNonempty] at result
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
                  simp [Legacy.identifyFuel, actionNonempty, ancestral,
                    freeComponents] at result
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases oneRemainingComponent :
                          G.isSingleCComponent remaining with
                      | true =>
                          simp [Legacy.identifyFuel, actionNonempty, ancestral,
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
                              simp [Legacy.identifyFuel, actionNonempty, ancestral,
                                freeComponents, oneRemainingComponent,
                                componentMaximal] at result
                          | false =>
                              cases containingComponent :
                                  G.containingCComponent remaining component with
                              | none =>
                                  simp [Legacy.identifyFuel, actionNonempty, ancestral,
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
                                Legacy.identifyFuel fuel G remaining factor
                                  (NodeSet.diff remaining factor) current))
                            (fun terms =>
                              .marginalize
                                (NodeSet.diff remaining
                                  (NodeSet.union
                                    (NodeSet.inter outcome remaining)
                                    (NodeSet.inter action remaining)))
                                (productTerms terms)) =
                            IdentificationOutcome.failed fail := by
                        simpa [Legacy.identifyFuel, actionNonempty, ancestral,
                          freeComponents] using result
                      rcases
                          IdentificationOutcome.firstFailureAt_of_combine_map_eq_failed
                            (fun factor =>
                              Legacy.identifyFuel fuel G remaining factor
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
    Legacy.identifyFuel fuel G remaining outcome action current =
        IdentificationOutcome.failed fail ↔
      Nonempty
        (IdentificationFailureTrace G fuel remaining outcome action current fail) :=
  ⟨fun result =>
      ⟨IdentificationFailureTrace.of_eq_failed fuel G remaining outcome action
        current result⟩,
    fun ⟨trace⟩ => IdentificationFailureTrace.eq_failed trace⟩

/-!
## Terminal immediate sites of arbitrary failure traces

Every failed recursive ID run eventually reaches the immediate 4.1 branch.
The following witness retains that terminal invocation and its Boolean branch
facts.  It is deliberately independent of the path taken to the leaf: shrink,
restriction, and product frames are removed by structural recursion over the
trace rather than by enumerating finite stacks of those frames.
-/

/--
The terminal immediate-failure invocation reached by a structural failure
trace.  `fail_eq` records that the public failure record is precisely the
remaining host and unique free component at this leaf.
-/
structure IdentificationImmediateFailureSite {S : ObservedSignature}
    (G : ObservedGraph S) (fail : IdentificationFail S) where
  fuel : Nat
  remaining : NodeSet S
  outcome : NodeSet S
  action : NodeSet S
  current : ProbabilityTerm S
  component : NodeSet S
  fail_eq :
    fail = ({ remaining := remaining, free := component } : IdentificationFail S)
  actionNonempty :
    NodeSet.isEmpty (NodeSet.inter action remaining) = false
  ancestral :
    NodeSet.equal
      (G.ancestralSet remaining
        (GraphMutilation.bar (NodeSet.inter action remaining))
        (NodeSet.inter outcome remaining))
      remaining = true
  oneFreeComponent :
    G.cComponents
      (NodeSet.diff remaining (NodeSet.inter action remaining)) = [component]
  oneRemainingComponent : G.isSingleCComponent remaining = true

namespace IdentificationFailureTrace

/--
Forget the recursive frames of a failure trace and return its terminal
immediate-failure site as inspectable data.  Product traces already select
their first failing factor, so no list search or choice is needed here.
-/
def immediateSite {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S} {fail : IdentificationFail S}
    (trace :
      IdentificationFailureTrace G fuel remaining outcome action current fail) :
    IdentificationImmediateFailureSite G fail :=
  match trace with
  | .immediate fuel remaining outcome action current component actionNonempty
      ancestral oneFreeComponent oneRemainingComponent =>
      { fuel := fuel
        remaining := remaining
        outcome := outcome
        action := action
        current := current
        component := component
        fail_eq := rfl
        actionNonempty := actionNonempty
        ancestral := ancestral
        oneFreeComponent := oneFreeComponent
        oneRemainingComponent := oneRemainingComponent }
  | .shrink _fuel _remaining _outcome _action _current _fail _actionNonempty
      _notAncestral nested =>
      immediateSite nested
  | .restrict _fuel _remaining _outcome _action _current _fail _component
      _larger _actionNonempty _ancestral _oneFreeComponent
      _severalRemainingComponents _componentNotMaximal _containingComponent
      nested =>
      immediateSite nested
  | .product _fuel _remaining _outcome _action _current _fail _component
      _component2 _rest _piece _actionNonempty _ancestral _freeComponents
      _firstFailingFactor nested =>
      immediateSite nested

/--
Whether the selected failure path reaches its immediate 4.1 site without
entering a product factor.  An ancestral shrink and a 4.3 c-component
restriction merely refine the working host; neither changes the substantive
outcome/action query on the eventual failure host.  A product frame is the
one branch that replaces that query by `piece | do(remaining \ piece)`.

This is a Boolean property because it is meant to be inspected alongside the
executable trace.  In particular, completeness code can distinguish the
query-preserving paths from the genuinely different product case without a
propositional excluded-middle split.
-/
def hasNoProductFrame {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S} {fail : IdentificationFail S}
    (trace :
      IdentificationFailureTrace G fuel remaining outcome action current fail) :
    Bool :=
  match trace with
  | .immediate .. => true
  | .shrink (nested := nested) .. => hasNoProductFrame nested
  | .restrict (nested := nested) .. => hasNoProductFrame nested
  | .product .. => false

/--
The failure record is supported inside the remaining set of every invocation
on its trace.  Stating this directly on traces is convenient for transport
proofs: callers need not first forget the trace back to an equality returned
by the executable engine.
-/
theorem fail_remaining_subset {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S} {fail : IdentificationFail S}
    (trace :
      IdentificationFailureTrace G fuel remaining outcome action current fail) :
    NodeSet.Subset fail.remaining remaining :=
  (identifyFuel_eq_failed fuel G remaining outcome action current
    trace.eq_failed).2

/--
Along a product-free failure path, the outcome and action stored at the
terminal immediate site agree with the original invocation after restriction
to the recorded failure host.

The only non-definitional step is a 4.3 restriction.  Its recursive action is
`(action ∩ remaining) ∩ larger`; the failed host lies in `larger`, while
`larger` lies in `remaining`, so both extra intersections disappear on that
host.  This single induction replaces every finite stack of shrink/restrict
unpackers and deliberately stops at the product boundary, where the statement
would be false.
-/
theorem immediateSite_query_agrees_of_hasNoProductFrame
    {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S} {fail : IdentificationFail S}
    (trace :
      IdentificationFailureTrace G fuel remaining outcome action current fail)
    (productFree : trace.hasNoProductFrame = true) :
    NodeSet.equal
          (NodeSet.inter trace.immediateSite.outcome fail.remaining)
          (NodeSet.inter outcome fail.remaining) = true ∧
      NodeSet.equal
          (NodeSet.inter trace.immediateSite.action fail.remaining)
          (NodeSet.inter action fail.remaining) = true := by
  induction trace with
  | immediate =>
      constructor <;>
        exact (NodeSet.equal_eq_true_iff _ _).mpr rfl
  | shrink _fuel _remaining _outcome _action _current _fail _actionNonempty
      _notAncestral nested inductionHypothesis =>
      exact inductionHypothesis productFree
  | restrict _fuel remaining _outcome action _current fail _component larger
      _actionNonempty _ancestral _oneFreeComponent
      _severalRemainingComponents _componentNotMaximal containingComponent
      nested inductionHypothesis =>
      have nestedAgreement := inductionHypothesis productFree
      refine ⟨nestedAgreement.1, ?_⟩
      have failedInLarger : NodeSet.Subset fail.remaining larger :=
        nested.fail_remaining_subset
      have largerInRemaining : NodeSet.Subset larger remaining :=
        containingCComponent_subset_host G remaining _ containingComponent
      have restrictedAction :
          NodeSet.inter
              (NodeSet.inter (NodeSet.inter action remaining) larger)
              fail.remaining =
            NodeSet.inter action fail.remaining := by
        funext i
        cases hFail : fail.remaining i with
        | false =>
            simp [NodeSet.inter, hFail]
        | true =>
            have hLarger : larger i = true := failedInLarger i hFail
            have hRemaining : remaining i = true :=
              largerInRemaining i hLarger
            simp [NodeSet.inter, hFail, hLarger, hRemaining]
      have localAgreement :
          NodeSet.inter nested.immediateSite.action fail.remaining =
            NodeSet.inter
              (NodeSet.inter (NodeSet.inter action remaining) larger)
              fail.remaining :=
        (NodeSet.equal_eq_true_iff _ _).mp nestedAgreement.2
      exact (NodeSet.equal_eq_true_iff _ _).mpr
        (localAgreement.trans restrictedAction)
  | product =>
      simp [hasNoProductFrame] at productFree

end IdentificationFailureTrace

namespace IdentificationImmediateFailureSite

/-- The extracted terminal site computes to its recorded immediate failure. -/
theorem eq_failed {S : ObservedSignature} {G : ObservedGraph S}
    {fail : IdentificationFail S}
    (site : IdentificationImmediateFailureSite G fail) :
    Legacy.identifyFuel (site.fuel + 1) G site.remaining site.outcome site.action
        site.current = IdentificationOutcome.failed fail := by
  rcases site with
    ⟨fuel, remaining, outcome, action, current, component, failEq,
      actionNonempty, ancestral, oneFreeComponent, oneRemainingComponent⟩
  cases failEq
  simp [Legacy.identifyFuel, actionNonempty, ancestral, oneFreeComponent,
    oneRemainingComponent]

/-- The failure record's remaining set is the terminal immediate host. -/
theorem fail_remaining {S : ObservedSignature} {G : ObservedGraph S}
    {fail : IdentificationFail S}
    (site : IdentificationImmediateFailureSite G fail) :
    fail.remaining = site.remaining :=
  congrArg IdentificationFail.remaining site.fail_eq

/-- The failure record's free set is the terminal unique free component. -/
theorem fail_free {S : ObservedSignature} {G : ObservedGraph S}
    {fail : IdentificationFail S}
    (site : IdentificationImmediateFailureSite G fail) :
    fail.free = site.component :=
  congrArg IdentificationFail.free site.fail_eq

/--
The terminal site's free component is its local action complement, and its
remaining host is ancestral of the local outcome after that cut.  These are
the two immediate hedge facts formerly recovered separately for every named
stack of outer ID branches.
-/
theorem local_query_site {S : ObservedSignature} {G : ObservedGraph S}
    {fail : IdentificationFail S}
    (site : IdentificationImmediateFailureSite G fail) :
    NodeSet.equal fail.free
          (NodeSet.diff fail.remaining
            (NodeSet.inter site.action fail.remaining)) = true ∧
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter site.outcome fail.remaining))
        fail.remaining = true := by
  have parts :=
    identifyFuel_eq_failed_immediate_query_site site.fuel G site.remaining
      site.outcome site.action site.current site.actionNonempty site.ancestral
      site.oneFreeComponent site.oneRemainingComponent site.eq_failed
  exact ⟨parts.2.2.1, parts.2.2.2⟩

end IdentificationImmediateFailureSite

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
A structural derivation of `Legacy.identifyFuel ... = identified term`.

Each constructor mirrors one successful branch of the executable definition.
Recursive constructors retain their nested success traces, and the product
constructor retains an ordered, term-aligned trace for every c-component.
-/
inductive IdentificationSuccessTrace {S : ObservedSignature}
    (G : ObservedGraph S) :
    (fuel : Nat) ->
    (remaining outcome action : NodeSet S) ->
    ProbabilityTerm S ->
    ProbabilityTerm S -> Type
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
    List (NodeSet S) -> List (ProbabilityTerm S) -> Type
  | nil :
      IdentificationProductSuccessTrace G fuel remaining current [] []
  | cons
      (component : NodeSet S) (term : ProbabilityTerm S)
      (rest : List (NodeSet S)) (terms : List (ProbabilityTerm S))
      (headResult :
        Legacy.identifyFuel fuel G remaining component
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
        Legacy.identifyFuel fuel G remaining component
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
    Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.identified term :=
  match trace with
  | .emptyAction fuel remaining outcome action current actionEmpty => by
      simp [Legacy.identifyFuel, actionEmpty]
  | .emptyFree fuel remaining outcome action current actionNonempty ancestral
      noFreeComponents => by
      simp [Legacy.identifyFuel, actionNonempty, ancestral, noFreeComponents]
  | .chain fuel remaining outcome action current component actionNonempty
      ancestral oneFreeComponent severalRemainingComponents componentMaximal => by
      simp [Legacy.identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentMaximal]
  | .shrink fuel remaining outcome action current term actionNonempty
      notAncestral nested => by
      simpa [Legacy.identifyFuel, actionNonempty, notAncestral] using
        eq_identified nested
  | .restrict fuel remaining outcome action current term component larger
      actionNonempty ancestral oneFreeComponent severalRemainingComponents
      componentNotMaximal containingComponent nested => by
      simpa [Legacy.identifyFuel, actionNonempty, ancestral, oneFreeComponent,
        severalRemainingComponents, componentNotMaximal,
        containingComponent] using eq_identified nested
  | .product fuel remaining outcome action current component component2 rest
      terms actionNonempty ancestral freeComponents factors => by
      let run := fun factor =>
        Legacy.identifyFuel fuel G remaining factor
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
      simpa [Legacy.identifyFuel, actionNonempty, ancestral, freeComponents,
        run, assemble] using combinedResult

/--
A structural success trace preserves action-freedom from its current term to
its identified result.  This packages the executable invariant under the
trace index, so a certificate compiler can obtain its syntactic target field
without re-running a branch analysis.
-/
theorem actionFree {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current term : ProbabilityTerm S}
    (trace :
      IdentificationSuccessTrace G fuel remaining outcome action current term)
    (currentFree : current.ActionFree) : term.ActionFree :=
  identifyFuel_identified_actionFree fuel G remaining outcome action current
    currentFree trace.eq_identified

end IdentificationSuccessTrace

namespace IdentificationProductSuccessTrace

/--
Every term aligned with a successful product trace is action-free whenever
the shared current expression is action-free.  The proof follows the
Type-valued factor list rather than inspecting membership in a computed
outcome list.
-/
theorem actionFree {S : ObservedSignature} {G : ObservedGraph S}
    {fuel : Nat} {remaining : NodeSet S} {current : ProbabilityTerm S}
    {components : List (NodeSet S)} {terms : List (ProbabilityTerm S)}
    (traces : IdentificationProductSuccessTrace G fuel remaining current
      components terms)
    (currentFree : current.ActionFree) :
    forall term, term ∈ terms -> term.ActionFree :=
  match traces with
  | .nil => by
      intro term member
      simp at member
  | .cons component term rest terms headResult headTrace tail => by
      intro candidate member
      rcases List.mem_cons.mp member with equal | later
      · subst candidate
        exact headTrace.actionFree currentFree
      · exact actionFree tail currentFree candidate later

end IdentificationProductSuccessTrace

namespace IdentificationSuccessTrace

/--
Turn an identified executable search into its complete structural success
derivation.  Product success recursively constructs one aligned factor trace
per computed c-component; no factor is selected or discarded.
-/
noncomputable def of_eq_identified {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current term : ProbabilityTerm S)
    (result : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.identified term) :
    IdentificationSuccessTrace G fuel remaining outcome action current term := by
  induction fuel generalizing remaining outcome action current term with
  | zero =>
      simp [Legacy.identifyFuel] at result
  | succ fuel inductionHypothesis =>
      cases actionEmpty :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [Legacy.identifyFuel, actionEmpty] at result
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
                  simp [Legacy.identifyFuel, actionEmpty, ancestral,
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
                          simp [Legacy.identifyFuel, actionEmpty, ancestral,
                            freeComponents, oneRemainingComponent] at result
                      | false =>
                          cases componentMaximal :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [Legacy.identifyFuel, actionEmpty, ancestral,
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
                                  simp [Legacy.identifyFuel, actionEmpty, ancestral,
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
                      let run := fun factor =>
                        Legacy.identifyFuel fuel G remaining factor
                          (NodeSet.diff remaining factor) current
                      let assemble := fun terms =>
                        ProbabilityTerm.marginalize
                          (NodeSet.diff remaining
                            (NodeSet.union
                              (NodeSet.inter outcome remaining)
                              (NodeSet.inter action remaining)))
                          (productTerms terms)
                      have combinedResult :
                          IdentificationOutcome.combine
                              ((component :: component2 :: rest).map run)
                              assemble =
                            IdentificationOutcome.identified term := by
                        simpa [Legacy.identifyFuel, actionEmpty, ancestral,
                          freeComponents, run, assemble] using result
                      rcases IdentificationOutcome.combineIdentifiedData
                          ((component :: component2 :: rest).map run)
                          assemble term combinedResult with
                        ⟨terms, factorResults, termEq⟩
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
                                    Legacy.identifyFuel fuel G remaining factor
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
                      rw [termEq]
                      simpa [assemble] using
                        (IdentificationSuccessTrace.product fuel remaining
                          outcome action current component component2 rest terms
                          actionEmpty ancestral freeComponents factors)

end IdentificationSuccessTrace

/--
Identified ID equations and structural success traces are interchangeable.
-/
theorem identifyFuel_eq_identified_iff_successTrace
    {S : ObservedSignature}
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current term : ProbabilityTerm S) :
    Legacy.identifyFuel fuel G remaining outcome action current =
        IdentificationOutcome.identified term ↔
      Nonempty
        (IdentificationSuccessTrace G fuel remaining outcome action current term) :=
  ⟨fun result =>
      ⟨IdentificationSuccessTrace.of_eq_identified fuel G remaining outcome
        action current term result⟩,
    fun ⟨trace⟩ => IdentificationSuccessTrace.eq_identified trace⟩

end Causality
end Thesis
