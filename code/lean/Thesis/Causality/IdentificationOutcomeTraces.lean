import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

open Probability

universe u

/-!
# Ordered finite collector witnesses shared by identification engines

An outcome collector stops at its first failure or unfinished factor, after
all preceding factors have identified. The dependent witnesses below preserve
that order and return the actual selected input as data. Successful collection
instead retains the exact aligned list of terms and the assembly equation.

Everything is obtained by recursion on supplied lists and case analysis on
concrete result constructors. No decidable equality on arbitrary inputs, choice
of a proposition-level witness or general excluded middle is required.
The existing `noncomputable` markers concern dependent code generation, not
additional logical axioms.

These generic collector facts are independent of legacy or current recursion.
The quarantined legacy trace module reexports the unchanged declarations;
current failure extraction imports this focused interface directly.
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
    (fail : IdentificationFail S) : List α -> α -> Type u
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
noncomputable def firstFailureAt_of_collect_map_eq_failed
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (acc : List (ProbabilityTerm S)) {fail : IdentificationFail S}
    (result : collect assemble (inputs.map run) acc =
      IdentificationOutcome.failed fail) :
    Sigma fun selected => FirstFailureAt run fail inputs selected := by
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
noncomputable def firstFailureAt_of_combine_map_eq_failed
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    {fail : IdentificationFail S}
    (result : combine (inputs.map run) assemble =
      IdentificationOutcome.failed fail) :
    Sigma fun selected => FirstFailureAt run fail inputs selected :=
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
      Nonempty (Sigma fun selected => FirstFailureAt run fail inputs selected) :=
  ⟨fun result =>
      ⟨firstFailureAt_of_combine_map_eq_failed run inputs assemble result⟩,
    fun witness => by
      rcases witness with ⟨⟨selected, path⟩⟩
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

/-!
The search module's `collect_eq_identified` exposes its aligned terms through
`Exists`, which is appropriate for proposition-level inversion but cannot feed
a Type-valued structural trace.  The two definitions below perform the same
finite-list inversion into dependent data.  Their noncomputable marker is only
a Lean code-generator limitation for the dependent list recursor; the bodies
use structural recursion and constructor equality, with no classical axiom.
-/

/-- Type-valued alignment data for a successful `collect` invocation. -/
structure CollectedIdentifiedData
    {S : ObservedSignature}
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (pending : List (IdentificationOutcome S))
    (acc : List (ProbabilityTerm S)) (term : ProbabilityTerm S) where
  terms : List (ProbabilityTerm S)
  pending_eq : pending = terms.map IdentificationOutcome.identified
  term_eq : term = assemble (acc.reverse ++ terms)

/-- Construct the Type-valued alignment data for a successful collection. -/
noncomputable def collectIdentifiedData
    {S : ObservedSignature}
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (pending : List (IdentificationOutcome S))
    (acc : List (ProbabilityTerm S)) (term : ProbabilityTerm S)
    (result : collect assemble pending acc =
      IdentificationOutcome.identified term) :
    CollectedIdentifiedData assemble pending acc term := by
  induction pending generalizing acc term with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      simpa [collect] using result.symm
  | cons head rest inductionHypothesis =>
      cases headResult : head with
      | identified headTerm =>
          have tailResult :
              collect assemble rest (headTerm :: acc) =
                IdentificationOutcome.identified term := by
            simpa [collect, headResult] using result
          rcases inductionHypothesis (headTerm :: acc) term tailResult with
            ⟨terms, restEq, termEq⟩
          refine ⟨headTerm :: terms, ?_, ?_⟩
          · simp [restEq]
          · simpa [List.reverse_cons, List.append_assoc] using termEq
      | failed fail =>
          simp [collect, headResult] at result
      | unfinished =>
          simp [collect, headResult] at result

/-- Type-valued alignment data for a successful `combine` invocation. -/
structure CombinedIdentifiedData
    {S : ObservedSignature}
    (outcomes : List (IdentificationOutcome S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (term : ProbabilityTerm S) where
  terms : List (ProbabilityTerm S)
  outcomes_eq : outcomes = terms.map IdentificationOutcome.identified
  term_eq : term = assemble terms

/-- Construct the Type-valued alignment data for a successful combination. -/
noncomputable def combineIdentifiedData
    {S : ObservedSignature}
    (outcomes : List (IdentificationOutcome S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (term : ProbabilityTerm S)
    (result : combine outcomes assemble =
      IdentificationOutcome.identified term) :
    CombinedIdentifiedData outcomes assemble term := by
  rcases collectIdentifiedData assemble outcomes [] term result with
    ⟨terms, outcomesEq, termEq⟩
  exact ⟨terms, outcomesEq, by simpa using termEq⟩

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
    (run : α -> IdentificationOutcome S) : List α -> α -> Type u
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
noncomputable def firstUnfinishedAt_of_collect_map_eq_unfinished
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (acc : List (ProbabilityTerm S))
    (result : collect assemble (inputs.map run) acc =
      IdentificationOutcome.unfinished) :
    Sigma fun selected => FirstUnfinishedAt run inputs selected := by
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
noncomputable def firstUnfinishedAt_of_combine_map_eq_unfinished
    {S : ObservedSignature} {α : Type u}
    (run : α -> IdentificationOutcome S) (inputs : List α)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (result : combine (inputs.map run) assemble =
      IdentificationOutcome.unfinished) :
    Sigma fun selected => FirstUnfinishedAt run inputs selected :=
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
      Nonempty (Sigma fun selected => FirstUnfinishedAt run inputs selected) :=
  ⟨fun result =>
      ⟨firstUnfinishedAt_of_combine_map_eq_unfinished run inputs assemble
        result⟩,
    fun witness => by
      rcases witness with ⟨⟨selected, path⟩⟩
      exact combine_map_eq_unfinished_of_firstUnfinishedAt run assemble path⟩

end IdentificationOutcome

end Causality
end Thesis
