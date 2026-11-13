import Thesis.CausalTransport.NativeDemandEncoding
import Thesis.CausalTransport.ObservationalFormulaSupport

namespace Thesis.Causality.NativeTargetRecognition

open Probability NativeDemandTyping NativeDemandEncoding

/-!
# Finite bottom-up states for target-formula recognition

A state retains the root demand, native undefined/zero/positive tables at
every supplied profile/reference, an observational status table, annotation
coherence and the syntactic action-free bit. None of its fields contains a
term, sibling, proof or rational value. The observational pattern is a fixed
input to the transitions, not an inferred causal model or a source-support
witness. Hypothetical patterns are allowed; evaluator agreement later uses
the support of an actual observed law.

All constructors use only the finite node label and child states. In
particular marginalization retains every substituted reference, and a
weighted factor receives its actual positive-weight demand. Its syntax and
annotation coherence are retained even when that demand is empty.

The explicit state catalogue is a finiteness witness, not an execution plan:
it can be very large and is never evaluated by the recognizer. Recognition
folds the supplied tree without enumerating candidate trees. Equal states do not establish a causal
equation, join proof endpoints, or identify probability values.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

abbrev NativeStatus (profiles : List (NativeTemplateInstance P)) :=
  Fin profiles.length → S.Assignment → ProbabilityResult.Status

structure State (profiles : List (NativeTemplateInstance P)) where
  demand : Demand profiles
  native : NativeStatus profiles
  observational : S.Assignment → ProbabilityResult.Status
  coherent : Bool
  actionFree : Bool

namespace State

variable {profiles : List (NativeTemplateInstance P)}

/-- Root-demand equality and internal coherence are separate finite tests. -/
def annotations (state : State profiles) (requested : Demand profiles) : Bool :=
  demandEqual profiles requested state.demand && state.coherent

def zero (requested : Demand profiles) : State profiles :=
  ⟨requested, fun _ _ => .zero, fun _ => .zero, true, true⟩

def kernel (pattern : S.Assignment → Bool) (requested : Demand profiles) (current : Kernel S) : State profiles :=
  ⟨requested, fun index reference => ProbabilityResult.status ((profiles.get index).model.kernelDenote current reference),
    (ProbabilityTerm.kernel current).supportStatus pattern, true, NodeSet.isEmpty current.action⟩

def marginalize (requested : Demand profiles) (nodes : NodeSet S) (inner : State profiles) : State profiles :=
  ⟨requested,
    fun index reference => ProbabilityResult.Status.sum
      ((ProbabilityTerm.marginalAssignments S nodes reference).map (inner.native index)),
    fun reference => ProbabilityResult.Status.sum
      ((ProbabilityTerm.marginalAssignments S nodes reference).map inner.observational),
    inner.annotations (marginalDemand profiles requested nodes), inner.actionFree⟩

def evaluateAt (requested : Demand profiles) (fixed : S.Assignment) (inner : State profiles) : State profiles :=
  ⟨requested, fun index _ => inner.native index fixed, fun _ => inner.observational fixed,
    inner.annotations (fixedDemand profiles requested fixed), inner.actionFree⟩

/-- Strict arithmetic checks both children's annotations. Denominator
positivity is retained by the status operation, rather than assumed here. -/
def strictBinary (operation : ProbabilityResult.Status → ProbabilityResult.Status → ProbabilityResult.Status)
    (requested : Demand profiles) (left right : State profiles) : State profiles :=
  ⟨requested, fun index reference => operation (left.native index reference) (right.native index reference),
    fun reference => operation (left.observational reference) (right.observational reference),
    left.annotations requested && right.annotations requested, left.actionFree && right.actionFree⟩

def add := @strictBinary S P profiles ProbabilityResult.Status.add
def multiply := @strictBinary S P profiles ProbabilityResult.Status.multiply
def divide := @strictBinary S P profiles ProbabilityResult.Status.divide

def weightedMultiply (requested : Demand profiles) (weight factor : State profiles) : State profiles :=
  ⟨requested,
    fun index reference => ProbabilityResult.Status.weightedMultiply (weight.native index reference) (factor.native index reference),
    fun reference => ProbabilityResult.Status.weightedMultiply (weight.observational reference) (factor.observational reference),
    weight.annotations requested && factor.annotations (positiveDemand profiles requested weight.native),
    weight.actionFree && factor.actionFree⟩

end State

variable {profiles : List (NativeTemplateInstance P)}

/-- Deterministic transitions on the finite ranked alphabet. Malformed
arity is refused; no default child or fabricated successful state is used. -/
def transition (pattern : S.Assignment → Bool) : Symbol profiles → List (State profiles) → Option (State profiles)
  | .zero requested, [] => some (State.zero requested)
  | .kernel requested current, [] => some (State.kernel pattern requested current)
  | .marginalize requested nodes, [inner] => some (State.marginalize requested nodes inner)
  | .evaluateAt requested fixed, [inner] => some (State.evaluateAt requested fixed inner)
  | .add requested, [left, right] => some (State.add requested left right)
  | .multiply requested, [left, right] => some (State.multiply requested left right)
  | .weightedMultiply requested, [weight, factor] => some (State.weightedMultiply requested weight factor)
  | .divide requested, [numerator, denominator] => some (State.divide requested numerator denominator)
  | _, _ => none

/-- Fold the actual tree. Only its label and previously computed child
states contribute to the parent state. The state catalogue is not run. -/
def summarize (pattern : S.Assignment → Bool) : Term profiles → State profiles
  | .zero requested => State.zero requested
  | .kernel requested current => State.kernel pattern requested current
  | .marginalize requested nodes inner => State.marginalize requested nodes (summarize pattern inner)
  | .evaluateAt requested fixed inner => State.evaluateAt requested fixed (summarize pattern inner)
  | .add requested left right => State.add requested (summarize pattern left) (summarize pattern right)
  | .multiply requested left right => State.multiply requested (summarize pattern left) (summarize pattern right)
  | .weightedMultiply requested weight factor => State.weightedMultiply requested (summarize pattern weight) (summarize pattern factor)
  | .divide requested numerator denominator => State.divide requested (summarize pattern numerator) (summarize pattern denominator)

theorem transition_summarize (pattern : S.Assignment → Bool) (term : Term profiles) :
    transition pattern term.label (term.children.map (summarize pattern)) = some (summarize pattern term) := by
  cases term <;> rfl

theorem demand_summarize (pattern : S.Assignment → Bool) (term : Term profiles) :
    (summarize pattern term).demand = term.demand := by cases term <;> rfl

theorem native_summarize (pattern : S.Assignment → Bool) (term : Term profiles) :
    (summarize pattern term).native = termStatus profiles term.erase := by
  induction term <;>
    simp only [summarize, State.zero, State.kernel, State.marginalize, State.evaluateAt,
      State.add, State.multiply, State.weightedMultiply, State.divide, State.strictBinary, Term.erase, termStatus, *]

theorem observational_summarize (pattern : S.Assignment → Bool) (term : Term profiles) :
    (summarize pattern term).observational = term.erase.supportStatus pattern := by
  induction term <;>
    simp only [summarize, State.zero, State.kernel, State.marginalize, State.evaluateAt,
      State.add, State.multiply, State.weightedMultiply, State.divide, State.strictBinary, Term.erase,
      ProbabilityTerm.supportStatus, *]

theorem actionFree_summarize (pattern : S.Assignment → Bool) (term : Term profiles) :
    (summarize pattern term).actionFree = term.actionFreeCheck := by
  induction term <;>
    simp only [summarize, State.zero, State.kernel, State.marginalize, State.evaluateAt,
      State.add, State.multiply, State.weightedMultiply, State.divide, State.strictBinary, Term.actionFreeCheck, *]

namespace State

def referenceStatuses (signature : ObservedSignature) : List (signature.Assignment → ProbabilityResult.Status) :=
  FiniteFunctionTable.functionEnumeration (referenceWitness signature) [.undefined, .zero, .positive]

theorem mem_referenceStatuses (signature : ObservedSignature) (table : signature.Assignment → ProbabilityResult.Status) :
    table ∈ referenceStatuses signature := by
  apply FiniteFunctionTable.functionEnumeration_complete
  intro value
  cases value <;> simp only [List.mem_cons, true_or, or_true, reduceCtorEq]

def nativeStatuses (profiles : List (NativeTemplateInstance P)) : List (NativeStatus profiles) :=
  FiniteProduct.enumeration profiles.length (fun _ => S.Assignment → ProbabilityResult.Status) (fun _ => referenceStatuses S)

theorem mem_nativeStatuses (profiles : List (NativeTemplateInstance P)) (table : NativeStatus profiles) :
    table ∈ nativeStatuses profiles :=
  FiniteProduct.enumeration_complete _ _ _ (fun _ => mem_referenceStatuses S) table

/-- Explicit finite coverage of all states, including states unreachable
from actual terms. This opt-in list imposes no tree-size or proof-size bound. -/
def enumeration (profiles : List (NativeTemplateInstance P)) : List (State profiles) :=
  (demandCatalogue profiles).flatMap (fun requested =>
    (nativeStatuses profiles).flatMap (fun native =>
      (referenceStatuses S).flatMap (fun observational =>
        [false, true].flatMap (fun coherent =>
          [false, true].map (fun actionFree => ⟨requested, native, observational, coherent, actionFree⟩)))))

private theorem bool_listed (value : Bool) : value ∈ [false, true] := by
  cases value <;> simp only [List.mem_cons, true_or, or_true]

theorem mem_enumeration (state : State profiles) : state ∈ enumeration profiles := by
  apply List.mem_flatMap.mpr
  refine ⟨state.demand, mem_demandCatalogue profiles _, List.mem_flatMap.mpr ?_⟩
  refine ⟨state.native, mem_nativeStatuses profiles _, List.mem_flatMap.mpr ?_⟩
  refine ⟨state.observational, mem_referenceStatuses S _, List.mem_flatMap.mpr ?_⟩
  refine ⟨state.coherent, bool_listed _, List.mem_map.mpr ?_⟩
  exact ⟨state.actionFree, bool_listed _, by cases state; rfl⟩

end State
end Thesis.Causality.NativeTargetRecognition
