import Thesis.Causality.ProbabilityTermEquality
import Thesis.Causality.NodeSetEnumeration

namespace Thesis.Causality

/-!
# Function-free codes for finite probability expressions

Codes contain natural indices, constructor tags and smaller codes. They do
not contain Boolean functions, observed values, equality proofs or semantic
interpretation functions. The public signature supplies the dictionaries:
all node masks and all declared observed assignments, including null values.
An out-of-range index is rejected, never replaced by a default value.

This is an abstract serialized language, not a byte parser or a formula
enumerator. Its recursive trees are unbounded; a future bounded search must
bound every intermediate expression separately. Decoding proves neither
causal validity nor support. Those are separate certificate checks.
-/

namespace ProbabilityCode

def mask (signature : ObservedSignature) (index : Nat) : Option (NodeSet signature) :=
  (NodeSet.subsets (S := signature) NodeSet.full)[index]?

def assignment (signature : ObservedSignature) (index : Nat) : Option signature.Assignment :=
  signature.assignmentEnumeration[index]?

structure KernelCode where
  outcome : Nat
  action : Nat
  condition : Nat
  deriving Repr, DecidableEq

def KernelCode.decode (signature : ObservedSignature) (code : KernelCode) : Option (Kernel signature) := do
  let outcome ← mask signature code.outcome
  let action ← mask signature code.action
  let condition ← mask signature code.condition
  pure ⟨outcome, action, condition⟩

inductive TermCode where
  | zero
  | kernel (code : KernelCode)
  | marginalize (nodes : Nat) (inner : TermCode)
  | evaluateAt (reference : Nat) (inner : TermCode)
  | add (left right : TermCode)
  | multiply (left right : TermCode)
  | weightedMultiply (weight factor : TermCode)
  | divide (numerator denominator : TermCode)
  deriving Repr, DecidableEq

def TermCode.decode (signature : ObservedSignature) : TermCode → Option (ProbabilityTerm signature)
  | .zero => some .zero
  | .kernel code => return .kernel (← code.decode signature)
  | .marginalize nodes inner => return .marginalize (← mask signature nodes) (← inner.decode signature)
  | .evaluateAt reference inner => return .evaluateAt (← assignment signature reference) (← inner.decode signature)
  | .add left right => return .add (← left.decode signature) (← right.decode signature)
  | .multiply left right => return .multiply (← left.decode signature) (← right.decode signature)
  | .weightedMultiply weight factor => return .weightedMultiply (← weight.decode signature) (← factor.decode signature)
  | .divide numerator denominator => return .divide (← numerator.decode signature) (← denominator.decode signature)

end ProbabilityCode

namespace ProbabilityTerm

/-- A printed observational formula must contain no actionful kernel,
including inside a currently zero-weighted or undefined branch. -/
def actionFreeCheck : ProbabilityTerm S → Bool
  | .zero => true
  | .kernel current => NodeSet.isEmpty current.action
  | .marginalize _ inner => inner.actionFreeCheck
  | .evaluateAt _ inner => inner.actionFreeCheck
  | .add left right | .multiply left right | .weightedMultiply left right | .divide left right =>
      left.actionFreeCheck && right.actionFreeCheck

theorem actionFreeCheck_exact (term : ProbabilityTerm S) : term.actionFreeCheck = true ↔ term.ActionFree := by
  induction term <;>
    simp [actionFreeCheck, ActionFree, NodeSet.isEmpty_eq_true_iff, *]

end ProbabilityTerm
end Thesis.Causality
