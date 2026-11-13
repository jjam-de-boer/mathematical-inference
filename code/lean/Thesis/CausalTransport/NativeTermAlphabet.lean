import Thesis.CausalTransport.NativeTypedPrimitives

namespace Thesis.Causality.NativeDemandEncoding

open Probability ProbabilityCode NativeDemandTyping

/-!
# A finite alphabet for demand-annotated probability terms

A symbol contains only its constructor tag, a demand table, and finite
kernel/mask/reference parameters. An unchanged sibling is a subtree, never
a symbol parameter: whole expression frames would give an infinite alphabet.
Some finite tables retain the codebase's function representation; the
explicit enumeration and its completeness proof establish their finiteness.
This is internal labelled syntax, not a new untrusted parser.

Strict multiplication has one symbol per demand. Operand or result grades
are not part of that symbol, so later associativity/commutativity treatment
can retain the same operation throughout a product. No AC quotient, context
encoding, equation, or termination theorem is introduced here. The finite
alphabet does not bound the size or number of its trees.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

inductive Symbol (profiles : List (NativeTemplateInstance P)) where
  | zero (demand : Demand profiles)
  | kernel (demand : Demand profiles) (kernel : Kernel S)
  | marginalize (demand : Demand profiles) (nodes : NodeSet S)
  | evaluateAt (demand : Demand profiles) (reference : S.Assignment)
  | add (demand : Demand profiles)
  | multiply (demand : Demand profiles)
  | weightedMultiply (demand : Demand profiles)
  | divide (demand : Demand profiles)

namespace Symbol

def arity {profiles : List (NativeTemplateInstance P)} : Symbol profiles → Nat
  | .zero _ | .kernel _ _ => 0
  | .marginalize _ _ | .evaluateAt _ _ => 1
  | .add _ | .multiply _ | .weightedMultiply _ | .divide _ => 2

def demand {profiles : List (NativeTemplateInstance P)} : Symbol profiles → Demand profiles
  | .zero requested | .kernel requested _ | .marginalize requested _ | .evaluateAt requested _
  | .add requested | .multiply requested | .weightedMultiply requested | .divide requested => requested

private theorem mask_mem {signature : ObservedSignature} (nodes : NodeSet signature) : nodes ∈ NodeSet.subsets NodeSet.full :=
  (NodeSet.subsets_member_iff _ _).mpr (fun _ _ => rfl)

def kernels (signature : ObservedSignature) : List (Kernel signature) :=
  CodeEnumeration.ternary Kernel.mk (NodeSet.subsets NodeSet.full)
    (NodeSet.subsets NodeSet.full) (NodeSet.subsets NodeSet.full)

theorem mem_kernels (signature : ObservedSignature) (kernel : Kernel signature) : kernel ∈ kernels signature := by
  exact (CodeEnumeration.mem_ternary _ _ _ _ _).mpr
    ⟨kernel.outcome, mask_mem _, kernel.action, mask_mem _, kernel.condition, mask_mem _, by cases kernel; rfl⟩

/-- Explicit finiteness of labels, independently of term or proof depth.
This list is opt-in and can be large; no full-tree enumeration is performed. -/
def enumeration (profiles : List (NativeTemplateInstance P)) : List (Symbol profiles) :=
  (demandCatalogue profiles).flatMap (fun requested =>
    [.zero requested, .add requested, .multiply requested, .weightedMultiply requested, .divide requested] ++
      (kernels S).map (.kernel requested) ++
      (NodeSet.subsets NodeSet.full).map (.marginalize requested) ++
      S.assignmentEnumeration.map (.evaluateAt requested))

theorem mem_enumeration {profiles : List (NativeTemplateInstance P)} (symbol : Symbol profiles) :
    symbol ∈ enumeration profiles := by
  apply List.mem_flatMap.mpr
  refine ⟨symbol.demand, mem_demandCatalogue profiles symbol.demand, ?_⟩
  cases symbol <;> simp only [demand, List.mem_append]
  case zero => exact Or.inl (Or.inl (Or.inl (by simp only [List.mem_cons, true_or])))
  case add => exact Or.inl (Or.inl (Or.inl (by simp only [List.mem_cons, true_or, or_true])))
  case multiply => exact Or.inl (Or.inl (Or.inl (by simp only [List.mem_cons, true_or, or_true])))
  case weightedMultiply => exact Or.inl (Or.inl (Or.inl (by simp only [List.mem_cons, true_or, or_true])))
  case divide => exact Or.inl (Or.inl (Or.inl (by simp only [List.mem_cons, true_or, or_true])))
  case kernel requested kernel => exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (mem_kernels S kernel))))
  case marginalize requested nodes => exact Or.inl (Or.inr (List.mem_map_of_mem (mask_mem nodes)))
  case evaluateAt requested reference => exact Or.inr (List.mem_map_of_mem (S.assignmentEnumeration_complete reference))

end Symbol

end Thesis.Causality.NativeDemandEncoding
