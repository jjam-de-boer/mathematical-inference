import Thesis.Causality.ProbabilityTermCode

namespace Thesis.Causality.ProbabilityCode

/-!
# Exact finite enumeration of bounded expression codes

The dictionaries are finite natural-index ranges, not positive-support
values. `ofSignature` uses the full mask and assignment dictionaries, so a
declared but factually null intervention value is not lost. Abstract empty
dictionaries are also allowed by the lower-level enumeration lemmas.

The expression budget counts tree depth: zero permits no expression, and
each constructor consumes one level. It bounds every branch, not only one
selected path. Bounded arity then also bounds total tree size. This is not a
byte-length budget or a bound on the numerical values of probabilities.

The membership theorem is exact in both directions. It certifies syntax
enumeration only; decoding, causal validity and support are separate checks.
The lists can be very large and are not claimed minimal or duplicate-free.
-/

structure CodeDictionaries where
  masks : Nat
  references : Nat
  deriving Repr, DecidableEq

def CodeDictionaries.ofSignature (signature : ObservedSignature) : CodeDictionaries :=
  ⟨(NodeSet.subsets (S := signature) NodeSet.full).length, signature.assignmentEnumeration.length⟩

namespace CodeEnumeration

/-- Constructor products keep each argument's finite source explicit.
Their membership lemmas avoid any enumeration of arbitrary functions. -/
def binary (constructor : A → B → C) (first : List A) (second : List B) : List C :=
  first.flatMap (fun left => second.map (constructor left))

theorem mem_binary (constructor : A → B → C) (first : List A) (second : List B) (value : C) :
    value ∈ binary constructor first second ↔
      ∃ left, left ∈ first ∧ ∃ right, right ∈ second ∧ constructor left right = value := by
  simp only [binary, List.mem_flatMap, List.mem_map]

def ternary (constructor : A → B → C → D) (first : List A) (second : List B) (third : List C) : List D :=
  first.flatMap (fun left => binary (constructor left) second third)

theorem mem_ternary (constructor : A → B → C → D) (first : List A) (second : List B)
    (third : List C) (value : D) :
    value ∈ ternary constructor first second third ↔
      ∃ left, left ∈ first ∧ ∃ middle, middle ∈ second ∧
        ∃ right, right ∈ third ∧ constructor left middle right = value := by
  simp only [ternary, List.mem_flatMap, mem_binary]

end CodeEnumeration

namespace KernelCode

def Within (dictionary : CodeDictionaries) (code : KernelCode) : Prop :=
  code.outcome < dictionary.masks ∧ code.action < dictionary.masks ∧ code.condition < dictionary.masks

def enumerate (dictionary : CodeDictionaries) : List KernelCode :=
  CodeEnumeration.ternary KernelCode.mk (List.range dictionary.masks)
    (List.range dictionary.masks) (List.range dictionary.masks)

theorem mem_enumerate_iff (dictionary : CodeDictionaries) (code : KernelCode) :
    code ∈ enumerate dictionary ↔ code.Within dictionary := by
  cases code
  simp [enumerate, Within, CodeEnumeration.mem_ternary]

end KernelCode

namespace TermCode

/-- Each smaller expression receives the remaining depth. In particular,
an arbitrary expression cannot hide inside an evaluation or weighted branch. -/
def Within (dictionary : CodeDictionaries) : Nat → TermCode → Prop
  | 0, _ => False
  | _ + 1, .zero => True
  | _ + 1, .kernel code => code.Within dictionary
  | depth + 1, .marginalize nodes inner => nodes < dictionary.masks ∧ inner.Within dictionary depth
  | depth + 1, .evaluateAt reference inner => reference < dictionary.references ∧ inner.Within dictionary depth
  | depth + 1, .add left right | depth + 1, .multiply left right
  | depth + 1, .weightedMultiply left right | depth + 1, .divide left right =>
      left.Within dictionary depth ∧ right.Within dictionary depth

def enumerate (dictionary : CodeDictionaries) : Nat → List TermCode
  | 0 => []
  | depth + 1 =>
      let smaller := enumerate dictionary depth
      [.zero] ++ (KernelCode.enumerate dictionary).map .kernel ++
        CodeEnumeration.binary marginalize (List.range dictionary.masks) smaller ++
        CodeEnumeration.binary evaluateAt (List.range dictionary.references) smaller ++
        CodeEnumeration.binary add smaller smaller ++
        CodeEnumeration.binary multiply smaller smaller ++
        CodeEnumeration.binary weightedMultiply smaller smaller ++
        CodeEnumeration.binary divide smaller smaller

/-- Exact bounded syntax coverage. No graph or probability-model premise is
needed, and no conclusion about causal correctness follows from membership. -/
theorem mem_enumerate_iff (dictionary : CodeDictionaries) (depth : Nat) (code : TermCode) :
    code ∈ enumerate dictionary depth ↔ code.Within dictionary depth := by
  induction depth with
  | zero => simp [enumerate, Within]
  | succ depth inductionHypothesis =>
      cases code <;>
        simp [enumerate, Within, CodeEnumeration.mem_binary, inductionHypothesis,
          KernelCode.mem_enumerate_iff]

end TermCode
end Thesis.Causality.ProbabilityCode
