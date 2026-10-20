import Thesis.Causality.DerivationCode
import Thesis.Causality.ProbabilityTermEnumeration

namespace Thesis.Causality.ProbabilityCode

/-!
# Exhaustive bounded enumeration of serialized derivations

There are two independent structural budgets. `expressionDepth` bounds every
explicit expression carried anywhere in a proof code, including expressions
inside intermediate subproofs and endpoint-reindexing constructors.
`proofDepth` bounds the entire derivation tree. Zero permits no derivation;
each proof constructor consumes one level. All indices range over the actual
finite dictionaries when the signature adapter is used.

Primitive rules generate their existing endpoint expressions when checked;
the expression budget concerns encoded expression fields, not the size of
those derived expansions. They introduce no unbounded syntax parameters.
This distinction is part of the precise bounded-search claim.

Every constructor in `DerivationCode` is included. Membership does not assert
that a graphical rule, endpoint join or probability support check succeeds.
Those remain the job of the existing certificate checker. There is no
unbounded search, formula selector or universal stopping argument here.
-/

namespace QuadCode

def Within (dictionary : CodeDictionaries) (code : QuadCode) : Prop :=
  code.x < dictionary.masks ∧ code.y < dictionary.masks ∧
    code.z < dictionary.masks ∧ code.w < dictionary.masks

def enumerate (dictionary : CodeDictionaries) : List QuadCode :=
  (List.range dictionary.masks).flatMap (fun x =>
    CodeEnumeration.ternary (QuadCode.mk x) (List.range dictionary.masks)
      (List.range dictionary.masks) (List.range dictionary.masks))

theorem mem_enumerate_iff (dictionary : CodeDictionaries) (code : QuadCode) :
    code ∈ enumerate dictionary ↔ code.Within dictionary := by
  cases code
  simp [enumerate, Within, List.mem_flatMap, CodeEnumeration.mem_ternary]

end QuadCode

def PrimitiveCode.enumerate : List PrimitiveCode :=
  [.rule1, .rule2, .rule3, .marginalization, .conditioning, .chain, .weightedChain]

@[simp] theorem PrimitiveCode.mem_enumerate (kind : PrimitiveCode) : kind ∈ PrimitiveCode.enumerate := by
  cases kind <;> decide

def CongruenceCode.enumerate : List CongruenceCode := [.add, .multiply, .weightedMultiply, .divide]

@[simp] theorem CongruenceCode.mem_enumerate (kind : CongruenceCode) : kind ∈ CongruenceCode.enumerate := by
  cases kind <;> decide

namespace DerivationCode

def Within (dictionary : CodeDictionaries) (expressionDepth : Nat) : Nat → DerivationCode → Prop
  | 0, _ => False
  | _ + 1, .refl term => term.Within dictionary expressionDepth
  | depth + 1, .symm inner => inner.Within dictionary expressionDepth depth
  | depth + 1, .trans first second | depth + 1, .congr _ first second =>
      first.Within dictionary expressionDepth depth ∧ second.Within dictionary expressionDepth depth
  | _ + 1, .primitive _ quad => quad.Within dictionary
  | _ + 1, .multiplyComm left right =>
      left.Within dictionary expressionDepth ∧ right.Within dictionary expressionDepth
  | _ + 1, .multiplyAssoc first second third =>
      first.Within dictionary expressionDepth ∧ second.Within dictionary expressionDepth ∧
        third.Within dictionary expressionDepth
  | depth + 1, .marginalizeCongr nodes inner =>
      nodes < dictionary.masks ∧ inner.Within dictionary expressionDepth depth
  | depth + 1, .evaluateAtCongr reference inner =>
      reference < dictionary.references ∧ inner.Within dictionary expressionDepth depth
  | depth + 1, .eqCongr left right inner =>
      left.Within dictionary expressionDepth ∧ right.Within dictionary expressionDepth ∧
        inner.Within dictionary expressionDepth depth

def enumerate (dictionary : CodeDictionaries) (expressionDepth : Nat) : Nat → List DerivationCode
  | 0 => []
  | depth + 1 =>
      let terms := TermCode.enumerate dictionary expressionDepth
      let smaller := enumerate dictionary expressionDepth depth
      terms.map refl ++ smaller.map symm ++
        CodeEnumeration.binary trans smaller smaller ++
        CodeEnumeration.binary primitive PrimitiveCode.enumerate (QuadCode.enumerate dictionary) ++
        CodeEnumeration.binary multiplyComm terms terms ++
        CodeEnumeration.ternary multiplyAssoc terms terms terms ++
        CodeEnumeration.binary marginalizeCongr (List.range dictionary.masks) smaller ++
        CodeEnumeration.binary evaluateAtCongr (List.range dictionary.references) smaller ++
        CodeEnumeration.ternary congr CongruenceCode.enumerate smaller smaller ++
        CodeEnumeration.ternary eqCongr terms terms smaller

/-- Exhaustiveness and exclusion are both proved for the same explicit
budget. No plateau in a sequence of larger budgets is a termination test. -/
theorem mem_enumerate_iff (dictionary : CodeDictionaries) (expressionDepth proofDepth : Nat)
    (code : DerivationCode) :
    code ∈ enumerate dictionary expressionDepth proofDepth ↔ code.Within dictionary expressionDepth proofDepth := by
  induction proofDepth with
  | zero => simp [enumerate, Within]
  | succ depth inductionHypothesis =>
      cases code <;>
        simp [enumerate, Within, CodeEnumeration.mem_binary, CodeEnumeration.mem_ternary,
          TermCode.mem_enumerate_iff, QuadCode.mem_enumerate_iff, inductionHypothesis]

end DerivationCode
end Thesis.Causality.ProbabilityCode
