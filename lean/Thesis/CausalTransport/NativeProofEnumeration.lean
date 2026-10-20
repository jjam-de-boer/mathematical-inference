import Thesis.Causality.DerivationEnumeration
import Thesis.CausalTransport.NativeGuardCompilation

namespace Thesis.Causality

open Probability

/-!
# Bounded native proof catalogues, without formula selection

Enumerate the already declared serialized language at explicit expression-
and proof-tree depth budgets. The native wrapper consumes one proof level;
its `actionOne` branch is a leaf. All dictionary indices use the full public
signature, including declared null intervention values. The expression
budget bounds explicit term fields throughout the code, not just its source
and printed answer; primitive endpoint expansions retain their existing
meaning and are not newly truncated by that budget.

Each enumerated code is passed to the existing source/graph/action-free
checker and automatic observable-guard compiler. Successful results form a
finite list of actual checked native formulas. No first available formula
is selected. Duplicate formulas and empty guards are permitted.

The coverage theorem is relative to this grammar and these budgets: any
passing supplied guard for a bounded proof has its acceptance preserved by
a member of the generated catalogue on every covered original model.
Fixed-DAG and projection-wide adapters supply the existing constructed
coverage theorems. Original conditional-source support remains a separate
soundness premise, as in the underlying checker.

No claim concerns arbitrary Lean semantic proofs, feasible execution of huge
full catalogues, coverage beyond the chosen budgets, or a universal stopping
test. Exhausting this list does not establish general non-identifiability.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace ProbabilityCode

variable {graph : ObservedGraph S} {profiles : List (NativeTemplateInstance Q)}

namespace NativeProofCode

def Within (signature : ObservedSignature) (expressionDepth : Nat) : Nat → NativeProofCode → Prop
  | 0, _ => False
  | depth + 1, .derivation code => code.Within (.ofSignature signature) expressionDepth depth
  | _ + 1, .actionOne code => code.Within (.ofSignature signature)

instance decidableWithin (signature : ObservedSignature) (expressionDepth proofDepth : Nat) (code : NativeProofCode) :
    Decidable (code.Within signature expressionDepth proofDepth) := by
  cases proofDepth <;> cases code <;> simp only [Within] <;> infer_instance

def enumerate (signature : ObservedSignature) (expressionDepth : Nat) : Nat → List NativeProofCode
  | 0 => []
  | depth + 1 =>
      (DerivationCode.enumerate (.ofSignature signature) expressionDepth depth).map derivation ++
        (KernelCode.enumerate (.ofSignature signature)).map actionOne

theorem mem_enumerate_iff (signature : ObservedSignature) (expressionDepth proofDepth : Nat)
    (code : NativeProofCode) :
    code ∈ enumerate signature expressionDepth proofDepth ↔ code.Within signature expressionDepth proofDepth := by
  cases proofDepth <;> cases code <;>
    simp [enumerate, Within, DerivationCode.mem_enumerate_iff, KernelCode.mem_enumerate_iff]

/-- This constructs the entire list of successful bounded certificates; it
does not pick a representative proof or an available observational answer. -/
def catalogueOn (graph : ObservedGraph S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat) : List (CheckedNativeFormula graph profiles) :=
  (enumerate S expressionDepth proofDepth).filterMap (fun proof => proof.compileGuardOn graph profiles source)

theorem mem_catalogueOn_iff (graph : ObservedGraph S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat) (checked : CheckedNativeFormula graph profiles) :
    checked ∈ catalogueOn graph profiles source expressionDepth proofDepth ↔
      ∃ proof : NativeProofCode, proof.Within S expressionDepth proofDepth ∧ proof.compileGuardOn graph profiles source = some checked := by
  simp only [catalogueOn, List.mem_filterMap, mem_enumerate_iff]

def catalogueFixed (projection : FiniteLatentProjection S) (source : TermCode) (expressionDepth proofDepth : Nat) :=
  catalogueOn projection.observedGraph projection.completeSupportCatalogue source expressionDepth proofDepth

def catalogueProjected (graph : ObservedGraph S) (source : TermCode) (expressionDepth proofDepth : Nat) :=
  catalogueOn graph graph.cliqueRootProjection.completeSupportCatalogue source expressionDepth proofDepth

end NativeProofCode

/-- An accepted supplied guard and an empty seed guard reconstruct the same
source and actual proof. Their compiled versions therefore agree. This
bridges existing supplied certificates to the new bounded catalogue without
requiring an equality decision on semantic proof objects. -/
theorem NativeCertificateCode.compileGuardOn_of_checkOn (code : NativeCertificateCode)
    (checked : CheckedNativeFormula graph profiles) (accepted : code.checkOn graph profiles = some checked) :
    code.proof.compileGuardOn graph profiles code.source = some checked.withCompiledGuard := by
  rcases code with ⟨source, proof, guard⟩
  cases decodedSource : source.decode S with
  | none =>
      simp only [NativeCertificateCode.checkOn, decodedSource, Option.bind_eq_bind,
        Option.bind_none, reduceCtorEq] at accepted
  | some sourceTerm =>
      cases decodedProof : proof.check graph with
      | none =>
          simp only [NativeCertificateCode.checkOn, decodedSource, Option.bind_eq_bind, Option.bind_some,
            decodedProof, Option.bind_none, reduceCtorEq] at accepted
      | some proofTerm =>
          by_cases sameSource : proofTerm.left = sourceTerm
          · by_cases actionFree : proofTerm.right.actionFreeCheck = true
            · by_cases guardChecked : NativeSupportGuard.check profiles proofTerm.demand guard = true
              · have same : (⟨sourceTerm, proofTerm, sameSource,
                    (ProbabilityTerm.actionFreeCheck_exact proofTerm.right).mp actionFree,
                    guard, guardChecked⟩ : CheckedNativeFormula graph profiles) = checked := by
                  exact Option.some.inj (by
                    simpa only [NativeCertificateCode.checkOn, decodedSource, Option.bind_eq_bind, Option.bind_some,
                      decodedProof, dif_pos sameSource, dif_pos actionFree, dif_pos guardChecked,
                      Option.pure_def] using accepted)
                cases same
                have emptyChecked : NativeSupportGuard.check profiles proofTerm.demand [] = true := rfl
                simpa only [NativeProofCode.compileGuardOn, NativeCertificateCode.checkOn, decodedSource,
                  Option.bind_eq_bind, Option.bind_some, decodedProof, dif_pos sameSource, dif_pos actionFree,
                  dif_pos emptyChecked, Option.pure_def, Option.map_some, CheckedNativeFormula.withCompiledGuard]
              · simp only [NativeCertificateCode.checkOn, decodedSource, Option.bind_eq_bind, Option.bind_some, decodedProof,
                  dif_pos sameSource, dif_pos actionFree, dif_neg guardChecked, reduceCtorEq] at accepted
            · simp only [NativeCertificateCode.checkOn, decodedSource, Option.bind_eq_bind, Option.bind_some, decodedProof,
                dif_pos sameSource, dif_neg actionFree, reduceCtorEq] at accepted
          · simp only [NativeCertificateCode.checkOn, decodedSource, Option.bind_eq_bind, Option.bind_some, decodedProof,
              dif_neg sameSource, reduceCtorEq] at accepted

/-- Bounded completeness is about acceptance coverage, not only whether a
raw tree occurs in a list. Every successful supplied guard for this bounded
proof is covered by an actual generated member on the original model. -/
theorem NativeProofCode.catalogueOn_covers (graph : ObservedGraph S) (profiles : List (NativeTemplateInstance Q))
    (expressionDepth proofDepth : Nat) (code : NativeCertificateCode)
    (bounded : code.proof.Within S expressionDepth proofDepth)
    (checked : CheckedNativeFormula graph profiles) (accepted : code.checkOn graph profiles = some checked)
    (model : FiniteHiddenDAGSCM S P)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment) (available : checked.available model.observationalDist reference = true) :
    ∃ generated, generated ∈ NativeProofCode.catalogueOn graph profiles code.source expressionDepth proofDepth ∧
      generated.available model.observationalDist reference = true :=
  ⟨checked.withCompiledGuard,
    (NativeProofCode.mem_catalogueOn_iff graph profiles code.source expressionDepth proofDepth _).mpr
      ⟨code.proof, bounded, code.compileGuardOn_of_checkOn checked accepted⟩,
    checked.withCompiledGuard_available model covered reference available⟩

theorem NativeProofCode.catalogueFixed_covers (projection : FiniteLatentProjection S)
    (expressionDepth proofDepth : Nat) (code : NativeCertificateCode)
    (bounded : code.proof.Within S expressionDepth proofDepth)
    (checked : CheckedNativeFormula projection.observedGraph projection.completeSupportCatalogue)
    (accepted : code.checkFixed projection = some checked)
    (model : FiniteHiddenDAGSCM S projection) (reference : S.Assignment)
    (available : checked.available model.observationalDist reference = true) :
    ∃ generated, generated ∈ NativeProofCode.catalogueFixed projection code.source expressionDepth proofDepth ∧
      generated.available model.observationalDist reference = true :=
  NativeProofCode.catalogueOn_covers _ _ expressionDepth proofDepth code bounded checked accepted
    model model.completeSupportCatalogue_covers reference available

theorem NativeProofCode.catalogueProjected_covers (graph : ObservedGraph S)
    (expressionDepth proofDepth : Nat) (code : NativeCertificateCode)
    (bounded : code.proof.Within S expressionDepth proofDepth)
    (checked : CheckedNativeFormula graph graph.cliqueRootProjection.completeSupportCatalogue)
    (accepted : code.checkProjected graph = some checked)
    (original : ProjectedHiddenDAGModel graph) (reference : S.Assignment)
    (available : checked.available original.model.observationalDist reference = true) :
    ∃ generated, generated ∈ NativeProofCode.catalogueProjected graph code.source expressionDepth proofDepth ∧
      generated.available original.model.observationalDist reference = true :=
  NativeProofCode.catalogueOn_covers _ _ expressionDepth proofDepth code bounded checked accepted
    original.model original.completeSupportCatalogue_covers reference available

end ProbabilityCode
end Thesis.Causality
