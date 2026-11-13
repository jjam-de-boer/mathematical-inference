import Thesis.CausalTransport.NativeProofEnumeration
import Thesis.Examples.NativeGuardCompilation

namespace Thesis.Causality.Examples.NativeProofEnumeration

open Probability ProbabilityCode NativeSupportProfiles NativeCertificateCheck

/-!
# Bounded syntax coverage and retained native acceptance

Tiny abstract dictionaries test literal executable lists. The actual
three-valued fixture then tests the full declared reference dictionary,
intermediate expression fields, the native-wrapper depth and all primitive
tags. Raw enumeration deliberately retains invalid graphical derivations:
the checker, not the generator, rejects them.

Catalogue membership and native coverage use the symbolic exactness theorem
rather than expanding a combinatorial concrete proof list. The last two
tests exercise original fixed-DAG and projection-wide coverage without
evaluating their enormous complete support catalogues. No selector is used.
-/

def tiny : CodeDictionaries := ⟨1, 1⟩

example : TermCode.enumerate tiny 0 = [] := rfl
example : TermCode.enumerate tiny 1 = [.zero, .kernel ⟨0, 0, 0⟩] := by decide +kernel
example : (DerivationCode.enumerate tiny 0 1).length = 7 := by decide +kernel
example : DerivationCode.enumerate tiny 1 0 = [] := rfl

example : (.add .zero .zero : TermCode) ∈ TermCode.enumerate tiny 2 :=
  (TermCode.mem_enumerate_iff tiny 2 _).mpr (by decide +kernel)

example : ¬ ((.add .zero .zero : TermCode) ∈ TermCode.enumerate tiny 1) := by
  intro member
  exact (by decide +kernel : ¬ TermCode.Within tiny 1 (.add .zero .zero))
    ((TermCode.mem_enumerate_iff tiny 1 _).mp member)

example : NativeProofCode.enumerate signature 1 0 = [] := rfl

theorem reflexivity_enumerated : (.derivation (.refl source) : NativeProofCode) ∈ NativeProofCode.enumerate signature 1 2 :=
  (NativeProofCode.mem_enumerate_iff signature 1 2 _).mpr (by decide +kernel)

theorem wrapper_consumes_depth : ¬ ((.derivation (.refl source) : NativeProofCode) ∈ NativeProofCode.enumerate signature 1 1) := by
  intro member
  exact (by decide +kernel : ¬ NativeProofCode.Within signature 1 1 (.derivation (.refl source)))
    ((NativeProofCode.mem_enumerate_iff signature 1 1 _).mp member)

/-- A kernel-only native leaf needs no explicit expression field. The full
mask dictionary still bounds all three of its kernel indices. -/
example : (.actionOne ⟨1, 1, 0⟩ : NativeProofCode) ∈ NativeProofCode.enumerate signature 0 1 :=
  (NativeProofCode.mem_enumerate_iff signature 0 1 _).mpr (by decide +kernel)

def hiddenBadReference : NativeProofCode := .derivation (.symm (.refl (.evaluateAt 3 source)))

theorem intermediate_reference_bounded : ¬ (hiddenBadReference ∈ NativeProofCode.enumerate signature 2 3) := by
  intro member
  exact (by decide +kernel : ¬ hiddenBadReference.Within signature 2 3)
    ((NativeProofCode.mem_enumerate_iff signature 2 3 _).mp member)

theorem graphical_failure_still_enumerated :
    (.derivation (.primitive .rule1 ⟨1, 1, 0, 0⟩) : NativeProofCode) ∈ NativeProofCode.enumerate signature 0 2 :=
  (NativeProofCode.mem_enumerate_iff signature 0 2 _).mpr (by decide +kernel)

example : ((NativeProofCode.derivation (.primitive .rule1 ⟨1, 1, 0, 0⟩)).check projection.observedGraph).isSome = false := by decide +kernel

/-- Intermediate support failure is not a reason to delete a syntactically
bounded tree. Its compiled guard, tested separately, excludes that null cell. -/
example : (.derivation strictCycle : NativeProofCode) ∈ NativeProofCode.enumerate signature 0 4 :=
  (NativeProofCode.mem_enumerate_iff signature 0 4 _).mpr (by decide +kernel)

theorem good_checked : goodCode.checkOn projection.observedGraph profiles = some good :=
  (Option.some_get unchanged_source_accepted).symm

theorem generated_member : good.withCompiledGuard ∈
    NativeProofCode.catalogueOn projection.observedGraph profiles source 1 2 :=
  (NativeProofCode.mem_catalogueOn_iff projection.observedGraph profiles source 1 2 _).mpr
    ⟨goodCode.proof, by decide +kernel, goodCode.compileGuardOn_of_checkOn good good_checked⟩

theorem null_cell_covered :
    ∃ generated, generated ∈ NativeProofCode.catalogueOn projection.observedGraph profiles source 1 2 ∧
      generated.available entry.model.observationalDist (reference 2) = true :=
  NativeProofCode.catalogueOn_covers _ _ 1 2 goodCode (by decide +kernel) good good_checked
    entry.model ⟨entry.uniformSupport, List.mem_cons_self, entry.uniformSupport_agreement⟩ (reference 2) good_available

theorem fixed_original_coverage (expressionDepth proofDepth : Nat) (code : NativeCertificateCode)
    (bounded : code.proof.Within signature expressionDepth proofDepth)
    (checked : CheckedNativeFormula projection.observedGraph projection.completeSupportCatalogue)
    (accepted : code.checkFixed projection = some checked)
    (available : checked.available entry.model.observationalDist (reference 2) = true) :
    ∃ generated, generated ∈ NativeProofCode.catalogueFixed projection code.source expressionDepth proofDepth ∧
      generated.available entry.model.observationalDist (reference 2) = true :=
  NativeProofCode.catalogueFixed_covers projection expressionDepth proofDepth code bounded checked accepted
    entry.model (reference 2) available

theorem projection_original_coverage (expressionDepth proofDepth : Nat) (code : NativeCertificateCode)
    (bounded : code.proof.Within signature expressionDepth proofDepth)
    (checked : CheckedNativeFormula projection.observedGraph projection.observedGraph.cliqueRootProjection.completeSupportCatalogue)
    (accepted : code.checkProjected projection.observedGraph = some checked)
    (available : checked.available projected.model.observationalDist (reference 2) = true) :
    ∃ generated, generated ∈ NativeProofCode.catalogueProjected projection.observedGraph code.source expressionDepth proofDepth ∧
      generated.available projected.model.observationalDist (reference 2) = true :=
  NativeProofCode.catalogueProjected_covers projection.observedGraph expressionDepth proofDepth code bounded checked accepted
    projected (reference 2) available

end Thesis.Causality.Examples.NativeProofEnumeration
