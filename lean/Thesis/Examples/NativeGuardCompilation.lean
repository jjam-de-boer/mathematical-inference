import Thesis.CausalTransport.NativeGuardCompilation
import Thesis.Examples.NativeCertificateCheck

namespace Thesis.Causality.Examples.NativeGuardCompilation

open Probability ProbabilityCode NativeSupportProfiles NativeCertificateCheck

/-!
# Generated guards recover supported cells without hiding proof failures

The old reflexivity certificate deliberately listed only the null outcome
reference. Compiling its guard also admits the other represented reference
cells, without changing its source or formula. A strict chain/inverse cycle
instead loses the null cell with its unsupported intermediate, even though
the endpoints there are the same defined expression. This is maximality of
the fixed proof discipline, not semantic maximality of that expression.

The zero-weighted proof still admits its null factor. The probability-one
action leaf admits only the truly almost-sure reference. An available printed
answer may still have an undefined original conditional source; generated
guards do not silently strengthen the separate source-support contract.

All executable cases use tiny explicit actual-profile lists. Whole fixed-DAG
and projection-wide applications are checked through their symbolic coverage
theorems, without evaluating the full structural catalogues.
-/

def compiledGood := good.withCompiledGuard

theorem old_guard_excluded_zero : good.available entry.model.observationalDist (reference 0) = false := by decide +kernel
theorem generated_guard_admits_zero : compiledGood.available entry.model.observationalDist (reference 0) = true := by decide +kernel
theorem generated_guard_keeps_null : compiledGood.available entry.model.observationalDist (reference 2) = true := by decide +kernel

theorem existing_acceptance_preserved : compiledGood.available entry.model.observationalDist (reference 2) = true :=
  good.withCompiledGuard_available entry.model
    ⟨entry.uniformSupport, List.mem_cons_self, entry.uniformSupport_agreement⟩ (reference 2) good_available

noncomputable def additional_cell_sound : entry.model.TermEquivalentAt compiledGood.source compiledGood.formula (reference 0) :=
  compiledGood.soundAt entry.model rfl
    ⟨entry.uniformSupport, List.mem_cons_self, entry.uniformSupport_agreement⟩ (reference 0)
    (ProbabilityResult.supportedOfIsSome _ (by decide +kernel)) generated_guard_admits_zero

def cycle : CheckedNativeFormula projection.observedGraph profiles :=
  ((NativeProofCode.derivation strictCycle).compileGuardOn projection.observedGraph profiles source).get (by decide +kernel)

theorem cycle_supported_cell : cycle.available entry.model.observationalDist (reference 0) = true := by decide +kernel
theorem cycle_null_intermediate_rejected : cycle.available entry.model.observationalDist (reference 2) = false := by decide +kernel

def compiledWeighted : CheckedNativeFormula projection.observedGraph profiles :=
  ((NativeProofCode.derivation weighted).compileGuardOn projection.observedGraph profiles
    (.weightedMultiply .zero nullTerm)).get (by decide +kernel)

example : compiledWeighted.available entry.model.observationalDist (reference 2) = true := by decide +kernel

def compiledActionOne : CheckedNativeFormula projection.observedGraph [almostSureEntry] :=
  ((NativeProofCode.actionOne ⟨1, 1, 0⟩).compileGuardOn projection.observedGraph [almostSureEntry]
    (.kernel ⟨1, 1, 0⟩)).get (by decide +kernel)

example : compiledActionOne.available almostSureEntry.model.observationalDist (reference 0) = true := by decide +kernel
example : compiledActionOne.available almostSureEntry.model.observationalDist (reference 1) = false := by decide +kernel

def compiledNullSource : CheckedNativeFormula projection.observedGraph profiles :=
  (nullSourceCode.proof.compileGuardOn projection.observedGraph profiles nullSourceCode.source).get (by decide +kernel)

example : compiledNullSource.available entry.model.observationalDist (reference 2) = true := by decide +kernel
theorem compiled_null_source_unsupported : ¬ Nonempty (entry.model.TermSupportedAt compiledNullSource.source (reference 2)) := by
  intro ⟨supported⟩
  have actual : (entry.model.termDenote compiledNullSource.source (reference 2)).isSome = false := by decide +kernel
  have impossible := ProbabilityResult.supported_isSome supported
  rw [actual] at impossible
  cases impossible

/-- Automatic guard construction cannot repair a mismatched source or an
actionful printed term: the original structural checker still rejects them. -/
example : ((NativeProofCode.derivation (.refl source)).compileGuardOn projection.observedGraph profiles .zero).isSome = false := by decide +kernel
example : ((NativeProofCode.derivation (.refl actionful)).compileGuardOn projection.observedGraph profiles actionful).isSome = false := by decide +kernel

noncomputable def fixed_original_sound
    (checked : CheckedNativeFormula projection.observedGraph projection.completeSupportCatalogue)
    (supported : entry.model.TermSupportedAt checked.source (reference 2))
    (accepted : checked.available entry.model.observationalDist (reference 2) = true) :
    entry.model.TermEquivalentAt checked.withCompiledGuard.source checked.withCompiledGuard.formula (reference 2) :=
  checked.withCompiledGuard.fixed_soundAt entry.model (reference 2) supported
    (checked.withCompiledGuard_available entry.model entry.model.completeSupportCatalogue_covers (reference 2) accepted)

noncomputable def projection_original_sound
    (checked : CheckedNativeFormula projection.observedGraph projection.observedGraph.cliqueRootProjection.completeSupportCatalogue)
    (supported : projected.model.TermSupportedAt checked.source (reference 2))
    (accepted : checked.available projected.model.observationalDist (reference 2) = true) :
    projected.model.TermEquivalentAt checked.withCompiledGuard.source checked.withCompiledGuard.formula (reference 2) :=
  checked.withCompiledGuard.projected_soundAt projected (reference 2) supported
    (checked.withCompiledGuard_available projected.model projected.completeSupportCatalogue_covers (reference 2) accepted)

end Thesis.Causality.Examples.NativeGuardCompilation
