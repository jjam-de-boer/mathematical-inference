import Thesis.CausalTransport.NativeQueryPaths
import Thesis.CausalTransport.NativePointGuard

namespace Thesis.Causality.ProbabilityCode

open Probability NativeDemandTyping NativeDemandEncoding

/-!
# Checked query traces reconstruct existing native certificates

The input is one literal trace from the canonically encoded query at its
fixed source-based mask, its full check, and recognition of its target.
Erasure supplies the existing do-calculus derivation. Only literal endpoint
equality is transported; no equation is inferred from recognition metadata.

A one-row guard retains exactly the observed support/reference cell. On
each matching profile where both endpoints have values, source definedness
activates the fixed mask, whose full trace check supplies every recursive
support obligation. The guard uses the original checker and introduces no
represented-pattern assumption. Recognition separately supplies syntactic
action-freeness and printed availability, including when the mask is empty.

The output is the existing `CheckedNativeFormula`, not a new semantic
interface. Its original-model soundness still requires graph agreement,
catalogue coverage and source support. A null source gains no probability
value. Only the derivation branch participates in the equivalence below;
`actionOne` remains a separate native certificate branch.

The equivalence concerns existence of supplied finite witnesses at one cell.
It neither chooses a witness from a proposition nor decides that one exists.
There is no serialized `NativeCertificateCode` exporter, byte parser, search,
normalization, ground-AC correspondence or stopping algorithm in this module.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
variable {profiles : List (NativeTemplateInstance P)}

/-- Wrap only the literal source erasure equality. The complete erased
proof, including its intermediate terms, remains inside this existing
equality-congruence constructor. -/
private def queryTraceDerivation (source : ProbabilityTerm S) (record : FiniteProbRecord S.Assignment)
    (fixed : S.Assignment) {target : Term profiles}
    (trace : RewriteTrace profiles
      (Term.encode profiles source (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)) target) :
    CheckedDerivation P.observedGraph :=
  ⟨source, target.erase, .eqCongr (Term.erase_encode profiles source _).symm rfl trace.toPath.erase.toDerivation⟩

private theorem queryTraceDerivation_checked (source : ProbabilityTerm S) (record : FiniteProbRecord S.Assignment)
    (fixed : S.Assignment) {target : Term profiles}
    (trace : RewriteTrace profiles
      (Term.encode profiles source (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)) target)
    (checked : trace.check (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) = true) :
    checkDerivation profiles (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)
      (queryTraceDerivation source record fixed trace).derivation = true := by
  have targetChecked := trace.target_checks_of_check _ checked
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨NativeQueryDemand.source_checked profiles source _ fixed, targetChecked.2⟩, trace.erase_checked _ checked⟩

/-- Checking the new guard uses every listed matching profile. Existential
list indices are eliminated only inside this propositional proof; none is
selected as certificate data or as a favorable modelwise proof. -/
private theorem queryTrace_guard_checked (source : ProbabilityTerm S) (record : FiniteProbRecord S.Assignment)
    (fixed : S.Assignment) {target : Term profiles}
    (trace : RewriteTrace profiles
      (Term.encode profiles source (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)) target)
    (checked : trace.check (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) = true) :
    NativeSupportGuard.check profiles (CheckedNativeProof.derivation (queryTraceDerivation source record fixed trace)).demand
      (NativeSupportGuard.point (NativeSupportGuard.pattern S record) fixed) = true := by
  have full := (checkDerivation_exact profiles _ (queryTraceDerivation source record fixed trace).derivation).symm.trans
    (queryTraceDerivation_checked source record fixed trace checked)
  apply (NativeSupportGuard.point_checked_iff ..).mpr
  intro entry listed matched
  rcases List.mem_iff_get.mp listed with ⟨index, same⟩
  subst entry
  change (if (CheckedNativeProof.derivation (queryTraceDerivation source record fixed trace)).endpoints P
    (profiles.get index).model fixed then
      HiddenDAGLocalDerivationSupport.check (profiles.get index).model fixed
        (queryTraceDerivation source record fixed trace).derivation else true) = true
  split
  · next endpoints =>
      have sourceChecked : ((profiles.get index).model.termDenote source fixed).isSome = true :=
        (Bool.and_eq_true_iff.mp endpoints).1
      have needed := (NativeQueryDemand.mask_exact profiles source (NativeSupportGuard.pattern S record) fixed index fixed).mpr
        ⟨matched.symm, rfl, sourceChecked⟩
      exact (allNeeded_exact ..).mp full index fixed needed
  · rfl

namespace CheckedNativeFormula

/-- Construct the old certificate directly from its actual finite trace and
two accepted Boolean checks. No source-support witness is manufactured. -/
def ofQueryTrace (source : ProbabilityTerm S) (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
    {target : Term profiles}
    (trace : RewriteTrace profiles
      (Term.encode profiles source (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)) target)
    (checked : trace.check (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) = true)
    (recognized : NativeTargetRecognition.recognize record.support
      (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) fixed target = true) :
    CheckedNativeFormula P.observedGraph profiles where
  source := source
  proof := .derivation (queryTraceDerivation source record fixed trace)
  source_eq := rfl
  actionFree := (ProbabilityTerm.actionFreeCheck_exact target.erase).mp (by
    rw [← Term.actionFreeCheck_eq_erased]
    exact ((NativeTargetRecognition.recognize_record_iff ..).mp recognized).2.2.1)
  guard := NativeSupportGuard.point (NativeSupportGuard.pattern S record) fixed
  guardChecked := queryTrace_guard_checked source record fixed trace checked

variable (source : ProbabilityTerm S) (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
variable {target : Term profiles}
variable (trace : RewriteTrace profiles
  (Term.encode profiles source (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)) target)
variable (checked : trace.check (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) = true)
variable (recognized : NativeTargetRecognition.recognize record.support
  (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) fixed target = true)

theorem ofQueryTrace_source : (ofQueryTrace source record fixed trace checked recognized).source = source := rfl

theorem ofQueryTrace_formula : (ofQueryTrace source record fixed trace checked recognized).formula = target.erase := rfl

/-- Recognition also retains the literal encoded target at this demand,
not merely its erased term or its finite status summary. -/
theorem ofQueryTrace_target :
    Term.encode profiles (ofQueryTrace source record fixed trace checked recognized).formula
      (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) = target :=
  (Term.checkAnnotations_exact ..).mp ((NativeTargetRecognition.recognize_record_iff ..).mp recognized).1

theorem ofQueryTrace_guard : (ofQueryTrace source record fixed trace checked recognized).guard =
    NativeSupportGuard.point (NativeSupportGuard.pattern S record) fixed := rfl

theorem ofQueryTrace_isDerivation : ∃ derivation : CheckedDerivation P.observedGraph,
    (ofQueryTrace source record fixed trace checked recognized).proof = .derivation derivation := ⟨_, rfl⟩

theorem ofQueryTrace_available : (ofQueryTrace source record fixed trace checked recognized).available record fixed = true :=
  Bool.and_eq_true_iff.mpr ⟨NativeSupportGuard.point_accepts_self record fixed,
    ((NativeTargetRecognition.recognize_record_iff ..).mp recognized).2.2.2⟩

/-- The returned certificate accepts exactly this observable cell, including
all numerical reweightings with its support. This is not maximality over
other cells or a claim that the causal source is supported there. -/
theorem ofQueryTrace_available_iff (other : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    (ofQueryTrace source record fixed trace checked recognized).available other reference = true ↔
      NativeSupportGuard.pattern S other = NativeSupportGuard.pattern S record ∧ reference = fixed := by
  constructor
  · intro available
    have guardAccepted := (Bool.and_eq_true_iff.mp available).1
    have atCell := (NativeSupportGuard.point_accepts_iff _ fixed other reference).mp guardAccepted
    exact ⟨atCell.1.symm, atCell.2.symm⟩
  · rintro ⟨same, sameReference⟩
    subst reference
    exact ((ofQueryTrace source record fixed trace checked recognized).available_eq_of_pattern_eq same fixed).trans
      (ofQueryTrace_available source record fixed trace checked recognized)

end CheckedNativeFormula

/-- Exact witness-existence equivalence for this source, printed term and
observable cell within the derivation branch. Both directions construct
their witnesses explicitly; this theorem performs no search and grants no
causal value without the old soundness theorem's application premises. -/
theorem query_certificate_iff_trace (source formula : ProbabilityTerm S) (record : FiniteProbRecord S.Assignment)
    (fixed : S.Assignment) :
    (∃ certificate : CheckedNativeFormula P.observedGraph profiles,
      certificate.source = source ∧ certificate.formula = formula ∧
      ∃ derivation : CheckedDerivation P.observedGraph, certificate.proof = .derivation derivation ∧
        certificate.available record fixed = true) ↔
    ∃ trace : RewriteTrace profiles
      (Term.encode profiles source (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed))
      (Term.encode profiles formula (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)),
      trace.check (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) = true ∧
      NativeTargetRecognition.recognize record.support
        (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed) fixed
        (Term.encode profiles formula (NativeQueryDemand.mask profiles source (NativeSupportGuard.pattern S record) fixed)) = true := by
  constructor
  · rintro ⟨certificate, sameSource, sameFormula, derivation, branch, available⟩
    subst source
    subst formula
    exact ⟨certificate.queryTrace derivation branch record fixed available,
      certificate.queryTrace_checked derivation branch record fixed available,
      certificate.queryTrace_target_recognized derivation branch record fixed available⟩
  · rintro ⟨trace, checked, recognized⟩
    let certificate := CheckedNativeFormula.ofQueryTrace source record fixed trace checked recognized
    refine ⟨certificate, rfl, ?_, queryTraceDerivation source record fixed trace, rfl, ?_⟩
    · exact Term.erase_encode profiles formula _
    · exact CheckedNativeFormula.ofQueryTrace_available source record fixed trace checked recognized

end Thesis.Causality.ProbabilityCode
