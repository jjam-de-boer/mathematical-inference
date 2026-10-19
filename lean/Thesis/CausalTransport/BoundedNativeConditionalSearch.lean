import Thesis.CausalTransport.BoundedNativeConditionalInspection
import Thesis.CausalTransport.BoundedNativeClassification

namespace Thesis.Causality

open Probability

/-!
# Exact bounded conditional search, with support reported separately

The observational fitting class is exactly the one used by the unconditional
checker: a fixed full hidden DAG, declared node/source enumeration bounds,
an independent-source denominator bound, and the entire observed law.

The public result first distinguishes incompatibility. For a compatible law
it independently returns (1) evidence support throughout the class or an
actual null-evidence witness and (2) the value classification among supported
models. The latter can be empty, attained and constant, or genuinely ambiguous.
Thus a mixed-support family can still have a unique supported value. It is
not advertised as a conditional defined on every compatible model.

All universal claims range over the original native model records, not merely
the canonical entries inspected by the executable search. The already proved
bounded representation preserves both evidence support and every supported
conditioned event. No conditional is formed at zero evidence and no bound is
inferred for the unrestricted rational model class.
-/

namespace NativeConditionalQuery

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

theorem representative_supported_iff (query : NativeConditionalQuery S) (original : FiniteHiddenDAGSCM S P) :
    query.Supported original.boundedSearchRepresentative.model ↔ query.Supported original :=
  original.boundedSearchRepresentative_eventPositive_iff query.intervention query.evidence

theorem representative_value (query : NativeConditionalQuery S) (original : FiniteHiddenDAGSCM S P)
    (positive : query.Supported original) :
    QProb.Equiv
      (query.value original.boundedSearchRepresentative.model ((query.representative_supported_iff original).mpr positive))
      (query.value original positive) :=
  original.boundedSearchRepresentative_conditionOn_probVal query.intervention query.evidence query.event positive

end NativeConditionalQuery

namespace BoundedNativeConditionalSearch

open BoundedNativeSearch

variable {S : ObservedSignature.{0}}
variable (P : FiniteLatentProjection S) (nodeBound sourceBound denominatorBound : Nat)
variable (observed : FiniteProbRecord S.Assignment)

/-- An actual fitted native model, with the positive causal evidence needed
to evaluate this query. The evidence proof is not supplied by the caller. -/
structure SupportedModel (query : NativeConditionalQuery S) where
  fitted : FittedModel P nodeBound sourceBound denominatorBound observed
  supported : query.Supported fitted.entry.model

inductive SupportReport (query : NativeConditionalQuery S) where
  | allSupported (positive : ∀ original, Fits P nodeBound sourceBound denominatorBound observed original →
      query.Supported original)
  | nullWitness (witness : FittedModel P nodeBound sourceBound denominatorBound observed)
      (nullEvidence : (witness.entry.model.interventionalValue query.intervention query.evidence).num = 0)

inductive ValueReport (query : NativeConditionalQuery S) where
  | unsupported (noSupport : ∀ original, Fits P nodeBound sourceBound denominatorBound observed original →
      ¬ query.Supported original)
  | identified (witness : SupportedModel P nodeBound sourceBound denominatorBound observed query)
      (constant : ∀ original, Fits P nodeBound sourceBound denominatorBound observed original →
        (positive : query.Supported original) →
        QProb.Equiv (query.value original positive) (query.value witness.fitted.entry.model witness.supported))
  | ambiguous (left right : SupportedModel P nodeBound sourceBound denominatorBound observed query)
      (different : ¬ QProb.Equiv (query.value left.fitted.entry.model left.supported)
        (query.value right.fitted.entry.model right.supported))

/-- Compatibility is a separate outer branch, so vacuous positivity on an
empty class is never presented as a usable supported conditional result. -/
inductive Result (query : NativeConditionalQuery S) where
  | incompatible (noMatch : ¬ Compatible P nodeBound sourceBound denominatorBound observed)
  | compatible (witness : FittedModel P nodeBound sourceBound denominatorBound observed)
      (support : SupportReport P nodeBound sourceBound denominatorBound observed query)
      (values : ValueReport P nodeBound sourceBound denominatorBound observed query)

theorem representative_mem (original : FiniteHiddenDAGSCM S P)
    (fits : Fits P nodeBound sourceBound denominatorBound observed original) :
    original.boundedSearchRepresentative ∈ fitted P nodeBound sourceBound denominatorBound observed :=
  native_representative_mem_fitted P nodeBound sourceBound denominatorBound observed original
    fits.1 fits.2.1 fits.2.2.1 fits.2.2.2

/-- Lift a finite-list support certificate to every bounded original record.
The null branch already contains an actual fitted native model. -/
def supportReport (query : NativeConditionalQuery S)
    (answer : NativeTemplateInstance.ConditionalSupportInspection query
      (fitted P nodeBound sourceBound denominatorBound observed)) :
    SupportReport P nodeBound sourceBound denominatorBound observed query :=
  match answer with
  | .allSupported positive => .allSupported (by
      intro original fits
      exact (query.representative_supported_iff original).mp
        (positive original.boundedSearchRepresentative (representative_mem P nodeBound sourceBound denominatorBound observed original fits)))
  | .nullWitness witness listed nullEvidence =>
      .nullWitness (fittedModelOfMem P nodeBound sourceBound denominatorBound observed witness listed) nullEvidence

/-- Lift the value comparison using only supported conditioned-record
preservation. A positive model cannot disappear into the null branch during
canonical coding, even when its original record has repeated or zero cells. -/
def valueReport (query : NativeConditionalQuery S)
    (answer : NativeTemplateInstance.ConditionalValueInspection query
      (fitted P nodeBound sourceBound denominatorBound observed)) :
    ValueReport P nodeBound sourceBound denominatorBound observed query :=
  match answer with
  | .unsupported noSupport => .unsupported (by
      intro original fits positive
      exact noSupport original.boundedSearchRepresentative
        (representative_mem P nodeBound sourceBound denominatorBound observed original fits)
        ((query.representative_supported_iff original).mpr positive))
  | .identified witness listed supported constant =>
      .identified ⟨fittedModelOfMem P nodeBound sourceBound denominatorBound observed witness listed, supported⟩ (by
        intro original fits positive
        exact QProb.equiv_trans (QProb.equiv_symm (query.representative_value original positive))
          (constant original.boundedSearchRepresentative
            (representative_mem P nodeBound sourceBound denominatorBound observed original fits)
            ((query.representative_supported_iff original).mpr positive)))
  | .ambiguous left right leftListed rightListed leftSupported rightSupported different =>
      .ambiguous
        ⟨fittedModelOfMem P nodeBound sourceBound denominatorBound observed left leftListed, leftSupported⟩
        ⟨fittedModelOfMem P nodeBound sourceBound denominatorBound observed right rightListed, rightSupported⟩ different

/-- One finite observational fitting pass, then two logically independent
inspections of that retained list. No arbitrary-proposition decision, external
optimizer, or conditional default at a null event is trusted by this search. -/
def solve (query : NativeConditionalQuery S) : Result P nodeBound sourceBound denominatorBound observed query :=
  let candidates := fitted P nodeBound sourceBound denominatorBound observed
  match listed : candidates with
  | [] => .incompatible (by
      rintro ⟨original, nodes, sources, denominators, matched⟩
      exact no_native_match_of_empty P nodeBound sourceBound denominatorBound observed listed
        original nodes sources denominators matched)
  | head :: tail =>
      .compatible
        (fittedModelOfMem P nodeBound sourceBound denominatorBound observed head (by
          change head ∈ candidates
          rw [listed]
          exact List.mem_cons_self))
        (supportReport P nodeBound sourceBound denominatorBound observed query
          (NativeTemplateInstance.inspectSupport query candidates))
        (valueReport P nodeBound sourceBound denominatorBound observed query
          (NativeTemplateInstance.inspectValues query candidates))

end BoundedNativeConditionalSearch
end Thesis.Causality
