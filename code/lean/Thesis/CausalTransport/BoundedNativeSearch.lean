import Thesis.CausalTransport.BoundedNativeRepresentation

namespace Thesis.Causality

open Probability

/-!
# Exact compatibility and target comparison in a bounded native model class

Filter the finite native catalogue by equality of all observational singleton
probabilities. Finite extensionality proves that this test is equivalent to
agreement on the entire supplied observed law, including its zero cells.
Then compare the requested unconditional interventional event probability
throughout the retained list. The constructive result carries its own proof:
incompatibility in this bounded class, an attained common value, or two actual
compatible native models with different target values.

Coverage is not restricted to the literal canonical factor records in the
list. Every bounded-denominator factor record on every listed structural
template has a canonical listed representative preserving all interventions.
The negative and uniqueness results transport through that construction.

The full hidden graph and alphabet/denominator bounds are inputs. No bound
on denominators follows from the projection-wide representation theorem.
This is consequently not an arbitrary-graph unrestricted decision procedure.
Conditional targets are not silently evaluated at null evidence: this first
search API deliberately takes an unconditional `NativeProbabilityQuery`.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace NativeTemplateInstance

def queryValue (entry : NativeTemplateInstance P) (query : NativeProbabilityQuery S) : QProb :=
  entry.model.interventionalValue query.intervention query.event

def MatchesObservation (entry : NativeTemplateInstance P) (observed : FiniteProbRecord S.Assignment) : Prop :=
  ∀ event, QProb.Equiv (entry.model.observationalValue event) (observed.probVal event)

def observationCheck (entry : NativeTemplateInstance P) (observed : FiniteProbRecord S.Assignment) : Bool :=
  S.assignmentEnumeration.all (fun reference =>
    decide (QProb.Equiv (entry.model.observationalValue (FiniteProbRecord.singletonEvent reference))
      (observed.probVal (FiniteProbRecord.singletonEvent reference))))

theorem observationCheck_exact (entry : NativeTemplateInstance P) (observed : FiniteProbRecord S.Assignment) :
    entry.observationCheck observed = true ↔ entry.MatchesObservation observed := by
  constructor
  · intro checked event
    apply FiniteProbRecord.probVal_extensional_of_singletons _ _ S.assignmentEnumeration
      S.assignmentEnumeration_nodup S.assignmentEnumeration_complete (fun reference => ?_) event
    exact of_decide_eq_true (List.all_eq_true.mp checked reference (S.assignmentEnumeration_complete reference))
  · intro matched
    apply List.all_eq_true.mpr
    intro reference _listed
    exact decide_eq_true (matched (FiniteProbRecord.singletonEvent reference))

/-- Inspect a finite list without choosing a representative from a bare
existential. The identified branch contains an actual attained witness. -/
inductive Inspection (query : NativeProbabilityQuery S) (candidates : List (NativeTemplateInstance P)) where
  | incompatible (empty : candidates = [])
  | identified (witness : NativeTemplateInstance P) (listed : witness ∈ candidates)
      (constant : ∀ entry, entry ∈ candidates → QProb.Equiv (entry.queryValue query) (witness.queryValue query))
  | ambiguous (left right : NativeTemplateInstance P) (leftListed : left ∈ candidates) (rightListed : right ∈ candidates)
      (different : ¬ QProb.Equiv (left.queryValue query) (right.queryValue query))

/-- Only exact natural cross-product equalities of rational probabilities
are decided. This does not invoke excluded middle for arbitrary propositions. -/
def inspect (query : NativeProbabilityQuery S) :
    (candidates : List (NativeTemplateInstance P)) → Inspection query candidates
  | [] => .incompatible rfl
  | head :: tail =>
      match inspect query tail with
      | .incompatible empty =>
          .identified head List.mem_cons_self (by
            intro entry member
            rcases List.mem_cons.mp member with same | remaining
            · subst entry
              exact QProb.equiv_refl _
            · rw [empty] at remaining
              exact False.elim (List.not_mem_nil remaining))
      | .identified witness listed constant =>
          if same : QProb.Equiv (head.queryValue query) (witness.queryValue query) then
            .identified head List.mem_cons_self (by
              intro entry member
              rcases List.mem_cons.mp member with equalHead | remaining
              · subst entry
                exact QProb.equiv_refl _
              · exact QProb.equiv_trans (constant entry remaining) (QProb.equiv_symm same))
          else .ambiguous head witness List.mem_cons_self (List.mem_cons_of_mem head listed) same
      | .ambiguous left right leftListed rightListed different =>
          .ambiguous left right (List.mem_cons_of_mem head leftListed) (List.mem_cons_of_mem head rightListed) different

end NativeTemplateInstance

namespace BoundedNativeSearch

variable (P : FiniteLatentProjection S) (nodeBound sourceBound denominatorBound : Nat)
variable (observed : FiniteProbRecord S.Assignment)

def MatchesNativeObservation (original : FiniteHiddenDAGSCM S P) : Prop :=
  ∀ event, QProb.Equiv (original.observationalValue event) (observed.probVal event)

def fitted : List (NativeTemplateInstance P) :=
  (P.boundedNativeCatalogue nodeBound sourceBound denominatorBound).filter (fun entry => entry.observationCheck observed)

theorem mem_fitted_iff (entry : NativeTemplateInstance P) :
    entry ∈ fitted P nodeBound sourceBound denominatorBound observed ↔
      entry ∈ P.boundedNativeCatalogue nodeBound sourceBound denominatorBound ∧ entry.MatchesObservation observed := by
  rw [fitted, List.mem_filter, entry.observationCheck_exact]

theorem canonical_mem_fitted (entry : NativeTemplateInstance P)
    (templateListed : entry.template ∈ P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound)
    (denominators : ∀ node, (entry.factors node).den ≤ denominatorBound) (matched : entry.MatchesObservation observed) :
    entry.canonical ∈ fitted P nodeBound sourceBound denominatorBound observed := by
  apply (mem_fitted_iff P nodeBound sourceBound denominatorBound observed entry.canonical).mpr
  refine ⟨P.canonical_mem_boundedNativeCatalogue _ _ _ entry templateListed denominators, ?_⟩
  intro event
  exact QProb.equiv_trans (entry.canonical_observationalValue event) (matched event)

/-- Every fitted witness is an actual model in the stated bounded structural
class, with its unchanged exact observational law. These are output proofs,
not uninhabited semantic interfaces supplied to the checker. -/
structure FittedModel where
  entry : NativeTemplateInstance P
  templateListed : entry.template ∈ P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound
  nodes : ∀ node, (entry.model.nodeEnumeration node).length ≤ nodeBound
  sources : ∀ node, (entry.model.noiseEnumeration node).length ≤ sourceBound
  denominators : ∀ node, (entry.factors node).den ≤ denominatorBound
  matched : entry.MatchesObservation observed

def fittedModelOfMem (entry : NativeTemplateInstance P)
    (listed : entry ∈ fitted P nodeBound sourceBound denominatorBound observed) :
    FittedModel P nodeBound sourceBound denominatorBound observed :=
  let parts := (mem_fitted_iff P nodeBound sourceBound denominatorBound observed entry).mp listed
  let templateListed := P.boundedNativeCatalogue_template_mem _ _ _ entry parts.1
  let bounds := P.hiddenDAG.nativeTemplateCatalogue_bounded_of_mem _ _ entry.template templateListed
  ⟨entry, templateListed,
    (fun node => by simpa only [NativeTemplateInstance.model, FiniteHiddenDAG.CodeNativeTemplate.model, List.length_finRange] using bounds.1 node),
    (fun node => by simpa only [NativeTemplateInstance.model, FiniteHiddenDAG.CodeNativeTemplate.model, List.length_finRange] using bounds.2 node),
    P.boundedNativeCatalogue_factor_den _ _ _ entry parts.1, parts.2⟩

theorem no_match_of_empty (empty : fitted P nodeBound sourceBound denominatorBound observed = [])
    (entry : NativeTemplateInstance P)
    (templateListed : entry.template ∈ P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound)
    (denominators : ∀ node, (entry.factors node).den ≤ denominatorBound) : ¬ entry.MatchesObservation observed := by
  intro matched
  have listed := canonical_mem_fitted P nodeBound sourceBound denominatorBound observed entry templateListed denominators matched
  rw [empty] at listed
  exact List.not_mem_nil listed

/-- Uniqueness over literal listed canonical records implies uniqueness over
every original bounded factor record, because all interventions are retained. -/
theorem constant_transfer (query : NativeProbabilityQuery S) (value : QProb)
    (constant : ∀ candidate, candidate ∈ fitted P nodeBound sourceBound denominatorBound observed →
      QProb.Equiv (candidate.queryValue query) value)
    (entry : NativeTemplateInstance P)
    (templateListed : entry.template ∈ P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound)
    (denominators : ∀ node, (entry.factors node).den ≤ denominatorBound) (matched : entry.MatchesObservation observed) :
    QProb.Equiv (entry.queryValue query) value :=
  QProb.equiv_trans (QProb.equiv_symm (entry.canonical_interventionalValue query.intervention query.event))
    (constant entry.canonical
      (canonical_mem_fitted P nodeBound sourceBound denominatorBound observed entry templateListed denominators matched))

/-- The input need not already use finite code types. Its actual complete
enumerations construct the code representative, with every original causal
probability preserved and its original source denominators unchanged. -/
theorem native_representative_mem_fitted (original : FiniteHiddenDAGSCM S P)
    (nodes : ∀ node, (original.nodeEnumeration node).length ≤ nodeBound)
    (sources : ∀ node, (original.noiseEnumeration node).length ≤ sourceBound)
    (denominators : ∀ node, (original.factor node).den ≤ denominatorBound)
    (matched : MatchesNativeObservation P observed original) :
    original.boundedSearchRepresentative ∈ fitted P nodeBound sourceBound denominatorBound observed := by
  apply (mem_fitted_iff P nodeBound sourceBound denominatorBound observed original.boundedSearchRepresentative).mpr
  refine ⟨original.boundedSearchRepresentative_mem _ _ _ nodes sources denominators, ?_⟩
  intro event
  exact QProb.equiv_trans (original.boundedSearchRepresentative_observationalValue event) (matched event)

theorem no_native_match_of_empty (empty : fitted P nodeBound sourceBound denominatorBound observed = [])
    (original : FiniteHiddenDAGSCM S P)
    (nodes : ∀ node, (original.nodeEnumeration node).length ≤ nodeBound)
    (sources : ∀ node, (original.noiseEnumeration node).length ≤ sourceBound)
    (denominators : ∀ node, (original.factor node).den ≤ denominatorBound) : ¬ MatchesNativeObservation P observed original := by
  intro matched
  have listed := native_representative_mem_fitted P nodeBound sourceBound denominatorBound observed original nodes sources denominators matched
  rw [empty] at listed
  exact List.not_mem_nil listed

theorem native_constant_transfer (query : NativeProbabilityQuery S) (value : QProb)
    (constant : ∀ candidate, candidate ∈ fitted P nodeBound sourceBound denominatorBound observed →
      QProb.Equiv (candidate.queryValue query) value)
    (original : FiniteHiddenDAGSCM S P)
    (nodes : ∀ node, (original.nodeEnumeration node).length ≤ nodeBound)
    (sources : ∀ node, (original.noiseEnumeration node).length ≤ sourceBound)
    (denominators : ∀ node, (original.factor node).den ≤ denominatorBound)
    (matched : MatchesNativeObservation P observed original) :
    QProb.Equiv (original.interventionalValue query.intervention query.event) value :=
  QProb.equiv_trans (QProb.equiv_symm (original.boundedSearchRepresentative_interventionalValue query.intervention query.event))
    (constant original.boundedSearchRepresentative
      (native_representative_mem_fitted P nodeBound sourceBound denominatorBound observed original nodes sources denominators matched))

inductive Result (query : NativeProbabilityQuery S) where
  | incompatible
      (noMatch : ∀ original : FiniteHiddenDAGSCM S P,
        (∀ node, (original.nodeEnumeration node).length ≤ nodeBound) →
        (∀ node, (original.noiseEnumeration node).length ≤ sourceBound) →
        (∀ node, (original.factor node).den ≤ denominatorBound) → ¬ MatchesNativeObservation P observed original)
  | identified (witness : FittedModel P nodeBound sourceBound denominatorBound observed)
      (unique : ∀ original : FiniteHiddenDAGSCM S P,
        (∀ node, (original.nodeEnumeration node).length ≤ nodeBound) →
        (∀ node, (original.noiseEnumeration node).length ≤ sourceBound) →
        (∀ node, (original.factor node).den ≤ denominatorBound) → MatchesNativeObservation P observed original →
        QProb.Equiv (original.interventionalValue query.intervention query.event) (witness.entry.queryValue query))
  | ambiguous (left right : FittedModel P nodeBound sourceBound denominatorBound observed)
      (different : ¬ QProb.Equiv (left.entry.queryValue query) (right.entry.queryValue query))

/-- Terminating exact bounded-class search, with attained witnesses and
coverage of every permitted factor presentation. No optimizer is trusted. -/
def solve (query : NativeProbabilityQuery S) : Result P nodeBound sourceBound denominatorBound observed query :=
  match NativeTemplateInstance.inspect query (fitted P nodeBound sourceBound denominatorBound observed) with
  | .incompatible empty => .incompatible (no_native_match_of_empty P nodeBound sourceBound denominatorBound observed empty)
  | .identified witness listed constant =>
      .identified (fittedModelOfMem P nodeBound sourceBound denominatorBound observed witness listed)
        (native_constant_transfer P nodeBound sourceBound denominatorBound observed query (witness.queryValue query) constant)
  | .ambiguous left right leftListed rightListed different =>
      .ambiguous (fittedModelOfMem P nodeBound sourceBound denominatorBound observed left leftListed)
        (fittedModelOfMem P nodeBound sourceBound denominatorBound observed right rightListed) different

end BoundedNativeSearch
end Thesis.Causality
