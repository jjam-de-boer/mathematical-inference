import Thesis.Causality.CodeSearchPreflight

namespace Thesis.Causality.ProbabilityCode

/-!
# Certified domain sizes for early resource refusal

A signature stores value-enumeration functions, not cheap cardinalities.
Calling a function and then measuring its returned list can already be too
expensive, even when the eventual product dictionary would be refused.

Supply explicit sizes with proofs that they are the lengths of the declared
coordinate lists. Proofs are erased by execution: for a `Fin n` domain, its
existing length theorem certifies the number `n` without generating values.
The metadata path reads only these numbers until both dictionary gates pass.
It then constructs the ordinary dictionaries and uses the existing exact
capped candidate count. It never drops declared null values or substitutes
an approximate dictionary for the real one.

The proved equality with `preflightSyntax` concerns mathematical results,
including refusal cases, NOT identical execution costs. In particular, that
theorem must not be installed as a compiler-simplification replacement for
this implementation. Metadata itself should be prepared cheaply: defining
its numerical fields by recomputing value-list lengths defeats its purpose.
This still does not time arbitrary caller-supplied functions or generate a
resource-bounded complete causal-profile catalogue.
-/

/-- Cardinalities are data; their binding to the actual declared domains is
checked by Lean. No cardinality oracle, choice principle or new axiom is used. -/
structure DomainSizeMetadata (signature : ObservedSignature) where
  cardinality : Fin signature.count → Nat
  exact : ∀ index, cardinality index = (signature.valueEnumeration index).length

/-- Check the cheap mask count first, then the certified numerical domain
sizes. Neither refusal branch calls a signature's value-enumeration function.
Only a successful pair of dictionary gates permits actual dictionary work. -/
def preflightSyntaxWithMetadata (limits : SearchLimits) (signature : ObservedSignature)
    (metadata : DomainSizeMetadata signature) (expressionDepth proofDepth : Nat) :
    Except SearchRefusal SyntaxEstimate :=
  if signature.count > limits.maxObservedNodes then
    .error (.observedNodes signature.count limits.maxObservedNodes)
  else if expressionDepth > limits.maxExpressionDepth then
    .error (.expressionDepth expressionDepth limits.maxExpressionDepth)
  else if proofDepth > limits.maxProofDepth then
    .error (.proofDepth proofDepth limits.maxProofDepth)
  else
    let masks := CappedCount.natProduct limits.maxDictionaryEntries signature.count (fun _ => 2)
    if masks > limits.maxDictionaryEntries then .error (.maskDictionary limits.maxDictionaryEntries)
    else
      let references := CappedCount.natProduct limits.maxDictionaryEntries signature.count metadata.cardinality
      if references > limits.maxDictionaryEntries then .error (.referenceDictionary limits.maxDictionaryEntries)
      else
        let dictionary := CodeDictionaries.ofSignature signature
        let candidates := CappedCount.native limits.maxRawCandidates dictionary expressionDepth proofDepth
        if candidates > limits.maxRawCandidates then .error (.rawCandidates limits.maxRawCandidates)
        else .ok ⟨dictionary, candidates⟩

/-- All mathematical decisions are unchanged; only the way the domain sizes
are obtained differs. Keep this a theorem, not an execution rewrite rule. -/
theorem preflightSyntaxWithMetadata_eq (limits : SearchLimits) (signature : ObservedSignature)
    (metadata : DomainSizeMetadata signature) (expressionDepth proofDepth : Nat) :
    preflightSyntaxWithMetadata limits signature metadata expressionDepth proofDepth =
      preflightSyntax limits signature expressionDepth proofDepth := by
  have sizes : metadata.cardinality = fun index => (signature.valueEnumeration index).length :=
    funext metadata.exact
  simp only [preflightSyntaxWithMetadata, preflightSyntax, sizes]

theorem preflightSyntaxWithMetadata_bounds (limits : SearchLimits) (signature : ObservedSignature)
    (metadata : DomainSizeMetadata signature) (expressionDepth proofDepth : Nat) (estimate : SyntaxEstimate)
    (accepted : preflightSyntaxWithMetadata limits signature metadata expressionDepth proofDepth = .ok estimate) :
    estimate.dictionary = CodeDictionaries.ofSignature signature ∧
      estimate.dictionary.masks ≤ limits.maxDictionaryEntries ∧
      estimate.dictionary.references ≤ limits.maxDictionaryEntries ∧
      CodeCount.native estimate.dictionary expressionDepth proofDepth ≤ limits.maxRawCandidates ∧
      estimate.candidates = CodeCount.native estimate.dictionary expressionDepth proofDepth := by
  rw [preflightSyntaxWithMetadata_eq] at accepted
  exact preflightSyntax_bounds limits signature expressionDepth proofDepth estimate accepted

end Thesis.Causality.ProbabilityCode
