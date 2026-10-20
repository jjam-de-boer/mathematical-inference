import Thesis.Causality.CodeEnumerationCounts
import Thesis.Probability.FiniteEnumerationBounds

namespace Thesis.Causality.ProbabilityCode

/-!
# Explicit admission limits for bounded code search

Admission is a resource decision, not an identification decision. A refusal
does not mean that a certificate is absent, even within the requested depth.
Limits are supplied explicitly; this module never raises them after failure.

Check node/depth limits first. Estimate dictionary lengths from coordinate
lengths, without enumerating their Cartesian products. The assignment
estimate bounds even the pre-deduplication product, so is never too small. Only
after those gates may the real, bounded dictionaries be constructed. Then
the saturated code count decides whether raw enumeration may start.

These are structural work bounds, not a hard RAM or wall-clock guarantee.
In particular, user-supplied signature enumeration functions are already
inputs: arbitrary computation hidden inside such a function is not timed
by a pure Lean function. External process safeguards remain appropriate.
-/

structure SearchLimits where
  maxObservedNodes : Nat
  maxDictionaryEntries : Nat
  maxExpressionDepth : Nat
  maxProofDepth : Nat
  maxSourceDepth : Nat
  maxRawCandidates : Nat
  maxProfiles : Nat
  maxGuardRows : Nat
  maxProfileComparisons : Nat
  maxTotalProfileComparisons : Nat
  deriving Repr, DecidableEq

/-- Overflow cases name the exceeded policy, without presenting a clipped
sentinel as the actual size. There is deliberately no `notIdentifiable` case. -/
inductive SearchRefusal where
  | observedNodes (requested limit : Nat)
  | expressionDepth (requested limit : Nat)
  | proofDepth (requested limit : Nat)
  | maskDictionary (limit : Nat)
  | referenceDictionary (limit : Nat)
  | rawCandidates (limit : Nat)
  | source (depthLimit : Nat)
  | profiles (limit : Nat)
  | guardRows (limit : Nat)
  | profileComparisons (limit : Nat)
  | totalProfileComparisons (limit : Nat)
  deriving Repr, DecidableEq

/-- A consumer can display a refusal without translating it into an empty
search result or accidentally asserting a causal impossibility theorem. -/
def SearchRefusal.message (reason : SearchRefusal) : String :=
  let detail := match reason with
    | .observedNodes requested limit => s!"Observed-node count {requested} exceeds limit {limit}."
    | .expressionDepth requested limit => s!"Expression depth {requested} exceeds limit {limit}."
    | .proofDepth requested limit => s!"Proof depth {requested} exceeds limit {limit}."
    | .maskDictionary limit => s!"Mask dictionary estimate exceeds limit {limit}."
    | .referenceDictionary limit => s!"Reference dictionary estimate exceeds limit {limit}."
    | .rawCandidates limit => s!"Raw proof-code count exceeds limit {limit}."
    | .source limit => s!"Source query is outside depth limit {limit} or the permitted dictionary indices."
    | .profiles limit => s!"Supplied profile count exceeds limit {limit}."
    | .guardRows limit => s!"Guard-row count per certificate exceeds limit {limit}."
    | .profileComparisons limit => s!"Profile comparisons per certificate exceed limit {limit}."
    | .totalProfileComparisons limit => s!"Total profile-comparison allowance exceeds limit {limit}."
  s!"Search refused: {detail} This is not a non-identifiability result."

namespace CappedCount

/-- Only coordinate counts are read. No product assignment is built. -/
def natProduct (limit : Nat) : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => clip limit 1
  | count + 1, values => mul limit (clip limit (values (Fin.last count)))
      (natProduct limit count (fun index => values index.castSucc))

theorem natProduct_exact (limit count : Nat) (values : Fin count → Nat) :
    natProduct limit count values = clip limit (Thesis.Probability.FiniteProduct.natProduct count values) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [natProduct, Thesis.Probability.FiniteProduct.natProduct, inductionHypothesis, clip_mul]

end CappedCount

/-- This cheap estimate deliberately precedes `CodeDictionaries.ofSignature`.
The latter obtains lengths by constructing the actual mask/assignment lists. -/
def dictionaryEstimate (limit : Nat) (signature : ObservedSignature) : CodeDictionaries :=
  ⟨CappedCount.natProduct limit signature.count (fun _ => 2),
    CappedCount.natProduct limit signature.count (fun index => (signature.valueEnumeration index).length)⟩

theorem mask_estimate_exact (limit : Nat) (signature : ObservedSignature) :
    (dictionaryEstimate limit signature).masks =
      CappedCount.clip limit (CodeDictionaries.ofSignature signature).masks := by
  simp only [dictionaryEstimate, CappedCount.natProduct_exact, CodeDictionaries.ofSignature,
    NodeSet.subsets, Thesis.Probability.FiniteProduct.enumeration_length]
  congr 2

theorem reference_dictionary_le_product (signature : ObservedSignature) :
    (CodeDictionaries.ofSignature signature).references ≤
      Thesis.Probability.FiniteProduct.natProduct signature.count
        (fun index => (signature.valueEnumeration index).length) := by
  change (Thesis.Probability.deduplicate _).length ≤ _
  rw [← Thesis.Probability.FiniteProduct.enumeration_length signature.count signature.Value signature.valueEnumeration]
  exact Thesis.Probability.deduplicate_length_le _

theorem dictionaryEstimate_bounds (limit : Nat) (signature : ObservedSignature)
    (masks : (dictionaryEstimate limit signature).masks ≤ limit)
    (references : (dictionaryEstimate limit signature).references ≤ limit) :
    (CodeDictionaries.ofSignature signature).masks ≤ limit ∧
      (CodeDictionaries.ofSignature signature).references ≤ limit := by
  constructor
  · exact (CappedCount.clip_le_iff _ _).mp (by simpa only [mask_estimate_exact] using masks)
  · exact Nat.le_trans (reference_dictionary_le_product signature)
      ((CappedCount.clip_le_iff _ _).mp (by
        simpa only [dictionaryEstimate, CappedCount.natProduct_exact] using references))

structure SyntaxEstimate where
  dictionary : CodeDictionaries
  candidates : Nat
  deriving Repr, DecidableEq

/-- Accepted `candidates` is exact. Refusal occurs before raw-code generation,
and dictionary refusal occurs before the Cartesian dictionaries are built. -/
def preflightSyntax (limits : SearchLimits) (signature : ObservedSignature)
    (expressionDepth proofDepth : Nat) : Except SearchRefusal SyntaxEstimate :=
  if signature.count > limits.maxObservedNodes then
    .error (.observedNodes signature.count limits.maxObservedNodes)
  else if expressionDepth > limits.maxExpressionDepth then
    .error (.expressionDepth expressionDepth limits.maxExpressionDepth)
  else if proofDepth > limits.maxProofDepth then
    .error (.proofDepth proofDepth limits.maxProofDepth)
  else
    let estimated := dictionaryEstimate limits.maxDictionaryEntries signature
    if estimated.masks > limits.maxDictionaryEntries then .error (.maskDictionary limits.maxDictionaryEntries)
    else if estimated.references > limits.maxDictionaryEntries then .error (.referenceDictionary limits.maxDictionaryEntries)
    else
      let dictionary := CodeDictionaries.ofSignature signature
      let candidates := CappedCount.native limits.maxRawCandidates dictionary expressionDepth proofDepth
      if candidates > limits.maxRawCandidates then .error (.rawCandidates limits.maxRawCandidates)
      else .ok ⟨dictionary, candidates⟩

theorem preflightSyntax_bounds (limits : SearchLimits) (signature : ObservedSignature)
    (expressionDepth proofDepth : Nat) (estimate : SyntaxEstimate)
    (accepted : preflightSyntax limits signature expressionDepth proofDepth = .ok estimate) :
    estimate.dictionary = CodeDictionaries.ofSignature signature ∧
      estimate.dictionary.masks ≤ limits.maxDictionaryEntries ∧
      estimate.dictionary.references ≤ limits.maxDictionaryEntries ∧
      CodeCount.native estimate.dictionary expressionDepth proofDepth ≤ limits.maxRawCandidates ∧
      estimate.candidates = CodeCount.native estimate.dictionary expressionDepth proofDepth := by
  unfold preflightSyntax at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  split at accepted
  · contradiction
  split at accepted
  · contradiction
  split at accepted
  · contradiction
  rename_i masksFit
  split at accepted
  · contradiction
  rename_i referencesFit
  split at accepted
  · contradiction
  rename_i candidatesFit
  cases accepted
  have dictionaries := dictionaryEstimate_bounds limits.maxDictionaryEntries signature
    (Nat.le_of_not_gt masksFit) (Nat.le_of_not_gt referencesFit)
  have candidates : CodeCount.native (.ofSignature signature) expressionDepth proofDepth ≤ limits.maxRawCandidates :=
    (CappedCount.clip_le_iff _ _).mp (by
      simpa only [CappedCount.native_exact] using Nat.le_of_not_gt candidatesFit)
  exact ⟨rfl, dictionaries.1, dictionaries.2, candidates,
    (CappedCount.native_exact _ _ _ _).trans (Nat.min_eq_left (Nat.le_trans candidates (Nat.le_succ _)))⟩

end Thesis.Causality.ProbabilityCode
