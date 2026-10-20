import Thesis.Causality.CodeSearchPreflight
import Thesis.CausalTransport.NativeProofEnumeration

namespace Thesis.Causality

open Probability

/-!
# Guarded admission to native bounded catalogues

This opt-in entry point refuses oversized work before calling the old raw
enumerator or guard compiler. A successful result is exactly the old finite
catalogue: no constructor, certificate or guard row is silently truncated.
`Except.error` means policy refusal; `Except.ok []` means no certificate in
this particular checked bounded catalogue. Neither proves non-identifiability.

There are independent limits on dictionaries, depths, raw codes, supplied
profiles, guard rows and per-certificate/total row/profile comparisons. For `p` profiles and `r`
references, compilation creates `p*r` rows (duplicates retained) and can
inspect `p*p*r` profiles per certificate. Short-circuiting may inspect fewer.
These counts do not bound the cost of evaluating one model or one demand.

Profiles must already be supplied. In a strict language, an argument such as
`projection.completeSupportCatalogue` is evaluated before a function can
inspect it. Consequently this module does NOT add automatic fixed/projection
wrappers that first expand that enormous generator and only then claim to
preflight it. Generation of complete model catalogues needs its own future
cost analysis. Keep external CPU/RSS limits when executing any search.
No formula selector or universal stopping argument is added here.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace ProbabilityCode

-- Expose the standard monad projections without unfolding semantic objects.
-- Both equalities are definitional; they add no interpretation assumption.
private theorem except_bind_eq_bind (value : Except E A) (next : A → Except E B) :
    (value >>= next) = Except.bind value next := rfl

private theorem except_pure_eq (value : A) : (pure value : Except E A) = .ok value := rfl

namespace CappedCount

/-- Inspect at most `limit + 1` list cells. This never computes the complete
length merely to discover that a supplied list exceeds its allowance. -/
def listLength : Nat → List A → Nat
  | _, [] => 0
  | 0, _ :: _ => 1
  | limit + 1, _ :: tail => 1 + listLength limit tail

theorem listLength_exact (limit : Nat) (values : List A) :
    listLength limit values = clip limit values.length := by
  induction limit generalizing values with
  | zero => cases values <;> simp [listLength, clip]
  | succ limit inductionHypothesis =>
      cases values with
      | nil => simp [listLength, clip]
      | cons head tail =>
          simp only [listLength, inductionHypothesis, List.length_cons, clip]
          omega

end CappedCount

structure ProfileEstimate where
  profiles : Nat
  rows : Nat
  comparisonsPerCertificate : Nat
  deriving Repr, DecidableEq

/-- Profile counting itself stops at its first overflow. The other two
checks use saturated multiplication, not enormous exact intermediate counts. -/
def preflightProfiles (limits : SearchLimits) (references : Nat) (profiles : List (NativeTemplateInstance Q)) :
    Except SearchRefusal ProfileEstimate :=
  let count := CappedCount.listLength limits.maxProfiles profiles
  if count > limits.maxProfiles then .error (.profiles limits.maxProfiles)
  else
    let rows := CappedCount.mul limits.maxGuardRows
      (CappedCount.clip limits.maxGuardRows count) (CappedCount.clip limits.maxGuardRows references)
    if rows > limits.maxGuardRows then .error (.guardRows limits.maxGuardRows)
    else
      let comparisons := CappedCount.mul limits.maxProfileComparisons
        (CappedCount.clip limits.maxProfileComparisons rows) (CappedCount.clip limits.maxProfileComparisons count)
      if comparisons > limits.maxProfileComparisons then .error (.profileComparisons limits.maxProfileComparisons)
      else .ok ⟨count, rows, comparisons⟩

theorem preflightProfiles_bounds (limits : SearchLimits) (references : Nat)
    (profiles : List (NativeTemplateInstance Q)) (estimate : ProfileEstimate)
    (accepted : preflightProfiles limits references profiles = .ok estimate) :
    estimate.profiles = profiles.length ∧ profiles.length ≤ limits.maxProfiles ∧
      estimate.rows = profiles.length * references ∧ estimate.rows ≤ limits.maxGuardRows ∧
      estimate.comparisonsPerCertificate = estimate.rows * profiles.length ∧
      estimate.comparisonsPerCertificate ≤ limits.maxProfileComparisons := by
  unfold preflightProfiles at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  rename_i profilesFit
  split at accepted
  · contradiction
  rename_i rowsFit
  split at accepted
  · contradiction
  rename_i comparisonsFit
  cases accepted
  have countBound : profiles.length ≤ limits.maxProfiles := (CappedCount.clip_le_iff _ _).mp
    (by simpa only [CappedCount.listLength_exact] using Nat.le_of_not_gt profilesFit)
  have countExact : CappedCount.listLength limits.maxProfiles profiles = profiles.length :=
    (CappedCount.listLength_exact _ _).trans (Nat.min_eq_left (Nat.le_trans countBound (Nat.le_succ _)))
  have rowBound : profiles.length * references ≤ limits.maxGuardRows := (CappedCount.clip_le_iff _ _).mp
    (by simpa only [countExact, CappedCount.clip_mul] using Nat.le_of_not_gt rowsFit)
  have rowExact : CappedCount.mul limits.maxGuardRows
      (CappedCount.clip limits.maxGuardRows (CappedCount.listLength limits.maxProfiles profiles))
      (CappedCount.clip limits.maxGuardRows references) = profiles.length * references := by
    rw [countExact, CappedCount.clip_mul]
    exact Nat.min_eq_left (Nat.le_trans rowBound (Nat.le_succ _))
  have comparisonBound : (profiles.length * references) * profiles.length ≤ limits.maxProfileComparisons :=
    (CappedCount.clip_le_iff _ _).mp (by
      have checked := Nat.le_of_not_gt comparisonsFit
      rw [rowExact, countExact, CappedCount.clip_mul] at checked
      exact checked)
  exact ⟨countExact, countBound, rowExact, Nat.le_of_not_gt rowsFit,
    by rw [rowExact, countExact, CappedCount.clip_mul]; exact Nat.min_eq_left (Nat.le_trans comparisonBound (Nat.le_succ _)),
    Nat.le_of_not_gt comparisonsFit⟩

/-- Independent small per-certificate limits are not enough: their product
with the number of candidates also has to fit an explicit total allowance. -/
def preflightTotal (limits : SearchLimits) (candidates comparisons : Nat) : Except SearchRefusal Nat :=
  let total := CappedCount.mul limits.maxTotalProfileComparisons
    (CappedCount.clip limits.maxTotalProfileComparisons candidates)
    (CappedCount.clip limits.maxTotalProfileComparisons comparisons)
  if total > limits.maxTotalProfileComparisons then .error (.totalProfileComparisons limits.maxTotalProfileComparisons)
  else .ok total

theorem preflightTotal_bounds (limits : SearchLimits) (candidates comparisons total : Nat)
    (accepted : preflightTotal limits candidates comparisons = .ok total) :
    total = candidates * comparisons ∧ total ≤ limits.maxTotalProfileComparisons := by
  unfold preflightTotal at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  rename_i totalFits
  cases accepted
  have bound : candidates * comparisons ≤ limits.maxTotalProfileComparisons :=
    (CappedCount.clip_le_iff _ _).mp (by
      simpa only [CappedCount.clip_mul] using Nat.le_of_not_gt totalFits)
  exact ⟨(CappedCount.clip_mul _ _ _).trans (Nat.min_eq_left (Nat.le_trans bound (Nat.le_succ _))),
    Nat.le_of_not_gt totalFits⟩

namespace NativeProofCode

theorem count_eq_length (signature : ObservedSignature) (expressionDepth proofDepth : Nat) :
    CodeCount.native (.ofSignature signature) expressionDepth proofDepth =
      (enumerate signature expressionDepth proofDepth).length := by
  cases proofDepth <;>
    simp only [CodeCount.native, enumerate, List.length_nil, List.length_append, List.length_map,
      ← CodeCount.derivation_eq_length, ← CodeCount.kernel_eq_length]

/-- Syntax-only admission is useful independently of causal profiles. It
does not run a graph check and must not be presented as a formula finder. -/
def guardedEnumeration (limits : SearchLimits) (signature : ObservedSignature)
    (expressionDepth proofDepth : Nat) : Except SearchRefusal (List NativeProofCode) :=
  (preflightSyntax limits signature expressionDepth proofDepth).map
    (fun _ => enumerate signature expressionDepth proofDepth)

theorem guardedEnumeration_exact (limits : SearchLimits) (signature : ObservedSignature)
    (expressionDepth proofDepth : Nat) (codes : List NativeProofCode)
    (accepted : guardedEnumeration limits signature expressionDepth proofDepth = .ok codes) :
    codes = enumerate signature expressionDepth proofDepth ∧ codes.length ≤ limits.maxRawCandidates := by
  cases checked : preflightSyntax limits signature expressionDepth proofDepth with
  | error reason => simp only [guardedEnumeration, checked, Except.map] at accepted; contradiction
  | ok estimate =>
      simp only [guardedEnumeration, checked, Except.map] at accepted
      cases accepted
      have bounds := preflightSyntax_bounds limits signature expressionDepth proofDepth estimate checked
      exact ⟨rfl, by simpa only [bounds.1, count_eq_length] using bounds.2.2.2.1⟩

/-- All admission checks precede construction of the raw proof list. The
source is bounded separately, because the enumerated-proof budget does not
bound an externally supplied query. This is an additional explicit resource
policy, not a change to the old grammar's completeness theorem. -/
def guardedCatalogueOn (limits : SearchLimits) (graph : ObservedGraph S)
    (profiles : List (NativeTemplateInstance Q)) (source : TermCode) (expressionDepth proofDepth : Nat) :
    Except SearchRefusal (List (CheckedNativeFormula graph profiles)) := do
  let metadata ← preflightSyntax limits S expressionDepth proofDepth
  if source.Within metadata.dictionary limits.maxSourceDepth then
    let profile ← preflightProfiles limits metadata.dictionary.references profiles
    let _ ← preflightTotal limits metadata.candidates profile.comparisonsPerCertificate
    pure (catalogueOn graph profiles source expressionDepth proofDepth)
  else .error (.source limits.maxSourceDepth)

/-- Admission does not prune mathematical results. Existing membership,
soundness and coverage theorems can be transported along this equality. -/
theorem guardedCatalogueOn_exact (limits : SearchLimits) (graph : ObservedGraph S)
    (profiles : List (NativeTemplateInstance Q)) (source : TermCode) (expressionDepth proofDepth : Nat)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (accepted : guardedCatalogueOn limits graph profiles source expressionDepth proofDepth = .ok catalogue) :
    catalogue = catalogueOn graph profiles source expressionDepth proofDepth := by
  cases metadataChecked : preflightSyntax limits S expressionDepth proofDepth with
  | error reason => simp only [guardedCatalogueOn, metadataChecked, except_bind_eq_bind, Except.bind] at accepted; contradiction
  | ok estimate =>
      simp only [guardedCatalogueOn, metadataChecked, except_bind_eq_bind, Except.bind] at accepted
      split at accepted
      · cases checked : preflightProfiles limits estimate.dictionary.references profiles with
        | error reason => simp only [checked, except_bind_eq_bind, Except.bind] at accepted; contradiction
        | ok result =>
            simp only [checked, except_bind_eq_bind, Except.bind] at accepted
            cases total : preflightTotal limits estimate.candidates result.comparisonsPerCertificate with
            | error reason => simp only [total, except_bind_eq_bind, Except.bind] at accepted; contradiction
            | ok result => simp only [total, except_bind_eq_bind, Except.bind, except_pure_eq] at accepted; cases accepted; rfl
      · contradiction

/-- Expose every successful admission gate, including the separately bounded
source. Application proofs need not unfold the potentially large catalogue. -/
theorem guardedCatalogueOn_admission (limits : SearchLimits) (graph : ObservedGraph S)
    (profiles : List (NativeTemplateInstance Q)) (source : TermCode) (expressionDepth proofDepth : Nat)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (accepted : guardedCatalogueOn limits graph profiles source expressionDepth proofDepth = .ok catalogue) :
    ∃ metadata, preflightSyntax limits S expressionDepth proofDepth = .ok metadata ∧
      source.Within metadata.dictionary limits.maxSourceDepth ∧
      ∃ profile, preflightProfiles limits metadata.dictionary.references profiles = .ok profile ∧
        ∃ total, preflightTotal limits metadata.candidates profile.comparisonsPerCertificate = .ok total := by
  cases metadataChecked : preflightSyntax limits S expressionDepth proofDepth with
  | error reason => simp only [guardedCatalogueOn, metadataChecked, except_bind_eq_bind, Except.bind] at accepted; contradiction
  | ok estimate =>
      simp only [guardedCatalogueOn, metadataChecked, except_bind_eq_bind, Except.bind] at accepted
      split at accepted
      · rename_i sourceFits
        cases checked : preflightProfiles limits estimate.dictionary.references profiles with
        | error reason => simp only [checked, except_bind_eq_bind, Except.bind] at accepted; contradiction
        | ok result =>
            simp only [checked, except_bind_eq_bind, Except.bind] at accepted
            cases total : preflightTotal limits estimate.candidates result.comparisonsPerCertificate with
            | error reason => simp only [total, except_bind_eq_bind, Except.bind] at accepted; contradiction
            | ok count => exact ⟨estimate, metadataChecked, sourceFits, result, checked, count, total⟩
      · contradiction

theorem guardedCatalogueOn_total_bound (limits : SearchLimits) (graph : ObservedGraph S)
    (profiles : List (NativeTemplateInstance Q)) (source : TermCode) (expressionDepth proofDepth : Nat)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (accepted : guardedCatalogueOn limits graph profiles source expressionDepth proofDepth = .ok catalogue) :
    (enumerate S expressionDepth proofDepth).length *
      ((profiles.length * (CodeDictionaries.ofSignature S).references) * profiles.length) ≤
        limits.maxTotalProfileComparisons := by
  rcases guardedCatalogueOn_admission limits graph profiles source expressionDepth proofDepth catalogue accepted with
    ⟨metadata, metadataChecked, _sourceFits, profile, profileChecked, total, totalChecked⟩
  have syntaxBounds := preflightSyntax_bounds limits S expressionDepth proofDepth metadata metadataChecked
  have profileBounds := preflightProfiles_bounds limits metadata.dictionary.references profiles profile profileChecked
  have totalBounds := preflightTotal_bounds limits metadata.candidates profile.comparisonsPerCertificate total totalChecked
  have rawExact : metadata.candidates = (enumerate S expressionDepth proofDepth).length := by
    rw [syntaxBounds.2.2.2.2, syntaxBounds.1, count_eq_length]
  have comparisonsExact : profile.comparisonsPerCertificate =
      (profiles.length * (CodeDictionaries.ofSignature S).references) * profiles.length := by
    rw [profileBounds.2.2.2.2.1, profileBounds.2.2.1, syntaxBounds.1]
  rw [rawExact, comparisonsExact] at totalBounds
  rw [← totalBounds.1]
  exact totalBounds.2

end NativeProofCode
end ProbabilityCode
end Thesis.Causality
