import Thesis.CausalTransport.BoundedNativeSearch

namespace Thesis.Causality.BoundedNativeSearch

open Probability

/-!
# Decidable compatibility and point identification for the full bounded class

The search result already contains native witnesses or exclusion proofs. This
module states its consequences as ordinary mathematical predicates and gives
explicit `Decidable` values and exact Boolean checks. Quantifiers range over
all original native records satisfying the declared enumeration/denominator
bounds, not just the literal canonical entries in the finite search list.

Point identification deliberately includes compatibility. An impossible
observational law is therefore not called identified merely because a
pairwise equality condition would hold vacuously. Separation contains two
actual fitted native models with different target probabilities.

Decisions are obtained by inspecting the constructed finite-search result;
there is no general excluded-middle or choice principle. They are explicit
functions, not global type-class instances that might silently launch an
expensive search during unrelated proof elaboration. Conditional support and
unrestricted rational-model decisions remain outside this module.
-/

variable {S : ObservedSignature.{0}}

section Predicates

variable (P : FiniteLatentProjection S) (nodeBound sourceBound denominatorBound : Nat)
variable (observed : FiniteProbRecord S.Assignment)

def Fits (original : FiniteHiddenDAGSCM S P) : Prop :=
  (∀ node, (original.nodeEnumeration node).length ≤ nodeBound) ∧
  (∀ node, (original.noiseEnumeration node).length ≤ sourceBound) ∧
  (∀ node, (original.factor node).den ≤ denominatorBound) ∧
  MatchesNativeObservation P observed original

def Compatible : Prop := ∃ original, Fits P nodeBound sourceBound denominatorBound observed original

/-- An attained bounded-class identification statement, not vacuous
uniqueness at an incompatible supplied law. -/
def PointIdentified (query : NativeProbabilityQuery S) : Prop :=
  Compatible P nodeBound sourceBound denominatorBound observed ∧
  ∀ left right, Fits P nodeBound sourceBound denominatorBound observed left →
    Fits P nodeBound sourceBound denominatorBound observed right →
    QProb.Equiv (left.interventionalValue query.intervention query.event)
      (right.interventionalValue query.intervention query.event)

def Separated (query : NativeProbabilityQuery S) : Prop :=
  ∃ left right, Fits P nodeBound sourceBound denominatorBound observed left ∧
    Fits P nodeBound sourceBound denominatorBound observed right ∧
    ¬ QProb.Equiv (left.interventionalValue query.intervention query.event)
      (right.interventionalValue query.intervention query.event)

end Predicates

variable {P : FiniteLatentProjection S} {nodeBound sourceBound denominatorBound : Nat}
variable {observed : FiniteProbRecord S.Assignment} {query : NativeProbabilityQuery S}

theorem FittedModel.fits (witness : FittedModel P nodeBound sourceBound denominatorBound observed) :
    Fits P nodeBound sourceBound denominatorBound observed witness.entry.model :=
  ⟨witness.nodes, witness.sources, witness.denominators, witness.matched⟩

theorem FittedModel.pointIdentified (witness : FittedModel P nodeBound sourceBound denominatorBound observed)
    (unique : ∀ original : FiniteHiddenDAGSCM S P,
      (∀ node, (original.nodeEnumeration node).length ≤ nodeBound) →
      (∀ node, (original.noiseEnumeration node).length ≤ sourceBound) →
      (∀ node, (original.factor node).den ≤ denominatorBound) → MatchesNativeObservation P observed original →
      QProb.Equiv (original.interventionalValue query.intervention query.event) (witness.entry.queryValue query)) :
    PointIdentified P nodeBound sourceBound denominatorBound observed query := by
  refine ⟨⟨witness.entry.model, witness.fits⟩, ?_⟩
  intro left right leftFits rightFits
  rcases leftFits with ⟨leftNodes, leftSources, leftDenominators, leftMatched⟩
  rcases rightFits with ⟨rightNodes, rightSources, rightDenominators, rightMatched⟩
  exact QProb.equiv_trans (unique left leftNodes leftSources leftDenominators leftMatched)
    (QProb.equiv_symm (unique right rightNodes rightSources rightDenominators rightMatched))

def Result.compatibilityDecision (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    Decidable (Compatible P nodeBound sourceBound denominatorBound observed) :=
  match answer with
  | .incompatible noMatch => .isFalse (by
      rintro ⟨original, nodes, sources, denominators, matched⟩
      exact noMatch original nodes sources denominators matched)
  | .identified witness _ => .isTrue ⟨witness.entry.model, witness.fits⟩
  | .ambiguous left _ _ => .isTrue ⟨left.entry.model, left.fits⟩

def Result.pointIdentificationDecision (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    Decidable (PointIdentified P nodeBound sourceBound denominatorBound observed query) :=
  match answer with
  | .incompatible noMatch => .isFalse (by
      rintro ⟨⟨original, nodes, sources, denominators, matched⟩, _⟩
      exact noMatch original nodes sources denominators matched)
  | .identified witness unique => .isTrue (witness.pointIdentified unique)
  | .ambiguous left right different => .isFalse (by
      rintro ⟨_, unique⟩
      exact different (unique left.entry.model right.entry.model left.fits right.fits))

def Result.separationDecision (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    Decidable (Separated P nodeBound sourceBound denominatorBound observed query) :=
  match answer with
  | .incompatible noMatch => .isFalse (by
      rintro ⟨left, _, ⟨nodes, sources, denominators, matched⟩, _, _⟩
      exact noMatch left nodes sources denominators matched)
  | .identified witness unique => .isFalse (by
      rintro ⟨left, right, ⟨leftNodes, leftSources, leftDenominators, leftMatched⟩,
        ⟨rightNodes, rightSources, rightDenominators, rightMatched⟩, different⟩
      exact different (QProb.equiv_trans (unique left leftNodes leftSources leftDenominators leftMatched)
        (QProb.equiv_symm (unique right rightNodes rightSources rightDenominators rightMatched))))
  | .ambiguous left right different => .isTrue ⟨left.entry.model, right.entry.model, left.fits, right.fits, different⟩

/-- Reuse a previously computed result rather than rerunning the finite
catalogue when asking several questions about the same observed law. -/
def Result.compatibleCheck (answer : Result P nodeBound sourceBound denominatorBound observed query) : Bool :=
  @decide (Compatible P nodeBound sourceBound denominatorBound observed) answer.compatibilityDecision

def Result.pointIdentifiedCheck (answer : Result P nodeBound sourceBound denominatorBound observed query) : Bool :=
  @decide (PointIdentified P nodeBound sourceBound denominatorBound observed query) answer.pointIdentificationDecision

def Result.separatedCheck (answer : Result P nodeBound sourceBound denominatorBound observed query) : Bool :=
  @decide (Separated P nodeBound sourceBound denominatorBound observed query) answer.separationDecision

theorem Result.compatibleCheck_exact (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    answer.compatibleCheck = true ↔ Compatible P nodeBound sourceBound denominatorBound observed := by
  simp only [compatibleCheck, decide_eq_true_eq]

theorem Result.pointIdentifiedCheck_exact (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    answer.pointIdentifiedCheck = true ↔ PointIdentified P nodeBound sourceBound denominatorBound observed query := by
  simp only [pointIdentifiedCheck, decide_eq_true_eq]

theorem Result.separatedCheck_exact (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    answer.separatedCheck = true ↔ Separated P nodeBound sourceBound denominatorBound observed query := by
  simp only [separatedCheck, decide_eq_true_eq]

/-- Within the full bounded class, compatibility has a constructive exact
alternative: an attained identified value or two disagreeing native models. -/
theorem compatible_iff_pointIdentified_or_separated
    (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    Compatible P nodeBound sourceBound denominatorBound observed ↔
      PointIdentified P nodeBound sourceBound denominatorBound observed query ∨
      Separated P nodeBound sourceBound denominatorBound observed query := by
  constructor
  · intro compatible
    cases answer with
    | incompatible noMatch =>
        rcases compatible with ⟨original, nodes, sources, denominators, matched⟩
        exact False.elim (noMatch original nodes sources denominators matched)
    | identified witness unique => exact Or.inl (witness.pointIdentified unique)
    | ambiguous left right different => exact Or.inr ⟨left.entry.model, right.entry.model, left.fits, right.fits, different⟩
  · intro alternative
    rcases alternative with identified | separated
    · exact identified.1
    · rcases separated with ⟨left, _, leftFits, _, _⟩
      exact ⟨left, leftFits⟩

/-- Failure of the attained identification predicate distinguishes an
incompatible input law from a genuine pair of fixed-law countermodels. -/
theorem not_pointIdentified_iff_incompatible_or_separated
    (answer : Result P nodeBound sourceBound denominatorBound observed query) :
    ¬ PointIdentified P nodeBound sourceBound denominatorBound observed query ↔
      (¬ Compatible P nodeBound sourceBound denominatorBound observed) ∨
      Separated P nodeBound sourceBound denominatorBound observed query := by
  constructor
  · intro notIdentified
    cases answer with
    | incompatible noMatch =>
        apply Or.inl
        rintro ⟨original, nodes, sources, denominators, matched⟩
        exact noMatch original nodes sources denominators matched
    | identified witness unique => exact False.elim (notIdentified (witness.pointIdentified unique))
    | ambiguous left right different => exact Or.inr ⟨left.entry.model, right.entry.model, left.fits, right.fits, different⟩
  · intro alternative identified
    rcases alternative with incompatible | separated
    · exact incompatible identified.1
    · rcases separated with ⟨left, right, leftFits, rightFits, different⟩
      exact different (identified.2 left right leftFits rightFits)

end Thesis.Causality.BoundedNativeSearch
