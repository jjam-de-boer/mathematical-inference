import Thesis.CausalTransport.ObservationalFormulaSupport

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Finite catalogue comparison over observational support patterns

A fixed observed signature has finitely many complete assignments and hence
finitely many Boolean support patterns. Enumerating those patterns lets an
application compare the domains of *given* plans, find uncovered patterns,
and test whether removing a candidate shrinks the catalogue's domain.

This can be exponentially larger than the assignment table; it is an opt-in
small-instance checker, not an instruction to evaluate large concrete cubes
inside a proof. Empty support is excluded because normalized records cannot
have it. Nonempty patterns need not be compatible with the supplied causal
graph. A reported uncovered pattern is therefore a coverage diagnostic, not
automatically a causal countermodel or proof of nonidentifiability.

No enumeration of valid formula certificates follows from this finite
support space. Proving that a catalogue covers every *coverable* pattern
still needs a separate completeness argument for discovering certificates.
-/

namespace ObservationalSupportPattern

def assignmentWitness (S : ObservedSignature) : FiniteWitness S.Assignment :=
  .ofList S.assignmentEnumeration S.assignmentEnumeration_complete S.assignmentEnumeration_nodup

/-- One Boolean bit per distinct full observed assignment. Codes are a
genuine finite bijection, so no choice of an assignment representative is used. -/
def all (S : ObservedSignature) : List (S.Assignment → Bool) :=
  (FiniteProduct.enumeration (assignmentWitness S).card (fun _ => Bool) (fun _ => [false, true])).map
    (fun bits value => bits ((assignmentWitness S).encode value))

theorem mem_all (pattern : S.Assignment → Bool) : pattern ∈ all S := by
  let coded : Fin (assignmentWitness S).card → Bool := fun code => pattern ((assignmentWitness S).decode code)
  have listed := FiniteProduct.enumeration_complete (assignmentWitness S).card (fun _ => Bool)
    (fun _ => [false, true]) (fun _ bit => by cases bit <;> simp) coded
  have recovered : (fun value => coded ((assignmentWitness S).encode value)) = pattern := by
    funext value
    exact congrArg pattern ((assignmentWitness S).decode_encode value)
  exact List.mem_map.mpr ⟨coded, listed, recovered⟩

def nonempty (S : ObservedSignature) : List (S.Assignment → Bool) :=
  (all S).filter (fun pattern => FiniteProbRecord.eventSupported S.assignmentEnumeration pattern (fun _ => true))

/-- Every normalized record appears among the retained patterns, even if
its atom list repeats labels or includes zero-weight entries. -/
theorem support_mem_nonempty (record : FiniteProbRecord S.Assignment) : record.support ∈ nonempty S := by
  apply List.mem_filter.mpr
  refine ⟨mem_all record.support, ?_⟩
  rw [FiniteProbRecord.eventSupported_eq record _ S.assignmentEnumeration_complete]
  apply (decide_eq_true_eq).mpr
  change 0 < FiniteProbRecord.eventMass record.atoms topEvent
  rw [FiniteProbRecord.eventMass_top, record.total_mass]
  exact record.den_pos

end ObservationalSupportPattern

namespace ObservationalFormulaPlan

/-- Exhaust all retained patterns and reference assignments. This is a
finite supplied-catalogue comparison, not a search for additional formulas. -/
def coverageIncluded (left right : List (ObservationalFormulaPlan S)) : Bool :=
  (ObservationalSupportPattern.nonempty S).all (fun pattern =>
    S.assignmentEnumeration.all (fun reference =>
      !(coversSupport left pattern reference) || coversSupport right pattern reference))

theorem coverageIncluded_iff (left right : List (ObservationalFormulaPlan S)) :
    coverageIncluded left right = true ↔
      ∀ pattern, pattern ∈ ObservationalSupportPattern.nonempty S → ∀ reference,
        coversSupport left pattern reference = true → coversSupport right pattern reference = true := by
  constructor
  · intro included pattern listed reference accepted
    have atPattern := List.all_eq_true.mp included pattern listed
    have atReference := List.all_eq_true.mp atPattern reference (S.assignmentEnumeration_complete reference)
    simpa only [accepted, Bool.not_true, Bool.false_or] using atReference
  · intro included
    apply List.all_eq_true.mpr
    intro pattern listed
    apply List.all_eq_true.mpr
    intro reference _listedReference
    cases accepted : coversSupport left pattern reference with
    | false => simp [accepted]
    | true => simp [accepted, included pattern listed reference accepted]

/-- A passing comparison applies to every actual normalized observed
record. Neither the numerical weights nor its hidden implementation matter. -/
theorem coverageIncluded_transfer (left right : List (ObservationalFormulaPlan S))
    (included : coverageIncluded left right = true) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) (accepted : left.any (fun plan => plan.available record reference) = true) :
    right.any (fun plan => plan.available record reference) = true := by
  rw [← coversSupport_exact left record reference] at accepted
  rw [← coversSupport_exact right record reference]
  exact (coverageIncluded_iff left right).mp included record.support
    (ObservationalSupportPattern.support_mem_nonempty record) reference accepted

/-- Catalogue equivalence is mutual domain inclusion. For a proposed
deletion, compare the remaining list against the original in both directions. -/
def sameCoverage (left right : List (ObservationalFormulaPlan S)) : Bool :=
  coverageIncluded left right && coverageIncluded right left

/-- Return unsupported support patterns at one requested assignment. This
does not assert graph compatibility of any listed pattern. -/
def uncoveredPatterns (plans : List (ObservationalFormulaPlan S)) (reference : S.Assignment) :
    List (S.Assignment → Bool) :=
  (ObservationalSupportPattern.nonempty S).filter (fun pattern => !(coversSupport plans pattern reference))

theorem mem_uncoveredPatterns_iff (plans : List (ObservationalFormulaPlan S)) (reference : S.Assignment)
    (pattern : S.Assignment → Bool) :
    pattern ∈ uncoveredPatterns plans reference ↔
      pattern ∈ ObservationalSupportPattern.nonempty S ∧ coversSupport plans pattern reference = false := by
  simp only [uncoveredPatterns, List.mem_filter, Bool.not_eq_true']

end ObservationalFormulaPlan
end Thesis.Causality
