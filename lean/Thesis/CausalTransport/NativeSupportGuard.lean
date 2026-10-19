import Thesis.Causality.ProbabilityTermCode
import Thesis.CausalTransport.NativeSupportProfiles

namespace Thesis.Causality

open Probability

/-!
# Finite observable guard tables checked against actual causal profiles

A row stores the support bits of every declared observed assignment and an
assignment-dictionary index. Thus guards are serialized finite data, not
arbitrary predicates or proofs. Runtime acceptance reads only the observed
record and reference. Incorrect row lengths cannot match an actual pattern;
an invalid reference index is rejected by the certificate checker.

To certify a guard, check its required support predicate in *every* listed
causal profile with that observed pattern. One favorable hidden model is
not enough. The generic soundness lemma uses support invariance and an actual
listed representative of the original model. Downstream public adapters
supply the constructed fixed-DAG or projection-wide coverage theorem, not
an external coverage interface.

The full catalogues may be enormous. These are opt-in finite checks, not a
claim of practical small complexity, numerical identity checking, proof
enumeration or universal alternative-formula completeness.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace NativeSupportGuard

structure Cell where
  observed : List Bool
  reference : Nat
  deriving Repr, DecidableEq

abbrev Code := List Cell

def pattern (signature : ObservedSignature) (record : FiniteProbRecord signature.Assignment) : List Bool :=
  signature.assignmentEnumeration.map record.support

def Cell.accepts (cell : Cell) (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) : Bool :=
  decide (cell.observed = pattern S record) &&
    match ProbabilityCode.assignment S cell.reference with
    | none => false
    | some fixed => decide (fixed = reference)

def accepts (code : Code) (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) : Bool :=
  code.any (fun cell => cell.accepts record reference)

/-- A support-only requirement may inspect interventional expressions, but
its invariance must be proved before uniform profiles may certify it. -/
abbrev Demand (signature : ObservedSignature.{0}) :=
  {projection : FiniteLatentProjection signature} →
    FiniteHiddenDAGSCM signature projection → signature.Assignment → Bool

def Invariant (demand : Demand S) : Prop :=
  ∀ {leftProjection rightProjection : FiniteLatentProjection S}
    (left : FiniteHiddenDAGSCM S leftProjection) (right : FiniteHiddenDAGSCM S rightProjection),
    CausalSupportAgreement left right → ∀ reference, demand left reference = demand right reference

def checkCell (profiles : List (NativeTemplateInstance Q)) (demand : Demand S) (cell : Cell) : Bool :=
  match ProbabilityCode.assignment S cell.reference with
  | none => false
  | some reference => profiles.all (fun entry =>
      if cell.observed = pattern S entry.model.observationalDist then demand entry.model reference else true)

def check (profiles : List (NativeTemplateInstance Q)) (demand : Demand S) (code : Code) : Bool :=
  code.all (checkCell profiles demand)

/-- Every accepted row is safe for the original model, because that model's
entire causal support behaviour occurs in the checked list. Numerical values
of the representative are never used to certify a causal equality. -/
theorem soundAt (profiles : List (NativeTemplateInstance Q)) (demand : Demand S)
    (invariant : Invariant demand) (code : Code) (checked : check profiles demand code = true)
    (model : FiniteHiddenDAGSCM S P)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment) (accepted : accepts code model.observationalDist reference = true) :
    demand model reference = true := by
  rcases List.any_eq_true.mp accepted with ⟨cell, member, atCell⟩
  rcases covered with ⟨entry, listed, same⟩
  have rowChecked := (List.all_eq_true.mp checked) cell member
  have observedPattern : pattern S entry.model.observationalDist = pattern S model.observationalDist :=
    congrArg (fun support => S.assignmentEnumeration.map support) same.observational_support
  cases decoded : ProbabilityCode.assignment S cell.reference with
  | none =>
      simp only [Cell.accepts, decoded, Bool.and_false, Bool.false_eq_true] at atCell
  | some fixed =>
      have rowAccepted : cell.observed = pattern S model.observationalDist ∧ fixed = reference := by
        simpa only [Cell.accepts, decoded, Bool.and_eq_true_iff, decide_eq_true_eq] using atCell
      have onEntry : cell.observed = pattern S entry.model.observationalDist :=
        rowAccepted.1.trans observedPattern.symm
      have tested : demand entry.model fixed = true := by
        have atEntry := (List.all_eq_true.mp (show profiles.all (fun candidate =>
          if cell.observed = pattern S candidate.model.observationalDist then demand candidate.model fixed else true) = true by
            simpa only [checkCell, decoded] using rowChecked)) entry listed
        simpa only [if_pos onEntry] using atEntry
      rw [invariant entry.model model same fixed, rowAccepted.2] at tested
      exact tested

end NativeSupportGuard
end Thesis.Causality
