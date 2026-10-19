import Thesis.CausalTransport.BoundedNativeConditionalSearch

namespace Thesis.Causality.Examples.BoundedNativeMixedConditionals

open Probability
open Causality.BoundedNativeSearch Causality.BoundedNativeConditionalSearch

/-!
# Mixed conditional support need not imply value agreement

Use a three-valued `X -> Y` graph. All three deterministic models have the
same factual point mass at `(0, 0)`. After forcing `X = 1`, their respective
responses are `Y = 0`, `Y = 1` and `Y = 2`. Evidence `Y != 0` is null in the
first model and positive in the other two. Among those positive models the
conditional probability of `Y = 1` takes both zero and one.

Together with the binary common-value regression, this checks both sides of
the separate-reporting policy: a null-evidence witness can coexist with
supported-value identification or supported-value ambiguity. Every witness
here is an actual observationally fitted bounded native model. Whole-class
tests use those witnesses to force the public result's branches without
expanding its full finite mechanism catalogue.
-/

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => finRange_nodup 3
  defaultValue := fun _ => 0
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by
    intro parent child selected
    have edge := of_decide_eq_true selected
    omega

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

def fullGraph : FiniteHiddenDAG signature where
  count := 2
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := fun _ => rfl
  node_classified := fun node => Or.inr ⟨node, rfl⟩
  edge := signature.directed
  rank := Fin.val
  edge_rank_lt := fun selected => signature.directed_earlier selected

def projection : FiniteLatentProjection signature where
  hiddenDAG := fullGraph
  directed_matches := by
    intro first second
    constructor
    · intro edge; exact .direct edge
    · intro path
      cases path with
      | direct edge => exact edge
      | tail _ hidden _ => cases hidden
  bidirected := fun _ _ => false
  bidirected_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · rintro ⟨_, _, hidden, _, _⟩; cases hidden

def unitFactor : FiniteProbRecord (Fin 1) := ⟨[(0, 1)], 1, by decide, rfl⟩

def model (response : Fin 3) : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Fin 3
  nodeEnumeration := fun _ => List.finRange 3
  node_complete := fun _ value => List.mem_finRange value
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := some
  observedIndex_observed := fun _ => rfl
  observedIndex_sound := fun _ _ same => (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ hidden; cases hidden
  Noise := fun _ => Fin 1
  noiseEnumeration := fun _ => List.finRange 1
  noise_complete := fun _ value => List.mem_finRange value
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => unitFactor
  prior := FiniteProduct.record 2 (fun _ => Fin 1) (fun _ => unitFactor)
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Fin 1) (fun _ => unitFactor)
  mechanism := fun child parents _noise =>
    if atY : child.val = 1 then
      if parents x (by change decide (x.val = 0 ∧ child.val = 1) = true; exact decide_eq_true ⟨rfl, atY⟩) = 1
      then response else 0
    else 0

def entry (response : Fin 3) : NativeTemplateInstance projection :=
  ⟨(model response).nativeTemplate (fun _ => 3) (fun _ => 1)
      (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩) (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩),
    (model response).nativeTemplateFactors (fun _ => 1) (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩)⟩

def observed : FiniteProbRecord signature.Assignment := ⟨[(fun _ => (0 : Fin 3), 1)], 1, by decide, rfl⟩
def query : NativeConditionalQuery signature :=
  ⟨(HardIntervention.empty signature).set x (1 : Fin 3),
    (fun values => decide (values y ≠ (0 : Fin 3))), (fun values => decide (values y = (1 : Fin 3)))⟩

theorem observational_agreement (response : Fin 3) : (entry response).MatchesObservation observed := by
  apply ((entry response).observationCheck_exact observed).mp
  have alternatives : response = 0 ∨ response = 1 ∨ response = 2 := by omega
  rcases alternatives with rfl | rfl | rfl <;> decide +kernel

theorem entry_fits (response : Fin 3) : Fits projection 3 1 1 observed (entry response).model := by
  refine ⟨?_, ?_, (fun _ => Nat.le_refl 1), observational_agreement response⟩
  · intro node
    change (List.finRange 3).length ≤ 3
    rw [List.length_finRange]
    exact Nat.le_refl 3
  · intro node
    change (List.finRange 1).length ≤ 1
    rw [List.length_finRange]
    exact Nat.le_refl 1

theorem zero_unsupported : ¬ query.Supported (entry 0).model := by decide +kernel
theorem one_supported : query.Supported (entry 1).model := by decide +kernel
theorem two_supported : query.Supported (entry 2).model := by decide +kernel
theorem different_supported_values :
    ¬ QProb.Equiv (query.value (entry 1).model one_supported) (query.value (entry 2).model two_supported) := by decide +kernel

def valueTag {candidates : List (NativeTemplateInstance projection)} :
    NativeTemplateInstance.ConditionalValueInspection query candidates → Nat
  | .unsupported _ => 0
  | .identified _ _ _ _ => 1
  | .ambiguous _ _ _ _ _ _ _ => 2

theorem inspect_mixed_ambiguity :
    valueTag (NativeTemplateInstance.inspectValues query [entry 0, entry 1, entry 2]) = 2 := by decide +kernel

/-- An already ambiguous supported tail stays ambiguous when either a null
or another supported model is prepended. -/
theorem inspect_preserves_ambiguity :
    valueTag (NativeTemplateInstance.inspectValues query [entry 1, entry 0, entry 1, entry 2]) = 2 := by decide +kernel

def resultTags : Causality.BoundedNativeConditionalSearch.Result projection 3 1 1 observed query → Nat × Nat
  | .incompatible _ => (0, 0)
  | .compatible _ support values =>
      ((match support with | .allSupported _ => 1 | .nullWitness _ _ => 2),
       (match values with | .unsupported _ => 1 | .identified _ _ => 2 | .ambiguous _ _ _ => 3))

theorem complete_class_mixed_ambiguous
    (answer : Causality.BoundedNativeConditionalSearch.Result projection 3 1 1 observed query) :
    resultTags answer = (2, 3) := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch ⟨(entry 0).model, entry_fits 0⟩)
  | compatible witness support values =>
      cases support with
      | allSupported positive => exact False.elim (zero_unsupported (positive (entry 0).model (entry_fits 0)))
      | nullWitness nullModel nullEvidence =>
          cases values with
          | unsupported noSupport => exact False.elim (noSupport (entry 1).model (entry_fits 1) one_supported)
          | identified witness constant =>
              have left := constant (entry 1).model (entry_fits 1) one_supported
              have right := constant (entry 2).model (entry_fits 2) two_supported
              exact False.elim (different_supported_values (QProb.equiv_trans left (QProb.equiv_symm right)))
          | ambiguous _ _ _ => rfl

theorem solver_mixed_ambiguous :
    resultTags (Causality.BoundedNativeConditionalSearch.solve projection 3 1 1 observed query) = (2, 3) :=
  complete_class_mixed_ambiguous _

end Thesis.Causality.Examples.BoundedNativeMixedConditionals
