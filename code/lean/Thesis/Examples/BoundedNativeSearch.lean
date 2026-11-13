import Thesis.CausalTransport.BoundedNativeSearch

namespace Thesis.Causality.Examples.BoundedNativeSearch

open Probability

/-!
# Exact bounded search distinguishes factual identification from a null action

Use the two-node observed DAG `X -> Y`, binary declared values, deterministic
one-code private sources and denominator bound one. Two actual native models
have the same factual point mass at `X = Y = 0`. In one, `Y` is always zero;
in the other it copies `X`. Thus `P(Y = 1 | do(X = 1))` differs, although the
whole observational laws agree. This is fixed-law ambiguity at an unsupported
action, not a counterexample to positive-class graphical completeness.

The complete bounded solver must report that ambiguity. For the factual
query it must instead return an attained identified value; with denominator
bound zero it must report incompatibility. These tests use the solver's
proved output obligations and two tiny computed models, not kernel expansion
of its whole structural catalogue. Separate two-entry inspection tests execute
the finite comparison algorithm directly. No runtime limit is increased.
-/

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Fin 2
  valueEnumeration := fun _ => List.finRange 2
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => finRange_nodup 2
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
    · intro edge
      exact .direct edge
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

def model (respond : Bool) : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Fin 2
  nodeEnumeration := fun _ => List.finRange 2
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
      if respond then parents x (by change decide (x.val = 0 ∧ child.val = 1) = true; exact decide_eq_true ⟨rfl, atY⟩)
      else 0
    else 0

def entry (respond : Bool) : NativeTemplateInstance projection :=
  ⟨(model respond).nativeTemplate (fun _ => 2) (fun _ => 1)
      (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩) (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩),
    (model respond).nativeTemplateFactors (fun _ => 1) (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩)⟩

def observed : FiniteProbRecord signature.Assignment := ⟨[(fun _ => (0 : Fin 2), 1)], 1, by decide, rfl⟩
def outcome : Event signature.Assignment := fun values => decide (values y = (1 : Fin 2))
def effect : NativeProbabilityQuery signature := ⟨(HardIntervention.empty signature).set x (1 : Fin 2), outcome⟩
def factual : NativeProbabilityQuery signature := ⟨HardIntervention.empty signature, outcome⟩

theorem template_listed (respond : Bool) :
    (entry respond).template ∈ fullGraph.nativeTemplateCatalogue 2 1 :=
  fullGraph.nativeTemplateCatalogue_complete 2 1 _ (fun _ => Nat.le_refl 2) (fun _ => Nat.le_refl 1)

theorem denominator_bounded (respond : Bool) (node : Fin fullGraph.count) : ((entry respond).factors node).den ≤ 1 := Nat.le_refl 1

theorem nodes_bounded (respond : Bool) (node : Fin fullGraph.count) :
    ((entry respond).model.nodeEnumeration node).length ≤ 2 := by
  change (List.finRange 2).length ≤ 2
  rw [List.length_finRange]
  exact Nat.le_refl 2

theorem sources_bounded (respond : Bool) (node : Fin fullGraph.count) :
    ((entry respond).model.noiseEnumeration node).length ≤ 1 := by
  change (List.finRange 1).length ≤ 1
  rw [List.length_finRange]
  exact Nat.le_refl 1

theorem observational_agreement (respond : Bool) : (entry respond).MatchesObservation observed := by
  apply ((entry respond).observationCheck_exact observed).mp
  cases respond <;> decide +kernel

theorem different_effects : ¬ QProb.Equiv ((entry false).queryValue effect) ((entry true).queryValue effect) := by decide +kernel

def inspectionTag {query : NativeProbabilityQuery signature} {candidates : List (NativeTemplateInstance projection)} :
    NativeTemplateInstance.Inspection query candidates → Nat
  | .incompatible _ => 0
  | .identified _ _ _ => 1
  | .ambiguous _ _ _ _ _ => 2

theorem inspect_empty : inspectionTag (NativeTemplateInstance.inspect effect ([] : List (NativeTemplateInstance projection))) = 0 := rfl
theorem inspect_singleton : inspectionTag (NativeTemplateInstance.inspect effect [entry false]) = 1 := by decide +kernel
theorem inspect_distinct_effects : inspectionTag (NativeTemplateInstance.inspect effect [entry false, entry true]) = 2 := by decide +kernel

def resultTag {denominatorBound : Nat} {query : NativeProbabilityQuery signature} :
    Causality.BoundedNativeSearch.Result projection 2 1 denominatorBound observed query → Nat
  | .incompatible _ => 0
  | .identified _ _ => 1
  | .ambiguous _ _ _ => 2

/-- Two supplied models in the *whole* bounded class force every sound
search result into its ambiguity branch, without expanding the catalogue. -/
theorem complete_class_effect_ambiguous
    (answer : Causality.BoundedNativeSearch.Result projection 2 1 1 observed effect) : resultTag answer = 2 := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch (entry false).model (nodes_bounded false) (sources_bounded false) (denominator_bounded false) (observational_agreement false))
  | identified witness unique =>
      have left := unique (entry false).model (nodes_bounded false) (sources_bounded false) (denominator_bounded false) (observational_agreement false)
      have right := unique (entry true).model (nodes_bounded true) (sources_bounded true) (denominator_bounded true) (observational_agreement true)
      exact False.elim (different_effects (QProb.equiv_trans left (QProb.equiv_symm right)))
  | ambiguous _ _ _ => rfl

theorem solver_effect_ambiguous :
    resultTag (Causality.BoundedNativeSearch.solve projection 2 1 1 observed effect) = 2 :=
  complete_class_effect_ambiguous _

theorem complete_class_factual_identified
    (answer : Causality.BoundedNativeSearch.Result projection 2 1 1 observed factual) : resultTag answer = 1 := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch (entry false).model (nodes_bounded false) (sources_bounded false) (denominator_bounded false) (observational_agreement false))
  | identified _ _ => rfl
  | ambiguous left right different =>
      exact False.elim (different (QProb.equiv_trans (left.matched outcome) (QProb.equiv_symm (right.matched outcome))))

theorem solver_factual_identified :
    resultTag (Causality.BoundedNativeSearch.solve projection 2 1 1 observed factual) = 1 :=
  complete_class_factual_identified _

theorem zero_bound_incompatible
    (answer : Causality.BoundedNativeSearch.Result projection 2 1 0 observed effect) : resultTag answer = 0 := by
  cases answer with
  | incompatible _ => rfl
  | identified witness _ =>
      exact False.elim ((Nat.not_le_of_lt (witness.entry.factors x).den_pos) (witness.denominators x))
  | ambiguous left _ _ =>
      exact False.elim ((Nat.not_le_of_lt (left.entry.factors x).den_pos) (left.denominators x))

theorem solver_zero_bound_incompatible :
    resultTag (Causality.BoundedNativeSearch.solve projection 2 1 0 observed effect) = 0 := zero_bound_incompatible _

end Thesis.Causality.Examples.BoundedNativeSearch
