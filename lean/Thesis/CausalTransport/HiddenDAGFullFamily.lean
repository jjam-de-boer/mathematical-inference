import Thesis.CausalTransport.HiddenDAG

namespace Thesis
namespace Causality

open Probability

universe u

variable {S : ObservedSignature.{u}}

/-!
# The full family of finite SCMs over a hidden DAG

`HiddenDAGModelFamily` also permits selected subfamilies, which may identify
more queries than their graph alone does.  A general hidden-DAG theorem must
therefore specify its model family rather than claim projection equivalence
uniformly for arbitrary selections.

The family constructed here indexes *every* `FiniteHiddenDAGSCM` record over
the given projection.  Observed value domains remain those of `S`; hidden
value domains and all private-noise domains range over arbitrary finite
presentations supplied by each record.  They are not fixed by the family.

Nonemptiness is proved by a concrete constant SCM, not assumed or obtained by
choice.  A finite observed-index lookup recovers each embedded observed node;
hidden nodes use a singleton value type in that one witness.  The complete
family is not restricted to this witness's hidden domains or mechanisms.

This module supplies the precise semantic domain for later support-qualified
soundness and completeness.  It does not inhabit `PublishedLatentProjection`
or assert individual-model equivalence to independent pairwise hidden roots.
-/

namespace FiniteHiddenDAG

/-! ## Finite observed-index lookup without choosing an inverse -/

/-- Scan the explicit finite observed-node enumeration for an embedded node.
The input graph's injectivity makes any found index the unique correct one. -/
def observedIndex (H : FiniteHiddenDAG S) (node : Fin H.count) :
    Option (Fin S.count) :=
  (List.finRange S.count).find? (fun index => decide (H.observedNode index = node))

/-- A successful lookup has the declared observed embedding. -/
theorem observedIndex_sound (H : FiniteHiddenDAG S) (node : Fin H.count)
    (index : Fin S.count) (found : H.observedIndex node = some index) :
    H.observedNode index = node :=
  of_decide_eq_true
    (List.find?_some (p := fun candidate => decide (H.observedNode candidate = node)) found)

/-- Every embedded observed node is found, with its original index.  The
missing case contradicts the explicitly listed index; the successful case
uses injectivity.  Neither case selects a witness from an existential. -/
theorem observedIndex_observed (H : FiniteHiddenDAG S) (index : Fin S.count) :
    H.observedIndex (H.observedNode index) = some index := by
  cases result : H.observedIndex (H.observedNode index) with
  | none =>
      have missing := (List.find?_eq_none.mp result) index (List.mem_finRange index)
      exact False.elim (missing (decide_eq_true rfl))
  | some found =>
      have same : found = index :=
        H.observedNode_injective (H.observedIndex_sound _ found result)
      exact congrArg some same

/-- A hidden node cannot be returned as an observed node. -/
theorem observedIndex_hidden (H : FiniteHiddenDAG S) (node : Fin H.count)
    (hidden : H.hidden node = true) : H.observedIndex node = none := by
  cases result : H.observedIndex node with
  | none => rfl
  | some index =>
      have embedding := H.observedIndex_sound node index result
      have notHidden : H.hidden node = false := embedding ▸ H.observed_not_hidden index
      exact False.elim (Bool.false_ne_true (notHidden.symm.trans hidden))

/-! ## A finite default presentation for the nonempty-family witness -/

/-- Use each observed node's unchanged value domain and a singleton at hidden
nodes.  This presentation belongs only to the constant witness constructed
below; it places no restriction on the full family. -/
def defaultNodeValue (H : FiniteHiddenDAG S) (node : Fin H.count) : Type u :=
  match H.observedIndex node with
  | none => PUnit.{u + 1}
  | some index => S.Value index

/-- The default presentation carries an explicit complete finite enumeration. -/
def defaultNodeEnumeration (H : FiniteHiddenDAG S) (node : Fin H.count) :
    List (H.defaultNodeValue node) := by
  -- Expose the dependent value type before inspecting the lookup.  A
  -- nondependent match would leave both branch lists at the unreduced type.
  unfold defaultNodeValue
  cases H.observedIndex node with
  | none => exact [PUnit.unit]
  | some index => exact S.valueEnumeration index

theorem defaultNode_complete (H : FiniteHiddenDAG S) (node : Fin H.count) :
    forall value, value ∈ H.defaultNodeEnumeration node := by
  unfold defaultNodeEnumeration defaultNodeValue
  cases index : H.observedIndex node with
  | none =>
      intro value
      cases value
      exact List.mem_cons.mpr (Or.inl rfl)
  | some observed =>
      exact S.value_complete observed

/-- Equality is inherited from the observed signature or the singleton type. -/
def defaultNodeDecidableEq (H : FiniteHiddenDAG S) (node : Fin H.count) :
    DecidableEq (H.defaultNodeValue node) := by
  cases index : H.observedIndex node with
  | none =>
      simpa only [defaultNodeValue, index] using
        (inferInstance : DecidableEq PUnit.{u + 1})
  | some observed =>
      simpa only [defaultNodeValue, index] using S.valueDecidableEq observed

/-- The witness's observed presentation is constructively equivalent to the
original signature, not merely equinumerous or propositionally inhabited. -/
def defaultObservedEquivalence (H : FiniteHiddenDAG S) (index : Fin S.count) :
    ValueEquivalence (H.defaultNodeValue (H.observedNode index)) (S.Value index) := by
  unfold defaultNodeValue
  rw [H.observedIndex_observed index]
  exact ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-- An explicit default value at every node avoids any finite-choice step. -/
def defaultNodeAssignment (H : FiniteHiddenDAG S) (node : Fin H.count) :
    H.defaultNodeValue node := by
  cases index : H.observedIndex node with
  | none =>
      simpa only [defaultNodeValue, index] using (PUnit.unit : PUnit.{u + 1})
  | some observed =>
      simpa only [defaultNodeValue, index] using S.defaultValue observed

end FiniteHiddenDAG

namespace FiniteHiddenDAGSCM

/-- One explicitly enumerated private noise value with probability one. -/
private def singletonNoise : FiniteProbRecord PUnit.{u + 1} where
  atoms := [(PUnit.unit, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

/-- A concrete finite SCM exists over every full hidden DAG.  Mechanisms may
ignore declared parents: graph compatibility bounds their permitted inputs,
not a faithfulness requirement.  Its independent private-noise prior is the
existing exact finite product construction, with its proved rectangular law.

This constant model intentionally need not have positive observational support;
its role is nonemptiness of the full family, not a completeness countermodel or
a witness for a positivity-restricted family. -/
def constant (projection : FiniteLatentProjection S) : FiniteHiddenDAGSCM S projection where
  NodeValue := projection.hiddenDAG.defaultNodeValue
  nodeEnumeration := projection.hiddenDAG.defaultNodeEnumeration
  node_complete := projection.hiddenDAG.defaultNode_complete
  nodeDecidableEq := projection.hiddenDAG.defaultNodeDecidableEq
  observedEquiv := projection.hiddenDAG.defaultObservedEquivalence
  observedIndex := projection.hiddenDAG.observedIndex
  observedIndex_observed := projection.hiddenDAG.observedIndex_observed
  observedIndex_sound := projection.hiddenDAG.observedIndex_sound
  hidden_has_no_observed_index := projection.hiddenDAG.observedIndex_hidden
  Noise := fun _ => PUnit.{u + 1}
  noiseEnumeration := fun _ => [PUnit.unit]
  noise_complete := by
    intro _ value
    cases value
    exact List.mem_cons.mpr (Or.inl rfl)
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => singletonNoise
  prior := FiniteProduct.record projection.hiddenDAG.count
    (fun _ => PUnit.{u + 1}) (fun _ => singletonNoise)
  product_law := FiniteProduct.record_rectangular_probVal projection.hiddenDAG.count
    (fun _ => PUnit.{u + 1}) (fun _ => singletonNoise)
  mechanism := fun node _parents _noise => projection.hiddenDAG.defaultNodeAssignment node

end FiniteHiddenDAGSCM

namespace HiddenDAGModelFamily

/-- The entire finite hidden-DAG model family, with arbitrary finite hidden
and private-noise domains.  Unlike a selected family, its model indices are
literally all SCM records over the projection; no semantic coverage condition
is supplied by an external caller. -/
def all (projection : FiniteLatentProjection S) : HiddenDAGModelFamily S projection where
  Model := FiniteHiddenDAGSCM S projection
  model_nonempty := ⟨FiniteHiddenDAGSCM.constant projection⟩
  semantics := id

/-- Every finite SCM over the projection is retained with its exact semantics.
This states the full-family coverage boundary, not a latent-projection theorem. -/
theorem all_semantics (projection : FiniteLatentProjection S)
    (model : FiniteHiddenDAGSCM S projection) :
    (HiddenDAGModelFamily.all projection).semantics model = model := rfl

end HiddenDAGModelFamily
end Causality
end Thesis
