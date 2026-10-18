import Thesis.CausalTransport.HiddenDAG
import Thesis.Causality.HiddenDAGObservedIndex

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

/-! ## A finite default presentation for the nonempty-family witness -/

/-- Keep a chosen node's value type and all of its finite presentation data
together.  Selecting this record by the computed observed index avoids moving
an enumeration across an unrelated dependent type equality afterward. -/
private structure DefaultNodePresentation where
  Value : Type u
  enumeration : List Value
  complete : forall value, value ∈ enumeration
  valueDecidableEq : DecidableEq Value
  defaultValue : Value

/-- Both branches explicitly construct all presentation data.  The observed
branch retains the original signature; the hidden branch is a singleton.
This finite match does not choose a type or an inhabitant from a proposition. -/
private def defaultNodePresentation (H : FiniteHiddenDAG S) (node : Fin H.count) :
    DefaultNodePresentation.{u} :=
  match H.observedIndex node with
  | none =>
      { Value := PUnit.{u + 1}
        enumeration := [PUnit.unit]
        complete := by
          intro value
          cases value
          exact List.mem_cons.mpr (Or.inl rfl)
        valueDecidableEq := inferInstance
        defaultValue := PUnit.unit }
  | some index =>
      { Value := S.Value index
        enumeration := S.valueEnumeration index
        complete := S.value_complete index
        valueDecidableEq := S.valueDecidableEq index
        defaultValue := S.defaultValue index }

/-- Use each observed node's unchanged value domain and a singleton at hidden
nodes.  This presentation belongs only to the constant witness constructed
below; it places no restriction on the full family. -/
def defaultNodeValue (H : FiniteHiddenDAG S) (node : Fin H.count) : Type u :=
  (defaultNodePresentation H node).Value

/-- The default presentation carries an explicit complete finite enumeration. -/
def defaultNodeEnumeration (H : FiniteHiddenDAG S) (node : Fin H.count) :
    List (H.defaultNodeValue node) :=
  (defaultNodePresentation H node).enumeration

theorem defaultNode_complete (H : FiniteHiddenDAG S) (node : Fin H.count) :
    forall value, value ∈ H.defaultNodeEnumeration node :=
  (defaultNodePresentation H node).complete

/-- Equality is inherited from the observed signature or the singleton type. -/
def defaultNodeDecidableEq (H : FiniteHiddenDAG S) (node : Fin H.count) :
    DecidableEq (H.defaultNodeValue node) :=
  (defaultNodePresentation H node).valueDecidableEq

/-- The witness's observed presentation is constructively equivalent to the
original signature, not merely equinumerous or propositionally inhabited. -/
def defaultObservedEquivalence (H : FiniteHiddenDAG S) (index : Fin S.count) :
    ValueEquivalence (H.defaultNodeValue (H.observedNode index)) (S.Value index) := by
  unfold defaultNodeValue defaultNodePresentation
  rw [H.observedIndex_observed index]
  exact ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-- An explicit default value at every node avoids any finite-choice step. -/
def defaultNodeAssignment (H : FiniteHiddenDAG S) (node : Fin H.count) :
    H.defaultNodeValue node :=
  (defaultNodePresentation H node).defaultValue

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
