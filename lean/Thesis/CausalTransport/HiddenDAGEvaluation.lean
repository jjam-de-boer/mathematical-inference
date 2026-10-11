import Thesis.CausalTransport.HiddenDAGRelayEquations

namespace Thesis
namespace Causality

/-!
# Unitwise preservation of the reverse hidden-DAG realization

For any compatible canonical projected model, any original root assignment,
and any partial hard observed intervention, encode the roots at their actual
allocated original-DAG sources.  The constructed full-DAG SCM then produces
exactly the original model's observed assignment under that same intervention.

The proof supplies an explicit solution of the full intervened equations.
Hidden equations hold by the relay coordinate laws.  At an observed node a
forced value is retained literally; an unforced value obeys the original
equation on the already intervened parent signals.  Finite acyclic uniqueness
then identifies this solution with the actual full-DAG evaluator.

This is a unitwise theorem, including original zero-weight units.  No
positivity or observed value-richness assumption is needed.  Equality of the
complete probability laws remains a separate task: the grouped private-noise
prior must be related to the original root prior for arbitrary joint events,
not just by its channel marginals.
-/

namespace FiniteLatentSCM

open HiddenDAGRelay

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- The explicit relay assignment, using the original model's *intervened*
observed signals, satisfies every constructed full-DAG structural equation.
An observed intervention replaces that equation rather than propagating a
factual reevaluation of the original source through its hidden descendants. -/
theorem toHiddenDAGSCM_expectedValue_solution (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (intervention : HardIntervention S)
    (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count) :
    expectedValue model compatible (model.evalUnder intervention.value roots) roots node =
      match (model.toHiddenDAGSCM compatible).interventionValueAt intervention node with
      | some value => value
      | none => (model.toHiddenDAGSCM compatible).mechanism node
          (fun parent _edge =>
            expectedValue model compatible (model.evalUnder intervention.value roots) roots parent)
          (HiddenDAGPlacedNoise.encode model compatible roots node) := by
  cases found : P.hiddenDAG.observedIndex node with
  | none =>
      rw [(model.toHiddenDAGSCM compatible).interventionValueAt_eq_none intervention node found]
      exact (mechanism_expectedValue_hidden model compatible
        (model.evalUnder intervention.value roots) roots node found).symm
  | some index =>
      have embedding := P.hiddenDAG.observedIndex_sound node index found
      cases embedding
      rw [(model.toHiddenDAGSCM compatible).interventionValueAt_observed_eq_map intervention index,
        expectedValue_observed]
      cases selected : intervention.value index with
      | some value =>
          change (observedEquivalence model P index).backward
            (model.evalNodeUnder intervention.value roots index) =
              (observedEquivalence model P index).backward value
          apply congrArg (observedEquivalence model P index).backward
          rw [evalNodeUnder, equationUnder, selected]
      | none =>
          change (observedEquivalence model P index).backward
            (model.evalNodeUnder intervention.value roots index) =
              HiddenDAGRelay.mechanism model compatible (P.hiddenDAG.observedNode index)
                (fun parent _edge =>
                  expectedValue model compatible (model.evalUnder intervention.value roots) roots parent)
                (HiddenDAGPlacedNoise.encode model compatible roots (P.hiddenDAG.observedNode index))
          rw [mechanism_expectedValue_observed]
          apply congrArg (observedEquivalence model P index).backward
          rw [evalNodeUnder, equationUnder, selected]
          rfl

/-- Every full-DAG node, including its hidden payload coordinates, agrees
with the explicit intervened relay solution at the encoded original unit.
This follows from actual local equations and the graph's strict rank; no
semantic preservation predicate is assumed. -/
theorem toHiddenDAGSCM_evalNode (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (intervention : HardIntervention S)
    (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count) :
    (model.toHiddenDAGSCM compatible).evalNode intervention
      (HiddenDAGPlacedNoise.encode model compatible roots) node =
      expectedValue model compatible (model.evalUnder intervention.value roots) roots node := by
  refine (model.toHiddenDAGSCM compatible).evalNode_eq_of_solution intervention
    (HiddenDAGPlacedNoise.encode model compatible roots)
    (expectedValue model compatible (model.evalUnder intervention.value roots) roots)
    ?_ node
  intro actualNode
  have solution :=
    model.toHiddenDAGSCM_expectedValue_solution compatible intervention roots actualNode
  -- The two elaborated matches use equivalent presentations of the same
  -- node type.  Splitting their actual computed option removes those motives
  -- before comparing the local equations; no semantic hypothesis is added.
  cases forced : (model.toHiddenDAGSCM compatible).interventionValueAt intervention actualNode with
  | none => simpa only [forced] using solution
  | some value => simpa only [forced] using solution

/-- Complete observed assignments agree pointwise under every partial hard
intervention and every original root assignment.  Observed domains are kept
fixed, while hidden and private-noise domains may have arbitrary finite sizes.
This is the unitwise reverse-realization theorem, not yet its probability law. -/
theorem toHiddenDAGSCM_evalObserved (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (intervention : HardIntervention S)
    (roots : model.latent.Assignment) :
    (model.toHiddenDAGSCM compatible).evalObserved intervention
      (HiddenDAGPlacedNoise.encode model compatible roots) =
      model.evalUnder intervention.value roots := by
  funext index
  unfold FiniteHiddenDAGSCM.evalObserved
  rw [model.toHiddenDAGSCM_evalNode compatible intervention roots,
    expectedValue_observed]
  exact (observedEquivalence model P index).forward_backward _

end FiniteLatentSCM
end Causality
end Thesis
