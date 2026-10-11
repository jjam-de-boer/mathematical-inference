import Thesis.CausalTransport.LocalSupportIdentification
import Thesis.Examples.SupportAwareChain

namespace Thesis
namespace Causality
namespace Examples
namespace ZeroCellLocalIdentification

open Probability ZeroCellChain

/-!
# Locally supported identification in a genuinely nonpositive SCM

Reuse the zero-containing SCM `X = false`, `Y = independent unbiased bit`.
The query is `P(Y | do(X))`.  The observational action cylinder `X = false`
has positive mass, although half of the complete observational assignments
have zero mass.  Rule 2 therefore identifies this supported action cell
without an `ObservationallyPositive` assumption.

The unsupported action value `X = true` is deliberately not passed through
this sufficient overlap theorem.  Its identifiability in this particular
edgeless graph can be established by a different do-rule; the local-overlap
condition here is not advertised as necessary for all graphs or queries.
-/

/-- Use the SCM's actual projected graph, with no assumed graph equality. -/
def graph : ObservedGraph signature := model.observedGraph

def query : JointKernelQuery signature :=
  ⟨NodeSet.singleton y, NodeSet.singleton x,
    NodeSet.disjoint_singletons_of_ne (by decide)⟩

/-- The only root is private, so the model is compatible with its own graph.
Finite root/vertex decisions are checked by the kernel, not by native code. -/
theorem compatible : Compatible model graph := by
  constructor
  · change latent.CanonicalSemiMarkovian
    unfold LatentExtension.CanonicalSemiMarkovian latent
    decide +kernel
  · intro _ _
    rfl

/-- Cutting outgoing arrows from the action leaves no route to the outcome.
The graph side condition is checked rather than supplied as an interface. -/
theorem rule2_separated : graph.dSeparated
    (.barUnderline NodeSet.empty query.action)
    query.outcome query.action NodeSet.empty = true := by
  decide +kernel

/-- Select the supported action value `X = false` and outcome `Y = true`. -/
def supportedReference : signature.Assignment :=
  fun node => decide (node.val = 1)

theorem action_cylinder_positive :
    ObservationalCylinderPositiveAt model query.action supportedReference := by
  decide +kernel

/-- The local theorem is not being applied to an implicitly positive model:
the complete `X = true, Y = true` cell has zero observational mass. -/
theorem model_not_observationally_positive : ¬ ObservationallyPositive model := by
  intro positive
  have impossible := positive reference
  have zero : (model.observationalDist.probVal
      (FiniteProbRecord.singletonEvent reference)).num = 0 := by
    decide +kernel
  rw [zero] at impossible
  exact Nat.not_lt_zero _ impossible

/-- Identify the supported action cell by the graph-derived causal rule,
using only the verified cylinder positivity above. -/
noncomputable def effect_at_supported_action :
    ProbabilityTerm.EquivalentAt model query.sourceTerm
      query.observationalActionConditional supportedReference :=
  JointKernelQuery.unconfounded_soundAt graph query rule2_separated
    model compatible supportedReference action_cylinder_positive

/-- Every observationally equal compatible model has the same effect at
this supported action cell.  Its own overlap is transported from the
observational law, not requested as another assumption. -/
noncomputable def effect_in_any_observationally_equal_model
    (other : ExactModel signature) (otherCompatible : Compatible other graph)
    (observational : ObservationallyEquivalent model other) :
    ProbabilityResult.Equivalent (query.sourceTerm.denote model supportedReference)
      (query.sourceTerm.denote other supportedReference) :=
  JointKernelQuery.unconfounded_identifiableAt graph query rule2_separated
    model other compatible otherCompatible observational supportedReference
    action_cylinder_positive

end ZeroCellLocalIdentification
end Examples
end Causality
end Thesis
