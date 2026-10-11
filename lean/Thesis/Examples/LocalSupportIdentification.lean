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
  unfold ObservationalCylinderPositiveAt
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

/-! ## Recursive guarded certificates in the same nonpositive model -/

/-- Compile the whole observational joint inside the unrestricted compatible
model class.  The positive model class would exclude this regression SCM. -/
noncomputable def guarded_compilation :
    PublishedObservationalGuardedChainCompilation (GraphModelClass.all graph)
      graph.dSeparationCorrectness (NodeSet.full : NodeSet signature) :=
  PublishedObservationalGuardedChainCompilation.ofModelClass
    (GraphModelClass.all graph) graph.dSeparationCorrectness NodeSet.full

/-- The certificate retains exactly the generated guarded syntax; it does
not replace the undefined conditional by an arbitrary observational value. -/
theorem guarded_compilation_formula :
    guarded_compilation.certificate.formula =
      guardedChainTerm (NodeSet.full : NodeSet signature) :=
  guarded_compilation.formula_eq

/-- At the impossible `X = true` reference, the complete joint is supported
but the displayed `P(Y | X)` factor is not.  The ordinary recursive support
tree can nevertheless be constructed because its factor branch is demanded
only under a positive prefix weight. -/
noncomputable def guarded_compilation_supported :
    LocalDerivationSupport model reference
      (guarded_compilation.certificate.derivation.compile graph.dSeparationCorrectness) :=
  guarded_compilation.certificate.supported model compatible reference
    ⟨((Kernel.mk NodeSet.full NodeSet.empty NodeSet.empty).distribution
        model reference).probVal (Kernel.agreesOn NodeSet.full reference),
      Kernel.unconditionalDenote model NodeSet.full NodeSet.empty reference⟩

/-- The existing derivation-soundness theorem interprets the guarded
certificate, rather than bypassing that theorem with a bespoke equality. -/
noncomputable def guarded_compilation_sound :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩)
      guarded_compilation.certificate.formula reference :=
  (guarded_compilation.certificate.derivation.compile
    graph.dSeparationCorrectness).denotational_soundAt
      (graph.publishedSoundness.primitive model compatible)
      guarded_compilation_supported

/-! ## Observable overlap does not demand a positive outcome -/

/-- `Y = true` has observational mass although the selected full reference
also asks for the impossible outcome `X = true`. -/
theorem zero_outcome_action_overlap :
    ObservationalCylinderPositiveAt model (NodeSet.singleton y) reference := by
  unfold ObservationalCylinderPositiveAt
  decide +kernel

/-- The causal kernel at that action is supported even with a zero outcome
numerator.  Its support comes from observable overlap and SCM consistency,
not from observational positivity or a graph-dependent do-rule. -/
noncomputable def zero_outcome_effect_supported :
    (ProbabilityTerm.kernel
      ⟨NodeSet.singleton x, NodeSet.singleton y, NodeSet.empty⟩).SupportedAt
      model reference :=
  Kernel.supportedAt_of_observational_overlap model
    ⟨NodeSet.singleton x, NodeSet.singleton y, NodeSet.empty⟩ reference
    (by simpa only [NodeSet.union_empty_right] using zero_outcome_action_overlap)

/-- A nonempty conditioner is checked with its actual action-and-condition
cylinder, rather than silently dropping the conditioner from the overlap. -/
theorem action_condition_cylinder_positive :
    ObservationalCylinderPositiveAt model
      (NodeSet.union (NodeSet.singleton x) (NodeSet.singleton y))
      supportedReference := by
  unfold ObservationalCylinderPositiveAt
  decide +kernel

/-- The actual intervened conditional is supported from the verified joint
overlap above.  This claims support, not identification of an arbitrary query. -/
noncomputable def nonempty_condition_effect_supported :
    (ProbabilityTerm.kernel
      ⟨NodeSet.empty, NodeSet.singleton x, NodeSet.singleton y⟩).SupportedAt
      model supportedReference :=
  Kernel.supportedAt_of_observational_overlap model
    ⟨NodeSet.empty, NodeSet.singleton x, NodeSet.singleton y⟩ supportedReference
    action_condition_cylinder_positive

end ZeroCellLocalIdentification
end Examples
end Causality
end Thesis
