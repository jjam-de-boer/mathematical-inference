import Thesis.Causality.HardIntervention

/-!
# Finite causal coarse-graining candidates

The assignment map (often written τ) merges observed variables through
explicit nonempty disjoint clusters. A chosen micro intervention represents
an admitted macro intervention. Its forced assignments must map to the
forced macro values. This compatibility is a property of the supplied maps;
it does not assert interventional consistency of the two SCMs.

`PreservesEvent` and `PreservesAt` state the separate distributional obligation
using actual finite pushforwards. The examples prove one AND-merge instance
and refute an OR-merge instance with an observationally correct macro CPT.
Symmetry of mechanisms can propose an assignment map but cannot select the
intervention representative or prove this obligation by itself.

Investigation boundary: a general exact-transformation theory would specify
allowed intervention families and a surjective order-preserving map ω from
micro interventions to macro interventions, and prove the pushforward law
for every allowed micro intervention (hence independence from representatives).
The supplied representative here is only one selected member of a macro
intervention's proposed fibre; it is not such an ω or a general abstraction
algorithm. Uniform/strong abstraction requires further conditions.
References: Rubenstein et al., Causal Consistency of Structural Equation
Models (UAI 2017), https://arxiv.org/abs/1707.00819; Beckers and Halpern,
Abstracting Causal Models (AAAI 2019), https://arxiv.org/abs/1812.03789.

Open questions: mechanism conditions supporting broader observed-node
merges, agreement for all representatives, emergent coarse-only variables,
and a real length scale L. This module supplies neither an RG decision
procedure nor those existence results. Gibbs fibre grouping coarsens states;
latent-root grouping coarsens hidden sources; terminal conservative learning
adds an observed child. None is substituted for observed-node causal zoom.
Unary/absorbed signatures need separate value-richness checks: published ID
completeness must not be applied to them without its original hypotheses.
-/

namespace Thesis.Causality
open Probability

/-- An assignment obeys every value explicitly forced by a hard intervention.
No observational conditional is completed at an unsupported assignment. -/
def HardIntervention.RealizedBy (action : HardIntervention S) (assignment : S.Assignment) : Prop :=
  ∀ node value, action.value node = some value → assignment node = value

/-- Finite observed-node coarse-graining data and a declared intervention
representative on an explicit domain. The two SCMs remain independent data;
interventional agreement is deliberately a separate property. Nonempty
clusters exclude introducing a new coarse variable from an empty block. -/
structure FiniteCausalCoarseGraining (micro coarse : ObservedSignature) where
  microModel : ExactModel micro
  macroModel : ExactModel coarse
  cluster : Fin coarse.count → NodeSet micro
  cluster_nonempty : ∀ node, ∃ member, cluster node member = true
  cluster_disjoint : ∀ first second, first ≠ second → NodeSet.Disjoint (cluster first) (cluster second)
  assignmentMap : micro.Assignment → coarse.Assignment
  coordinate_local : ∀ node first second,
    (∀ member, cluster node member = true → first member = second member) →
      assignmentMap first node = assignmentMap second node
  admissible : HardIntervention coarse → Prop
  representative : ∀ action, admissible action → HardIntervention micro
  representative_respects : ∀ action admitted assignment,
    (representative action admitted).RealizedBy assignment → action.RealizedBy (assignmentMap assignment)

namespace FiniteCausalCoarseGraining

/-- Pull back a coarse node set to the union of its disjoint micro clusters.
The assignment map may aggregate each cluster's values nonlinearly. -/
def microNodes (coarsening : FiniteCausalCoarseGraining micro coarse) (nodes : NodeSet coarse) : NodeSet micro :=
  fun member => finAny coarse.count (fun node => nodes node && coarsening.cluster node member)

/-- Push forward the actual micro interventional record, keeping its total
mass and null outcomes. This is not a conditional-probability completion. -/
def pushedInterventionalLaw (coarsening : FiniteCausalCoarseGraining micro coarse)
    (action : HardIntervention coarse) (admitted : coarsening.admissible action) : FiniteProbRecord coarse.Assignment :=
  (coarsening.microModel.interventionalDist (coarsening.representative action admitted).value).map coarsening.assignmentMap

def PreservesEvent (coarsening : FiniteCausalCoarseGraining micro coarse)
    (action : HardIntervention coarse) (admitted : coarsening.admissible action)
    (event : Event coarse.Assignment) : Prop :=
  QProb.Equiv (coarsening.macroModel.interventionalValue action.value event)
    ((coarsening.pushedInterventionalLaw action admitted).probVal event)

/-- Full finite-law consistency at this one declared intervention. The
bounded examples do not assert this for every possible hard intervention. -/
def PreservesAt (coarsening : FiniteCausalCoarseGraining micro coarse)
    (action : HardIntervention coarse) (admitted : coarsening.admissible action) : Prop :=
  ∀ event, coarsening.PreservesEvent action admitted event

theorem pushedInterventionalLaw_probVal (coarsening : FiniteCausalCoarseGraining micro coarse)
    (action : HardIntervention coarse) (admitted : coarsening.admissible action) (event : Event coarse.Assignment) :
    QProb.Equiv ((coarsening.pushedInterventionalLaw action admitted).probVal event)
      (coarsening.microModel.interventionalValue (coarsening.representative action admitted).value
        (fun assignment => event (coarsening.assignmentMap assignment))) :=
  FiniteProbRecord.map_probVal _ _ _

end FiniteCausalCoarseGraining
end Thesis.Causality
