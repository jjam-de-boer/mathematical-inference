import Thesis.Causality.HardIntervention

/-!
# Finite causal coarse-graining candidates

The assignment map (often written τ) merges observed variables through
explicit nonempty disjoint clusters. A chosen micro intervention represents
an admitted macro intervention. Its forced assignments must map to the
forced macro values. This compatibility is a property of the supplied maps;
it does not assert interventional consistency of the two SCMs.

`PreservesEvent` and `PreservesAt` separate distributional obligations
from cluster compatibility. `CausalInterventionMap` adds a partial ω and
full-law exactness for every defined micro surgery; exact maps compose when
the middle SCM agrees. A section transfers exactness to `PreservesAt`.
The AND/copy examples construct the merge from explicit interchangeable
mechanism data and prove full-law consistency for its entire unique-forced-
preimage class. The observationally matched OR macro remains a counterexample.

A partial map and a section do not alone establish a globally surjective,
order-preserving exact transformation. Domain, mechanism and equality-of-law
proofs remain obligations for each construction. Emergent coordinates have
a separate constructor: ordinary merged blocks remain nonempty and disjoint.
References: Rubenstein et al., Causal Consistency of Structural Equation
Models (UAI 2017), https://arxiv.org/abs/1707.00819; Beckers and Halpern,
Abstracting Causal Models (AAAI 2019), https://arxiv.org/abs/1812.03789.

Broader mechanism classes, uniform/strong abstraction and a real length
scale L remain open. This is not an RG decision procedure. Gibbs fibre
grouping coarsens states; latent-root grouping coarsens hidden sources;
terminal conservative learning adds an observed child. None is substituted
for observed-node causal zoom. Unary/absorbed signatures need separate value-
richness checks: published ID completeness must not be applied to them
without its original hypotheses.
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

/-- A partial intervention map ω. `none` excludes a micro surgery from the
allowed family. Forced-value compatibility is separate from equality of laws.
No surjectivity or order property is asserted without a further proof. -/
structure CausalInterventionMap (micro coarse : ObservedSignature) where
  microModel : ExactModel micro
  macroModel : ExactModel coarse
  assignmentMap : micro.Assignment → coarse.Assignment
  omega : HardIntervention micro → Option (HardIntervention coarse)
  respects : ∀ intervention action, omega intervention = some action →
    ∀ assignment, intervention.RealizedBy assignment →
      action.RealizedBy (assignmentMap assignment)

namespace CausalInterventionMap

/-- Equality of the entire finite interventional law for every defined ω.
This concerns every allowed micro intervention, not only a chosen section. -/
def Exact (mapping : CausalInterventionMap micro coarse) : Prop :=
  ∀ intervention action, mapping.omega intervention = some action →
    ∀ event, QProb.Equiv
      (mapping.macroModel.interventionalValue action.value event)
      (mapping.microModel.interventionalValue intervention.value
        (fun assignment => event (mapping.assignmentMap assignment)))

/-- A supplied representative is a section on its declared macro domain. -/
def IsSection (mapping : CausalInterventionMap micro coarse)
    (admissible : HardIntervention coarse → Prop)
    (representative : ∀ action, admissible action → HardIntervention micro) : Prop :=
  ∀ action admitted, mapping.omega (representative action admitted) = some action

/-- Composition is defined only when both successive intervention maps are
 defined. The shared middle SCM is an explicit equality requirement. -/
def comp (first : CausalInterventionMap fine middle)
    (second : CausalInterventionMap middle coarse)
    (_shared : first.macroModel = second.microModel) : CausalInterventionMap fine coarse where
  microModel := first.microModel
  macroModel := second.macroModel
  assignmentMap := fun assignment => second.assignmentMap (first.assignmentMap assignment)
  omega intervention := (first.omega intervention).bind second.omega
  respects := by
    intro intervention action defined assignment realizes
    cases firstDefined : first.omega intervention with
    | none => simp [firstDefined] at defined
    | some middleAction =>
      have secondDefined : second.omega middleAction = some action := by
        simpa [firstDefined] using defined
      exact second.respects middleAction action secondDefined _
        (first.respects intervention middleAction firstDefined assignment realizes)

theorem comp_exact (first : CausalInterventionMap fine middle)
    (second : CausalInterventionMap middle coarse)
    (shared : first.macroModel = second.microModel)
    (firstExact : first.Exact) (secondExact : second.Exact) :
    (first.comp second shared).Exact := by
  intro intervention action defined event
  change (first.omega intervention).bind second.omega = some action at defined
  cases firstDefined : first.omega intervention with
  | none => simp [firstDefined] at defined
  | some middleAction =>
    have secondDefined : second.omega middleAction = some action := by
      simpa [firstDefined] using defined
    have upper := secondExact middleAction action secondDefined event
    have lower := firstExact intervention middleAction firstDefined
      (fun assignment => event (second.assignmentMap assignment))
    rw [shared] at lower
    exact QProb.equiv_trans upper lower

end CausalInterventionMap

/-- A section of an exact ω supplies the earlier full-law `PreservesAt`.
The model and state maps must be the same, not merely observationally matched. -/
theorem FiniteCausalCoarseGraining.preservesAt_of_section
    (coarsening : FiniteCausalCoarseGraining micro coarse)
    (mapping : CausalInterventionMap micro coarse)
    (microEqual : mapping.microModel = coarsening.microModel)
    (macroEqual : mapping.macroModel = coarsening.macroModel)
    (mapEqual : mapping.assignmentMap = coarsening.assignmentMap)
    (isSection : mapping.IsSection coarsening.admissible coarsening.representative)
    (exactness : mapping.Exact) (action) (admitted : coarsening.admissible action) :
    coarsening.PreservesAt action admitted := by
  intro event
  have agreement := exactness _ action (isSection action admitted) event
  rw [microEqual, macroEqual, mapEqual] at agreement
  exact QProb.equiv_trans agreement
    (QProb.equiv_symm (coarsening.pushedInterventionalLaw_probVal action admitted event))

/-- Separate data for a genuinely coarse-only coordinate. `none` is an
emergent coordinate, not an empty merged cluster. Ordinary merged coordinates
still have nonempty disjoint blocks and local state maps. Interventions on
emergent coordinates need their own semantics; they need not have a micro do. -/
structure EmergentCausalCoarseGraining (micro coarse : ObservedSignature) where
  microModel : ExactModel micro
  macroModel : ExactModel coarse
  origin : Fin coarse.count → Option (NodeSet micro)
  has_emergent : ∃ node, origin node = none
  merged_nonempty : ∀ node members, origin node = some members → ∃ member, members member = true
  merged_disjoint : ∀ first second left right, first ≠ second →
    origin first = some left → origin second = some right → NodeSet.Disjoint left right
  assignmentMap : micro.Assignment → coarse.Assignment
  merged_local : ∀ node members, origin node = some members → ∀ first second,
    (∀ member, members member = true → first member = second member) →
      assignmentMap first node = assignmentMap second node

/-- The two constructors keep emergence distinct from merging nonempty blocks. -/
inductive FiniteCausalZoom (micro coarse : ObservedSignature) where
  | merge : FiniteCausalCoarseGraining micro coarse → FiniteCausalZoom micro coarse
  | emergent : EmergentCausalCoarseGraining micro coarse → FiniteCausalZoom micro coarse

end Thesis.Causality
