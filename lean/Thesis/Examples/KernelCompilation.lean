import Thesis.CausalTransport.KernelCompilation
import Thesis.Examples.IdentificationRegression

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentKernelCompilation

open Probability
open FrontDoorIdentification

/-!
# Regression checks for supported current-input chain compilation

These examples exercise the general compiler rather than checking another
isolated ID output value.  The first host has a gap in its topological order;
the second retains a nonempty external intervention; the final signature has
no observed vertices at all.  In each case Lean constructs an inspectable,
formula-aligned certificate and checks its complete support tree.

The front-door graph is reused only as concrete finite graph data.  The
gapped and external-action certificates are valid throughout its positive
model class, not just at the numerical reference assignment used by the older
engine regression.  Using completed soundness *here* checks their denotation;
the compiler itself does not import or depend on the soundness module.
-/

/-! ## A host with a missing topological position -/

/-- Reflexivity supplies the initial observational current expression.
No assumed identification or completeness theorem is used to seed the
current-kernel compiler. -/
noncomputable def observationalInput :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness (observationalJointTerm signature) :=
  PublishedIdentificationCertificate.refl
    (observationalJointTerm signature) (observationalJointTerm_actionFree signature)

/-- The host contains `X` and `Y`, but not the intervening topological
position of the mediator.  Prefix induction must preserve this gap. -/
def gappedHost : NodeSet signature :=
  NodeSet.union (NodeSet.singleton x) (NodeSet.singleton y)

/-- The current expression is a marginal of the full observational joint,
not a kernel node silently substituted by the chain compiler. -/
noncomputable def gappedInput :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨gappedHost, NodeSet.empty, NodeSet.empty⟩) :=
  currentKernelMarginalPublishedCertificate (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    NodeSet.full NodeSet.empty gappedHost
    (NodeSet.disjoint_empty_left _) (fun _ _ => rfl) observationalInput

/-- Construct the whole gapped-host product from two current-input prefix
quotients.  Positive support of the input marginal is supplied directly by
finite summation of positive observational kernel values. -/
noncomputable def gappedChainCompilation :
    PublishedCurrentKernelChainCompilation (GraphModelClass.positive graph)
      graph.dSeparationCorrectness gappedHost NodeSet.empty gappedInput.formula :=
  PublishedCurrentKernelChainCompilation.ofPositive (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    gappedHost NodeSet.empty (NodeSet.disjoint_empty_left _) gappedInput
    (fun model member reference =>
      ProbabilityTerm.marginalizePositiveSupportedValue model
        (NodeSet.diff NodeSet.full gappedHost) (observationalJointTerm signature)
        reference (fun variant => member.2.kernelPositiveSupportedValue
          ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ variant))

/-- Exact target syntax: both factors read the actual current marginal,
including their explicit total-mass and prefix-mass denominators. -/
theorem gappedChainCompilation_formula :
    gappedChainCompilation.certificate.formula =
      chainProductFrom gappedHost
        (.marginalize (NodeSet.diff NodeSet.full gappedHost)
          (observationalJointTerm signature)) gappedHost :=
  gappedChainCompilation.formula_eq

/-- Check the assembled support tree by applying published soundness in
every positive compatible model, not only the regression model's one value. -/
noncomputable def gappedChainCompilation_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨gappedHost, NodeSet.empty, NodeSet.empty⟩)
      gappedChainCompilation.certificate.formula reference :=
  let certificate := gappedChainCompilation.certificate.compile
  DoCalculusDerivation.denotational_soundAt
    (graph.publishedSoundness.primitive model member.1) certificate.derivation
    (certificate.supported model member reference
      (member.2.kernelPositiveSupportedValue
        ⟨gappedHost, NodeSet.empty, NodeSet.empty⟩ reference).toSupported)

/-! ## A nonempty external intervention retained in the source -/

/-- Intervening on the mediator is external to the singleton `X` host.
The graph makes this action removable for `X`; the nonempty action remains
in the chain compiler's source rather than being erased from its interface. -/
def externalActionQuery : JointKernelQuery signature :=
  ⟨NodeSet.singleton x, NodeSet.singleton mediator,
    NodeSet.disjoint_singletons_of_ne (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The incoming-cut path test confirms rule 3's side condition for this
concrete external action.  Ordinary kernel reduction checks the finite graph;
no native evaluator or additional logical axiom is used. -/
theorem externalActionQuery_dSeparated :
    graph.dSeparated (GraphMutilation.bar externalActionQuery.action)
      externalActionQuery.outcome externalActionQuery.action NodeSet.empty = true := by
  decide +kernel

/-- Seed a genuine intervention-bearing input certificate by the proved
rule-3 deletion and observational marginalization, rather than postulating
an arbitrary certified input for this example. -/
noncomputable def externalActionInput :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness externalActionQuery.sourceTerm :=
  (deleteActionIdentifiedPublishedCertificate graph.dSeparationCorrectness
    externalActionQuery
    (graph.dSeparationCorrectness.pathDSeparated_of_dSeparated
      externalActionQuery_dSeparated)).toGeneric

/-- Even the singleton case keeps its explicit current-input denominator.
The source still reads `do(mediator)`, while the displayed quotient is
action-free because it uses the certified observational marginal. -/
noncomputable def externalActionChainCompilation :
    PublishedCurrentKernelChainCompilation (GraphModelClass.positive graph)
      graph.dSeparationCorrectness externalActionQuery.outcome
      externalActionQuery.action externalActionInput.formula :=
  PublishedCurrentKernelChainCompilation.ofPositive (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    externalActionQuery.outcome externalActionQuery.action
    externalActionQuery.action_outcome_disjoint externalActionInput
    (fun model member reference =>
      ProbabilityTerm.marginalizePositiveSupportedValue model
        (NodeSet.diff NodeSet.full externalActionQuery.outcome)
        (observationalJointTerm signature) reference
        (fun variant => member.2.kernelPositiveSupportedValue
          ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ variant))

/-- The compiled nonempty-action source and its exact quotient agree
throughout the positive graph-model class. -/
noncomputable def externalActionChainCompilation_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model externalActionQuery.sourceTerm
      externalActionChainCompilation.certificate.formula reference :=
  let certificate := externalActionChainCompilation.certificate.compile
  DoCalculusDerivation.denotational_soundAt
    (graph.publishedSoundness.primitive model member.1) certificate.derivation
    (certificate.supported model member reference
      (member.2.kernelPositiveSupportedValue
        ⟨externalActionQuery.outcome, externalActionQuery.action, NodeSet.empty⟩
        reference).toSupported)

/-! ## No selected vertex exists in the zero-node signature -/

/-- A genuinely empty observed signature.  Enumerations remain constructive
data, although no observed index can ever request one. -/
def zeroSignature : ObservedSignature where
  count := 0
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ edge; cases edge

/-- The unique empty directed-and-bidirected graph has no edge obligations. -/
def zeroGraph : ObservedGraph zeroSignature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := fun _ => rfl

/-- Compile the *full* host of the zero-node signature.  This checks the
signature-bound entry point itself, not a positive-size host disguised by
an empty component list. -/
noncomputable def zeroHostChainCompilation :
    PublishedCurrentKernelChainCompilation (GraphModelClass.positive zeroGraph)
      zeroGraph.dSeparationCorrectness NodeSet.full NodeSet.empty
      (observationalJointTerm zeroSignature) :=
  PublishedCurrentKernelChainCompilation.ofPositive (C := GraphModelClass.positive zeroGraph)
    zeroGraph.dSeparationCorrectness (fun member => member.2)
    NodeSet.full NodeSet.empty (NodeSet.disjoint_empty_left _)
    (PublishedIdentificationCertificate.refl (observationalJointTerm zeroSignature)
      (observationalJointTerm_actionFree zeroSignature))
    (fun _model member reference => member.2.kernelPositiveSupportedValue
      ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference)

end CurrentKernelCompilation
end Examples
end Causality
end Thesis
