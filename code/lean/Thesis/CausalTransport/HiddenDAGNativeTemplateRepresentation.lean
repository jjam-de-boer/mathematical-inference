import Thesis.CausalTransport.HiddenDAGNativeTemplateCoverage

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Finite structural-template coverage of the full fixed-DAG family

Every original native model is first compressed and presented on bounded
source/hidden alphabets. Its bounded equations and full observed conversions
are then encoded as a member of the *same finite template catalogue*, fixed
only by the graph, public signature and target count. Explicit mapped rational
factor records instantiate that standalone entry. Native-law simulation and
the earlier compression theorems prove all factual events and retained targets
agree with the original model. No semantic correspondence is requested from
the caller, and the instantiated constructor does not receive a base model.

This is finite coverage of structural templates with rational source-law
parameters. It does not make those parameters finite, decide their exact
feasibility, establish sharpness of supplied bounds, or cover varying hidden
topologies. Conditional applications must retain both joint and evidence
queries and keep the original positive causal conditioner explicit.
-/

namespace FiniteHiddenDAGSCM

namespace BoundedRepresentation

variable {original : FiniteHiddenDAGSCM S P} {targets : List (NativeProbabilityQuery S)}

def standaloneTemplate (represented : BoundedRepresentation original targets) : P.hiddenDAG.CodeNativeTemplate :=
  represented.model.nativeTemplate represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence

def standaloneFactors (represented : BoundedRepresentation original targets) (node : Fin P.hiddenDAG.count) :
    FiniteProbRecord (Fin (represented.standaloneTemplate.entry.shape.sourceCard node)) :=
  represented.model.nativeTemplateFactors represented.sourceCard represented.sourceCodeEquivalence node

theorem standaloneTemplate_mem (represented : BoundedRepresentation original targets) :
    represented.standaloneTemplate ∈ P.hiddenDAG.nativeTemplateCatalogue
      (representationNodeBound P targets.length) (representationSourceBound S targets.length) :=
  represented.model.nativeTemplate_mem represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence _ _
    represented.nodeCard_bounded_uniformly represented.source_bounded

theorem standaloneTemplate_observational (represented : BoundedRepresentation original targets) (event : Event S.Assignment) :
    QProb.Equiv ((represented.standaloneTemplate.model (P := P) represented.standaloneFactors).observationalValue event)
      (original.observationalValue event) :=
  QProb.equiv_trans (represented.model.nativeTemplateModel_observationalValue represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence event) (represented.observational event)

theorem standaloneTemplate_preserved (represented : BoundedRepresentation original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    QProb.Equiv ((represented.standaloneTemplate.model (P := P) represented.standaloneFactors).interventionalValue query.intervention query.event)
      (original.interventionalValue query.intervention query.event) :=
  QProb.equiv_trans (represented.model.nativeTemplateModel_interventionalValue represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence query.intervention query.event) (represented.preserved query listed)

end BoundedRepresentation

/-- A constructed entry and rational source law in a fixed finite structural
catalogue, with actual native probability preservation. All fields are proved
by `nativeTemplateRepresentation`, not postulated as an external interface. -/
structure NativeTemplateRepresentation (original : FiniteHiddenDAGSCM S P) (targets : List (NativeProbabilityQuery S)) where
  template : P.hiddenDAG.CodeNativeTemplate
  listed : template ∈ P.hiddenDAG.nativeTemplateCatalogue
    (representationNodeBound P targets.length) (representationSourceBound S targets.length)
  factors : (node : Fin P.hiddenDAG.count) → FiniteProbRecord (Fin (template.entry.shape.sourceCard node))
  observational : ∀ event, QProb.Equiv ((template.model (P := P) factors).observationalValue event) (original.observationalValue event)
  preserved : ∀ query, query ∈ targets →
    QProb.Equiv ((template.model (P := P) factors).interventionalValue query.intervention query.event)
      (original.interventionalValue query.intervention query.event)

/-- Constructive coverage of every finite native model on this fixed full
hidden DAG, with no bound on its original hidden/source alphabets or rational
denominators. The finite structural list is independent of the input model. -/
def nativeTemplateRepresentation (original : FiniteHiddenDAGSCM S P) (targets : List (NativeProbabilityQuery S)) :
    NativeTemplateRepresentation original targets :=
  let represented := original.boundedRepresentation targets
  { template := represented.standaloneTemplate
    listed := represented.standaloneTemplate_mem
    factors := represented.standaloneFactors
    observational := represented.standaloneTemplate_observational
    preserved := represented.standaloneTemplate_preserved }

namespace NativeTemplateRepresentation

variable {original : FiniteHiddenDAGSCM S P} {targets : List (NativeProbabilityQuery S)}

def model (represented : NativeTemplateRepresentation original targets) : FiniteHiddenDAGSCM S P :=
  represented.template.model (P := P) represented.factors

theorem query_eventPositive_iff (represented : NativeTemplateRepresentation original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    (represented.model.interventionalDist query.intervention).EventPositive query.event ↔
      (original.interventionalDist query.intervention).EventPositive query.event :=
  QProb.equiv_num_pos_iff (represented.preserved query listed)

/-- Retaining the joint event and evidence suffices. Null target evidence
is not completed by the source parameters or by the finite template list. -/
theorem conditionOn_probVal (represented : NativeTemplateRepresentation original targets)
    (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (jointListed : (⟨intervention, fun value => evidence value && event value⟩ : NativeProbabilityQuery S) ∈ targets)
    (evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery S) ∈ targets)
    (supported : (original.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      (((represented.model.interventionalDist intervention).conditionOn evidence
        ((represented.query_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((original.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  let supportedNew := (represented.query_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported
  exact QProb.equiv_trans ((represented.model.interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans (QProb.div_congr (represented.preserved _ jointListed) (represented.preserved _ evidenceListed) supportedNew supported)
      (QProb.equiv_symm ((original.interventionalDist intervention).conditionOn_probVal evidence event supported)))

end NativeTemplateRepresentation
end FiniteHiddenDAGSCM
end Thesis.Causality
