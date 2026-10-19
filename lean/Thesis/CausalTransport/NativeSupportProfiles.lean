import Thesis.CausalTransport.NativeTemplateSupport
import Thesis.CausalTransport.ProjectionTemplateRepresentation
import Thesis.Causality.NodeSetEnumeration

namespace Thesis.Causality

open Probability

/-!
# Complete finite support profiles of the original native causal model class

The public observed signature has finitely many reference assignments and
intervention masks. Retain every observed singleton event under each of these
interventions in the existing constructive representation theorem. Singleton
extensionality then gives every interventional event probability, including
all conditioners used by any current nonnegative expression or derivation.

For each listed structural template, retain one actual rational model per
nonempty independent source-support mask. Source reweighting preserves every
interventional support event but intentionally forgets numerical values. This
gives a finite catalogue covering the complete support behaviour of every
original native model, with no original alphabet or denominator restriction.

The fixed-full-DAG and fixed-observed-projection statements are separate.
Projection-wide coverage retains the earlier multi-child clique-root model
class; it does not replace shared roots by independent pair roots. Neither
coverage theorem searches proof codes, certifies an arbitrary formula, fits
a supplied numerical law, or supplies an unrestricted rational optimizer.
-/

variable {S : ObservedSignature.{0}}

namespace NativeSupportProfiles

def intervention (action : NodeSet S) (reference : S.Assignment) : HardIntervention S :=
  ⟨(Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference⟩

theorem intervention_referenceFor (original : HardIntervention S) :
    intervention original.targets (original.referenceFor S.defaultValue) = original := by
  apply HardIntervention.extensional
  intro node
  exact congrFun (original.intervention_referenceFor NodeSet.empty NodeSet.empty S.defaultValue) node

/-- A finite basis of unconditional probabilities. Values at null actions
remain included because references enumerate the whole declared domain. -/
def queries (signature : ObservedSignature.{0}) : List (NativeProbabilityQuery signature) :=
  (NodeSet.subsets NodeSet.full).flatMap (fun action =>
    signature.assignmentEnumeration.flatMap (fun reference =>
      signature.assignmentEnumeration.map (fun value =>
        ⟨intervention action reference, FiniteProbRecord.singletonEvent value⟩)))

theorem singleton_query_mem (original : HardIntervention S) (value : S.Assignment) :
    (⟨original, FiniteProbRecord.singletonEvent value⟩ : NativeProbabilityQuery S) ∈ queries S := by
  have maskListed : original.targets ∈ NodeSet.subsets NodeSet.full :=
    (NodeSet.subsets_member_iff NodeSet.full original.targets).mpr (fun _ _ => rfl)
  have member :
      (⟨intervention original.targets (original.referenceFor S.defaultValue), FiniteProbRecord.singletonEvent value⟩ : NativeProbabilityQuery S) ∈ queries S := by
    unfold queries
    apply List.mem_flatMap_of_mem maskListed
    apply List.mem_flatMap_of_mem (S.assignmentEnumeration_complete (original.referenceFor S.defaultValue))
    exact List.mem_map_of_mem (f := fun reference : S.Assignment =>
      (⟨intervention original.targets (original.referenceFor S.defaultValue), FiniteProbRecord.singletonEvent reference⟩ : NativeProbabilityQuery S))
      (S.assignmentEnumeration_complete value)
  rw [intervention_referenceFor original] at member
  exact member

/-- Preserving this finite basis implies support agreement for all events
under all hard interventions, not just for a caller's selected query list. -/
theorem agreement_of_basis {P Q : FiniteLatentProjection S}
    (left : FiniteHiddenDAGSCM S P) (right : FiniteHiddenDAGSCM S Q)
    (preserved : ∀ query, query ∈ queries S →
      QProb.Equiv (left.interventionalValue query.intervention query.event) (right.interventionalValue query.intervention query.event)) :
    CausalSupportAgreement left right := by
  intro current event
  have whole : QProb.Equiv (left.interventionalValue current event) (right.interventionalValue current event) := by
    apply FiniteProbRecord.probVal_extensional_of_singletons _ _ S.assignmentEnumeration
      S.assignmentEnumeration_nodup S.assignmentEnumeration_complete (fun reference => ?_) event
    exact preserved ⟨current, FiniteProbRecord.singletonEvent reference⟩ (singleton_query_mem current reference)
  exact QProb.equiv_num_pos_iff whole

end NativeSupportProfiles

namespace FiniteLatentProjection

/-- The structural bounds are derived once from the finite intervention
basis and public signature; they do not restrict the input model class. -/
def completeSupportCatalogue (projection : FiniteLatentProjection S) : List (NativeTemplateInstance projection) :=
  projection.supportCatalogue
    (FiniteHiddenDAGSCM.representationNodeBound projection (NativeSupportProfiles.queries S).length)
    (FiniteHiddenDAGSCM.representationSourceBound S (NativeSupportProfiles.queries S).length)

end FiniteLatentProjection

namespace FiniteHiddenDAGSCM

variable {P : FiniteLatentProjection S}

/-- Construct the actual listed profile representative; no preservation or
coverage witness is requested from the caller. Its new probability values
need not equal the original ones. -/
def supportProfileRepresentative (original : FiniteHiddenDAGSCM S P) : NativeTemplateInstance P :=
  let represented := original.nativeTemplateRepresentation (NativeSupportProfiles.queries S)
  (⟨represented.template, represented.factors⟩ : NativeTemplateInstance P).uniformSupport

theorem supportProfileRepresentative_mem (original : FiniteHiddenDAGSCM S P) :
    original.supportProfileRepresentative ∈ P.completeSupportCatalogue := by
  let represented := original.nativeTemplateRepresentation (NativeSupportProfiles.queries S)
  exact P.uniformSupport_mem_supportCatalogue _ _ ⟨represented.template, represented.factors⟩ represented.listed

theorem supportProfileRepresentative_agreement (original : FiniteHiddenDAGSCM S P) :
    CausalSupportAgreement original.supportProfileRepresentative.model original := by
  let represented := original.nativeTemplateRepresentation (NativeSupportProfiles.queries S)
  exact (NativeTemplateInstance.uniformSupport_agreement (⟨represented.template, represented.factors⟩ : NativeTemplateInstance P)).trans
    (NativeSupportProfiles.agreement_of_basis represented.model original represented.preserved)

theorem supportProfileRepresentative_term_status (original : FiniteHiddenDAGSCM S P) (term : ProbabilityTerm S) (reference : S.Assignment) :
    ProbabilityResult.status (original.supportProfileRepresentative.model.termDenote term reference) =
      ProbabilityResult.status (original.termDenote term reference) :=
  original.supportProfileRepresentative_agreement.term_status term reference

/-- The catalogue covers every finite original native model on this full
DAG, not only records already using the template code alphabets. -/
theorem completeSupportCatalogue_covers (original : FiniteHiddenDAGSCM S P) :
    ∃ entry, entry ∈ P.completeSupportCatalogue ∧ CausalSupportAgreement entry.model original :=
  ⟨original.supportProfileRepresentative, original.supportProfileRepresentative_mem, original.supportProfileRepresentative_agreement⟩

end FiniteHiddenDAGSCM

namespace ProjectedHiddenDAGModel

variable {graph : ObservedGraph S}

/-- Across every original full hidden DAG with this observed projection,
the representative lives on the single fixed clique-root graph. -/
def supportProfileRepresentative (original : ProjectedHiddenDAGModel graph) : NativeTemplateInstance graph.cliqueRootProjection :=
  let represented := original.projectionTemplateRepresentation (NativeSupportProfiles.queries S)
  (⟨represented.template, represented.factors⟩ : NativeTemplateInstance graph.cliqueRootProjection).uniformSupport

theorem supportProfileRepresentative_mem (original : ProjectedHiddenDAGModel graph) :
    original.supportProfileRepresentative ∈ graph.cliqueRootProjection.completeSupportCatalogue := by
  let represented := original.projectionTemplateRepresentation (NativeSupportProfiles.queries S)
  exact graph.cliqueRootProjection.uniformSupport_mem_supportCatalogue _ _ ⟨represented.template, represented.factors⟩ represented.listed

theorem supportProfileRepresentative_agreement (original : ProjectedHiddenDAGModel graph) :
    CausalSupportAgreement original.supportProfileRepresentative.model original.model := by
  let represented := original.projectionTemplateRepresentation (NativeSupportProfiles.queries S)
  exact (NativeTemplateInstance.uniformSupport_agreement
    (⟨represented.template, represented.factors⟩ : NativeTemplateInstance graph.cliqueRootProjection)).trans
      (NativeSupportProfiles.agreement_of_basis represented.model original.model represented.preserved)

theorem completeSupportCatalogue_covers (original : ProjectedHiddenDAGModel graph) :
    ∃ entry, entry ∈ graph.cliqueRootProjection.completeSupportCatalogue ∧ CausalSupportAgreement entry.model original.model :=
  ⟨original.supportProfileRepresentative, original.supportProfileRepresentative_mem, original.supportProfileRepresentative_agreement⟩

end ProjectedHiddenDAGModel
end Thesis.Causality
