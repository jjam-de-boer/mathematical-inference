import Thesis.Causality.CausalAbstractionQuery
import Thesis.Causality.CausalRemainder
import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ObservationalEvaluation

namespace Thesis.Causality
open Probability

/-!
Exactness of one SCM pair transports an identified empty-condition joint
value onto a pulled-back macro event. Identifiability is a property of a
graph class and is not transferred. Event equality is hypothesized: a
cluster-local query does not by itself equate the fine outcome cylinder
with `E ∘ τ` when the outcome cluster is a non-injective aggregate.

The identification result and its soundness at the supplied micro model and
reference are explicit inputs. Exactness then compares this one model pair.
No macro model-class identification theorem follows from that comparison.
The transported query is unconditional after intervention, so its result is
a defined probability even when the selected outcome has zero mass.
-/

namespace FiniteCausalCoarseGraining

/-- Locality of `E ∘ τ` follows from query pullback. Equality of that
event with the fine outcome cylinder is a separate hypothesis. -/
theorem pullback_query_event_local
    (coarsening : FiniteCausalCoarseGraining micro coarse)
    (fineQuery : JointKernelQuery micro) (coarseQuery : JointKernelQuery coarse)
    (localQuery : coarsening.PullsBackQuery fineQuery coarseQuery)
    (event : Event coarse.Assignment)
    (localEvent : EventDependsOnlyOn coarseQuery.outcome event) :
    EventDependsOnlyOn fineQuery.outcome
      (fun state => event (coarsening.assignmentMap state)) := by
  rw [localQuery.1]
  exact coarsening.pullback_event_local coarseQuery.outcome event localEvent

end FiniteCausalCoarseGraining

namespace JointKernelQuery

/-- The hard intervention encoded by a joint kernel at one reference.
`Kernel.intervention` has the same target type as `HardIntervention.value`. -/
def sourceIntervention (q : JointKernelQuery S) (reference : S.Assignment) :
    HardIntervention S where
  value := q.operationKernel.intervention reference

@[simp] theorem sourceIntervention_value (q : JointKernelQuery S)
    (reference : S.Assignment) :
    (q.sourceIntervention reference).value =
      q.operationKernel.intervention reference :=
  rfl

end JointKernelQuery

namespace Kernel

/-- An empty-condition kernel's table is the interventional law of its
encoded `do`, including the empty surgery. -/
theorem distribution_probVal_interventionalValue
    (model : FiniteLatentSCM S) (kernel : Kernel S) (reference : S.Assignment)
    (event : Event S.Assignment) :
    QProb.Equiv
      ((kernel.distribution model reference).probVal event)
      (model.interventionalValue (kernel.intervention reference) event) :=
  QProb.equiv_trans
    (Kernel.distribution_probVal model kernel reference event)
    (QProb.equiv_symm
      (model.interventionalValue_eq (kernel.intervention reference) event))

end Kernel

namespace CausalInterventionMap

/-- Identified fine syntax, already equal to the fine source kernel by
soundness, denotes the macro interventional mass of `E`. Undefined stays
undefined under `ProbabilityResult.Equivalent`; for the unconditional
query certified here the displayed macro mass is defined, including zero.
The formula is action-free, so its observational-table interpretation agrees
with its SCM interpretation. This record contains a value certificate for
the supplied model pair, rather than class-wide macro identifiability. -/
structure IdentifiedExactJointValue
    {micro coarse : ObservedSignature}
    (mapping : CausalInterventionMap micro coarse)
    (Q_fine : JointKernelQuery micro) (φ : ProbabilityTerm micro)
    (fineRef : micro.Assignment) (J : HardIntervention coarse)
    (E : Event coarse.Assignment) where
  source_equivalent :
    ProbabilityTerm.EquivalentAt mapping.microModel Q_fine.sourceTerm φ fineRef
  formula_value :
    ProbabilityResult.Equivalent
      (φ.denote mapping.microModel fineRef)
      (some (mapping.macroModel.interventionalValue J.value E))
  observational_eq :
    φ.observationalDenote mapping.microModel.observationalDist fineRef =
      φ.denote mapping.microModel fineRef

/-- Exact ω on this pair, a hypothesized event pullback, and ID soundness
at one reference. The `identified` input supplies action-freeness of the
formula; `sound` separately supplies equality with the actual fine source.
Neither node-set locality nor the successful ID syntax alone replaces that
model-specific soundness obligation. Not a lift of identifiability to the
coarse graph class. -/
noncomputable def identifiedExactJointValue
    {micro coarse : ObservedSignature}
    (mapping : CausalInterventionMap micro coarse) (exact : mapping.Exact)
    (coarsening : FiniteCausalCoarseGraining micro coarse)
    (Q_coarse : JointKernelQuery coarse) (Q_fine : JointKernelQuery micro)
    (localQuery : coarsening.PullsBackQuery Q_fine Q_coarse)
    (fineRef : micro.Assignment)
    (I : HardIntervention micro)
    (I_eq : I.value = Q_fine.operationKernel.intervention fineRef)
    (J : HardIntervention coarse) (defined : mapping.omega I = some J)
    (E : Event coarse.Assignment)
    (E_local : EventDependsOnlyOn Q_coarse.outcome E)
    (eventPullback :
      Kernel.agreesOn Q_fine.outcome fineRef =
        fun s => E (mapping.assignmentMap s))
    (G_fine : ObservedGraph micro) {φ : ProbabilityTerm micro}
    (identified : identifyJointKernel G_fine Q_fine = .identified φ)
    (sound :
      ProbabilityTerm.EquivalentAt mapping.microModel Q_fine.sourceTerm φ
        fineRef) :
    mapping.IdentifiedExactJointValue Q_fine φ fineRef J E :=
  let _ := FiniteCausalCoarseGraining.pullback_query_event_local
    coarsening Q_fine Q_coarse localQuery E E_local
  let kernel := Q_fine.operationKernel
  have sourceUncond :
      ProbabilityResult.Equivalent
        (Q_fine.sourceTerm.denote mapping.microModel fineRef)
        (some ((kernel.distribution mapping.microModel fineRef).probVal
          (Kernel.agreesOn Q_fine.outcome fineRef))) :=
    Kernel.unconditionalDenote mapping.microModel Q_fine.outcome Q_fine.action
      fineRef
  have mass :
      QProb.Equiv
        ((kernel.distribution mapping.microModel fineRef).probVal
          (Kernel.agreesOn Q_fine.outcome fineRef))
        (mapping.macroModel.interventionalValue J.value E) := by
    refine QProb.equiv_trans
      (Kernel.distribution_probVal_interventionalValue mapping.microModel kernel
        fineRef _) ?_
    refine QProb.equiv_trans ?_
      (QProb.equiv_symm
        ((CausalRemainder.eventRemainder_zero_iff mapping.microModel
          mapping.macroModel mapping.assignmentMap I J E).mp
          ((mapping.exact_iff_remainder_zero.mp exact) I J defined E)))
    have sameTarget : kernel.intervention fineRef = I.value := I_eq.symm
    have sameEvent :
        Kernel.agreesOn Q_fine.outcome fineRef =
          fun s => E (mapping.assignmentMap s) := eventPullback
    rw [sameTarget, sameEvent]
    exact QProb.equiv_refl _
  { source_equivalent := sound
    formula_value :=
      ProbabilityResult.trans (ProbabilityResult.symm sound)
        (ProbabilityResult.trans sourceUncond (.value mass))
    observational_eq :=
      ProbabilityTerm.observationalDenote_eq_scm mapping.microModel φ
        (identifyJointKernel_identified_actionFree G_fine Q_fine identified)
        fineRef }

end CausalInterventionMap
end Thesis.Causality
