import Thesis.CausalTransport.HiddenDAGEvaluation
import Thesis.CausalTransport.HiddenDAGNoiseLaw
import Thesis.CausalTransport.HiddenDAGSemantics

namespace Thesis
namespace Causality

open Probability

/-!
# Observable probability preservation of the reverse hidden-DAG realization

Combine the two independently proved parts of the construction: the complete
joint-noise allocation law and unitwise evaluation preservation under every
hard intervention.  Every Boolean event on the observed assignment then has
the same probability in the original canonical projected model and its actual
finite original-DAG realization.

The statement compares rational probabilities extensionally, not raw atom
lists or common-denominator presentations.  The two records group independent
inputs differently and need not be literally the same record.  Observational
zeros, zero-weight noise units, unused roots and repeated atom labels are all
included.  No positivity or observed value-richness premise is used.

These are individual-model preservation theorems for the *reverse* canonical
realization.  They do not assert that an arbitrary multi-child hidden cause
can be replaced by independent pair roots while preserving its distribution.
`HiddenDAGCountermodelLift` and `HiddenDAGCompleteness` use this law to lift
actual countermodels and prove the native completeness converse separately.
-/

namespace FiniteLatentSCM

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- All hard-interventional observed event probabilities are preserved by
the constructed original-DAG model.  The proof uses the full joint-noise law;
single-channel marginals alone would not justify this statement. -/
theorem toHiddenDAGSCM_interventionalValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (intervention : HardIntervention S)
    (event : S.Assignment → Bool) :
    QProb.Equiv ((model.toHiddenDAGSCM compatible).interventionalValue intervention event)
      (model.interventionalValue intervention.value event) := by
  let realized := model.toHiddenDAGSCM compatible
  let noiseEvent := fun noise => event (realized.evalObserved intervention noise)
  have evaluated : QProb.Equiv (realized.interventionalValue intervention event)
      ((HiddenDAGPlacedNoise.prior model compatible).probVal noiseEvent) :=
    realized.prior.map_probVal (realized.evalObserved intervention) event
  have allocated := HiddenDAGPlacedNoise.prior_probVal_encode model compatible noiseEvent
  have encoded := model.prior.map_probVal (HiddenDAGPlacedNoise.encode model compatible) noiseEvent
  have units : QProb.Equiv
      (model.prior.probVal (fun roots => noiseEvent (HiddenDAGPlacedNoise.encode model compatible roots)))
      (model.prior.probVal (fun roots => event (model.evalUnder intervention.value roots))) := by
    apply model.prior.probVal_congr
    intro roots
    exact congrArg event (model.toHiddenDAGSCM_evalObserved compatible intervention roots)
  exact QProb.equiv_trans evaluated (QProb.equiv_trans allocated (QProb.equiv_trans encoded
    (QProb.equiv_trans units (QProb.equiv_symm (model.interventionalValue_eq intervention.value event)))))

/-- Every observational event probability is preserved as well.  Empty
hard intervention is genuinely the source model's unforced evaluator, not
an extra model-equivalence or positivity assumption. -/
theorem toHiddenDAGSCM_observationalValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (event : S.Assignment → Bool) :
    QProb.Equiv ((model.toHiddenDAGSCM compatible).observationalValue event)
      (model.observationalValue event) := by
  exact model.toHiddenDAGSCM_interventionalValue compatible (HardIntervention.empty S) event

/-- The actual native record selected by a kernel preserves every event
probability.  Both branches use the proved model laws: an action selects its
hard-interventional law and an empty action selects its observational law. -/
theorem toHiddenDAGSCM_kernelDistribution_probVal (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (kernel : Kernel S)
    (assignment : S.Assignment) (event : S.Assignment → Bool) :
    QProb.Equiv
      (((model.toHiddenDAGSCM compatible).kernelDistribution kernel assignment).probVal event)
      ((kernel.distribution model assignment).probVal event) := by
  unfold FiniteHiddenDAGSCM.kernelDistribution Kernel.distribution
  split
  · exact model.toHiddenDAGSCM_interventionalValue compatible
      { value := kernel.intervention assignment } event
  · exact model.toHiddenDAGSCM_observationalValue compatible event

/-- Every native partial kernel result agrees with its original canonical
result, including unsupported conditioners and supported zero outcomes.
Equivalent division uses both numerator and denominator probabilities, so no
positive-denominator premise or replacement value for `0 / 0` is inserted. -/
noncomputable def toHiddenDAGSCM_kernelDenote (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (kernel : Kernel S)
    (assignment : S.Assignment) :
    ProbabilityResult.Equivalent ((model.toHiddenDAGSCM compatible).kernelDenote kernel assignment)
      (kernel.denote model assignment) := by
  unfold FiniteHiddenDAGSCM.kernelDenote Kernel.denote
  exact ProbabilityResult.divide_congr
    (.value (model.toHiddenDAGSCM_kernelDistribution_probVal compatible kernel assignment
      (kernel.numeratorEvent assignment)))
    (.value (model.toHiddenDAGSCM_kernelDistribution_probVal compatible kernel assignment
      (kernel.conditionEvent assignment)))

/-- Strict positivity of each original observed atom is preserved when it
is present.  This is intrinsic probability transfer, not an application of
denotational soundness or a canonical-membership claim about a collapse. -/
theorem toHiddenDAGSCM_observational_num_pos (model : ExactModel S)
    (compatible : Compatible model P.observedGraph)
    (positive : Causality.ObservationallyPositive model) :
    forall assignment : S.Assignment,
      0 < ((model.toHiddenDAGSCM compatible).observationalDist.probVal
        (FiniteProbRecord.singletonEvent assignment)).num := by
  intro assignment
  exact (QProb.equiv_num_pos_iff
    (model.toHiddenDAGSCM_observationalValue compatible (FiniteProbRecord.singletonEvent assignment))).mpr
    (positive assignment)

end FiniteLatentSCM
end Causality
end Thesis
