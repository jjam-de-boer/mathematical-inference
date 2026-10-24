import Thesis.Causality.SharedResponseModel
import Thesis.CausalTransport.HiddenDAGCollapse
import Thesis.CausalTransport.LatentRootNativeEvaluation
import Thesis.CausalTransport.ProjectedHiddenDAGModels

namespace Thesis.Causality.SharedResponse

open Probability

/-!
# Exact native-model coverage for the fully shared-root projection

The public class still ranges over all original finite hidden DAGs with the
fixed observed signature and complete bidirected projection. Their topology,
hidden values, private noise and rational denominators need not be bounded.
Collapse an actual input model, then push its joint law to response tables.
Conversely every rational response-table law has an actual native realization
in that very class, using one root incident at all observed nodes.

Both directions preserve all hard-intervention events, not only the factual
law or a finite selected target list. Conditional evidence is retained as its
own event, including a proof of nullness when appropriate. No conditional is
defined at zero evidence. These coverage statements justify a later linear
procedure for this class; they do not change a sparser graph's independence
requirements or decide an arbitrary rational polynomial system.
-/

variable (S : ObservedSignature.{0})

def nativeModel (law : FiniteProbRecord (Table S)) : FiniteHiddenDAGSCM S (latent S).rootProjection :=
  LatentRootNative.model (model S law)

def asProjectedModel (law : FiniteProbRecord (Table S)) : ProjectedHiddenDAGModel (graph S) :=
  ProjectedHiddenDAGModel.ofModel (nativeModel S law) (model_projectedGraph S law)

theorem nativeModel_interventionalValue (law : FiniteProbRecord (Table S))
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((nativeModel S law).interventionalValue intervention event)
      (law.probVal (fun table => event (eval S intervention.value table))) :=
  QProb.equiv_trans (LatentRootNative.interventionalValue (model S law) intervention event)
    (model_interventionalValue S law intervention.value event)

/-- The probability parameters are produced from the actual original model,
not supplied as a feasibility premise or selected from an existence proof. -/
def lawOfNative {projection : FiniteLatentProjection S} (original : FiniteHiddenDAGSCM S projection) :
    FiniteProbRecord (Table S) := lawOf S original.toLatentRootSCM

theorem lawOfNative_interventionalValue {projection : FiniteLatentProjection S}
    (original : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((lawOfNative S original).probVal (fun table => event (eval S intervention.value table)))
      (original.interventionalValue intervention event) := by
  have preserved := lawOf_interventionalValue S original.toLatentRootSCM intervention.value event
  rw [original.toLatentRootSCM_interventionalValue intervention event] at preserved
  exact preserved

/-- A representative in the unchanged projection-wide class. The complete
bidirected graph is an explicit type parameter, not an implicit relaxation. -/
def representative (original : ProjectedHiddenDAGModel (graph S)) : ProjectedHiddenDAGModel (graph S) :=
  asProjectedModel S (lawOfNative S original.model)

theorem representative_interventionalValue (original : ProjectedHiddenDAGModel (graph S))
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((representative S original).model.interventionalValue intervention event)
      (original.model.interventionalValue intervention event) :=
  QProb.equiv_trans (nativeModel_interventionalValue S _ intervention event)
    (lawOfNative_interventionalValue S original.model intervention event)

theorem representative_eventPositive_iff (original : ProjectedHiddenDAGModel (graph S))
    (intervention : HardIntervention S) (evidence : Event S.Assignment) :
    ((representative S original).model.interventionalDist intervention).EventPositive evidence ↔
      (original.model.interventionalDist intervention).EventPositive evidence :=
  QProb.equiv_num_pos_iff (representative_interventionalValue S original intervention evidence)

theorem representative_num_zero_iff (original : ProjectedHiddenDAGModel (graph S))
    (intervention : HardIntervention S) (evidence : Event S.Assignment) :
    ((representative S original).model.interventionalValue intervention evidence).num = 0 ↔
      (original.model.interventionalValue intervention evidence).num = 0 :=
  QProb.equiv_num_zero_iff (representative_interventionalValue S original intervention evidence)

theorem representative_conditionOn_probVal (original : ProjectedHiddenDAGModel (graph S))
    (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (supported : (original.model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      ((((representative S original).model.interventionalDist intervention).conditionOn evidence
        ((representative_eventPositive_iff S original intervention evidence).mpr supported)).probVal event)
      (((original.model.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  let supportedNew := (representative_eventPositive_iff S original intervention evidence).mpr supported
  exact QProb.equiv_trans
    (((representative S original).model.interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans
      (QProb.div_congr
        (representative_interventionalValue S original intervention (fun value => evidence value && event value))
        (representative_interventionalValue S original intervention evidence) supportedNew supported)
      (QProb.equiv_symm ((original.model.interventionalDist intervention).conditionOn_probVal evidence event supported)))

end Thesis.Causality.SharedResponse
