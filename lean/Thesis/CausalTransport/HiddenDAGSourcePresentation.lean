import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.FiniteProductPresentation

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Finite private-source alphabets on the unchanged native hidden DAG

Replace each private noise type by supplied finite sampling codes. The graph,
all endogenous value types, observed conversions and intervention targets stay
unchanged. Each old equation reads its decoded private source. The actual new
prior is the independent product of the presented factor records, not a joint
law supplied by an external semantic interface.

Unit-level simulation compares a coded noise assignment with its explicit
decoded assignment. Whole-law decoding then preserves every observational and
hard-intervention event, including zero cells and permitted null action values.
The original prior need only satisfy its product law. Neither source positivity
nor distinct atom labels nor an inverse on the whole old noise type is assumed.

The default atom presentation counts weighted occurrences, not unit cells.
Applied after source compression, these are genuinely bounded finite alphabets.
That later combination preserves the compression's retained queries, not every
unretained effect of the original uncompressed model. Endogenous hidden-value
compression and mechanism-table enumeration are separate representation steps.
-/

namespace FiniteHiddenDAGSCM

/-- Present private sources while retaining every structural field that does
not depend on their types. Sampling codes are not new observed distinctions. -/
def presentSources (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node)) :
    FiniteHiddenDAGSCM S P :=
  { model with
    Noise := FiniteProduct.PresentationCode presentations
    noiseEnumeration := fun node => List.finRange (presentations node).card
    noise_complete := fun _ code => List.mem_finRange code
    noiseDecidableEq := fun _ => inferInstance
    factor := fun node => (presentations node).record
    prior := FiniteProduct.presentationRecord presentations
    product_law := FiniteProduct.record_rectangular_probVal P.hiddenDAG.count _ _
    mechanism := fun child parents code => model.mechanism child parents ((presentations child).decode code) }

/-- Actual private-noise alphabets with one code per original weighted atom.
There is no expansion by the factor denominator or by total natural weight. -/
def atomSourceModel (model : FiniteHiddenDAGSCM S P) : FiniteHiddenDAGSCM S P :=
  model.presentSources (fun node => (model.factor node).atomPresentation)

theorem presentSources_interventionValueAt (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (intervention : HardIntervention S) (node : Fin P.hiddenDAG.count) :
    (model.presentSources presentations).interventionValueAt intervention node = model.interventionValueAt intervention node := rfl

/-- Simulation follows the unchanged acyclic equations. It is valid for
every code assignment, not only samples having positive probability. -/
theorem presentSources_evalNode (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (intervention : HardIntervention S) (codes : (model.presentSources presentations).NoiseAssignment)
    (node : Fin P.hiddenDAG.count) :
    (model.presentSources presentations).evalNode intervention codes node =
      model.evalNode intervention (FiniteProduct.decodePresentation presentations codes) node := by
  apply (model.presentSources presentations).evalNode_eq_of_solution intervention codes
    (model.evalFull intervention (FiniteProduct.decodePresentation presentations codes))
  intro current
  simp only [evalFull, presentSources_interventionValueAt]
  rw [evalNode]
  cases model.interventionValueAt intervention current <;> rfl

theorem presentSources_evalObserved (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (intervention : HardIntervention S) (codes : (model.presentSources presentations).NoiseAssignment) :
    (model.presentSources presentations).evalObserved intervention codes =
      model.evalObserved intervention (FiniteProduct.decodePresentation presentations codes) := by
  funext index
  change (model.observedEquiv index).forward
      ((model.presentSources presentations).evalNode intervention codes (P.hiddenDAG.observedNode index)) = _
  rw [presentSources_evalNode]
  rfl

/-- Decode the whole coded prior, including events that inspect several
private coordinates together. No canonical presentation of the old prior is
assumed, and arbitrary source denominators are retained as rational values. -/
theorem presentSources_prior_probVal (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (event : Event model.NoiseAssignment) :
    QProb.Equiv ((model.presentSources presentations).prior.probVal
      (fun codes => event (FiniteProduct.decodePresentation presentations codes))) (model.prior.probVal event) :=
  FiniteProduct.presentation_probVal model.prior model.product_law model.noiseEnumeration
    model.noise_complete model.noiseDecidableEq presentations event

theorem presentSources_interventionalValue (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((model.presentSources presentations).interventionalValue intervention event)
      (model.interventionalValue intervention event) := by
  apply QProb.equiv_trans ((model.presentSources presentations).prior.map_probVal _ _)
  apply QProb.equiv_trans ((model.presentSources presentations).prior.probVal_congr _ _
    (fun codes => congrArg event (model.presentSources_evalObserved presentations intervention codes)))
  exact QProb.equiv_trans (model.presentSources_prior_probVal presentations _)
    (QProb.equiv_symm (model.prior.map_probVal _ _))

theorem presentSources_observationalValue (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (event : Event S.Assignment) :
    QProb.Equiv ((model.presentSources presentations).observationalValue event) (model.observationalValue event) :=
  model.presentSources_interventionalValue presentations (HardIntervention.empty S) event

/-- Positivity is equivalent in both directions. A zero evidence event does
not become a supported conditional merely by changing private-source codes. -/
theorem presentSources_eventPositive_iff (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    ((model.presentSources presentations).interventionalDist intervention).EventPositive event ↔
      (model.interventionalDist intervention).EventPositive event :=
  QProb.equiv_num_pos_iff (model.presentSources_interventionalValue presentations intervention event)

/-- Actual conditioned interventional records agree at every supported
evidence event. Null evidence is left undefined, never assigned a default. -/
theorem presentSources_conditionOn_probVal (model : FiniteHiddenDAGSCM S P)
    (presentations : (node : Fin P.hiddenDAG.count) → FiniteProbRecord.FinitePresentation (model.factor node))
    (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (supported : (model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      ((((model.presentSources presentations).interventionalDist intervention).conditionOn evidence
        ((model.presentSources_eventPositive_iff presentations intervention evidence).mpr supported)).probVal event)
      (((model.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  let supportedNew := (model.presentSources_eventPositive_iff presentations intervention evidence).mpr supported
  exact QProb.equiv_trans
    (((model.presentSources presentations).interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans
      (QProb.div_congr (model.presentSources_interventionalValue presentations intervention (fun value => evidence value && event value))
        (model.presentSources_interventionalValue presentations intervention evidence) supportedNew supported)
      (QProb.equiv_symm ((model.interventionalDist intervention).conditionOn_probVal evidence event supported)))

end FiniteHiddenDAGSCM
end Thesis.Causality
