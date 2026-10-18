import Thesis.CausalTransport.HiddenDAGNativeTemplates
import Thesis.CausalTransport.HiddenDAGSourcePresentation

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Native-law coverage by standalone templates

Explicit finite value/noise equivalences give a model's code equations,
observed conversions and rational factor records. Those data instantiate a
standalone template, with its own graph-derived observed lookup and actual
independent product prior. No base model is passed to that constructor.

The proof below establishes the correspondence rather than postulating it.
The supplied acyclic evaluator-uniqueness theorem gives unit-level simulation
under every hard intervention. The finite source-presentation theorem then
identifies the entire decoded independent law, not merely rectangles. Thus
every interventional event probability agrees, including zeros; all supported
conditionals transport without completing a null denominator.

The original model occurs only as input to the encoding and preservation
proof. Once encoded, template instantiation uses finite structural data and
the rational source factors alone. Cardinality bounds and finite-catalogue
membership are supplied separately by the bounded-representation adapter.
-/

namespace FiniteHiddenDAGSCM

/-- Graph classification makes every valid native lookup the same explicit
graph-only search. This is an equality proof, not an inverse chosen as data. -/
theorem observedIndex_eq_graph (model : FiniteHiddenDAGSCM S P) : model.observedIndex = P.hiddenDAG.observedIndex := by
  funext node
  rcases P.hiddenDAG.node_classified node with hidden | ⟨index, same⟩
  · rw [model.hidden_has_no_observed_index node hidden, P.hiddenDAG.observedIndex_hidden node hidden]
  · rw [← same, model.observedIndex_observed, P.hiddenDAG.observedIndex_observed]

variable (model : FiniteHiddenDAGSCM S P) (nodeCard sourceCard : Fin P.hiddenDAG.count → Nat)
variable (nodeCodes : ∀ node, ValueEquivalence (model.NodeValue node) (Fin (nodeCard node)))
variable (sourceCodes : ∀ node, ValueEquivalence (model.Noise node) (Fin (sourceCard node)))

def codedObservedEquivalence (index : Fin S.count) :
    ValueEquivalence (Fin (nodeCard (P.hiddenDAG.observedNode index))) (S.Value index) where
  forward := fun code => (model.observedEquiv index).forward ((nodeCodes _).backward code)
  backward := fun value => (nodeCodes _).forward ((model.observedEquiv index).backward value)
  forward_backward := by
    intro value
    rw [(nodeCodes _).backward_forward, (model.observedEquiv index).forward_backward]
  backward_forward := by
    intro code
    rw [(model.observedEquiv index).backward_forward, (nodeCodes _).forward_backward]

def nativeTemplate : P.hiddenDAG.CodeNativeTemplate :=
  { entry := ⟨⟨nodeCard, sourceCard⟩, model.ownCodeTables nodeCard sourceCard nodeCodes sourceCodes⟩
    observed := model.codedObservedEquivalence nodeCard nodeCodes }

/-- Map each actual factor to its finite codes, retaining natural weights
and denominators. No positivity of individual codes is needed. -/
def nativeTemplateFactors (node : Fin P.hiddenDAG.count) : FiniteProbRecord (Fin (sourceCard node)) :=
  (model.factor node).map (sourceCodes node).forward

def nativeTemplateModel : FiniteHiddenDAGSCM S P :=
  (model.nativeTemplate nodeCard sourceCard nodeCodes sourceCodes).model (P := P)
    (model.nativeTemplateFactors sourceCard sourceCodes)

def decodeTemplateNoise (codes : (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).NoiseAssignment) :
    model.NoiseAssignment := fun node => (sourceCodes node).backward (codes node)

theorem nativeTemplateModel_mechanism (child : Fin P.hiddenDAG.count)
    (parents : P.hiddenDAG.ParentValues (P.hiddenDAG.CodeValues nodeCard) child) (noise : Fin (sourceCard child)) :
    (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).mechanism child parents noise =
      (model.mechanismAsCodes nodeCard sourceCard nodeCodes sourceCodes) child parents noise := by
  change (P.hiddenDAG.lookupCodeMechanisms nodeCard sourceCard
    (P.hiddenDAG.tabulateCodeMechanisms nodeCard sourceCard (model.mechanismAsCodes nodeCard sourceCard nodeCodes sourceCodes)))
      child parents noise = _
  rw [P.hiddenDAG.lookupCodeMechanisms_tabulate]

theorem nativeTemplateModel_interventionValueAt (intervention : HardIntervention S) (node : Fin P.hiddenDAG.count) :
    (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).interventionValueAt intervention node =
      (model.interventionValueAt intervention node).map (nodeCodes node).forward := by
  cases selected : model.observedIndex node with
  | none =>
      have missing : (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).observedIndex node = none :=
        (congrFun model.observedIndex_eq_graph node).symm.trans selected
      rw [(model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).interventionValueAt_eq_none intervention node missing,
        model.interventionValueAt_eq_none intervention node selected]
      rfl
  | some index =>
      have same := model.observedIndex_sound node index selected
      subst node
      rw [(model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).interventionValueAt_observed_eq_map,
        model.interventionValueAt_observed_eq_map]
      cases intervention.value index <;> rfl

/-- Simulation is valid for every code unit and every hard intervention.
The graph and public signature are unchanged; only finite presentations differ. -/
theorem nativeTemplateModel_evalNode (intervention : HardIntervention S)
    (codes : (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).NoiseAssignment) (node : Fin P.hiddenDAG.count) :
    (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).evalNode intervention codes node =
      (nodeCodes node).forward (model.evalNode intervention
        (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes) node) := by
  apply (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).evalNode_eq_of_solution intervention codes
    (fun current => (nodeCodes current).forward (model.evalNode intervention
      (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes) current))
  intro current
  rw [model.nativeTemplateModel_interventionValueAt nodeCard sourceCard nodeCodes sourceCodes intervention current]
  rw [evalNode]
  cases forced : model.interventionValueAt intervention current with
  | some value => rfl
  | none =>
      rw [model.nativeTemplateModel_mechanism nodeCard sourceCard nodeCodes sourceCodes]
      change (nodeCodes current).forward (model.mechanism current
          (fun parent _ => model.evalNode intervention (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes) parent)
          ((sourceCodes current).backward (codes current))) =
        (nodeCodes current).forward (model.mechanism current
          (fun parent _ => (nodeCodes parent).backward ((nodeCodes parent).forward
            (model.evalNode intervention (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes) parent)))
          ((sourceCodes current).backward (codes current)))
      have sameParents :
          (fun parent (_ : P.hiddenDAG.edge parent current = true) => (nodeCodes parent).backward ((nodeCodes parent).forward
            (model.evalNode intervention (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes) parent))) =
          (fun parent (_ : P.hiddenDAG.edge parent current = true) =>
            model.evalNode intervention (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes) parent) := by
        funext parent edge
        exact (nodeCodes parent).backward_forward _
      rw [sameParents]

theorem nativeTemplateModel_evalObserved (intervention : HardIntervention S)
    (codes : (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).NoiseAssignment) :
    (model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).evalObserved intervention codes =
      model.evalObserved intervention (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes) := by
  funext index
  change (model.observedEquiv index).forward ((nodeCodes _).backward
    ((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).evalNode intervention codes (P.hiddenDAG.observedNode index))) = _
  rw [model.nativeTemplateModel_evalNode nodeCard sourceCard nodeCodes sourceCodes, (nodeCodes _).backward_forward]
  rfl

/-- Encoding/decoding reconstructs the literal original marginal record,
including repeated labels and zero-weight atoms. -/
def sourceCodePresentation (node : Fin P.hiddenDAG.count) : FiniteProbRecord.FinitePresentation (model.factor node) where
  card := sourceCard node
  record := model.nativeTemplateFactors sourceCard sourceCodes node
  decode := (sourceCodes node).backward
  recovered := by
    rw [nativeTemplateFactors, FiniteProbRecord.map_comp]
    have same : (fun value => (sourceCodes node).backward ((sourceCodes node).forward value)) = id :=
      funext (fun value => (sourceCodes node).backward_forward value)
    rw [same, FiniteProbRecord.map_id]

/-- The original prior need only satisfy its independent product law;
it need not literally be the canonical product chosen by the template. -/
theorem nativeTemplateModel_prior_probVal (event : Event model.NoiseAssignment) :
    QProb.Equiv ((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).prior.probVal
      (fun codes => event (model.decodeTemplateNoise nodeCard sourceCard nodeCodes sourceCodes codes))) (model.prior.probVal event) :=
  FiniteProduct.presentation_probVal model.prior model.product_law model.noiseEnumeration model.noise_complete model.noiseDecidableEq
    (model.sourceCodePresentation sourceCard sourceCodes) event

theorem nativeTemplateModel_interventionalValue (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).interventionalValue intervention event)
      (model.interventionalValue intervention event) := by
  apply QProb.equiv_trans ((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).prior.map_probVal _ _)
  apply QProb.equiv_trans ((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).prior.probVal_congr _ _
    (fun codes => congrArg event (model.nativeTemplateModel_evalObserved nodeCard sourceCard nodeCodes sourceCodes intervention codes)))
  exact QProb.equiv_trans (model.nativeTemplateModel_prior_probVal nodeCard sourceCard nodeCodes sourceCodes
      (fun noise => event (model.evalObserved intervention noise))) (QProb.equiv_symm (model.prior.map_probVal _ _))

theorem nativeTemplateModel_observationalValue (event : Event S.Assignment) :
    QProb.Equiv ((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).observationalValue event)
      (model.observationalValue event) :=
  model.nativeTemplateModel_interventionalValue nodeCard sourceCard nodeCodes sourceCodes (HardIntervention.empty S) event

theorem nativeTemplateModel_eventPositive_iff (intervention : HardIntervention S) (evidence : Event S.Assignment) :
    ((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).interventionalDist intervention).EventPositive evidence ↔
      (model.interventionalDist intervention).EventPositive evidence :=
  QProb.equiv_num_pos_iff (model.nativeTemplateModel_interventionalValue nodeCard sourceCard nodeCodes sourceCodes intervention evidence)

theorem nativeTemplateModel_conditionOn_probVal (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (supported : (model.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      ((((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).interventionalDist intervention).conditionOn evidence
        ((model.nativeTemplateModel_eventPositive_iff nodeCard sourceCard nodeCodes sourceCodes intervention evidence).mpr supported)).probVal event)
      (((model.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  let supportedNew := (model.nativeTemplateModel_eventPositive_iff nodeCard sourceCard nodeCodes sourceCodes intervention evidence).mpr supported
  exact QProb.equiv_trans
    (((model.nativeTemplateModel nodeCard sourceCard nodeCodes sourceCodes).interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans
      (QProb.div_congr (model.nativeTemplateModel_interventionalValue nodeCard sourceCard nodeCodes sourceCodes intervention
          (fun value => evidence value && event value))
        (model.nativeTemplateModel_interventionalValue nodeCard sourceCard nodeCodes sourceCodes intervention evidence) supportedNew supported)
      (QProb.equiv_symm ((model.interventionalDist intervention).conditionOn_probVal evidence event supported)))

theorem nativeTemplate_mem (nodeBound sourceBound : Nat) (nodes : ∀ node, nodeCard node ≤ nodeBound)
    (sources : ∀ node, sourceCard node ≤ sourceBound) :
    model.nativeTemplate nodeCard sourceCard nodeCodes sourceCodes ∈ P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound :=
  P.hiddenDAG.nativeTemplateCatalogue_complete nodeBound sourceBound _ nodes sources

end FiniteHiddenDAGSCM
end Thesis.Causality
