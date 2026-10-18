import Thesis.CausalTransport.HiddenDAGMechanismTables
import Thesis.CausalTransport.HiddenDAGFiniteRepresentation

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Exact native reconstruction from a listed finite mechanism table

Explicit two-sided value/noise conversions present a native model on a fixed
finite cardinality shape. Tabulate its equations on the graph-compatible row
codes, prove membership in the shape's exhaustive catalogue, and reconstruct
the native model by lookup. Reconstruction is literal record equality: it
preserves every equation input and every intervention, not just the originally
retained probabilities. The base model's source law, observed conversions and
other nonmechanism fields are kept unchanged by this particular adapter.

Applying it to the existing bounded representation gives an explicitly listed
mechanism table for every original model's bounded representative. The code
catalogue depends on the graph/cardinality vectors, not that representative's
equations or source weights. `HiddenDAGMechanismCatalogue` combines finitely
many bounded shapes; normalizing the remaining observed-conversion data is
a separate native-template coverage step. Likewise,
infinitely many rational source-weight assignments are not enumerated here.
-/

namespace FiniteHiddenDAGSCM

variable (model : FiniteHiddenDAGSCM S P) (nodeCard sourceCard : Fin P.hiddenDAG.count → Nat)
variable (nodeCodes : ∀ node, ValueEquivalence (model.NodeValue node) (Fin (nodeCard node)))
variable (sourceCodes : ∀ node, ValueEquivalence (model.Noise node) (Fin (sourceCard node)))

def mechanismAsCodes : P.hiddenDAG.CodeMechanisms nodeCard sourceCard :=
  fun child parents noise => (nodeCodes child).forward
    (model.mechanism child (fun parent edge => (nodeCodes parent).backward (parents parent edge))
      ((sourceCodes child).backward noise))

def mechanismFromCodes (equations : P.hiddenDAG.CodeMechanisms nodeCard sourceCard) :
    (child : Fin P.hiddenDAG.count) → P.hiddenDAG.ParentValues model.NodeValue child → model.Noise child → model.NodeValue child :=
  fun child parents noise => (nodeCodes child).backward
    (equations child (fun parent edge => (nodeCodes parent).forward (parents parent edge))
      ((sourceCodes child).forward noise))

/-- Conversions are inverted on all typed parent inputs, not only ones that
happen to be reached or have positive prior mass in this particular model. -/
theorem mechanismFromCodes_asCodes :
    model.mechanismFromCodes nodeCard sourceCard nodeCodes sourceCodes
      (model.mechanismAsCodes nodeCard sourceCard nodeCodes sourceCodes) = model.mechanism := by
  funext child parents noise
  dsimp only [mechanismFromCodes, mechanismAsCodes]
  have sameParents :
      (fun parent (edge : P.hiddenDAG.edge parent child = true) =>
        (nodeCodes parent).backward ((nodeCodes parent).forward (parents parent edge))) = parents := by
    funext parent edge
    exact (nodeCodes parent).backward_forward (parents parent edge)
  rw [sameParents, (sourceCodes child).backward_forward, (nodeCodes child).backward_forward]

def ownCodeTables : P.hiddenDAG.CodeMechanismTables nodeCard sourceCard :=
  P.hiddenDAG.tabulateCodeMechanisms nodeCard sourceCard (model.mechanismAsCodes nodeCard sourceCard nodeCodes sourceCodes)

theorem ownCodeTables_mem :
    model.ownCodeTables nodeCard sourceCard nodeCodes sourceCodes ∈ P.hiddenDAG.codeMechanismCatalogue nodeCard sourceCard :=
  P.hiddenDAG.codeMechanismCatalogue_complete nodeCard sourceCard _

/-- Only the mechanism field is replaced. In particular, this is not an
unproved identification of all source laws on the same graph. -/
def withCodeTables (tables : P.hiddenDAG.CodeMechanismTables nodeCard sourceCard) : FiniteHiddenDAGSCM S P :=
  { model with
    mechanism := model.mechanismFromCodes nodeCard sourceCard nodeCodes sourceCodes
      (P.hiddenDAG.lookupCodeMechanisms nodeCard sourceCard tables) }

theorem withCodeTables_ownCodeTables :
    model.withCodeTables nodeCard sourceCard nodeCodes sourceCodes
      (model.ownCodeTables nodeCard sourceCard nodeCodes sourceCodes) = model := by
  unfold withCodeTables ownCodeTables
  rw [P.hiddenDAG.lookupCodeMechanisms_tabulate, model.mechanismFromCodes_asCodes]

/-- Whole native intervention records, including their zero cells, survive
tabulation. This is a consequence of exact reconstruction, not a positivity
claim or an external semantic-transfer interface. -/
theorem withCodeTables_own_interventionalDist (intervention : HardIntervention S) :
    (model.withCodeTables nodeCard sourceCard nodeCodes sourceCodes
      (model.ownCodeTables nodeCard sourceCard nodeCodes sourceCodes)).interventionalDist intervention =
      model.interventionalDist intervention :=
  congrArg (fun native => native.interventionalDist intervention)
    (model.withCodeTables_ownCodeTables nodeCard sourceCard nodeCodes sourceCodes)

namespace BoundedRepresentation

variable {original : FiniteHiddenDAGSCM S P} {targets : List (NativeProbabilityQuery S)}

/-- These are transports along supplied type equalities, not choices of a
bijection from a proof that two cardinalities happen to be equal. -/
def nodeCodeEquivalence (represented : BoundedRepresentation original targets) (node : Fin P.hiddenDAG.count) :
    ValueEquivalence (represented.model.NodeValue node) (Fin (represented.nodeCard node)) := by
  rw [represented.node_type node]
  exact ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def sourceCodeEquivalence (represented : BoundedRepresentation original targets) (node : Fin P.hiddenDAG.count) :
    ValueEquivalence (represented.model.Noise node) (Fin (represented.sourceCard node)) := by
  rw [represented.noise_type node]
  exact ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def mechanismTables (represented : BoundedRepresentation original targets) :
    P.hiddenDAG.CodeMechanismTables represented.nodeCard represented.sourceCard :=
  represented.model.ownCodeTables represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence

theorem mechanismTables_mem (represented : BoundedRepresentation original targets) :
    represented.mechanismTables ∈ P.hiddenDAG.codeMechanismCatalogue represented.nodeCard represented.sourceCard :=
  represented.model.ownCodeTables_mem represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence

def tabulatedModel (represented : BoundedRepresentation original targets) : FiniteHiddenDAGSCM S P :=
  represented.model.withCodeTables represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence represented.mechanismTables

theorem tabulatedModel_eq (represented : BoundedRepresentation original targets) : represented.tabulatedModel = represented.model :=
  represented.model.withCodeTables_ownCodeTables represented.nodeCard represented.sourceCard
    represented.nodeCodeEquivalence represented.sourceCodeEquivalence

theorem tabulatedModel_observational (represented : BoundedRepresentation original targets) (event : Event S.Assignment) :
    QProb.Equiv (represented.tabulatedModel.observationalValue event) (original.observationalValue event) := by
  rw [represented.tabulatedModel_eq]
  exact represented.observational event

theorem tabulatedModel_preserved (represented : BoundedRepresentation original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    QProb.Equiv (represented.tabulatedModel.interventionalValue query.intervention query.event)
      (original.interventionalValue query.intervention query.event) := by
  rw [represented.tabulatedModel_eq]
  exact represented.preserved query listed

end BoundedRepresentation
end FiniteHiddenDAGSCM
end Thesis.Causality
