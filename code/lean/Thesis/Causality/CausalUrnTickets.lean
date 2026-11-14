import Thesis.Causality.CausalUrnGame

namespace Thesis.Causality.CausalUrnGame
open Probability
universe u
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Fresh cell choices and one common superurn

Each parent row receives its own uniformly sampled cell index. Taking a
dependent product over rows handles parent-dependent sizes without padding,
rounding or conditioning. Taking a second product over nodes makes different
urns' primitive choices independent. Shared **values** are still possible:
an unrecorded node's reading may influence several later recipes.

This explicit response-table coupling serves all experiments. Off-path table
entries integrate out. We prove exact uniform row marginals and the product
law here; no probabilistic independence premise is supplied by a game caller.
-/

/-- A uniform finite cell urn. Labels are the distinct cell identities;
repeated outcome labels enter only when the recipe reads these cells. -/
def cellUrn (size : Nat) (positive : 0 < size) : UrnProb (ULift.{u} (Fin size)) :=
  ⟨size, positive, ULift.up⟩

private theorem uniform_cast (urns : A → UrnProb B) (first second : A)
    (same : first = second) (event : Event B) :
    QProb.Equiv ((cellUrn (urns first).n (urns first).pos).probVal
      (fun cell => event ((urns second).draw
        (cast (congrArg (fun input => Fin (urns input).n) same) cell.down))))
      ((urns second).probVal event) := by
  cases same
  unfold QProb.Equiv UrnProb.probVal
  rw [UrnProb.probNum_eq_cellCount, UrnProb.probNum_eq_cellCount]
  rfl

def cellFactor (game : CausalUrnGame S P) (child) (row : Fin (game.parentWitness child).card) :
    FiniteProbRecord (game.Cell child row) :=
  FiniteProbRecord.ofUrn (cellUrn _ (game.contents child ((game.parentWitness child).decode row)).pos)

def seedFactor (game : CausalUrnGame S P) (child) : FiniteProbRecord (game.Seed child) :=
  FiniteProduct.record (game.parentWitness child).card (game.Cell child) (game.cellFactor child)

def seedValues (game : CausalUrnGame S P) (child) : List (game.Seed child) :=
  FiniteProduct.enumeration (game.parentWitness child).card (game.Cell child)
    (fun _ => (List.finRange _).map ULift.up)

theorem seedValues_complete (game : CausalUrnGame S P) (child) (seed : game.Seed child) :
    seed ∈ game.seedValues child :=
  FiniteProduct.enumeration_complete _ _ _
    (fun _ cell => List.mem_map.mpr ⟨cell.down, List.mem_finRange _, rfl⟩) seed

instance (game : CausalUrnGame S P) (child) : DecidableEq (game.Seed child) :=
  FiniteProduct.assignmentDecidableEq _ _ (fun _ => inferInstance)

/-- The entire random experiment is fixed before any setting is executed.
This law includes unused rows and unused nodes, which integrate to one. -/
def ticketLaw (game : CausalUrnGame S P) : FiniteProbRecord game.Ticket :=
  FiniteProduct.record P.hiddenDAG.count game.Seed game.seedFactor

def superurn (game : CausalUrnGame S P) : UrnProb game.Ticket := game.ticketLaw.toUrn

theorem ticketLaw_product (game : CausalUrnGame S P)
    (events : (node : Fin P.hiddenDAG.count) → Event (game.Seed node)) :
    QProb.Equiv (game.ticketLaw.probVal (FiniteProduct.rectangularEvent _ game.Seed events))
      (FiniteProduct.qProduct _ (fun node => (game.seedFactor node).probVal (events node))) :=
  FiniteProduct.record_rectangular_probVal _ _ _ events

/-- Looking up any fixed parent tuple has precisely its recipe's cell-count
law. The row may have any positive number of cells; no common denominator
across rows, positivity of outcome labels, or visited-row assumption occurs. -/
theorem draw_uniform (game : CausalUrnGame S P) (child) (parents : game.Parents child)
    (event : Event (game.Value child)) :
    QProb.Equiv ((game.seedFactor child).probVal (fun seed => event (game.draw child parents seed)))
      ((game.contents child parents).probVal event) := by
  let witness := game.parentWitness child
  let row := witness.encode parents
  let transfer : game.Cell child row → game.Value child := fun cell =>
    (game.contents child parents).draw
      (cast (congrArg (fun input => Fin (game.contents child input).n)
        (witness.decode_encode parents)) cell.down)
  have marginal := FiniteProduct.record_coordinate_probVal_dependent
    witness.card (game.Cell child) (game.cellFactor child) row (fun cell => event (transfer cell))
  refine QProb.equiv_trans marginal ?_
  have decoded := witness.decode_encode parents
  change QProb.Equiv ((FiniteProbRecord.ofUrn (cellUrn _ _)).probVal _)
    ((game.contents child parents).probVal event)
  exact QProb.equiv_trans (FiniteProbRecord.ofUrn_agrees _ _)
    (uniform_cast (game.contents child) _ _ decoded event)

/-- Direct operational law: run the interpreter on the fixed ticket law,
then retain just recorded coordinates. No SCM evaluator defines this law. -/
def law (game : CausalUrnGame S P) (setting : HardIntervention S) : FiniteProbRecord S.Assignment :=
  game.ticketLaw.map (game.record setting)

/-- The actual superurn's labels are recomputed when an instruction is set.
The cells and their sampling distribution remain the same. -/
def recordUrn (game : CausalUrnGame S P) (setting : HardIntervention S) : UrnProb S.Assignment :=
  game.superurn.map (game.record setting)

theorem recordUrn_agrees (game : CausalUrnGame S P) (setting) (event : Event S.Assignment) :
    QProb.Equiv ((game.law setting).probVal event) ((game.recordUrn setting).probVal event) := by
  exact QProb.equiv_trans (game.ticketLaw.map_probVal _ _)
    (QProb.equiv_trans (game.ticketLaw.toUrn_agrees _)
      (QProb.equiv_symm (game.superurn.probVal_map _ _)))

/-- Compile the urn instructions to a full hidden-DAG SCM. Its model fields
are constructed here: the caller supplies neither a prior nor a mechanism.
The full graph is retained, including every unrecorded common cause. -/
def toSCM (game : CausalUrnGame S P) : FiniteHiddenDAGSCM S P where
  NodeValue := game.Value
  nodeEnumeration := game.values
  node_complete := game.complete
  nodeDecidableEq := game.valueEq
  observedEquiv := game.recordedValue
  observedIndex := P.hiddenDAG.observedIndex
  observedIndex_observed := P.hiddenDAG.observedIndex_observed
  observedIndex_sound := P.hiddenDAG.observedIndex_sound
  hidden_has_no_observed_index := P.hiddenDAG.observedIndex_hidden
  Noise := game.Seed
  noiseEnumeration := game.seedValues
  noise_complete := game.seedValues_complete
  noiseDecidableEq := fun _ => inferInstance
  factor := game.seedFactor
  prior := game.ticketLaw
  product_law := game.ticketLaw_product
  mechanism := game.draw

theorem toSCM_forcedAt (game : CausalUrnGame S P) (setting) (node) :
    game.toSCM.interventionValueAt setting node = game.forcedAt setting node := by
  rfl

/-- Pointwise representation, including every unused ticket: both interpreters
solve the same local instructions. This is proved after the independent game
interpreter, not inserted as a field of the game definition. -/
theorem toSCM_read (game : CausalUrnGame S P) (setting) (ticket) (node) :
    game.toSCM.evalNode setting ticket node = game.read setting ticket node := by
  apply game.toSCM.evalNode_eq_of_solution setting ticket (game.read setting ticket)
  intro child
  rw [read]
  rw [game.toSCM_forcedAt]
  cases game.forcedAt setting child <;> rfl

theorem toSCM_record (game : CausalUrnGame S P) (setting) (ticket) :
    game.toSCM.evalObserved setting ticket = game.record setting ticket := by
  funext node
  exact congrArg (game.recordedValue node).forward (game.toSCM_read setting ticket _)

/-- One model represents the full recorded law for EVERY hard experiment.
Literal record equality is stronger than singleton or selected-event equality.
There is no restriction to observationally supported intervention values. -/
theorem toSCM_law (game : CausalUrnGame S P) (setting) :
    game.toSCM.interventionalDist setting = game.law setting := by
  change game.ticketLaw.map (game.toSCM.evalObserved setting) = game.ticketLaw.map (game.record setting)
  exact congrArg game.ticketLaw.map (funext (game.toSCM_record setting))

theorem toSCM_event (game : CausalUrnGame S P) (setting) (event : Event S.Assignment) :
    game.toSCM.interventionalValue setting event = (game.law setting).probVal event := by
  unfold FiniteHiddenDAGSCM.interventionalValue
  rw [game.toSCM_law]

end Thesis.Causality.CausalUrnGame
