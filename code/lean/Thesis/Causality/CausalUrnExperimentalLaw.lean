import Thesis.Causality.QualitativeExperiments
import Thesis.Causality.CausalUrnFreshness

namespace Thesis.Causality.CausalUrnGame
open Probability
universe u
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Full experimental laws and freshness before a complete history

The ordinary game law records only the observed coordinates. The abstract
rules also reason about unrecorded values, so first retain the complete
assignment from the same interpreter and the same tickets. Recording is a
projection afterwards; no extra setting of a hidden node is introduced.

Freshness must hold after ALL earlier values are read, not just a fixed
parent row. Earlier values may themselves be dependent through unrecorded
common causes. The product argument separates their entire joint readout
from the current node's private seed without asserting their mutual
independence. Any complete compatible node order is allowed.
-/

abbrev FullAssignment (game : CausalUrnGame S P) :=
  (node : Fin P.hiddenDAG.count) → game.Value node

def fullRead (game : CausalUrnGame S P) (setting : HardIntervention S)
    (ticket : game.Ticket) : game.FullAssignment := fun node => game.read setting ticket node

def fullLaw (game : CausalUrnGame S P) (setting : HardIntervention S) : FiniteProbRecord game.FullAssignment :=
  game.ticketLaw.map (game.fullRead setting)

def fullUrn (game : CausalUrnGame S P) (setting : HardIntervention S) : UrnProb game.FullAssignment :=
  game.superurn.map (game.fullRead setting)

theorem fullUrn_agrees (game : CausalUrnGame S P) (setting) (event : Event game.FullAssignment) :
    QProb.Equiv ((game.fullLaw setting).probVal event) ((game.fullUrn setting).probVal event) := by
  exact QProb.equiv_trans (game.ticketLaw.map_probVal _ _)
    (QProb.equiv_trans (game.ticketLaw.toUrn_agrees _)
      (QProb.equiv_symm (game.superurn.probVal_map _ _)))

/-- Forget the operational recipes, retaining ordinary experimental urns
and the supplied graph/alphabets only. The causal rules are proved later. -/
def experimentData (game : CausalUrnGame S P) (order : CausalOrder P.hiddenDAG) : CausalExperimentData S P where
  Value := game.Value
  values := game.values
  complete := game.complete
  valueEq := game.valueEq
  defaultValue := game.defaultValue
  recordedValue := game.recordedValue
  order := order
  slice := game.fullUrn

theorem experimentData_forcedAt (game : CausalUrnGame S P) (order) (setting) (node) :
    (game.experimentData order).forcedAt setting node = game.forcedAt setting node := rfl

/-- Recording after constructing the full experimental law is the original
game record urn, for every hard setting, including observationally null ones. -/
theorem experimentData_recordedUrn (game : CausalUrnGame S P) (order) (setting) :
    (game.experimentData order).recordedUrn setting = game.recordUrn setting := rfl

/-- Deterministic non-influence in any compatible total order. This follows
from local reading instructions before probability or independence is used. -/
theorem read_agrees_before (game : CausalUrnGame S P) (order : CausalOrder P.hiddenDAG)
    (setting) (first second : game.Ticket) (bound : Nat)
    (agree : ∀ node, order.nodes.idxOf node < bound → first node = second node)
    (node) (earlier : order.nodes.idxOf node < bound) :
    game.read setting first node = game.read setting second node := by
  rw [read, read]
  cases game.forcedAt setting node with
  | some => rfl
  | none =>
    rw [agree node earlier]
    apply congrArg (fun parents => game.draw node parents (second node))
    funext parent edge
    exact game.read_agrees_before order setting first second bound agree parent
      (Nat.lt_trans (order.parent_before parent node edge) earlier)
termination_by P.hiddenDAG.rank node
decreasing_by exact P.hiddenDAG.edge_rank_lt edge

/-- A full assignment type is convenient for readout products. Later slots
are filled with explicit defaults, which carry no information about their
actual future readings and do not alter any causal recipe. -/
def earlierReadings (game : CausalUrnGame S P) (order : CausalOrder P.hiddenDAG)
    (setting : HardIntervention S) (child : Fin P.hiddenDAG.count) (ticket : game.Ticket) : game.FullAssignment :=
  fun node => if order.nodes.idxOf node < order.nodes.idxOf child then
    game.read setting ticket node else game.defaultValue node

/-- The complete earlier readout and the current seed have a product law
for arbitrary joint tests. In particular this includes correlated siblings
and unrecorded earlier variables, rather than only fixed parent tuples. -/
theorem earlier_seed_product (game : CausalUrnGame S P) (order : CausalOrder P.hiddenDAG)
    (setting) (child)
    (event : Event (game.FullAssignment × game.Seed child)) :
    QProb.Equiv (game.ticketLaw.probVal
      (fun ticket => event (game.earlierReadings order setting child ticket, ticket child)))
      (((game.ticketLaw.map (game.earlierReadings order setting child)).product
        (game.ticketLaw.map (fun ticket => ticket child))).probVal event) := by
  let allocation := fun node => decide (order.nodes.idxOf node < order.nodes.idxOf child)
  apply FiniteProduct.readouts_product_probVal game.ticketLaw game.seedFactor game.ticketLaw_product
    game.seedValues game.seedValues_complete (fun _ => inferInstance) allocation
    (game.earlierReadings order setting child) (fun ticket => ticket child)
  · intro first second
    funext node
    unfold earlierReadings
    split
    · rename_i before
      apply game.read_agrees_before order setting _ first (order.nodes.idxOf child)
      · intro index earlier
        simp only [FiniteProduct.splice, allocation, decide_eq_true earlier, if_true]
      · exact before
    · rfl
  · intro first second
    simp only [FiniteProduct.splice, allocation, Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false]

/-- Fresh drawing after any earlier-measurable evidence fixing the parent
row. This denominator-free statement includes null evidence, zero outcomes
and differently sized recipe rows. Supported conditionals are obtained only
after a separate positive-evidence check. -/
theorem fresh_event_joint (game : CausalUrnGame S P) (order : CausalOrder P.hiddenDAG)
    (setting) (child) (unforced : game.forcedAt setting child = none)
    (parents : game.Parents child) (event : Event (game.Value child))
    (evidence : Event game.FullAssignment)
    (depends : (game.experimentData order).DependsBefore child evidence)
    (fixesParents : ∀ a, evidence a = true → (game.experimentData order).parents child a = parents) :
    QProb.Equiv ((game.fullUrn setting).probVal
      (inter ((game.experimentData order).nodeEvent child event) evidence))
      (QProb.mul ((game.fullUrn setting).probVal evidence) ((game.contents child parents).probVal event)) := by
  let early := game.earlierReadings order setting child
  let joint : Event (game.FullAssignment × game.Seed child) :=
    fun pair => evidence pair.1 && event (game.draw child parents pair.2)
  have evidenceSame : ∀ ticket, evidence (game.fullRead setting ticket) = evidence (early ticket) := by
    intro ticket
    apply depends
    intro node before
    change order.nodes.idxOf node < order.nodes.idxOf child at before
    simp only [early, earlierReadings, before, if_true, fullRead]
  have sameEvent : ∀ ticket,
      inter ((game.experimentData order).nodeEvent child event) evidence (game.fullRead setting ticket) =
      joint (early ticket, ticket child) := by
    intro ticket
    cases selected : evidence (game.fullRead setting ticket) with
    | false =>
        have noEvidence : evidence (early ticket) = false := (evidenceSame ticket).symm.trans selected
        simp only [inter, selected, Bool.and_false, joint, noEvidence, Bool.false_and]
    | true =>
        have parentValues := fixesParents (game.fullRead setting ticket) selected
        have sameRead : game.read setting ticket child = game.draw child parents (ticket child) := by
          rw [read, unforced]
          exact congrArg (fun pa => game.draw child pa (ticket child)) parentValues
        have hasEvidence : evidence (early ticket) = true := (evidenceSame ticket).symm.trans selected
        simp only [inter, CausalExperimentData.nodeEvent, fullRead, sameRead, selected,
          Bool.and_true, joint, hasEvidence, Bool.true_and]
  have sourceIdentity : QProb.Equiv
      (game.ticketLaw.probVal (fun ticket =>
        inter ((game.experimentData order).nodeEvent child event) evidence (game.fullRead setting ticket)))
      (QProb.mul (game.ticketLaw.probVal (fun ticket => evidence (game.fullRead setting ticket)))
        ((game.contents child parents).probVal event)) := by
    refine QProb.equiv_trans (game.ticketLaw.probVal_congr _ _ sameEvent) ?_
    refine QProb.equiv_trans (game.earlier_seed_product order setting child joint) ?_
    refine QProb.equiv_trans (FiniteProbRecord.product_probVal _ _ evidence
      (fun seed => event (game.draw child parents seed))) ?_
    apply QProb.mul_congr
    · refine QProb.equiv_trans (game.ticketLaw.map_probVal early evidence) ?_
      exact game.ticketLaw.probVal_congr _ _ (fun ticket => (evidenceSame ticket).symm)
    · exact QProb.equiv_trans (game.ticketLaw.map_probVal _ _)
        (QProb.equiv_trans (FiniteProduct.record_coordinate_probVal_dependent _ game.Seed game.seedFactor child
          (fun seed => event (game.draw child parents seed))) (game.draw_uniform child parents event))
  refine QProb.equiv_trans (QProb.equiv_symm (game.fullUrn_agrees setting _)) ?_
  refine QProb.equiv_trans (game.ticketLaw.map_probVal _ _) ?_
  refine QProb.equiv_trans sourceIdentity ?_
  apply QProb.mul_congr
  · exact QProb.equiv_trans (QProb.equiv_symm (game.ticketLaw.map_probVal _ _))
      (game.fullUrn_agrees setting evidence)
  · exact QProb.equiv_refl _

/-- Only evidence positivity licenses the conditional. The resulting value
may be zero; no positivity of the child event or recipe label is required. -/
theorem conditional_event_recipe (game : CausalUrnGame S P) (order : CausalOrder P.hiddenDAG)
    (setting) (child) (unforced : game.forcedAt setting child = none)
    (parents : game.Parents child) (event : Event (game.Value child))
    (evidence : Event game.FullAssignment)
    (depends : (game.experimentData order).DependsBefore child evidence)
    (fixesParents : ∀ a, evidence a = true → (game.experimentData order).parents child a = parents)
    (supported : 0 < (game.fullUrn setting).probNum evidence) :
    QProb.Equiv ((game.fullUrn setting).condVal
      ((game.experimentData order).nodeEvent child event) evidence supported)
      ((game.contents child parents).probVal event) := by
  have joint := game.fresh_event_joint order setting child unforced parents event evidence depends fixesParents
  have product := QProb.equiv_trans joint (QProb.mul_comm _ _)
  have ratio : QProb.Equiv
      ((game.fullUrn setting).condVal ((game.experimentData order).nodeEvent child event) evidence supported)
      (QProb.div ((game.fullUrn setting).probVal
        (inter ((game.experimentData order).nodeEvent child event) evidence))
        ((game.fullUrn setting).probVal evidence) supported) := by
    simp only [QProb.Equiv, UrnProb.condVal, UrnProb.probVal, QProb.div]
    ac_rfl
  exact QProb.equiv_trans ratio
    (QProb.equiv_trans (QProb.div_congr product (QProb.equiv_refl _) supported supported)
      (by simp only [QProb.Equiv, QProb.div, QProb.mul]; ac_rfl))

/-- **Game → qualitative rules.** Effectiveness follows from skipping the
selected draw. Parent sufficiency follows from freshness after the complete
earlier history. Experimental stability follows because both experiments
use the same recipe at the same parent values. No SCM or Pearl certificate
is supplied, and no supported child event is required to be positive. -/
theorem qualitativeRules (game : CausalUrnGame S P) (order : CausalOrder P.hiddenDAG)
    (scale : Probability.ClaytonWaddington.QualitativeUrnScale) :
    QualitativeCausalRules (game.experimentData order) scale := by
  let data := game.experimentData order
  constructor
  · intro setting child value forced
    change game.forcedAt setting child = some value at forced
    apply (data.eventPlaus_eqv_iff scale setting setting _ _).mpr
    have counts : (game.fullUrn setting).probNum
        (data.nodeEvent child (fun actual => decide (actual = value))) =
        (game.fullUrn setting).probNum topEvent := by
      rw [UrnProb.probNum_eq_cellCount, UrnProb.probNum_eq_cellCount]
      apply count_congr
      intro cell
      change decide (game.read setting (game.superurn.draw cell) child = value) = true
      rw [read, forced]
      exact decide_eq_true rfl
    change (game.fullUrn setting).probNum _ * (game.fullUrn setting).n =
      (game.fullUrn setting).probNum _ * (game.fullUrn setting).n
    rw [counts]
    rfl
  · intro setting child reference event unforced supported
    change game.forcedAt setting child = none at unforced
    apply (data.conditionalPlaus_eqv_iff scale setting setting _ _ _ _ _ _).mpr
    have historyLaw := game.conditional_event_recipe order setting child unforced
      (data.parents child reference) event (data.history child reference)
      (data.history_dependsBefore child reference)
      (fun a selected => data.history_implies_parent child reference a selected |> of_decide_eq_true)
      supported
    have parentLaw := game.conditional_event_recipe order setting child unforced
      (data.parents child reference) event (data.parentEvent child (data.parents child reference))
      (data.parentEvent_dependsBefore child (data.parents child reference))
      (fun _ selected => of_decide_eq_true selected)
      (data.parents_supported_of_history setting child reference supported)
    exact QProb.equiv_trans historyLaw (QProb.equiv_symm parentLaw)
  · intro first second child parents event firstUnforced secondUnforced firstSupported secondSupported
    change game.forcedAt first child = none at firstUnforced
    change game.forcedAt second child = none at secondUnforced
    apply (data.conditionalPlaus_eqv_iff scale first second _ _ _ _ _ _).mpr
    have firstLaw := game.conditional_event_recipe order first child firstUnforced parents event
      (data.parentEvent child parents) (data.parentEvent_dependsBefore child parents)
      (fun _ selected => of_decide_eq_true selected) firstSupported
    have secondLaw := game.conditional_event_recipe order second child secondUnforced parents event
      (data.parentEvent child parents) (data.parentEvent_dependsBefore child parents)
      (fun _ selected => of_decide_eq_true selected) secondSupported
    exact QProb.equiv_trans firstLaw (QProb.equiv_symm secondLaw)

end Thesis.Causality.CausalUrnGame
