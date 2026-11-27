import Thesis.Causality.QualitativeTies
import Thesis.Probability.AffineInterval

namespace Thesis.Causality.QualitativeTies
open Probability

/-!
# Recipe probabilities determine the literal masses

The ordinary urn game may represent its two values using any type equipped
with the supplied equivalence to Bool. Every proof uses the recorded bit and
its inverse, so the formula is about arbitrary games on the matching. At an
unforced child the two parent events partition the tickets. Freshness of the
child draw gives a product on each part before the parts are added. This
argument also evaluates recipes reached only by intervention: it does not
condition on positive observational mass.
-/

variable {n : Nat} {graph : Matching n}
local notation "Game" => CausalUrnGame graph.signature graph.projection

/-- The setting as a partial Boolean reading. This is also convenient in
arithmetization, where a set literal has constant mass. -/
def Experiment.forced (experiment : Experiment n) (node : Fin n) : Option Bool :=
  match experiment with
  | .observe => none
  | .set target value => if node = target then some value else none

theorem Experiment.intervention_value (experiment : Experiment n) (node : Fin n) :
    (experiment.intervention graph).value node = experiment.forced node := by
  cases experiment with
  | observe => rfl
  | set target value =>
    by_cases selected : node = target
    · subst node
      simp [intervention, forced, HardIntervention.set_at_target] <;> rfl
    · rw [intervention, HardIntervention.set_away_from_target _ _ _ _ selected]
      simp [HardIntervention.empty, FiniteLatentSCM.noIntervention, forced, selected] <;> rfl

private theorem forcedAt_eq (game : Game) (experiment : Experiment n) (node : Fin n) :
    game.forcedAt (experiment.intervention graph) node =
      (experiment.forced node).map (game.recordedValue node).backward := by
  have found := graph.fullGraph.observedIndex_observed node
  change graph.fullGraph.observedIndex node = some node at found
  unfold CausalUrnGame.forcedAt
  split
  · rename_i missing
    have impossible := found.symm.trans missing
    cases impossible
  · rename_i index indexed
    change graph.fullGraph.observedIndex node = some index at indexed
    have same := Option.some.inj (found.symm.trans indexed)
    subst index
    rw [Experiment.intervention_value]
    cases experiment.forced node <;> rfl

/-- The recorded literal as a test on the game's own value representation. -/
private def valueTest (game : Game) (node : Fin n) (bit : Bool) : Event (game.Value node) :=
  fun value => decide ((game.recordedValue node).forward value = bit)

/-- Supply a parent tuple from a bit. On an edge its sole coordinate is
that bit. At a root the tuple is empty, independently of the supplied bit. -/
private def rowParents (game : Game) (node : Fin n) (bit : Bool) : game.Parents node :=
  fun source _ => (game.recordedValue source).backward bit

/-- The recipe mass for the specified child bit in the specified parent row.
The input bit can be fixed to false for a root. -/
def recipeMass (game : Game) (node : Fin n) (input output : Bool) : QProb :=
  (game.contents node (rowParents game node input)).probVal (valueTest game node output)

private def ticketTest (game : Game) (experiment : Experiment n) (node : Fin n) (bit : Bool) :
    Event game.Ticket :=
  fun ticket => valueTest game node bit (game.read (experiment.intervention graph) ticket node)

private def ticketMass (game : Game) (experiment : Experiment n) (node : Fin n) (bit : Bool) : QProb :=
  game.ticketLaw.probVal (ticketTest game experiment node bit)

/-- The test of a literal on the actual record is its test on the ticket's
reading. This connects the calculation to the semantic input predicate. -/
private theorem Literal.mass_eq_ticket (literal : Literal n) (game : Game) (experiment : Experiment n) :
    QProb.Equiv ((game.recordUrn (experiment.intervention graph)).probVal (literal.event graph))
      (ticketMass game experiment literal.node literal.value) := by
  refine QProb.equiv_trans (game.superurn.probVal_map _ _) ?_
  exact QProb.equiv_symm (game.ticketLaw.toUrn_agrees _)

private def bitMass (actual wanted : Bool) : QProb :=
  if actual = wanted then QProb.one else QProb.zero

private theorem ticketMass_forced (game : Game) (experiment : Experiment n)
    {node : Fin n} {actual : Bool} (forced : experiment.forced node = some actual) (bit : Bool) :
    QProb.Equiv (ticketMass game experiment node bit) (bitMass actual bit) := by
  have pointwise (ticket : game.Ticket) :
      ticketTest game experiment node bit ticket = decide (actual = bit) := by
    unfold ticketTest
    rw [CausalUrnGame.read, forcedAt_eq, forced]
    change decide ((game.recordedValue node).forward ((game.recordedValue node).backward actual) = bit) = _
    rw [(game.recordedValue node).forward_backward]
    rfl
  refine QProb.equiv_trans (game.ticketLaw.toUrn_agrees _) ?_
  by_cases same : actual = bit
  · rw [bitMass, if_pos same]
    have eventEq : ticketTest game experiment node bit = topEvent := by
      funext ticket
      simpa [topEvent, same] using pointwise ticket
    rw [eventEq]
    exact game.ticketLaw.toUrn.normalization
  · rw [bitMass, if_neg same]
    have eventEq : ticketTest game experiment node bit = bottomEvent := by
      funext ticket
      simpa [bottomEvent, same] using pointwise ticket
    rw [eventEq]
    exact game.ticketLaw.toUrn.probVal_bottom

private theorem unforced_eq (game : Game) (experiment : Experiment n) (node : Fin n)
    (unforced : experiment.forced node = none) :
    game.forcedAt (experiment.intervention graph) node = none := by
  rw [forcedAt_eq, unforced]
  rfl

private theorem readParents_root (game : Game) (experiment : Experiment n) (node : Fin n)
    (root : graph.parent node = none) (ticket : game.Ticket) :
    game.readParents (experiment.intervention graph) ticket node = rowParents game node false := by
  funext source edge
  have impossible : graph.parent node = some source := of_decide_eq_true edge
  rw [root] at impossible
  cases impossible

private theorem ticketMass_root (game : Game) (experiment : Experiment n) (node : Fin n)
    (root : graph.parent node = none) (unforced : experiment.forced node = none) (bit : Bool) :
    QProb.Equiv (ticketMass game experiment node bit) (recipeMass game node false bit) := by
  have testEq (ticket : game.Ticket) : ticketTest game experiment node bit ticket =
      valueTest game node bit (game.draw node (rowParents game node false) (ticket node)) := by
    unfold ticketTest
    rw [CausalUrnGame.read, unforced_eq game experiment node unforced]
    exact congrArg (fun row => valueTest game node bit (game.draw node row (ticket node)))
      (readParents_root game experiment node root ticket)
  apply QProb.equiv_trans (game.ticketLaw.probVal_congr _ _ testEq)
  refine QProb.equiv_trans (FiniteProduct.record_coordinate_probVal_dependent _ game.Seed
    game.seedFactor node (fun seed => valueTest game node bit (game.draw node (rowParents game node false) seed))) ?_
  exact game.draw_uniform node (rowParents game node false) (valueTest game node bit)

private theorem matchesParent (game : Game) (experiment : Experiment n) {node source : Fin n}
    (parent : graph.parent node = some source) (ticket : game.Ticket) (value : Bool) :
    game.readParents (experiment.intervention graph) ticket node = rowParents game node value ↔
      (game.recordedValue source).forward (game.read (experiment.intervention graph) ticket source) = value := by
  have edge : graph.projection.hiddenDAG.edge source node = true := decide_eq_true parent
  constructor
  · intro same
    have readEq := congrFun (congrFun same source) edge
    change game.read (experiment.intervention graph) ticket source =
      (game.recordedValue source).backward value at readEq
    rw [readEq, (game.recordedValue source).forward_backward]
  · intro reading
    funext index incident
    have incidentParent : graph.parent node = some index := of_decide_eq_true incident
    have same := Option.some.inj (incidentParent.symm.trans parent)
    subst index
    change game.read (experiment.intervention graph) ticket source =
      (game.recordedValue source).backward value
    rw [← reading, (game.recordedValue source).backward_forward]

private theorem ticketMass_child_joint (game : Game) (experiment : Experiment n) {node source : Fin n}
    (parent : graph.parent node = some source) (unforced : experiment.forced node = none)
    (input output : Bool) :
    QProb.Equiv (game.ticketLaw.probVal (fun ticket =>
        ticketTest game experiment source input ticket && ticketTest game experiment node output ticket))
      (QProb.mul (ticketMass game experiment source input) (recipeMass game node input output)) := by
  have tests (ticket : game.Ticket) : ticketTest game experiment source input ticket =
      decide (game.readParents (experiment.intervention graph) ticket node = rowParents game node input) := by
    have iff := (matchesParent game experiment parent ticket input).symm
    unfold ticketTest valueTest
    by_cases reading : (game.recordedValue source).forward
        (game.read (experiment.intervention graph) ticket source) = input
    · simp [reading, iff.mp reading]
    · have noRow : game.readParents (experiment.intervention graph) ticket node ≠ rowParents game node input :=
        fun same => reading (iff.mpr same)
      simp [reading, noRow]
  refine QProb.equiv_trans (game.ticketLaw.probVal_congr _ _ (fun ticket =>
    congrArg (fun test => test && ticketTest game experiment node output ticket) (tests ticket))) ?_
  refine QProb.equiv_trans (game.fresh_draw_joint (experiment.intervention graph) node
    (unforced_eq game experiment node unforced) (rowParents game node input) (valueTest game node output)) ?_
  exact QProb.mul_congr (game.ticketLaw.probVal_congr _ _ (fun ticket => (tests ticket).symm))
    (QProb.equiv_refl _)

private theorem ticketMass_split (game : Game) (experiment : Experiment n)
    (node source : Fin n) (output : Bool) :
    QProb.Equiv (ticketMass game experiment node output)
      (QProb.add
        (game.ticketLaw.probVal (fun ticket =>
          ticketTest game experiment source false ticket && ticketTest game experiment node output ticket))
        (game.ticketLaw.probVal (fun ticket =>
          ticketTest game experiment source true ticket && ticketTest game experiment node output ticket))) := by
  let negative := fun ticket =>
    ticketTest game experiment source false ticket && ticketTest game experiment node output ticket
  let positive := fun ticket =>
    ticketTest game experiment source true ticket && ticketTest game experiment node output ticket
  have disjointParts : disjoint negative positive := by
    intro ticket left right
    let reading := (game.recordedValue source).forward (game.read (experiment.intervention graph) ticket source)
    change (decide (reading = false) && ticketTest game experiment node output ticket) = true at left
    change (decide (reading = true) && ticketTest game experiment node output ticket) = true at right
    cases reading <;> simp_all
  have cover : ticketTest game experiment node output = union negative positive := by
    funext ticket
    let reading := (game.recordedValue source).forward (game.read (experiment.intervention graph) ticket source)
    change ticketTest game experiment node output ticket =
      ((decide (reading = false) && _) || (decide (reading = true) && _))
    cases reading <;> simp
  change QProb.Equiv (game.ticketLaw.probVal (ticketTest game experiment node output))
    (QProb.add (game.ticketLaw.probVal negative) (game.ticketLaw.probVal positive))
  rw [cover]
  refine QProb.equiv_trans (game.ticketLaw.toUrn_agrees _) ?_
  refine QProb.equiv_trans (game.ticketLaw.toUrn.finite_additivity _ _ disjointParts) ?_
  exact QProb.add_congr (QProb.equiv_symm (game.ticketLaw.toUrn_agrees _))
    (QProb.equiv_symm (game.ticketLaw.toUrn_agrees _))

/-- A root's recorded mass is its own recipe unless it has been set.
This separates the weights in the child mixture from the two child rows. -/
def rootMass (rows : Fin n → Bool → Bool → QProb) (experiment : Experiment n)
    (node : Fin n) (bit : Bool) : QProb :=
  match experiment.forced node with
  | some value => bitMass value bit
  | none => rows node false bit

private theorem ticketMass_eq_rootMass (game : Game) (experiment : Experiment n) (node : Fin n)
    (root : graph.parent node = none) (bit : Bool) :
    QProb.Equiv (ticketMass game experiment node bit) (rootMass (recipeMass game) experiment node bit) := by
  cases decision : experiment.forced node with
  | none => simpa only [rootMass, decision] using ticketMass_root game experiment node root decision bit
  | some value => simpa only [rootMass, decision] using ticketMass_forced game experiment decision bit

/-- Each literal mass is a constant, a root recipe mass, or a sum of the
products of parent mass and child recipe mass. The same formula covers
observation, settings on this component, and settings in other components. -/
def Literal.massFromRows (literal : Literal n) (graph : Matching n)
    (rows : Fin n → Bool → Bool → QProb) (experiment : Experiment n) : QProb :=
  match experiment.forced literal.node with
  | some value => bitMass value literal.value
  | none => match graph.parent literal.node with
    | none => rows literal.node false literal.value
    | some source => QProb.add
        (QProb.mul (rootMass rows experiment source false) (rows literal.node false literal.value))
        (QProb.mul (rootMass rows experiment source true) (rows literal.node true literal.value))

/-- The polynomial-shaped formula computes the mass of the actual urn-game
literal for every experiment. Null parent events contribute a zero term. -/
theorem Literal.mass_eq_rows (literal : Literal n) (game : Game) (experiment : Experiment n) :
    QProb.Equiv ((game.recordUrn (experiment.intervention graph)).probVal (literal.event graph))
      (literal.massFromRows graph (recipeMass game) experiment) := by
  refine QProb.equiv_trans (literal.mass_eq_ticket game experiment) ?_
  cases decision : experiment.forced literal.node with
  | some value =>
    simpa only [massFromRows, decision] using ticketMass_forced game experiment decision literal.value
  | none =>
    cases relation : graph.parent literal.node with
    | none =>
      simpa only [massFromRows, decision, relation] using
        ticketMass_root game experiment literal.node relation decision literal.value
    | some source =>
      rw [massFromRows, decision, relation]
      refine QProb.equiv_trans (ticketMass_split game experiment literal.node source literal.value) ?_
      apply QProb.add_congr
      · refine QProb.equiv_trans (ticketMass_child_joint game experiment relation decision false literal.value) ?_
        exact QProb.mul_congr (ticketMass_eq_rootMass game experiment source (graph.parentRoot relation) false)
          (QProb.equiv_refl _)
      · refine QProb.equiv_trans (ticketMass_child_joint game experiment relation decision true literal.value) ?_
        exact QProb.mul_congr (ticketMass_eq_rootMass game experiment source (graph.parentRoot relation) true)
          (QProb.equiv_refl _)

/-!
## Exact conversion between finite recipes and bounded rational rates

Only the success rate of each recipe is free. The false mass is its
complement, including for a monochromatic urn. A root consumes just its
false-indexed entry; the extra index lets the executable construction use
one uniform function type for roots and children.
-/

/-- The complement in the original denominator, for a unit-interval rate. -/
def opposite (rate : QProb) : QProb :=
  ⟨rate.den - rate.num, rate.den, rate.den_pos⟩

private theorem opposite_congr {first second : QProb} (same : QProb.Equiv first second) :
    QProb.Equiv (opposite first) (opposite second) := by
  change (first.den - first.num) * second.den = (second.den - second.num) * first.den
  rw [Nat.mul_sub_right_distrib, Nat.mul_sub_right_distrib, same, Nat.mul_comm first.den second.den]

/-- The recipe's rate of true, with the bound witnessed by its finite cell
count. Both endpoints are legal local rates. -/
def Rates (n : Nat) := (node : Fin n) → Bool → {rate : QProb // QProb.LE rate QProb.one}

def ratesOfGame (game : Game) : Rates n := fun node input =>
  ⟨recipeMass game node input true, UrnProb.probVal_le_one _ _⟩

/-- Recover either output's mass from the true rate. -/
def Rates.rowMass (rates : Rates n) (node : Fin n) (input output : Bool) : QProb :=
  if output then (rates node input).val else opposite (rates node input).val

private theorem valueTest_false (game : Game) (node : Fin n) :
    valueTest game node false = complement (valueTest game node true) := by
  funext value
  change decide ((game.recordedValue node).forward value = false) =
    !(decide ((game.recordedValue node).forward value = true))
  cases (game.recordedValue node).forward value <;> rfl

theorem probVal_complement_eq (urn : UrnProb Ω) (event : Event Ω) :
    urn.probVal (complement event) = opposite (urn.probVal event) := by
  have total := count_add_count_complement urn.support event
  rw [urn.support_length] at total
  change urn.probNum event + urn.probNum (complement event) = urn.n at total
  have countEq : urn.probNum (complement event) = urn.n - urn.probNum event := by omega
  unfold UrnProb.probVal opposite
  simp only [countEq]

theorem recipeMass_eq_rate (game : Game) (node : Fin n) (input output : Bool) :
    QProb.Equiv (recipeMass game node input output) ((ratesOfGame game).rowMass node input output) := by
  cases output with
  | true => exact QProb.equiv_refl _
  | false =>
    change QProb.Equiv ((game.contents node (rowParents game node input)).probVal (valueTest game node false)) _
    rw [valueTest_false, probVal_complement_eq]
    exact QProb.equiv_refl _

private def Matching.rowInput (graph : Matching n) (node : Fin n)
    (inputs : graph.fullGraph.ParentValues (fun _ => Bool) node) : Bool :=
  match parent : graph.parent node with
  | none => false
  | some source => inputs source (decide_eq_true parent)

/-- Construct the actual urn game from bounded rational recipes. The
Bernoulli record uses the numerator and its complement as cell counts,
and conversion to an urn retains a positive ticket count at both endpoints. -/
def Matching.gameOfRates (graph : Matching n) (rates : Rates n) :
    CausalUrnGame graph.signature graph.projection where
  Value _ := Bool
  values _ := [false, true]
  complete := by intro _ value; cases value <;> simp
  valueEq _ := inferInstance
  defaultValue _ := false
  recordedValue _ := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  contents node inputs :=
    let rate := rates node (graph.rowInput node inputs)
    (QProb.bernoulliRecord rate.val rate.property).toUrn

private theorem gameOfRates_recipe (graph : Matching n) (rates : Rates n)
    (node : Fin n) (input : Bool) :
    QProb.Equiv (recipeMass (graph.gameOfRates rates) node input true)
      (rates node (if (graph.parent node).isSome then input else false)).val := by
  have success : valueTest (graph.gameOfRates rates) node true = id := by
    funext bit
    cases bit <;> rfl
  have chosen : graph.rowInput node (rowParents (graph.gameOfRates rates) node input) =
      (if (graph.parent node).isSome then input else false) := by
    unfold Matching.rowInput
    split
    · rename_i root
      simp [root]
    · rename_i source child
      simp only [child, Option.isSome_some, if_true]
      rfl
  rw [recipeMass, success]
  let selected := rates node (graph.rowInput node (rowParents (graph.gameOfRates rates) node input))
  change QProb.Equiv ((QProb.bernoulliRecord selected.val selected.property).toUrn.probVal id) _
  refine QProb.equiv_trans (QProb.equiv_symm ((QProb.bernoulliRecord _ _).toUrn_agrees id)) ?_
  refine QProb.equiv_trans (QProb.bernoulliRecord_probVal _ _) ?_
  unfold selected
  rw [chosen]
  exact QProb.equiv_refl _

/-- For roots only the false index is used. Child rows are both available,
even when the parent never reaches one of them in observation. -/
theorem gameOfRates_recipeMass_eq (graph : Matching n) (rates : Rates n)
    (node : Fin n) (input output : Bool) (used : input = false ∨ (graph.parent node).isSome = true) :
    QProb.Equiv (recipeMass (graph.gameOfRates rates) node input output)
      (rates.rowMass node input output) := by
  have trueRate := gameOfRates_recipe graph rates node input
  have indexEq : (if (graph.parent node).isSome then input else false) = input := by
    rcases used with falseInput | child
    · simp [falseInput]
    · simp [child]
  rw [indexEq] at trueRate
  apply QProb.equiv_trans (recipeMass_eq_rate (graph.gameOfRates rates) node input output)
  cases output with
  | true => exact trueRate
  | false => exact opposite_congr trueRate

private theorem Literal.rows_congr (literal : Literal n) (graph : Matching n)
    (first second : Fin n → Bool → Bool → QProb) (experiment : Experiment n)
    (equal : ∀ node input output, (input = false ∨ (graph.parent node).isSome = true) →
      QProb.Equiv (first node input output) (second node input output)) :
    QProb.Equiv (literal.massFromRows graph first experiment) (literal.massFromRows graph second experiment) := by
  have rootCongr (node : Fin n) (bit : Bool) :
      QProb.Equiv (rootMass first experiment node bit) (rootMass second experiment node bit) := by
    cases forced : experiment.forced node with
    | some value => simp only [rootMass, forced]; exact QProb.equiv_refl _
    | none => exact (by simpa only [rootMass, forced] using equal node false bit (.inl rfl))
  unfold massFromRows
  cases forced : experiment.forced literal.node with
  | some value => exact QProb.equiv_refl _
  | none =>
    cases parent : graph.parent literal.node with
    | none => exact equal literal.node false literal.value (.inl rfl)
    | some source =>
      apply QProb.add_congr
      · exact QProb.mul_congr (rootCongr source false) (equal literal.node false literal.value (.inl rfl))
      · exact QProb.mul_congr (rootCongr source true) (equal literal.node true literal.value (.inr (by simp [parent])))

/-- When checking ties there is an exact witness conversion from ordinary
finite rates to the same operational urn semantics used in the input. -/
theorem Literal.mass_gameOfRates (literal : Literal n) (graph : Matching n) (rates : Rates n)
    (experiment : Experiment n) :
    QProb.Equiv (((graph.gameOfRates rates).recordUrn (experiment.intervention graph)).probVal (literal.event graph))
      (literal.massFromRows graph rates.rowMass experiment) :=
  QProb.equiv_trans (literal.mass_eq_rows (graph.gameOfRates rates) experiment)
    (literal.rows_congr graph _ _ _ (gameOfRates_recipeMass_eq graph rates))

theorem Literal.mass_ratesOfGame (literal : Literal n) (game : Game) (experiment : Experiment n) :
    QProb.Equiv ((game.recordUrn (experiment.intervention graph)).probVal (literal.event graph))
      (literal.massFromRows graph (ratesOfGame game).rowMass experiment) :=
  QProb.equiv_trans (literal.mass_eq_rows game experiment)
    (literal.rows_congr graph _ _ _ (fun node input output _ => recipeMass_eq_rate game node input output))

/-- Realizability can be checked against the small row equations, with a
witness in either direction. Independence and experimental stability enter
through the game proof above, rather than through extra numeric input. -/
theorem Instance.realizable_iff_rates (problem : Instance) : problem.Realizable ↔
    ∃ rates : Rates problem.count, ∀ tie ∈ problem.ties,
      QProb.Equiv (tie.left.massFromRows problem.graph rates.rowMass tie.experiment)
        (tie.right.massFromRows problem.graph rates.rowMass tie.experiment) := by
  constructor
  · rintro ⟨game, obeys⟩
    refine ⟨ratesOfGame game, fun tie member => ?_⟩
    exact QProb.equiv_trans (QProb.equiv_symm (tie.left.mass_ratesOfGame game tie.experiment))
      (QProb.equiv_trans (obeys tie member) (tie.right.mass_ratesOfGame game tie.experiment))
  · rintro ⟨rates, obeys⟩
    refine ⟨problem.graph.gameOfRates rates, fun tie member => ?_⟩
    exact QProb.equiv_trans (tie.left.mass_gameOfRates problem.graph rates tie.experiment)
      (QProb.equiv_trans (obeys tie member) (QProb.equiv_symm (tie.right.mass_gameOfRates problem.graph rates tie.experiment)))

end Thesis.Causality.QualitativeTies
