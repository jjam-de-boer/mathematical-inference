import Thesis.Causality.CausalUrnTickets
import Thesis.Probability.Reindexing

namespace Thesis.Causality.CausalUrnGame
open Probability
universe u
variable {S T : ObservedSignature.{u}} {P : FiniteLatentProjection S} {Q : FiniteLatentProjection T}

/-!
# Consistent renaming preserves experiments

A renaming gives actual inverses for node names, value labels and uniform
ticket cells. It preserves declared arrows and the recorded/unrecorded
classification. Its local obligation concerns recipes on arbitrary supplied
parent tuples, not executed records or equality of probability laws.

The projection obligation likewise concerns arbitrary assignments, before
execution. It permits the observed value presentation to change consistently.
We derive the global reading correspondence by acyclic induction and derive
the law correspondence by a permutation of uniformly weighted source cells.
No probability-preservation or SCM-equivalence premise is hidden in the data.
-/

/-- Read only the declared recorded nodes, converting each game label to
the corresponding observed value. Hidden instructions remain part of the
execution even though their readings are absent from this assignment. -/
def project (game : CausalUrnGame S P)
    (assignment : (node : Fin P.hiddenDAG.count) → game.Value node) : S.Assignment :=
  fun i => (game.recordedValue i).forward (assignment (P.hiddenDAG.observedNode i))

/-- A checked isomorphism of the primitive game instructions. Cell bijections
are between the common superurns, not between outcome supports: repeated
labels must remain distinct equally weighted cells. -/
structure Renaming (first : CausalUrnGame S P) (second : CausalUrnGame T Q) where
  nodes : ValueEquivalence (Fin P.hiddenDAG.count) (Fin Q.hiddenDAG.count)
  values : (node : Fin P.hiddenDAG.count) →
    ValueEquivalence (first.Value node) (second.Value (nodes.forward node))
  edges : ∀ parent child, Q.hiddenDAG.edge (nodes.forward parent) (nodes.forward child) = P.hiddenDAG.edge parent child
  classification : ∀ node, Q.hiddenDAG.hidden (nodes.forward node) = P.hiddenDAG.hidden node
  cells : ValueEquivalence (Fin first.superurn.n) (Fin second.superurn.n)
  records : ValueEquivalence S.Assignment T.Assignment
  projection : ∀ left right,
    (∀ node, (values node).forward (left node) = right (nodes.forward node)) →
      records.forward (first.project left) = second.project right
  recipes : ∀ node (left : first.Parents node) (right : second.Parents (nodes.forward node)),
    (∀ parent (sourceEdge : P.hiddenDAG.edge parent node = true)
      (targetEdge : Q.hiddenDAG.edge (nodes.forward parent) (nodes.forward node) = true),
      (values parent).forward (left parent sourceEdge) = right (nodes.forward parent) targetEdge) →
    ∀ cell, (values node).forward
      (first.draw node left (first.superurn.draw cell node)) =
      second.draw (nodes.forward node) right (second.superurn.draw (cells.forward cell) (nodes.forward node))

namespace Renaming
variable {first : CausalUrnGame S P} {second : CausalUrnGame T Q}

/-- Corresponding settings agree locally on forced values after renaming.
This is a check on the declared knobs, not on outcomes of either execution. -/
def SettingsCorrespond (rename : Renaming first second) (left : HardIntervention S) (right : HardIntervention T) : Prop :=
  ∀ node, (first.forcedAt left node).map (rename.values node).forward =
    second.forcedAt right (rename.nodes.forward node)

/-- A consistent local relabelling commutes with the complete execution.
The induction follows the original graph rank; the target may use a different
compatible rank and a different numbering of nodes. -/
theorem read_corresponds (rename : Renaming first second) (left right)
    (settings : rename.SettingsCorrespond left right) (cell) (node) :
    (rename.values node).forward (first.read left (first.superurn.draw cell) node) =
      second.read right (second.superurn.draw (rename.cells.forward cell)) (rename.nodes.forward node) := by
  rw [read, read]
  have forced := settings node
  cases source : first.forcedAt left node with
  | some value =>
    have target : second.forcedAt right (rename.nodes.forward node) = some ((rename.values node).forward value) := by
      simpa only [source, Option.map_some] using forced.symm
    rw [target]
  | none =>
    have target : second.forcedAt right (rename.nodes.forward node) = none := by
      simpa only [source, Option.map_none] using forced.symm
    rw [target]
    apply rename.recipes
    intro parent sourceEdge _targetEdge
    exact rename.read_corresponds left right settings cell parent
termination_by P.hiddenDAG.rank node
decreasing_by exact P.hiddenDAG.edge_rank_lt sourceEdge

/-- The local reading correspondence descends to the complete recorded
assignment through the separately checked projection map. -/
theorem record_corresponds (rename : Renaming first second) (left right)
    (settings : rename.SettingsCorrespond left right) (cell) :
    rename.records.forward (first.record left (first.superurn.draw cell)) =
      second.record right (second.superurn.draw (rename.cells.forward cell)) :=
  rename.projection _ _ (fun node => rename.read_corresponds left right settings cell node)

/-- An explicit cell bijection transports the whole finite enumeration.
The statement allows different numeric cardinality presentations; equality
of those cardinalities follows later from this permutation's length. -/
private theorem cells_perm {n m : Nat} (cells : ValueEquivalence (Fin n) (Fin m)) :
    ((List.finRange n).map cells.forward).Perm (List.finRange m) := by
  apply AdditiveCarrier.perm_of_count_eq_constructive
  intro target
  have pointwise : ∀ cell, (cells.forward cell == target) = (cell == cells.backward target) := by
    intro cell
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro same
      exact beq_iff_eq.mpr ((cells.backward_forward cell).symm.trans
        (congrArg cells.backward (beq_iff_eq.mp same)))
    · intro same
      exact beq_iff_eq.mpr ((congrArg cells.forward (beq_iff_eq.mp same)).trans (cells.forward_backward target))
  calc
    ((List.finRange n).map cells.forward).count target =
        (List.finRange n).countP (fun cell => cells.forward cell == target) := by
      rw [List.count_eq_countP, List.countP_map]
      rfl
    _ = (List.finRange n).countP (fun cell => cell == cells.backward target) := by
      apply List.countP_congr
      intro cell _
      rw [pointwise cell]
    _ = (List.finRange n).count (cells.backward target) := List.count_eq_countP.symm
    _ = 1 := count_finRange _ _
    _ = (List.finRange m).count target := (count_finRange _ _).symm

/-- A bijection of uniform cells preserves counting, even when the two
cell types use different cardinality presentations. Their cardinalities
agree by the proved permutation, rather than by a separate axiom. -/
private theorem uniform_relabel (leftUrn : UrnProb A) (rightUrn : UrnProb B)
    (cells : ValueEquivalence (Fin leftUrn.n) (Fin rightUrn.n))
    (leftEvent : Event A) (rightEvent : Event B)
    (agrees : ∀ cell, leftEvent (leftUrn.draw cell) = rightEvent (rightUrn.draw (cells.forward cell))) :
    QProb.Equiv (leftUrn.probVal leftEvent) (rightUrn.probVal rightEvent) := by
  have permutation := cells_perm cells
  have size : leftUrn.n = rightUrn.n := by simpa only [List.length_map, List.length_finRange] using permutation.length_eq
  have counts : leftUrn.probNum leftEvent = rightUrn.probNum rightEvent := by
    rw [leftUrn.probNum_eq_cellCount, rightUrn.probNum_eq_cellCount]
    change count (List.finRange leftUrn.n) _ = count (List.finRange rightUrn.n) _
    calc
      _ = count (List.finRange leftUrn.n) (fun cell => rightEvent (rightUrn.draw (cells.forward cell))) := count_congr agrees
      _ = count ((List.finRange leftUrn.n).map cells.forward) (fun cell => rightEvent (rightUrn.draw cell)) := by
        unfold count
        rw [List.countP_map]
        rfl
      _ = _ := count_reindex permutation _
  change leftUrn.probNum leftEvent * rightUrn.n = rightUrn.probNum rightEvent * leftUrn.n
  rw [counts, size]

/-- Complete observed-law invariance under consistent renaming, for every
corresponding hard setting and every recorded event. The only probability
step is uniform finite counting after the independently proved execution
correspondence. This includes zero and repeated-label events. -/
theorem law_invariant (rename : Renaming first second) (left right)
    (settings : rename.SettingsCorrespond left right) (event : Event T.Assignment) :
    QProb.Equiv (((first.law left).map rename.records.forward).probVal event)
      ((second.law right).probVal event) := by
  have ticketAgreement := uniform_relabel first.superurn second.superurn rename.cells
    (fun ticket => event (rename.records.forward (first.record left ticket)))
    (fun ticket => event (second.record right ticket))
    (fun cell => congrArg event (rename.record_corresponds left right settings cell))
  -- First compare the independent ticket interpreters. Only after this
  -- counting step do the record-urn agreement theorems identify their laws.
  have urnAgreement := QProb.equiv_trans
    (first.superurn.probVal_map (first.record left) (fun record => event (rename.records.forward record)))
    (QProb.equiv_trans ticketAgreement (QProb.equiv_symm (second.superurn.probVal_map (second.record right) event)))
  exact QProb.equiv_trans ((first.law left).map_probVal _ _)
    (QProb.equiv_trans (first.recordUrn_agrees left _)
      (QProb.equiv_trans urnAgreement (QProb.equiv_symm (second.recordUrn_agrees right event))))

end Renaming

/-- The local renaming conditions are jointly satisfiable for every game;
they do not obtain a vacuous invariance theorem from impossible premises. -/
def Renaming.refl (game : CausalUrnGame S P) : Renaming game game where
  nodes := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  values _ := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  edges _ _ := rfl
  classification _ := rfl
  cells := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  records := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  projection := by
    intro left right agree
    funext node
    exact congrArg (game.recordedValue node).forward (agree (P.hiddenDAG.observedNode node))
  recipes := by
    intro node left right agree cell
    have same : left = right := by
      funext parent edge
      exact agree parent edge edge
    rw [same]
    rfl

end Thesis.Causality.CausalUrnGame
