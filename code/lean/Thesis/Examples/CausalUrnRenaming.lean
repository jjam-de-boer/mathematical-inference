import Thesis.Examples.CausalUrnGame

namespace Thesis.Examples.CausalUrnRenaming
open Probability Causality
open Thesis.Examples.CausalUrnGame

/-!
# A nontrivial consistent change of value labels

Exchange false and true everywhere in the common-cause game, including its
unrecorded U, both recorded values, and the two primitive random cells. The
recipes still commute on arbitrary parent inputs, not just the observed
support. The general renaming theorem therefore proves full-law invariance
of the relabelled record. This exercises actual renaming data beyond the
identity isomorphism available for every game.
-/

def flip : ValueEquivalence Bool Bool :=
  ⟨Bool.not, Bool.not, by intro value; cases value <;> rfl, by intro value; cases value <;> rfl⟩

def cellFlip (cell : Fin commonCauseGame.superurn.n) : Fin commonCauseGame.superurn.n :=
  ⟨1 - cell.val, by have bound : cell.val < 2 := cell.isLt; change 1 - cell.val < 2; omega⟩

private theorem cellFlip_inverse : ∀ cell, cellFlip (cellFlip cell) = cell := by decide +kernel

def flipRecord (record : (signature false).Assignment) : (signature false).Assignment :=
  fun node => !(record node)

private theorem flipRecord_inverse (record : (signature false).Assignment) :
    flipRecord (flipRecord record) = record := by
  funext node
  exact Bool.not_not _

private def rootParents : commonCauseGame.Parents (0 : Fin 3) := fun _ _ => false

private theorem rootParents_unique (parents : commonCauseGame.Parents (0 : Fin 3)) : parents = rootParents := by
  funext parent edge
  change (fullGraph false).edge parent (0 : Fin 3) = true at edge
  simp [fullGraph] at edge

private theorem root_recipe_flip : ∀ cell,
    Bool.not (commonCauseGame.draw (0 : Fin 3) rootParents (commonCauseGame.superurn.draw cell (0 : Fin 3))) =
      commonCauseGame.draw (0 : Fin 3) rootParents
        (commonCauseGame.superurn.draw (cellFlip cell) (0 : Fin 3)) := by decide +kernel

private theorem node_cases (node : Fin 3) : node = 0 ∨ node = 1 ∨ node = 2 := by
  have bound := node.isLt
  by_cases zero : node.val = 0
  · exact Or.inl (Fin.ext zero)
  · by_cases one : node.val = 1
    · exact Or.inr (Or.inl (Fin.ext one))
    · exact Or.inr (Or.inr (Fin.ext (by change node.val = 2; omega)))

/-- The complete local obligations: wiring and hidden status are fixed,
values and primitive cells are bijectively renamed, and every recipe commutes
with those renamings for all of its input tuples. -/
def flipRenaming : Causality.CausalUrnGame.Renaming commonCauseGame commonCauseGame where
  nodes := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  values _ := flip
  edges _ _ := rfl
  classification _ := rfl
  cells := ⟨cellFlip, cellFlip, cellFlip_inverse, cellFlip_inverse⟩
  records := ⟨flipRecord, flipRecord, flipRecord_inverse, flipRecord_inverse⟩
  projection := by
    intro left right agree
    funext node
    exact agree ((projection false).hiddenDAG.observedNode node)
  recipes := by
    intro node left right agree cell
    rcases node_cases node with rfl | rfl | rfl
    · change Bool.not (commonCauseGame.draw (0 : Fin 3) left (commonCauseGame.superurn.draw cell (0 : Fin 3))) =
        commonCauseGame.draw (0 : Fin 3) right (commonCauseGame.superurn.draw (cellFlip cell) (0 : Fin 3))
      rw [rootParents_unique left, rootParents_unique right]
      exact root_recipe_flip cell
    · change Bool.not (left (0 : Fin 3) (by decide +kernel)) = right (0 : Fin 3) (by decide +kernel)
      exact agree (0 : Fin 3) (by decide +kernel) (by decide +kernel)
    · change Bool.not (left (0 : Fin 3) (by decide +kernel)) = right (0 : Fin 3) (by decide +kernel)
      exact agree (0 : Fin 3) (by decide +kernel) (by decide +kernel)

/-- Every observed event is preserved after applying the declared record
relabeling. Equality follows from local recipe compatibility and source-cell
counting, rather than from a separate finite calculation of every event. -/
theorem negated_observational_law (event : Event (signature false).Assignment) :
    QProb.Equiv (((commonCauseGame.law (idle false)).map flipRecord).probVal event)
      ((commonCauseGame.law (idle false)).probVal event) :=
  flipRenaming.law_invariant (idle false) (idle false) (by
    intro node
    have unforced : commonCauseGame.forcedAt (idle false) node = none := by
      unfold Causality.CausalUrnGame.forcedAt
      split <;> rfl
    change (commonCauseGame.forcedAt (idle false) node).map Bool.not =
      commonCauseGame.forcedAt (idle false) node
    simp only [unforced]
    rfl) event

end Thesis.Examples.CausalUrnRenaming
