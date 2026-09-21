import Thesis.Probability.Core

namespace Thesis
namespace Probability
namespace ConstructivePermutation

/-!
# Constructive permutation reconstruction

For lists with decidable equality, matching occurrence counts determine an
explicit `List.Perm`.  The proof recursively moves the first value of the left
list to the front of the right list and cancels the matching occurrence.  It
therefore supplies permutation evidence without appealing to choice.
-/

private theorem perm_cons_erase {A : Type u}
    [BEq A] [LawfulBEq A] {value : A} : ∀ {values : List A},
    value ∈ values → values.Perm (value :: values.erase value) := by
  intro values member
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      by_cases equal : (head == value) = true
      · have headEqual : head = value := LawfulBEq.eq_of_beq equal
        cases headEqual
        rw [List.erase_cons_head]
      · have tailMember : value ∈ tail := by
          rcases List.mem_cons.mp member with headEqual | tailMember
          · cases headEqual
            exact False.elim (equal (beq_self_eq_true value))
          · exact tailMember
        rw [List.erase_cons_tail equal]
        exact ((ih tailMember).cons head).trans
          (List.Perm.swap value head (tail.erase value))

private theorem nil_counts_impossible {A : Type u}
    [BEq A] [LawfulBEq A] {value : A} {rest : List A}
    (countsEqual : ∀ item,
      List.count item [] = List.count item (value :: rest)) : False := by
  have impossible := countsEqual value
  rw [List.count_nil, List.count_cons_self] at impossible
  omega

private theorem member_from_counts {A : Type u}
    [BEq A] [LawfulBEq A] {value : A} {rest right : List A}
    (countsEqual : ∀ item,
      List.count item (value :: rest) = List.count item right) :
    value ∈ right := by
  apply List.count_pos_iff.mp
  rw [← countsEqual value]
  simp

private theorem cancel_front_counts {A : Type u}
    [BEq A] [LawfulBEq A] {value other : A} {rest right : List A}
    (equal : List.count other (value :: rest) = List.count other right)
    (front : right.Perm (value :: right.erase value)) :
    List.count other rest = List.count other (right.erase value) := by
  rw [front.count_eq, List.count_cons, List.count_cons] at equal
  exact Nat.add_right_cancel equal

/--
Reconstruct an explicit list permutation from matching decidable occurrence
counts.  The hypotheses contain all equality data used by the construction.
-/
theorem perm_of_count_eq {A : Type u}
    [BEq A] [LawfulBEq A] : ∀ {left right : List A},
    (∀ value, List.count value left = List.count value right) →
      left.Perm right := by
  intro left
  induction left with
  | nil =>
      intro right countsEqual
      cases right with
      | nil => exact List.Perm.nil
      | cons value rest =>
          exact False.elim (nil_counts_impossible countsEqual)
  | cons value rest ih =>
      intro right countsEqual
      have member := member_from_counts countsEqual
      have front := perm_cons_erase member
      have tailCounts : ∀ other,
          List.count other rest = List.count other (right.erase value) :=
        fun other => cancel_front_counts (countsEqual other) front
      exact ((ih tailCounts).cons value).trans front.symm

/--
Duplicate-free finite enumerations with the same members differ only by a
permutation.  The proof removes the matching head from the right-hand list
and recurses, so it needs neither a selected inverse nor choice.
-/
theorem perm_of_nodup_mem_iff {A : Type u} [BEq A] [LawfulBEq A]
    (left right : List A) (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Perm.refl []
      | cons head tail =>
          have impossible : head ∈ ([] : List A) :=
            (sameMembers head).mpr (by simp)
          exact False.elim (List.not_mem_nil impossible)
  | cons head tail inductionHypothesis =>
      have leftParts := List.nodup_cons.mp leftNodup
      have headMemRight := (sameMembers head).mp (by simp)
      obtain ⟨before, suffix, rightEq⟩ := List.append_of_mem headMemRight
      subst right
      have rightParts := List.nodup_append.mp rightNodup
      have suffixParts := List.nodup_cons.mp rightParts.2.1
      have removedNodup : (before ++ suffix).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨rightParts.1, suffixParts.2, ?_⟩
        intro first firstMem second secondMem same
        exact rightParts.2.2 first firstMem second (by simp [secondMem]) same
      have headNotRemoved : head ∉ before ++ suffix := by
        intro occurs
        simp only [List.mem_append] at occurs
        rcases occurs with inPrefix | inSuffix
        · exact rightParts.2.2 head inPrefix head (by simp) rfl
        · exact suffixParts.1 inSuffix
      have tailMembers : ∀ value,
          value ∈ tail ↔ value ∈ before ++ suffix := by
        intro value
        constructor
        · intro tailMem
          have different : value ≠ head := by
            intro same
            subst value
            exact leftParts.1 tailMem
          have rightMem := (sameMembers value).mp (by simp [tailMem])
          simp only [List.mem_append, List.mem_cons] at rightMem ⊢
          rcases rightMem with inPrefix | same | inSuffix
          · exact Or.inl inPrefix
          · exact False.elim (different same)
          · exact Or.inr inSuffix
        · intro removedMem
          have rightMem : value ∈ before ++ head :: suffix := by
            simp only [List.mem_append, List.mem_cons] at removedMem ⊢
            rcases removedMem with inPrefix | inSuffix
            · exact Or.inl inPrefix
            · exact Or.inr (Or.inr inSuffix)
          have leftMem := (sameMembers value).mpr rightMem
          simp only [List.mem_cons] at leftMem
          rcases leftMem with same | inTail
          · subst value
            exact False.elim (headNotRemoved removedMem)
          · exact inTail
      have tailPerm :=
        inductionHypothesis (before ++ suffix) leftParts.2 removedNodup
          tailMembers
      exact (tailPerm.cons head).trans List.perm_middle.symm

/--
Mapping a duplicate-free list by a function that is injective on that list
preserves duplicate-freeness.  Unlike global injectivity, the hypothesis may
use membership evidence for both source values.
-/
theorem nodup_map_of_injective_on {A : Type u} {B : Type v}
    [BEq B] [LawfulBEq B]
    (forward : A → B) (values : List A)
    (injectiveOn : ∀ left, left ∈ values → ∀ right, right ∈ values →
      forward left = forward right → left = right)
    (nodup : values.Nodup) :
    (values.map forward).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp nodup
      apply List.nodup_cons.mpr
      constructor
      · intro occurs
        rcases List.mem_map.mp occurs with ⟨value, valueMem, equal⟩
        have same := injectiveOn head (by simp) value (by simp [valueMem])
          equal.symm
        exact parts.1 (same ▸ valueMem)
      · apply inductionHypothesis
        · intro left leftMem right rightMem equal
          exact injectiveOn left (by simp [leftMem]) right (by simp [rightMem])
            equal
        · exact parts.2

/--
A duplicate-free finite list cannot be longer than a list containing every
one of its values.  The proof removes one explicit matching occurrence at a
time and therefore does not choose a global embedding.
-/
theorem length_le_of_nodup_subset {A : Type u}
    [BEq A] [LawfulBEq A] : ∀ {left right : List A},
    left.Nodup → (∀ value, value ∈ left → value ∈ right) →
      left.length ≤ right.length := by
  intro left
  induction left with
  | nil => simp
  | cons head tail inductionHypothesis =>
      intro right nodup subset
      have parts := List.nodup_cons.mp nodup
      have headMem := subset head (by simp)
      obtain ⟨before, after, rightEq⟩ := List.append_of_mem headMem
      subst right
      have tailSubset : ∀ value, value ∈ tail → value ∈ before ++ after := by
        intro value valueMem
        have inRight := subset value (by simp [valueMem])
        simp only [List.mem_append, List.mem_cons] at inRight ⊢
        rcases inRight with inBefore | equal | inAfter
        · exact Or.inl inBefore
        · subst value
          exact False.elim (parts.1 valueMem)
        · exact Or.inr inAfter
      have tailLength := inductionHypothesis parts.2 tailSubset
      simp only [List.length_append] at tailLength
      simp only [List.length_cons, List.length_append]
      omega

end ConstructivePermutation
end Probability
end Thesis
