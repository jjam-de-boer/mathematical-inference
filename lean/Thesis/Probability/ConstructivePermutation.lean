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

end ConstructivePermutation
end Probability
end Thesis
