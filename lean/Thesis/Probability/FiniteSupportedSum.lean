import Thesis.Probability.ConstructivePermutation

namespace Thesis
namespace Probability
namespace FiniteSupportedSum

/-!
# Exact elimination of zero terms from a finite integer sum

A complete expansion can contain many terms that integrate to zero.  A
shorter list of canonical terms gives the same literal sum only after its
membership, uniqueness and zero-outside facts are proved.  In particular,
dropping duplicates is not valid when the complete expansion counts them.

The theorem below retains those obligations explicitly.  Equality decisions
are supplied for the finite labels; no proposition about semantic nonzeroness
is decided classically.  Integers are auxiliary integrands, not signed
probability weights or a change in the underlying finite-record semantics.
-/

private theorem sum_perm {left right : List Int} (permutation : left.Perm right) : left.sum = right.sum := by
  induction permutation with
  | nil => rfl
  | cons value _ inductionHypothesis => simp only [List.sum_cons, inductionHypothesis]
  | swap left right rest => exact Int.add_left_comm _ _ _
  | trans _ _ leftEqual rightEqual => exact leftEqual.trans rightEqual

private theorem sum_filter (values : List α) (keep : α -> Bool) (term : α -> Int)
    (zero : forall value, value ∈ values -> keep value = false -> term value = 0) :
    (values.map term).sum = ((values.filter keep).map term).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      have tailZero : forall item, item ∈ rest -> keep item = false -> term item = 0 :=
        fun item member absent => zero item (List.mem_cons_of_mem value member) absent
      cases selected : keep value with
      | true => simp only [List.map_cons, List.sum_cons, List.filter_cons, selected, if_true,
          inductionHypothesis tailZero]
      | false => simp only [List.map_cons, List.sum_cons, List.filter_cons, selected, Bool.false_eq_true,
          if_false, zero value List.mem_cons_self selected, Int.zero_add, inductionHypothesis tailZero]

/-- A repetition-free sublist of canonical terms has the same exact sum
as a repetition-free complete list when every omitted term is proved zero.
Only membership in the supplied finite canonical list is tested. -/
theorem sum_eq_of_zero_outside {α : Type u} [DecidableEq α] (complete canonical : List α)
    (completeNodup : complete.Nodup) (canonicalNodup : canonical.Nodup)
    (included : forall value, value ∈ canonical -> value ∈ complete) (term : α -> Int)
    (zero : forall value, value ∈ complete -> value ∉ canonical -> term value = 0) :
    (complete.map term).sum = (canonical.map term).sum := by
  let keep := fun value => decide (value ∈ canonical)
  have filteredNodup := List.Pairwise.filter keep completeNodup
  have same : forall value, value ∈ complete.filter keep ↔ value ∈ canonical := by
    intro value
    constructor
    · intro member
      exact of_decide_eq_true (List.mem_filter.mp member).2
    · intro member
      exact List.mem_filter.mpr ⟨included value member, decide_eq_true member⟩
  have permutation := ConstructivePermutation.perm_of_nodup_mem_iff
    (complete.filter keep) canonical filteredNodup canonicalNodup same
  refine (sum_filter complete keep term ?_).trans (sum_perm (permutation.map term))
  intro value member absent
  exact zero value member (of_decide_eq_false absent)

end FiniteSupportedSum
end Probability
end Thesis
