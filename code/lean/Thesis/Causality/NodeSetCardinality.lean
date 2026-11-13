import Thesis.Causality.Graph

namespace Thesis
namespace Causality
namespace NodeSet

/-!
# Literal cardinalities of Boolean node selections

Node selections already come with the fixed topological `Fin` enumeration.
Their cardinality is the length of the existing member list, not a quotient
cardinality or the size of a newly chosen enumeration.  These identities
connect that length to finite Boolean counts and to disjoint partitions.

The proofs inspect only membership bits.  In particular a supplied member
proves positivity directly, without an emptiness test on a proposition or
extracting a representative from an existential statement.
-/

variable {S : ObservedSignature}

/-- Count selected indices in exactly the existing topological order. -/
theorem members_length_eq_countP (nodes : NodeSet S) :
    (members nodes).length = (List.finRange S.count).countP nodes := by
  simpa only [members, enumerated, List.finRange] using
    (List.countP_eq_length_filter (p := nodes) (l := List.finRange S.count)).symm

/-- A selection cannot have more members than observed coordinates. -/
theorem members_length_le_count (nodes : NodeSet S) : (members nodes).length <= S.count := by
  rw [members_length_eq_countP]
  simpa only [List.length_finRange] using
    List.countP_le_length (p := nodes) (l := List.finRange S.count)

/-- An explicitly supplied selected coordinate gives a positive length. -/
theorem members_length_positive_of_mem (nodes : NodeSet S) (node : Fin S.count)
    (selected : nodes node = true) : 0 < (members nodes).length := by
  rw [members_length_eq_countP]
  exact List.countP_pos_iff.mpr ⟨node, List.mem_finRange node, selected⟩

private theorem countP_union_of_disjoint (left right : NodeSet S) (disjoint : Disjoint left right)
    (indices : List (Fin S.count)) :
    indices.countP (union left right) = indices.countP left + indices.countP right := by
  induction indices with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons, inductionHypothesis]
      cases selected : left node with
      | false =>
          cases other : right node <;>
            simp only [union, selected, other, Bool.false_or, Bool.false_eq_true, if_false, if_true] <;> omega
      | true =>
          simp only [union, selected, disjoint node selected, Bool.true_or,
            Bool.false_eq_true, if_false, if_true]
          omega

/-- Disjoint member lengths add, even though the topological union list
need not be the written concatenation of the two component lists. -/
theorem members_length_union_of_disjoint (left right : NodeSet S) (disjoint : Disjoint left right) :
    (members (union left right)).length = (members left).length + (members right).length := by
  rw [members_length_eq_countP, members_length_eq_countP, members_length_eq_countP]
  exact countP_union_of_disjoint left right disjoint (List.finRange S.count)

/-- A contained selection and its literal complement within the larger
selection partition that larger member count.  No subtraction is needed. -/
theorem members_length_split_of_subset (smaller larger : NodeSet S) (subset : Subset smaller larger) :
    (members larger).length = (members smaller).length + (members (diff larger smaller)).length := by
  have partition : union smaller (diff larger smaller) = larger := by
    funext node
    cases selected : smaller node with
    | false => simp only [union, diff, selected, Bool.not_false, Bool.and_true, Bool.false_or]
    | true => simp only [union, selected, Bool.true_or, subset node selected]
  have disjoint : Disjoint smaller (diff larger smaller) := by
    intro node selected
    simp only [diff, selected, Bool.not_true, Bool.and_false]
  exact (congrArg (fun nodes => (members nodes).length) partition).symm.trans
    (members_length_union_of_disjoint smaller (diff larger smaller) disjoint)

end NodeSet
end Causality
end Thesis
