import Thesis.Causality.Reductions
import Thesis.Probability.FiniteFunctionTables
import Init.Data.List.Sort.Lemmas
import Init.Data.List.Nat.Pairwise

namespace Thesis.Causality
open Probability

/-!
# Complete compatible orders for qualitative experimental histories

A graph rank need not distinguish siblings. Conditioning only on smaller
ranks would consequently miss correlations between two same-rank children.
The qualitative rules instead use a COMPLETE linear listing of all nodes,
including unrecorded nodes and unrelated predecessors. Every parent occurs
before its child. This is structural data, not an extra probabilistic axiom.

Sorting the supplied finite graph ranks constructs such a listing. Equal
ranks may be ordered either way; they still occupy distinct list positions.
The eventual representation theorem preserves the same laws for any chosen
compatible listing, without asserting equal raw urn presentations.
-/

structure CausalOrder (H : FiniteHiddenDAG S) where
  nodes : List (Fin H.count)
  distinct : nodes.Nodup
  complete : ∀ node, node ∈ nodes
  parent_before : ∀ parent child, H.edge parent child = true → nodes.idxOf parent < nodes.idxOf child

namespace CausalOrder

/- In this Lean version the general `EquivBEq (Fin n)` instance can be
inferred through order-law proofs containing classical choice. Finite
equality already has an explicit decision procedure, so prove its three
equivalence laws directly instead of importing that unrelated route. -/
local instance finiteEqualityEquivalence (size : Nat) : EquivBEq (Fin size) where
  rfl := by intro value; exact decide_eq_true rfl
  symm := by
    intro first second equal
    have same : first = second := of_decide_eq_true equal
    exact decide_eq_true same.symm
  trans := by
    intro first middle last firstEqual lastEqual
    have firstSame : first = middle := of_decide_eq_true firstEqual
    have lastSame : middle = last := of_decide_eq_true lastEqual
    exact decide_eq_true (firstSame.trans lastSame)

def witness (order : CausalOrder H) : FiniteWitness (Fin H.count) :=
  FiniteWitness.ofList order.nodes order.complete order.distinct

def earlier (order : CausalOrder H) (child : Fin H.count) : List (Fin H.count) :=
  order.nodes.take (order.nodes.idxOf child)

theorem mem_earlier_iff (order : CausalOrder H) (node child : Fin H.count) :
    node ∈ order.earlier child ↔ order.nodes.idxOf node < order.nodes.idxOf child := by
  constructor
  · intro listed
    rcases List.mem_take_iff_getElem.mp listed with ⟨index, bound, same⟩
    have inList : index < order.nodes.length := Nat.lt_of_lt_of_le bound (Nat.min_le_right _ _)
    have sameGet : order.nodes.get ⟨index, inList⟩ = node := by
      simpa only [List.get_eq_getElem] using same
    have atIndex := Probability.idxOf_get_of_nodup order.nodes order.distinct ⟨index, inList⟩
    rw [sameGet] at atIndex
    rw [atIndex]
    exact Nat.lt_of_lt_of_le bound (Nat.min_le_left _ _)
  · intro before
    let codes := order.witness
    apply List.mem_take_iff_getElem.mpr
    refine ⟨(codes.encode node).val, ?_, ?_⟩
    · change order.nodes.idxOf node < min (order.nodes.idxOf child) order.nodes.length
      exact Nat.lt_min.mpr ⟨before, List.idxOf_lt_length_of_mem (order.complete node)⟩
    · change codes.decode (codes.encode node) = node
      exact codes.decode_encode node

private def rankedNodes (H : FiniteHiddenDAG S) : List (Fin H.count) :=
  (List.finRange H.count).mergeSort (fun first second => decide (H.rank first ≤ H.rank second))

private theorem ranked_complete (H : FiniteHiddenDAG S) (node : Fin H.count) : node ∈ rankedNodes H :=
  (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_finRange node)

private theorem ranked_distinct (H : FiniteHiddenDAG S) : (rankedNodes H).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Probability.finRange_nodup H.count)

private theorem ranked_sorted (H : FiniteHiddenDAG S) :
    (rankedNodes H).Pairwise (fun first second => H.rank first ≤ H.rank second) := by
  have sorted := List.pairwise_mergeSort
    (le := fun first second : Fin H.count => decide (H.rank first ≤ H.rank second))
    (fun first middle last hfirst hlast => decide_eq_true
      (Nat.le_trans (of_decide_eq_true hfirst) (of_decide_eq_true hlast)))
    (fun first second => by
      apply Bool.or_eq_true_iff.mpr
      rcases Nat.le_total (H.rank first) (H.rank second) with before | after
      · exact Or.inl (decide_eq_true before)
      · exact Or.inr (decide_eq_true after))
    (List.finRange H.count)
  exact sorted.imp (fun ordered => of_decide_eq_true ordered)

private theorem position_lt_of_rank_lt (H : FiniteHiddenDAG S)
    (parent child : Fin H.count) (rankLt : H.rank parent < H.rank child) :
    (rankedNodes H).idxOf parent < (rankedNodes H).idxOf child := by
  let codes := FiniteWitness.ofList (rankedNodes H) (ranked_complete H) (ranked_distinct H)
  change (codes.encode parent).val < (codes.encode child).val
  by_cases before : (codes.encode parent).val < (codes.encode child).val
  · exact before
  · have different : codes.encode parent ≠ codes.encode child := by
      intro same
      have sameNodes : parent = child :=
        (codes.decode_encode parent).symm.trans ((congrArg codes.decode same).trans (codes.decode_encode child))
      subst parent
      exact (Nat.lt_irrefl _) rankLt
    have reverse : (codes.encode child).val < (codes.encode parent).val := by
      have differentValues : (codes.encode parent).val ≠ (codes.encode child).val :=
        fun same => different (Fin.ext same)
      omega
    have reversedRanks := (List.pairwise_iff_getElem.mp (ranked_sorted H))
      (codes.encode child).val (codes.encode parent).val
      (codes.encode child).isLt (codes.encode parent).isLt reverse
    change H.rank (codes.decode (codes.encode child)) ≤ H.rank (codes.decode (codes.encode parent)) at reversedRanks
    rw [codes.decode_encode, codes.decode_encode] at reversedRanks
    omega

/-- Every supplied finite acyclic graph has an explicit complete compatible
order. No representative or topological sort is selected by choice. -/
def canonical (H : FiniteHiddenDAG S) : CausalOrder H where
  nodes := rankedNodes H
  distinct := ranked_distinct H
  complete := ranked_complete H
  parent_before parent child edge := position_lt_of_rank_lt H parent child (H.edge_rank_lt edge)

/-- Every declared parent is included in the complete earlier history. -/
theorem parent_mem_earlier (order : CausalOrder H) (parent child : Fin H.count)
    (edge : H.edge parent child = true) : parent ∈ order.earlier child := by
  let codes := order.witness
  have before := order.parent_before parent child edge
  apply List.mem_take_iff_getElem.mpr
  refine ⟨(codes.encode parent).val, ?_, ?_⟩
  · change (codes.encode parent).val < min (order.nodes.idxOf child) order.nodes.length
    change order.nodes.idxOf parent < min (order.nodes.idxOf child) order.nodes.length
    exact Nat.lt_min.mpr ⟨before, List.idxOf_lt_length_of_mem (order.complete parent)⟩
  · change codes.decode (codes.encode parent) = parent
    exact codes.decode_encode parent

end CausalOrder
end Thesis.Causality
