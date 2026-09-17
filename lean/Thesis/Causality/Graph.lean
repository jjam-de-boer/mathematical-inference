import Std
import Thesis.Probability.Core

namespace Thesis
namespace Causality

open Probability
export Probability (finAll finAny finBeq natBeq_comm natBeq_refl finAll_true
  finAll_congr finAll_eq_true_iff finAny_congr finAny_eq_false_iff
  finAny_eq_true_of finAny_eq_true_iff)

/-!
Finite graph data used by the theorem-facing causal formalization.

The primary representation is an all-directed graph with explicit latent
roots.  A directed-and-bidirected graph over observed variables is derived
from that representation.  The directed relation is Boolean so all edge
tests are computational; structural properties are proof fields.
-/

/--
Observed variables, their value types, and the acyclic directed causal graph.
The natural index order is a chosen topological order.
-/
structure ObservedSignature where
  count : Nat
  Value : Fin count -> Type u
  valueEnumeration : (i : Fin count) -> List (Value i)
  value_complete : forall i value, value ∈ valueEnumeration i
  value_nodup : forall i, (valueEnumeration i).Nodup
  defaultValue : (i : Fin count) -> Value i
  valueDecidableEq : (i : Fin count) -> DecidableEq (Value i)
  directed : Fin count -> Fin count -> Bool
  directed_earlier :
    forall {parent child}, directed parent child = true -> parent.val < child.val

namespace ObservedSignature

instance (S : ObservedSignature) (i : Fin S.count) : DecidableEq (S.Value i) :=
  S.valueDecidableEq i

abbrev Assignment (S : ObservedSignature) :=
  (i : Fin S.count) -> S.Value i

def Prefix (S : ObservedSignature) (k : Nat) (hk : k <= S.count) :=
  (i : Fin k) -> S.Value ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

def ParentValues (S : ObservedSignature) (child : Fin S.count) :=
  (parent : Fin S.count) ->
    S.directed parent child = true -> S.Value parent

/--
Constructive two-value richness of every observed coordinate.

This is data, not a mere existence proof: hedge countermodels must pick two
distinct values without invoking choice.  Completeness of identification is
inhabited only after such a pair is supplied; unary coordinates make a
graphical hedge fail to separate `P(Y | do(X))`.
-/
structure ValueRich (S : ObservedSignature) where
  first : (i : Fin S.count) -> S.Value i
  second : (i : Fin S.count) -> S.Value i
  first_enumerated : forall i, first i ∈ S.valueEnumeration i
  second_enumerated : forall i, second i ∈ S.valueEnumeration i
  different : forall i, first i ≠ second i

end ObservedSignature

/-- A decidable set of observed nodes. -/
abbrev NodeSet (S : ObservedSignature) := Fin S.count -> Bool

namespace NodeSet

def empty : NodeSet S := fun _ => false

def full : NodeSet S := fun _ => true

def singleton (node : Fin S.count) : NodeSet S :=
  fun i => decide (i = node)

theorem singleton_eq_true_iff {S : ObservedSignature}
    (node i : Fin S.count) :
    singleton node i = true ↔ i = node := by
  simp [singleton]

def union (X Y : NodeSet S) : NodeSet S :=
  fun i => X i || Y i

/-- Add one index to a selection. -/
def insert (X : NodeSet S) (node : Fin S.count) : NodeSet S :=
  union X (singleton node)

theorem insert_eq_true_iff (X : NodeSet S) (node i : Fin S.count) :
    insert X node i = true ↔ X i = true ∨ i = node := by
  simp [insert, union, singleton]

def inter (X Y : NodeSet S) : NodeSet S :=
  fun i => X i && Y i

def diff (X Y : NodeSet S) : NodeSet S :=
  fun i => X i && !(Y i)

def Subset (X Y : NodeSet S) : Prop :=
  forall i, X i = true -> Y i = true

theorem Subset.trans {X Y Z : NodeSet S}
    (hXY : Subset X Y) (hYZ : Subset Y Z) : Subset X Z :=
  fun i hi => hYZ i (hXY i hi)

def Disjoint (X Y : NodeSet S) : Prop :=
  forall i, X i = true -> Y i = false

def Meets (X Y : NodeSet S) : Prop :=
  Exists fun i => X i = true /\ Y i = true

/-- Every observed index, in topological `Fin` order. -/
def enumerated (S : ObservedSignature) : List (Fin S.count) :=
  List.ofFn (fun i : Fin S.count => i)

/-- Members of a node set, still in topological order. -/
def members (X : NodeSet S) : List (Fin S.count) :=
  (enumerated S).filter (fun i => X i)

/-- Boolean emptiness: no selected index. -/
def isEmpty (X : NodeSet S) : Bool :=
  (members X).isEmpty

/-- Boolean overlap: some shared selected index. -/
def meetsBool (X Y : NodeSet S) : Bool :=
  !(isEmpty (inter X Y))

/-- Boolean disjointness: no selected index of `X` lies in `Y`. -/
def disjointBool (X Y : NodeSet S) : Bool :=
  (members X).all (fun i => !Y i)

/-- Boolean inclusion, decided by enumerating the smaller set. -/
def subsetBool (X Y : NodeSet S) : Bool :=
  (members X).all (fun i => Y i)

/-- Boolean extensional equality of node sets. -/
def equal (X Y : NodeSet S) : Bool :=
  subsetBool X Y && subsetBool Y X

theorem mem_enumerated (S : ObservedSignature) (i : Fin S.count) :
    i ∈ enumerated S :=
  (List.mem_ofFn).mpr ⟨i, rfl⟩

theorem length_enumerated (S : ObservedSignature) :
    (enumerated S).length = S.count :=
  List.length_ofFn

theorem mem_members_iff (X : NodeSet S) (i : Fin S.count) :
    i ∈ members X ↔ X i = true := by
  simp [members, List.mem_filter, mem_enumerated]

/--
Emptiness is decided by inspecting `members`, not by `List.filter_eq_nil_iff`.
That Init lemma depends on `Classical.choice`; the nil/cons split does not.
-/
theorem isEmpty_eq_true_iff (X : NodeSet S) :
    isEmpty X = true ↔ forall i, X i = false := by
  constructor
  · intro h i
    unfold isEmpty at h
    cases hm : members X with
    | nil =>
        have notMember : i ∉ members X := by simp [hm]
        cases hX : X i
        · rfl
        · exact False.elim (notMember ((mem_members_iff X i).mpr hX))
    | cons _head _tail =>
        simp [hm] at h
  · intro h
    unfold isEmpty
    cases hm : members X with
    | nil => rfl
    | cons head _tail =>
        have hTrue : X head = true :=
          (mem_members_iff X head).mp (by simp [hm])
        exact False.elim (Bool.false_ne_true ((h head).symm.trans hTrue))

theorem isEmpty_empty {S : ObservedSignature} :
    isEmpty (empty : NodeSet S) = true :=
  (isEmpty_eq_true_iff (empty : NodeSet S)).mpr (fun _i => rfl)

theorem subsetBool_eq_true_iff (X Y : NodeSet S) :
    subsetBool X Y = true ↔ Subset X Y := by
  constructor
  · intro h i hi
    have mem := (mem_members_iff X i).mpr hi
    have allTrue : forall j, j ∈ members X -> Y j = true :=
      List.all_eq_true.mp h
    exact allTrue i mem
  · intro h
    refine List.all_eq_true.mpr ?_
    intro i hi
    exact h i ((mem_members_iff X i).mp hi)

theorem equal_eq_true_iff (X Y : NodeSet S) :
    equal X Y = true ↔ X = Y := by
  constructor
  · intro h
    have parts := Bool.and_eq_true_iff.mp h
    have subsetXY : Subset X Y := (subsetBool_eq_true_iff X Y).mp parts.1
    have subsetYX : Subset Y X := (subsetBool_eq_true_iff Y X).mp parts.2
    funext i
    cases hX : X i
    · cases hY : Y i
      · rfl
      · exact False.elim (Bool.false_ne_true (hX.symm.trans (subsetYX i hY)))
    · exact (subsetXY i hX).symm
  · intro h
    subst h
    have reflSubset : Subset X X := fun _i hi => hi
    exact Bool.and_eq_true_iff.mpr
      ⟨(subsetBool_eq_true_iff X X).mpr reflSubset,
        (subsetBool_eq_true_iff X X).mpr reflSubset⟩

theorem inter_empty_left (X : NodeSet S) : inter empty X = empty := by
  funext i
  simp [inter, empty]

theorem inter_full_right (X : NodeSet S) : inter X full = X := by
  funext i
  simp [inter, full]

theorem disjoint_union_of {X Y Z : NodeSet S}
    (disjointY : Disjoint X Y) (disjointZ : Disjoint X Z) :
    Disjoint X (union Y Z) := by
  intro i hi
  simp [union, disjointY i hi, disjointZ i hi]

theorem Disjoint.of_subset_left {X Y Z : NodeSet S}
    (h : Disjoint Y Z) (sub : Subset X Y) : Disjoint X Z :=
  fun i hi => h i (sub i hi)

theorem Meets.of_mem {X Y : NodeSet S} {i : Fin S.count}
    (hX : X i = true) (hY : Y i = true) : Meets X Y :=
  ⟨i, hX, hY⟩

theorem inter_subset_left (X Y : NodeSet S) : Subset (inter X Y) X := by
  intro i hi
  exact (Bool.and_eq_true_iff.mp hi).1

theorem inter_subset_right (X Y : NodeSet S) : Subset (inter X Y) Y := by
  intro i hi
  exact (Bool.and_eq_true_iff.mp hi).2

theorem diff_subset_left (X Y : NodeSet S) : Subset (diff X Y) X := by
  intro i hi
  exact (Bool.and_eq_true_iff.mp hi).1

theorem Disjoint.diff_right (X Y : NodeSet S) : Disjoint (diff X Y) Y := by
  intro i hi
  have parts := Bool.and_eq_true_iff.mp hi
  cases hY : Y i
  · rfl
  · have : (!Y i) = true := parts.2
    simp [hY] at this

/-- A set disjoint from `Z` and contained in `Y` lives in `Y \ Z`. -/
theorem Subset.diff_of_subset_disjoint {X Y Z : NodeSet S}
    (sub : Subset X Y) (disj : Disjoint X Z) : Subset X (diff Y Z) := by
  intro i hi
  refine Bool.and_eq_true_iff.mpr ⟨sub i hi, ?_⟩
  have hZ : Z i = false := disj i hi
  simp [hZ]

/-- Preferred first selected index in topological order, if any. -/
def firstMember (X : NodeSet S) : Option (Fin S.count) :=
  (members X).head?

theorem firstMember_mem {X : NodeSet S} {i : Fin S.count}
    (h : firstMember X = some i) : X i = true := by
  have hx : (members X).head? = some i := by
    simpa [firstMember] using h
  rcases (List.head?_eq_some_iff).mp hx with ⟨_tail, ht⟩
  have mem : i ∈ members X := by simp [ht]
  exact (mem_members_iff X i).mp mem

theorem firstMember_of_not_empty {X : NodeSet S}
    (h : isEmpty X = false) :
    Exists fun i => firstMember X = some i := by
  cases hfm : firstMember X with
  | none =>
      have emptyMembers : members X = [] :=
        (List.head?_eq_none_iff).mp (by simpa [firstMember] using hfm)
      have empty : isEmpty X = true := List.isEmpty_iff.mpr emptyMembers
      exact False.elim (Bool.false_ne_true (h.symm.trans empty))
  | some i => exact ⟨i, rfl⟩

theorem isEmpty_eq_false_iff (X : NodeSet S) :
    isEmpty X = false ↔ Exists fun i => X i = true := by
  constructor
  · intro h
    rcases firstMember_of_not_empty h with ⟨i, hi⟩
    exact ⟨i, firstMember_mem hi⟩
  · intro h
    rcases h with ⟨i, hi⟩
    cases he : isEmpty X with
    | true =>
        have allFalse : X i = false := (isEmpty_eq_true_iff X).mp he i
        exact False.elim (Bool.false_ne_true (allFalse.symm.trans hi))
    | false => rfl

theorem meetsBool_eq_true_iff (X Y : NodeSet S) :
    meetsBool X Y = true ↔ Meets X Y := by
  constructor
  · intro h
    have emptyFalse : isEmpty (inter X Y) = false := by
      cases he : isEmpty (inter X Y) with
      | false => rfl
      | true =>
          simp [meetsBool, he] at h
    rcases (isEmpty_eq_false_iff (inter X Y)).mp emptyFalse with ⟨i, hi⟩
    have parts := Bool.and_eq_true_iff.mp hi
    exact ⟨i, parts.1, parts.2⟩
  · intro h
    rcases h with ⟨i, hX, hY⟩
    have interTrue : inter X Y i = true :=
      Bool.and_eq_true_iff.mpr ⟨hX, hY⟩
    have emptyFalse : isEmpty (inter X Y) = false :=
      (isEmpty_eq_false_iff (inter X Y)).mpr ⟨i, interTrue⟩
    simp [meetsBool, emptyFalse]

theorem disjointBool_eq_true_iff (X Y : NodeSet S) :
    disjointBool X Y = true ↔ Disjoint X Y := by
  constructor
  · intro h i hi
    have mem := (mem_members_iff X i).mpr hi
    have notY : (!Y i) = true := (List.all_eq_true.mp h) i mem
    cases hY : Y i
    · rfl
    · simp [hY] at notY
  · intro h
    refine List.all_eq_true.mpr ?_
    intro i hi
    have hiX : X i = true := (mem_members_iff X i).mp hi
    have hY : Y i = false := h i hiX
    simp [hY]

theorem union_comm (X Y : NodeSet S) : union X Y = union Y X := by
  funext i
  exact Bool.or_comm (X i) (Y i)

theorem union_assoc (X Y Z : NodeSet S) :
    union (union X Y) Z = union X (union Y Z) := by
  funext i
  exact Bool.or_assoc (X i) (Y i) (Z i)

end NodeSet

/-- The observed directed-and-bidirected projection of a latent model. -/
structure ObservedGraph (S : ObservedSignature) where
  bidirected : Fin S.count -> Fin S.count -> Bool
  bidirected_symmetric : forall {i j},
    bidirected i j = true -> bidirected j i = true
  bidirected_irreflexive : forall i, bidirected i i = false

namespace ObservedGraph

def DirectedEdge (_G : ObservedGraph S) (i j : Fin S.count) : Prop :=
  S.directed i j = true

inductive DirectedReachable (G : ObservedGraph S) :
    Fin S.count -> Fin S.count -> Prop
  | refl (i) : DirectedReachable G i i
  | tail {i j k} :
      DirectedReachable G i j -> G.DirectedEdge j k -> DirectedReachable G i k

inductive BidirectedConnected (G : ObservedGraph S) :
    Fin S.count -> Fin S.count -> Prop
  | refl (i) : BidirectedConnected G i i
  | tail {i j k} :
      BidirectedConnected G i j -> G.bidirected j k = true ->
        BidirectedConnected G i k

theorem directed_edge_earlier (G : ObservedGraph S) {i j : Fin S.count}
    (h : G.DirectedEdge i j) : i.val < j.val :=
  S.directed_earlier h

end ObservedGraph

/-- Nodes of the full latent-expanded graph. -/
inductive ExpandedNode (latentCount observedCount : Nat) where
  | latent : Fin latentCount -> ExpandedNode latentCount observedCount
  | observed : Fin observedCount -> ExpandedNode latentCount observedCount
  deriving DecidableEq, Repr

namespace ExpandedNode

def rank : ExpandedNode latentCount observedCount -> Nat
  | latent _ => 0
  | observed i => i.val + 1

end ExpandedNode

/--
The all-directed graph obtained by making latent roots explicit.  There are
no arrows into latent roots.  Observed arrows come from the declared parent
relation and latent-to-observed arrows come from incidence.
-/
def expandedEdge (S : ObservedSignature) (latentCount : Nat)
    (incident : Fin latentCount -> Fin S.count -> Bool) :
    ExpandedNode latentCount S.count -> ExpandedNode latentCount S.count -> Bool
  | .latent l, .observed v => incident l v
  | .observed i, .observed j => S.directed i j
  | _, _ => false

theorem expandedEdge_rank_lt (S : ObservedSignature) (latentCount : Nat)
    (incident : Fin latentCount -> Fin S.count -> Bool)
    {i j : ExpandedNode latentCount S.count}
    (h : expandedEdge S latentCount incident i j = true) :
    i.rank < j.rank := by
  cases i with
  | latent l =>
      cases j with
      | latent l' => simp [expandedEdge] at h
      | observed j => simp [ExpandedNode.rank]
  | observed i =>
      cases j with
      | latent l => simp [expandedEdge] at h
      | observed j =>
          simp [ExpandedNode.rank]
          exact S.directed_earlier h

/--
Hard intervention graph mutilation.  `cut i = true` removes every arrowhead
into observed node `i`, including a projected bidirected arrowhead.
-/
def mutilatedDirected (S : ObservedSignature) (cut : Fin S.count -> Bool)
    (parent child : Fin S.count) : Bool :=
  if cut child then false else S.directed parent child

def mutilatedBidirected (G : ObservedGraph S) (cut : Fin S.count -> Bool)
    (i j : Fin S.count) : Bool :=
  !(cut i) && !(cut j) && G.bidirected i j

theorem mutilatedDirected_earlier (S : ObservedSignature)
    (cut : Fin S.count -> Bool) {parent child}
    (h : mutilatedDirected S cut parent child = true) :
    parent.val < child.val := by
  by_cases hc : cut child = true
  · simp [mutilatedDirected, hc] at h
  · have hcFalse : cut child = false := by
      cases hcut : cut child <;> simp_all
    simp [mutilatedDirected, hcFalse] at h
    exact S.directed_earlier h

theorem mutilatedBidirected_removed_left (G : ObservedGraph S)
    (cut : Fin S.count -> Bool) (i j : Fin S.count)
    (hi : cut i = true) : mutilatedBidirected G cut i j = false := by
  simp [mutilatedBidirected, hi]

end Causality
end Thesis
