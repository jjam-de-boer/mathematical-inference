import Std

namespace Thesis
namespace Causality

/-!
Finite graph data used by the theorem-facing causal formalization.

The primary representation is an all-directed graph with explicit latent
roots.  A directed-and-bidirected graph over observed variables is derived
from that representation.  The directed relation is Boolean so all edge
tests are computational; structural properties are proof fields.
-/

def finAll : (n : Nat) -> (Fin n -> Bool) -> Bool
  | 0, _ => true
  | n + 1, p => finAll n (fun i => p i.castSucc) && p (Fin.last n)

def finAny : (n : Nat) -> (Fin n -> Bool) -> Bool
  | 0, _ => false
  | n + 1, p => finAny n (fun i => p i.castSucc) || p (Fin.last n)

theorem natBeq_comm (left right : Nat) :
    Nat.beq left right = Nat.beq right left := by
  induction left generalizing right with
  | zero => cases right <;> rfl
  | succ left ih =>
      cases right with
      | zero => rfl
      | succ right => exact ih right

theorem natBeq_refl (value : Nat) : Nat.beq value value = true := by
  induction value with
  | zero => rfl
  | succ value ih => exact ih

def finBeq {n : Nat} (left right : Fin n) : Bool :=
  Nat.beq left.val right.val

theorem finAll_true (n : Nat) :
    finAll n (fun _ => true) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finAll, ih]

theorem finAll_congr {n : Nat} {p q : Fin n -> Bool}
    (h : forall i, p i = q i) : finAll n p = finAll n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finAll]
      rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem finAll_eq_true_iff {n : Nat} (p : Fin n -> Bool) :
    finAll n p = true <-> forall i, p i = true := by
  induction n with
  | zero =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        rfl
  | succ n ih =>
      constructor
      · intro h i
        have hparts :
            finAll n (fun j => p j.castSucc) = true /\
              p (Fin.last n) = true := by
          exact Bool.and_eq_true_iff.mp h
        refine Fin.lastCases hparts.2 (fun j => ?_) i
        exact (ih (fun j => p j.castSucc)).mp hparts.1 j
      · intro h
        exact Bool.and_eq_true_iff.mpr
          ⟨(ih (fun j => p j.castSucc)).mpr (fun j => h j.castSucc),
            h (Fin.last n)⟩

theorem finAny_congr {n : Nat} {p q : Fin n -> Bool}
    (h : forall i, p i = q i) : finAny n p = finAny n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finAny]
      rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem finAny_eq_false_iff {n : Nat} (p : Fin n -> Bool) :
    finAny n p = false <-> forall i, p i = false := by
  induction n with
  | zero =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        rfl
  | succ n ih =>
      constructor
      · intro h i
        have hleft : finAny n (fun j => p j.castSucc) = false := by
          cases ha : finAny n (fun j => p j.castSucc) <;>
            cases hb : p (Fin.last n) <;> simp [finAny, ha, hb] at h ⊢
        have hright : p (Fin.last n) = false := by
          cases ha : finAny n (fun j => p j.castSucc) <;>
            cases hb : p (Fin.last n) <;> simp [finAny, ha, hb] at h ⊢
        refine Fin.lastCases hright (fun j => ?_) i
        exact (ih (fun j => p j.castSucc)).mp hleft j
      · intro h
        have hleft : finAny n (fun j => p j.castSucc) = false :=
          (ih (fun j => p j.castSucc)).mpr (fun j => h j.castSucc)
        simp [finAny, hleft, h (Fin.last n)]

theorem finAny_eq_true_of {n : Nat} (p : Fin n -> Bool)
    (i : Fin n) (hi : p i = true) : finAny n p = true := by
  cases hAny : finAny n p with
  | false =>
      have hall := (finAny_eq_false_iff p).mp hAny
      rw [hall i] at hi
      contradiction
  | true => rfl

theorem finAny_eq_true_iff {n : Nat} (p : Fin n -> Bool) :
    finAny n p = true <-> Exists fun i => p i = true := by
  induction n with
  | zero =>
      constructor
      · intro impossible
        simp [finAny] at impossible
      · intro witness
        rcases witness with ⟨i, _⟩
        exact Fin.elim0 i
  | succ n ih =>
      constructor
      · intro h
        simp only [finAny, Bool.or_eq_true] at h
        cases h with
        | inl earlier =>
            rcases (ih (fun i => p i.castSucc)).mp earlier with ⟨i, hi⟩
            exact ⟨i.castSucc, hi⟩
        | inr last => exact ⟨Fin.last n, last⟩
      · intro witness
        rcases witness with ⟨i, hi⟩
        exact finAny_eq_true_of p i hi

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

end ObservedSignature

/-- A decidable set of observed nodes. -/
abbrev NodeSet (S : ObservedSignature) := Fin S.count -> Bool

namespace NodeSet

def empty : NodeSet S := fun _ => false

def singleton (node : Fin S.count) : NodeSet S :=
  fun i => decide (i = node)

def union (X Y : NodeSet S) : NodeSet S :=
  fun i => X i || Y i

def inter (X Y : NodeSet S) : NodeSet S :=
  fun i => X i && Y i

def diff (X Y : NodeSet S) : NodeSet S :=
  fun i => X i && !(Y i)

def Subset (X Y : NodeSet S) : Prop :=
  forall i, X i = true -> Y i = true

def Disjoint (X Y : NodeSet S) : Prop :=
  forall i, X i = true -> Y i = false

def Meets (X Y : NodeSet S) : Prop :=
  Exists fun i => X i = true /\ Y i = true

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
