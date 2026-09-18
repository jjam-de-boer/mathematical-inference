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

/-- A selected index is the singleton of that index, as a subset. -/
theorem singleton_subset_of_mem {X : NodeSet S} {i : Fin S.count}
    (h : X i = true) : Subset (singleton i) X := by
  intro j hj
  have heq : j = i := (singleton_eq_true_iff i j).mp hj
  exact heq ▸ h

/-- Every set is contained in a union on the left. -/
theorem subset_union_left (X Y : NodeSet S) : Subset X (union X Y) := by
  intro i hx
  simp [union, hx]

/-- Every set is contained in a union on the right. -/
theorem subset_union_right (X Y : NodeSet S) : Subset Y (union X Y) := by
  intro i hy
  simp [union, hy]

/-- A union stays inside any set that contains both sides. -/
theorem union_subset {X Y Z : NodeSet S}
    (hX : Subset X Z) (hY : Subset Y Z) : Subset (union X Y) Z := by
  intro i hi
  cases hx : X i with
  | true =>
      exact hX i hx
  | false =>
      have hy : Y i = true := by
        simp [union, hx] at hi
        exact hi
      exact hY i hy

def Disjoint (X Y : NodeSet S) : Prop :=
  forall i, X i = true -> Y i = false

/-- The empty selection is disjoint from every set: it contributes no true
index that could land in the other side. -/
theorem disjoint_empty_left (X : NodeSet S) : Disjoint empty X := by
  intro i hi
  simp [empty] at hi

/-- Every set is disjoint from the empty selection: the right-hand side is
never true. -/
theorem disjoint_empty_right (X : NodeSet S) : Disjoint X empty := by
  intro i _hi
  rfl

/-- A set is disjoint from its complement inside any ambient selection:
membership in `Y` forces the difference bit off. -/
theorem disjoint_diff (X Y : NodeSet S) : Disjoint Y (diff X Y) := by
  intro i hY
  simp [diff, hY]

/-- The complementary orientation: nothing in `X \ Y` lies in `Y`.
Rule 1 inserting extra chain-rule predecessors uses this side of the
cut, without a general `Disjoint` symmetry lemma. -/
theorem disjoint_diff_right (X Y : NodeSet S) : Disjoint (diff X Y) Y := by
  intro i hi
  simp [diff] at hi
  cases hY : Y i with
  | false =>
      rfl
  | true =>
      simp [hY] at hi

/-- Distinct singletons are disjoint: the unique true index of the
left-hand side cannot be the unique true index of the right. -/
theorem disjoint_singletons_of_ne {S : ObservedSignature}
    {i j : Fin S.count} (hne : i ≠ j) :
    Disjoint (singleton i) (singleton j) := by
  intro k hk
  have heq : k = i := (singleton_eq_true_iff i k).mp hk
  cases hj : singleton j k with
  | false =>
      rfl
  | true =>
      have kj : k = j := (singleton_eq_true_iff j k).mp hj
      exact False.elim (hne (heq.symm.trans kj))

/-- Shrink the right-hand set of a disjointness along a subset. -/
theorem disjoint_of_subset_right {X Y Z : NodeSet S}
    (hdis : Disjoint X Y) (hsub : Subset Z Y) : Disjoint X Z := by
  intro i hX
  cases hZ : Z i with
  | false =>
      rfl
  | true =>
      exact False.elim
        (Bool.false_ne_true ((hdis i hX).symm.trans (hsub i hZ)))

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

/-- The head of a nonempty member list is selected. -/
theorem mem_of_members_cons {X : NodeSet S} {head : Fin S.count}
    {tail : List (Fin S.count)} (h : members X = head :: tail) :
    X head = true :=
  (mem_members_iff X head).mp (by simp [h])

/-- Dropping the first matching element of a Boolean filter, once that
element does not reappear in the leftover tail. -/
theorem filter_erase_head {α} [DecidableEq α] (p : α -> Bool) :
    forall (l : List α) {head : α} {tail : List α},
      l.filter p = head :: tail ->
        (forall x, x ∈ tail -> x ≠ head) ->
          l.filter (fun x => p x && !decide (x = head)) = tail := by
  intro l head tail h huniq
  induction l with
  | nil =>
      simp [List.filter] at h
  | cons x xs ih =>
      cases hx : p x with
      | false =>
          simp [List.filter, hx] at h ⊢
          exact ih h
      | true =>
          simp [List.filter, hx] at h
          have hxeq : x = head := h.1
          have htail : xs.filter p = tail := h.2
          have hskip : decide (x = head) = true := by
            simp [hxeq]
          simp [List.filter, hx, hskip]
          refine (List.filter_congr ?_).trans htail
          intro y hy
          cases hp : p y with
          | false =>
              simp
          | true =>
              have yin : y ∈ tail := by
                rw [← htail]
                exact List.mem_filter.mpr ⟨hy, hp⟩
              have hne : y ≠ head := huniq y yin
              simp [hne]

/-- `List.ofFn` of an injective encoding has no duplicate entries. -/
theorem nodup_ofFn_injective {α : Type _} {n : Nat} {f : Fin n -> α}
    (hinj : forall i j, f i = f j -> i = j) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ]
      refine List.Pairwise.cons ?_ ?_
      · intro x hx heq
        rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
        have h0 : (0 : Fin (n + 1)) = Fin.succ i := hinj _ _ heq
        exact Nat.succ_ne_zero i.val (congrArg Fin.val h0).symm
      · exact ih (fun i j hij =>
          Fin.eq_of_val_eq (by
            have hval :=
              congrArg Fin.val (hinj (Fin.succ i) (Fin.succ j) hij)
            simpa [Fin.val_succ] using hval))

/-- The topological enumeration lists each index once. -/
theorem nodup_enumerated (S : ObservedSignature) :
    (enumerated S).Nodup := by
  unfold enumerated
  exact nodup_ofFn_injective fun _ _ h => h

/-- Boolean filtering preserves uniqueness of the ambient list. -/
theorem nodup_filter {α} (p : α -> Bool) {l : List α} (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil =>
      simp [List.filter]
  | cons x xs ih =>
      have hnd := List.pairwise_cons.mp h
      cases hx : p x with
      | false =>
          have heq : (x :: xs).filter p = xs.filter p := by
            simp [List.filter, hx]
          rw [heq]
          exact ih hnd.2
      | true =>
          have heq : (x :: xs).filter p = x :: xs.filter p := by
            simp [List.filter, hx]
          rw [heq]
          refine List.Pairwise.cons ?_ (ih hnd.2)
          intro y hy heqxy
          exact hnd.1 y (List.mem_filter.mp hy).1 heqxy

/-- Selected indices never repeat: they are a filter of the injective
topological enumeration. -/
theorem nodup_members (X : NodeSet S) : (members X).Nodup :=
  nodup_filter _ (nodup_enumerated S)

/-- Peeling the earliest selected index leaves the member tail. -/
theorem members_diff_of_cons {X : NodeSet S} {head : Fin S.count}
    {tail : List (Fin S.count)} (h : members X = head :: tail) :
    members (diff X (singleton head)) = tail := by
  have huniq : forall x, x ∈ tail -> x ≠ head := by
    intro x hx heq
    have hnd := nodup_members X
    rw [h] at hnd
    exact (List.pairwise_cons.mp hnd).1 x hx heq.symm
  have hfilter :=
    filter_erase_head (fun i => X i) (enumerated S) h huniq
  unfold members diff
  change (enumerated S).filter (fun i => X i && !decide (i = head)) = tail
  simpa [singleton] using hfilter

/-- Peeling strictly decreases the member-list length, so successive
product-splits are well-founded. -/
theorem length_members_diff_of_cons {X : NodeSet S} {head : Fin S.count}
    {tail : List (Fin S.count)} (h : members X = head :: tail) :
    (members (diff X (singleton head))).length < (members X).length := by
  rw [members_diff_of_cons h, h]
  exact Nat.lt_succ_self _

/-- Filtering never grows a list. -/
theorem length_filter_le {α} (p : α -> Bool) :
    forall (l : List α), (l.filter p).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: xs => by
      cases hx : p x with
      | false =>
          have heq : (x :: xs).filter p = xs.filter p := by
            simp [List.filter, hx]
          rw [heq]
          exact Nat.le_succ_of_le (length_filter_le p xs)
      | true =>
          have heq : (x :: xs).filter p = x :: xs.filter p := by
            simp [List.filter, hx]
          rw [heq]
          exact Nat.succ_le_succ (length_filter_le p xs)

/-- A false witness makes a Boolean filter strictly shorter. -/
theorem length_filter_lt_of_mem_false {α} (p : α -> Bool) :
    forall (l : List α) {a : α}, a ∈ l -> p a = false ->
      (l.filter p).length < l.length
  | [], a, hmem, _ => False.elim (List.not_mem_nil hmem)
  | x :: xs, a, hmem, hpfalse => by
      cases hx : p x with
      | false =>
          have heq : (x :: xs).filter p = xs.filter p := by
            simp [List.filter, hx]
          rw [heq]
          exact Nat.lt_succ_of_le (length_filter_le p xs)
      | true =>
          have hne : a ≠ x := by
            intro heq
            exact Bool.false_ne_true (hpfalse.symm.trans (heq ▸ hx))
          have hat : a ∈ xs := by
            rcases List.mem_cons.mp hmem with heq | hxs
            · exact False.elim (hne heq)
            · exact hxs
          have heq : (x :: xs).filter p = x :: xs.filter p := by
            simp [List.filter, hx]
          rw [heq]
          exact Nat.succ_lt_succ
            (length_filter_lt_of_mem_false p xs hat hpfalse)

/-- Members of an intersection are the members of `X` that also lie in
`Y`.  Nested 4.3 shrinks the action along this filter. -/
theorem members_inter (X Y : NodeSet S) :
    members (inter X Y) = (members X).filter (fun i => Y i) := by
  have aux :
      forall l : List (Fin S.count),
        l.filter (fun i => X i && Y i) =
          (l.filter (fun i => X i)).filter (fun i => Y i) := by
    intro l
    induction l with
    | nil =>
        simp [List.filter]
    | cons i rest ih =>
        cases hX : X i <;> cases hY : Y i <;> simp [List.filter, hX, hY, ih]
  unfold members inter
  exact aux (enumerated S)

/-- A nonempty complementary cut `X \ Y` strictly shortens `X ∩ Y`.
Recursive 4.3 uses this as a well-founded measure on the action. -/
theorem length_members_inter_lt_of_diff_nonempty {X Y : NodeSet S}
    (h : isEmpty (diff X Y) = false) :
    (members (inter X Y)).length < (members X).length := by
  cases hm : members (diff X Y) with
  | nil =>
      have hempty : isEmpty (diff X Y) = true := by
        unfold isEmpty
        simp [hm]
      exact False.elim (Bool.false_ne_true (h.symm.trans hempty))
  | cons i _tail =>
      have hmemDiff : diff X Y i = true := mem_of_members_cons hm
      have hX : X i = true := (Bool.and_eq_true_iff.mp hmemDiff).1
      have hY : Y i = false := by
        have hn : (!Y i) = true := (Bool.and_eq_true_iff.mp hmemDiff).2
        cases hYi : Y i with
        | false =>
            rfl
        | true =>
            simp [hYi] at hn
      have hmem : i ∈ members X := (mem_members_iff X i).mpr hX
      rw [members_inter]
      exact length_filter_lt_of_mem_false (fun j => Y j) (members X) hmem hY

/-- A singleton member list names every selected index. -/
theorem eq_of_members_singleton {X : NodeSet S} {i j : Fin S.count}
    (h : members X = [i]) (hj : X j = true) : j = i := by
  have mem : j ∈ members X := (mem_members_iff X j).mpr hj
  simp [h] at mem
  exact mem

/-- A one-element member list is the singleton of that index. -/
theorem eq_singleton_of_members {X : NodeSet S} {i : Fin S.count}
    (h : members X = [i]) : X = singleton i := by
  funext j
  cases hX : X j with
  | false =>
      cases hY : singleton i j with
      | false =>
          rfl
      | true =>
          have heq : j = i := (singleton_eq_true_iff i j).mp hY
          have hi : X i = true :=
            (mem_members_iff X i).mp (by simp [h])
          have hj : X j = true := heq ▸ hi
          exact False.elim (Bool.false_ne_true (hX.symm.trans hj))
  | true =>
      have heq : j = i := eq_of_members_singleton h hX
      exact ((singleton_eq_true_iff i j).mpr heq).symm

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

/-- Boolean emptiness is extensional emptiness.  The empty-action ID
base case uses this to replace a query action by `empty` without
choice: the Boolean test already enumerated the members. -/
theorem eq_empty_of_isEmpty {X : NodeSet S} (h : isEmpty X = true) :
    X = empty := by
  funext i
  exact (isEmpty_eq_true_iff X).mp h i

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

/-- A union is disjoint from `X` once both sides are.  The complementary
orientation of `disjoint_union_of`, used by a three-vertex chain-rule
split whose summed block is `{i, k}`. -/
theorem disjoint_union_left_of {X Y Z : NodeSet S}
    (disjointY : Disjoint Y X) (disjointZ : Disjoint Z X) :
    Disjoint (union Y Z) X := by
  intro i hi
  cases hY : Y i with
  | true =>
      exact disjointY i hY
  | false =>
      have hZ : Z i = true := by
        simp [union, hY] at hi
        exact hi
      exact disjointZ i hZ

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

theorem Disjoint.diff_left (X Y : NodeSet S) : Disjoint Y (diff X Y) := by
  intro i hi
  cases hd : diff X Y i with
  | false =>
      rfl
  | true =>
      have hY : Y i = false := Disjoint.diff_right X Y i hd
      exact False.elim (Bool.false_ne_true (hY.symm.trans hi))

/-- The kept slice `X ∩ H` is disjoint from the complementary cut `X \ H`.
Rule 3 shrinking an intervention from `X` to `X ∩ H` uses this pairwise
obligation. -/
theorem disjoint_inter_diff (X Y : NodeSet S) :
    Disjoint (inter X Y) (diff X Y) :=
  Disjoint.of_subset_left (Disjoint.diff_left X Y) (inter_subset_right X Y)

theorem inter_eq_of_subset {X Y : NodeSet S} (h : Subset X Y) :
    inter Y X = X := by
  funext i
  cases hY : Y i with
  | false =>
      cases hX : X i with
      | false =>
          simp [inter, hY, hX]
      | true =>
          exact False.elim (Bool.false_ne_true (hY.symm.trans (h i hX)))
  | true =>
      simp [inter, hY]

theorem diff_diff (X Y : NodeSet S) : diff X (diff X Y) = inter X Y := by
  funext i
  cases hX : X i with
  | false =>
      simp [diff, inter, hX]
  | true =>
      cases hY : Y i <;> simp [diff, inter, hX, hY]

theorem diff_inter (X Y : NodeSet S) :
    diff X (inter X Y) = diff X Y := by
  funext i
  cases hX : X i with
  | false =>
      simp [diff, inter, hX]
  | true =>
      cases hY : Y i <;> simp [diff, inter, hX, hY]

/-- Complementary cut of `Y` through `X`: the kept slice and the deleted
slice recover `X`.  Rule 3's left kernel `P(Y | do((X ∩ H) ∪ (X \ H)))`
is therefore the original `P(Y | do(X))`. -/
theorem union_inter_diff (X Y : NodeSet S) :
    union (inter X Y) (diff X Y) = X := by
  funext i
  cases hX : X i with
  | false =>
      simp [union, inter, diff, hX]
  | true =>
      cases hY : Y i <;> simp [union, inter, diff, hX, hY]

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

/--
The first selected index, as data.  `firstMember` is computed from the
member list independently of any `Exists` proof that the set is inhabited;
the `none` branch is `False` because emptiness is the Boolean `isEmpty`.
This is the constructive substitute for unpacking `Exists` into `Type`.
-/
def getMember (X : NodeSet S) (h : isEmpty X = false) : Fin S.count :=
  match hfm : firstMember X with
  | some i => i
  | none =>
      False.elim (by
        have emptyMembers : members X = [] :=
          (List.head?_eq_none_iff).mp (by simpa [firstMember] using hfm)
        have empty : isEmpty X = true := List.isEmpty_iff.mpr emptyMembers
        exact Bool.false_ne_true (h.symm.trans empty))

theorem getMember_eq_some (X : NodeSet S) (h : isEmpty X = false) :
    firstMember X = some (getMember X h) := by
  unfold getMember
  split
  · next i hfm => exact hfm
  · next hfm =>
      have emptyMembers : members X = [] :=
        (List.head?_eq_none_iff).mp (by simpa [firstMember] using hfm)
      have empty : isEmpty X = true := List.isEmpty_iff.mpr emptyMembers
      exact False.elim (Bool.false_ne_true (h.symm.trans empty))

theorem getMember_mem (X : NodeSet S) (h : isEmpty X = false) :
    X (getMember X h) = true :=
  firstMember_mem (getMember_eq_some X h)

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

/-- Boolean overlap is exactly non-emptiness of the intersection. -/
theorem isEmpty_inter_eq_false_of_meetsBool {X Y : NodeSet S}
    (h : meetsBool X Y = true) :
    isEmpty (inter X Y) = false := by
  cases he : isEmpty (inter X Y) with
  | false => rfl
  | true => simp [meetsBool, he] at h

/--
A shared index of `X` and `Y`, recovered from the intersection's member
list.  The Boolean `meetsBool` is the emptiness test; no `Meets`/`Exists`
unpacking into `Type` is required.
-/
def getMeeting (X Y : NodeSet S) (h : meetsBool X Y = true) : Fin S.count :=
  getMember (inter X Y) (isEmpty_inter_eq_false_of_meetsBool h)

theorem getMeeting_left {X Y : NodeSet S} (h : meetsBool X Y = true) :
    X (getMeeting X Y h) = true :=
  (Bool.and_eq_true_iff.mp
    (getMember_mem (inter X Y) (isEmpty_inter_eq_false_of_meetsBool h))).1

theorem getMeeting_right {X Y : NodeSet S} (h : meetsBool X Y = true) :
    Y (getMeeting X Y h) = true :=
  (Bool.and_eq_true_iff.mp
    (getMember_mem (inter X Y) (isEmpty_inter_eq_false_of_meetsBool h))).2

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

/-- `X ∪ ∅ = X`.  Conditioning writes the given set as `Z ∪ W`; the
empty-`W` case of IDC is the kernel `P(Y | Z)` itself. -/
theorem union_empty_right (X : NodeSet S) : union X empty = X := by
  funext i
  simp [union, empty]

/-- `∅ ∪ X = X`. -/
theorem union_empty_left (X : NodeSet S) : union empty X = X := by
  funext i
  simp [union, empty]

/-- `X \ ∅ = X`.  Empty-outcome ID writes the complementary sum as
`∑_V P(V)`. -/
theorem diff_empty (X : NodeSet S) : diff X empty = X := by
  funext i
  simp [diff, empty]

/-- `X \ X = ∅`.  Singleton 4.2 writes a complementary sum whose
summed block is empty once the free c-component is the outcome. -/
theorem diff_self (X : NodeSet S) : diff X X = empty := by
  funext i
  cases h : X i <;> simp [diff, empty, h]

/-- `Y ∪ (V \ Y) = V`.  Do-calculus marginalization writes the joint as
the union of the kept outcome and the summed-out complement; the ID
engine writes the same joint as `P(V)`.  The two kernels agree once
this covering is substituted. -/
theorem union_diff_full (X : NodeSet S) :
    union X (diff full X) = full := by
  funext i
  cases h : X i <;> simp [union, diff, full, h]

/--
If `Y ⊆ A`, the two-block covering `(A \ Y) ∪ (V \ A)` is `V \ Y`.
Ancestral restriction of ID writes a nested marginal along this split;
empty-action ID writes the single complementary marginal.
-/
theorem union_diff_of_subset {Y A : NodeSet S} (hY : Subset Y A) :
    union (diff A Y) (diff full A) = diff full Y := by
  funext i
  cases hA : A i with
  | true =>
      cases hYbit : Y i <;> simp [union, diff, full, hA, hYbit]
  | false =>
      have hYf : Y i = false := by
        cases hYbit : Y i with
        | false =>
            rfl
        | true =>
            exact False.elim
              (Bool.false_ne_true (hA.symm.trans (hY i hYbit)))
      simp [union, diff, full, hA, hYf]

/-- If `Y ⊆ A`, then `Y ∪ (A \ Y) = A`.  Empty-action marginalization
onto an ancestral host uses this covering. -/
theorem union_diff_eq {Y A : NodeSet S} (hY : Subset Y A) :
    union Y (diff A Y) = A := by
  funext i
  cases hA : A i with
  | true =>
      cases hYbit : Y i <;> simp [union, diff, hA, hYbit]
  | false =>
      have hYf : Y i = false := by
        cases hYbit : Y i with
        | false =>
            rfl
        | true =>
            exact False.elim
              (Bool.false_ne_true (hA.symm.trans (hY i hYbit)))
      simp [union, diff, hA, hYf]

/-- If `Y ⊆ A`, then `(A \ Y) ∪ Y = A`.  Inserting extra chain-rule
predecessors recovers the full conditioner from the observed action. -/
theorem diff_union_eq {Y A : NodeSet S} (hY : Subset Y A) :
    union (diff A Y) Y = A := by
  rw [union_comm]
  exact union_diff_eq hY

theorem inter_comm (X Y : NodeSet S) : inter X Y = inter Y X := by
  funext i
  exact Bool.and_comm (X i) (Y i)

theorem inter_assoc (X Y Z : NodeSet S) :
    inter (inter X Y) Z = inter X (inter Y Z) := by
  funext i
  exact Bool.and_assoc (X i) (Y i) (Z i)

/-- Intersecting with a set already used on the right is idempotent. -/
theorem inter_idempotent_right (X Y : NodeSet S) :
    inter (inter X Y) Y = inter X Y := by
  funext i
  cases hX : X i <;> cases hY : Y i <;> simp [inter, hX, hY]

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
