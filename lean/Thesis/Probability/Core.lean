import Std

namespace Thesis
namespace Probability

/-!
This file formalizes the finite constructive probability core used in the
thesis.  It deliberately avoids measure theory and global excluded middle.

Probabilities are represented by natural numerators and positive natural
denominators.  Equality of such rational values is cross-multiplication.  This
keeps the development inside Lean's standard library while still checking the
finite Kolmogorov and Bayes calculations used in the prose proof.
-/

/-- Boolean conjunction over a finite index type. -/
def finAll : (n : Nat) -> (Fin n -> Bool) -> Bool
  | 0, _ => true
  | n + 1, p => finAll n (fun i => p i.castSucc) && p (Fin.last n)

/-- Boolean disjunction over a finite index type. -/
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

/-- A decidable event on `X`, represented by an executable Boolean predicate. -/
abbrev Event (X : Type u) := X → Bool

/-- The event containing every value of the finite sample space. -/
def topEvent : Event X :=
  fun _ => true

/-- The event containing no values. -/
def bottomEvent : Event X :=
  fun _ => false

/-- Boolean union of two decidable events. -/
def union (E F : Event X) : Event X :=
  fun x => E x || F x

/-- Boolean intersection of two decidable events. -/
def inter (E F : Event X) : Event X :=
  fun x => E x && F x

/-- Boolean complement of a decidable event. -/
def complement (E : Event X) : Event X :=
  fun x => !E x

/-- Boolean union of a finite list of decidable events. -/
def unionList : List (Event X) → Event X
  | [] => bottomEvent
  | event :: events => union event (unionList events)

/-- Disjointness is stated propositionally, but only for Boolean events. -/
def disjoint (E F : Event X) : Prop :=
  ∀ x, E x = true → F x = true → False

/-- Count the members of a finite list satisfying a decidable event. -/
def count (xs : List X) (E : Event X) : Nat :=
  xs.countP E

theorem count_nonneg (xs : List X) (E : Event X) :
    0 ≤ count xs E := by
  exact Nat.zero_le _

theorem count_le_length (xs : List X) (E : Event X) :
    count xs E ≤ xs.length := by
  exact List.countP_le_length

theorem count_top (xs : List X) :
    count xs topEvent = xs.length := by
  simp [count, topEvent]

/-- The empty event selects no entries of a finite enumeration. -/
theorem count_bottom (xs : List X) :
    count xs bottomEvent = 0 := by
  induction xs with
  | nil => rfl
  | cons value values ih =>
      change List.countP (fun _ : X => false) (value :: values) = 0
      rw [List.countP_cons]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih

/-- Pointwise-equal Boolean events have equal finite counts. -/
theorem count_congr {xs : List X} {E F : Event X}
    (h : ∀ x, E x = F x) :
    count xs E = count xs F := by
  unfold count
  apply List.countP_congr
  intro x _
  rw [h x]

/-- Reordering a finite enumeration does not change an event count. -/
theorem count_reindex {xs ys : List X} (h : xs.Perm ys) (E : Event X) :
    count xs E = count ys E := by
  exact h.countP_eq E

theorem count_inter_comm (xs : List X) (E F : Event X) :
    count xs (inter E F) = count xs (inter F E) := by
  apply count_congr
  intro x
  exact Bool.and_comm (E x) (F x)

theorem count_union_disjoint (xs : List X) (E F : Event X)
    (h : disjoint E F) :
    count xs (union E F) = count xs E + count xs F := by
  induction xs with
  | nil =>
      simp [count]
  | cons x xs ih =>
      have ih' :
          List.countP (union E F) xs = List.countP E xs + List.countP F xs := by
        simpa [count] using ih
      change
        List.countP (union E F) (x :: xs) =
          List.countP E (x :: xs) + List.countP F (x :: xs)
      rw [List.countP_cons, List.countP_cons, List.countP_cons, ih']
      cases hE : E x <;> cases hF : F x
      · simp [union, hE, hF]
      · simp [union, hE, hF]
        omega
      · simp [union, hE, hF]
        omega
      · exact False.elim (h x hE hF)

/-- An event and its Boolean complement partition every finite enumeration. -/
theorem count_add_count_complement (xs : List X) (E : Event X) :
    count xs E + count xs (complement E) = xs.length := by
  simpa [count, complement] using
    (List.length_eq_countP_add_countP E (l := xs)).symm

/-- A Boolean event is disjoint from its complement. -/
theorem disjoint_complement (E : Event X) :
    disjoint E (complement E) := by
  intro x hE hComplement
  simp [complement, hE] at hComplement

/-- An event and its complement cover the total event pointwise. -/
theorem union_complement (E : Event X) :
    union E (complement E) = topEvent := by
  funext x
  cases E x <;> simp [union, complement, topEvent]

/-- Disjointness from every member implies disjointness from their finite union. -/
theorem disjoint_unionList {E : Event X} : ∀ {events : List (Event X)},
    (∀ F ∈ events, disjoint E F) → disjoint E (unionList events)
  | [], _ => by
      simp [disjoint, unionList, bottomEvent]
  | F :: events, h => by
      intro x hE hUnion
      simp only [unionList, union, Bool.or_eq_true] at hUnion
      rcases hUnion with hF | hTail
      · exact h F (by simp) x hE hF
      · exact disjoint_unionList
          (fun G hG => h G (by simp [hG])) x hE hTail

/-- A finite pairwise-disjoint union has the sum of its member counts. -/
theorem count_unionList_pairwise (xs : List X) : ∀ {events : List (Event X)},
    events.Pairwise disjoint →
      count xs (unionList events) = (events.map (count xs)).sum
  | [], _ => count_bottom xs
  | E :: events, pairwise => by
      rw [unionList,
        count_union_disjoint xs E (unionList events)
          (disjoint_unionList (List.pairwise_cons.mp pairwise).1),
        count_unionList_pairwise xs (List.pairwise_cons.mp pairwise).2]
      rfl

/-- Event inclusion is monotone for finite counts. -/
theorem count_mono {xs : List X} {E F : Event X}
    (h : ∀ x, E x = true → F x = true) :
    count xs E ≤ count xs F := by
  unfold count
  apply List.countP_mono_left
  intro x _ hx
  exact h x hx

theorem count_union_inter (xs : List X) (E F : Event X) :
    count xs (union E F) + count xs (inter E F) =
      count xs E + count xs F := by
  induction xs with
  | nil =>
      simp [count]
  | cons x xs ih =>
      have ih' :
          List.countP (union E F) xs + List.countP (inter E F) xs =
            List.countP E xs + List.countP F xs := by
        simpa [count] using ih
      change
        List.countP (union E F) (x :: xs) + List.countP (inter E F) (x :: xs) =
          List.countP E (x :: xs) + List.countP F (x :: xs)
      rw [List.countP_cons, List.countP_cons, List.countP_cons,
        List.countP_cons]
      cases hE : E x <;> cases hF : F x <;>
        simp [union, inter, hE, hF] <;> omega

theorem list_ofFn_get {α : Type u} (xs : List α) :
    List.ofFn (fun i : Fin xs.length => xs.get i) = xs := by
  induction xs with
  | nil =>
      simp
  | cons _ _ _ =>
      simp

/-- The canonical enumeration of `Fin n` contains no duplicate indices. -/
theorem finRange_nodup : ∀ n, (List.finRange n).Nodup := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      exact List.nodup_cons.mpr ⟨by
        intro member
        rcases List.mem_map.mp member with ⟨value, _, equal⟩
        exact Fin.succ_ne_zero value equal,
        List.Pairwise.map Fin.succ (fun left right different equal =>
          different (Fin.succ_inj.mp equal)) ih⟩

/-- Every index occurs exactly once in the canonical `Fin n` enumeration. -/
theorem count_finRange (n : Nat) (j : Fin n) :
    (List.finRange n).count j = 1 := by
  rw [(finRange_nodup n).count]
  simp

/-- The three finite-inspection outcomes used for proposition-status events. -/
inductive Status where
  | proved
  | refuted
  | unresolved
  deriving DecidableEq, Repr

namespace Status

def isProved : Status → Bool
  | proved => true
  | _ => false

def isRefuted : Status → Bool
  | refuted => true
  | _ => false

def isUnresolved : Status → Bool
  | unresolved => true
  | _ => false

theorem exhaustive (s : Status) :
    isProved s || isRefuted s || isUnresolved s = true := by
  cases s <;> rfl

theorem proved_refuted_disjoint (s : Status) :
    isProved s = true → isRefuted s = true → False := by
  cases s <;> simp [isProved, isRefuted]

theorem proved_unresolved_disjoint (s : Status) :
    isProved s = true → isUnresolved s = true → False := by
  cases s <;> simp [isProved, isUnresolved]

theorem refuted_unresolved_disjoint (s : Status) :
    isRefuted s = true → isUnresolved s = true → False := by
  cases s <;> simp [isRefuted, isUnresolved]

end Status

/--
A finite inspection procedure for a state-indexed proposition `A`.

The status tag is decidable by construction.  The two soundness fields are what
make `proved` and `refuted` genuine proof-status claims rather than mere labels.
No field is provided for `unresolved`, because unresolved only means that the
chosen finite inspection procedure did not find a proof or refutation.
-/
structure Inspection (S : Type u) (A : S → Sort v) where
  status : S → Status
  proved_sound :
    ∀ s, status s = Status.proved → A s
  refuted_sound :
    ∀ s, status s = Status.refuted → A s → False

namespace Inspection

/-- The decidable event on states whose inspection returned `proved`. -/
def provedEvent (I : Inspection S A) : Event S :=
  fun s => Status.isProved (I.status s)

def refutedEvent (I : Inspection S A) : Event S :=
  fun s => Status.isRefuted (I.status s)

def unresolvedEvent (I : Inspection S A) : Event S :=
  fun s => Status.isUnresolved (I.status s)

theorem proved_refuted_disjoint (I : Inspection S A) :
    disjoint I.provedEvent I.refutedEvent := by
  intro s hp hr
  exact Status.proved_refuted_disjoint (I.status s) hp hr

theorem proved_unresolved_disjoint (I : Inspection S A) :
    disjoint I.provedEvent I.unresolvedEvent := by
  intro s hp hu
  exact Status.proved_unresolved_disjoint (I.status s) hp hu

theorem refuted_unresolved_disjoint (I : Inspection S A) :
    disjoint I.refutedEvent I.unresolvedEvent := by
  intro s hr hu
  exact Status.refuted_unresolved_disjoint (I.status s) hr hu

theorem status_count_partition (xs : List S) (status : S → Status) :
    count xs (fun s => Status.isProved (status s)) +
      count xs (fun s => Status.isRefuted (status s)) +
      count xs (fun s => Status.isUnresolved (status s)) =
      xs.length := by
  let P : Event S := fun s => Status.isProved (status s)
  let R : Event S := fun s => Status.isRefuted (status s)
  let U : Event S := fun s => Status.isUnresolved (status s)
  change count xs P + count xs R + count xs U = xs.length
  have hcover :
      count xs (union P (union R U)) = xs.length := by
    calc
      count xs (union P (union R U)) = count xs topEvent := by
        apply count_congr
        intro s
        cases hs : status s <;>
          simp [P, R, U, union, topEvent, Status.isProved,
            Status.isRefuted, Status.isUnresolved, hs]
      _ = xs.length := count_top xs
  have hRU : disjoint R U := by
    intro s hr hu
    exact Status.refuted_unresolved_disjoint (status s) hr hu
  have hPRU : disjoint P (union R U) := by
    intro s hp hru
    cases hs : status s
    · simp [R, U, union, Status.isRefuted, Status.isUnresolved, hs] at hru
    · simp [P, Status.isProved, hs] at hp
    · simp [P, Status.isProved, hs] at hp
  have haddRU :
      count xs (union R U) = count xs R + count xs U :=
    count_union_disjoint xs R U hRU
  have haddAll :
      count xs (union P (union R U)) =
        count xs P + count xs (union R U) :=
    count_union_disjoint xs P (union R U) hPRU
  rw [Nat.add_assoc, ← haddRU, ← haddAll]
  exact hcover

end Inspection

/--
Rational values as numerator/positive-denominator pairs.

`Equiv p q` is the usual equality of fractions by cross multiplication.
-/
structure QProb where
  num : Nat
  den : Nat
  den_pos : 0 < den

namespace QProb

def Equiv (p q : QProb) : Prop :=
  p.num * q.den = q.num * p.den

instance (p q : QProb) : Decidable (Equiv p q) := by
  unfold Equiv
  infer_instance

def zero : QProb where
  num := 0
  den := 1
  den_pos := by decide

def one : QProb where
  num := 1
  den := 1
  den_pos := by decide

def add (p q : QProb) : QProb where
  num := p.num * q.den + q.num * p.den
  den := p.den * q.den
  den_pos := Nat.mul_pos p.den_pos q.den_pos

def scale (k : Nat) (p : QProb) : QProb where
  num := k * p.num
  den := p.den
  den_pos := p.den_pos

def mul (p q : QProb) : QProb where
  num := p.num * q.num
  den := p.den * q.den
  den_pos := Nat.mul_pos p.den_pos q.den_pos

def div (p q : QProb) (hq : 0 < q.num) : QProb where
  num := p.num * q.den
  den := p.den * q.num
  den_pos := Nat.mul_pos p.den_pos hq

theorem equiv_refl (p : QProb) :
    Equiv p p := by
  rfl

theorem equiv_symm {p q : QProb} (h : Equiv p q) :
    Equiv q p := by
  exact h.symm

/-- Reassociate four natural factors while exchanging the middle pair. -/
theorem mul_reorder_four (a b c d : Nat) :
    a * b * (c * d) = a * c * (b * d) := by
  ac_rfl

theorem mul_reorder_three (a b c : Nat) :
    a * b * c = a * c * b := by
  ac_rfl

theorem equiv_trans {p q r : QProb}
    (hpq : Equiv p q) (hqr : Equiv q r) :
    Equiv p r := by
  apply Nat.eq_of_mul_eq_mul_right q.den_pos
  calc
    p.num * r.den * q.den = p.num * q.den * r.den :=
      mul_reorder_three p.num r.den q.den
    _ = (q.num * p.den) * r.den := by
      rw [hpq]
    _ = (q.num * r.den) * p.den :=
      mul_reorder_three q.num p.den r.den
    _ = (r.num * q.den) * p.den := by
      rw [hqr]
    _ = r.num * p.den * q.den :=
      mul_reorder_three r.num q.den p.den

theorem equiv_num_zero_iff {p q : QProb} (h : Equiv p q) :
    p.num = 0 <-> q.num = 0 := by
  constructor
  · intro hp
    have hzero : q.num * p.den = 0 := by
      rw [← h]
      simp [hp]
    exact (Nat.mul_eq_zero.mp hzero).resolve_right
      (Nat.ne_of_gt p.den_pos)
  · intro hq
    have hzero : p.num * q.den = 0 := by
      rw [h]
      simp [hq]
    exact (Nat.mul_eq_zero.mp hzero).resolve_right
      (Nat.ne_of_gt q.den_pos)

theorem equiv_num_pos_iff {p q : QProb} (h : Equiv p q) :
    0 < p.num <-> 0 < q.num := by
  constructor
  · intro hp
    cases Nat.eq_zero_or_pos q.num with
    | inl hzero =>
        exact False.elim ((Nat.ne_of_gt hp) ((equiv_num_zero_iff h).mpr hzero))
    | inr hpos => exact hpos
  · intro hq
    cases Nat.eq_zero_or_pos p.num with
    | inl hzero =>
        exact False.elim ((Nat.ne_of_gt hq) ((equiv_num_zero_iff h).mp hzero))
    | inr hpos => exact hpos

theorem add_congr {p p' q q' : QProb}
    (hp : Equiv p p') (hq : Equiv q q') :
    Equiv (add p q) (add p' q') := by
  change
    (p.num * q.den + q.num * p.den) * (p'.den * q'.den) =
      (p'.num * q'.den + q'.num * p'.den) * (p.den * q.den)
  have hleft :
      p.num * q.den * (p'.den * q'.den) =
        p'.num * q'.den * (p.den * q.den) := by
    calc
      p.num * q.den * (p'.den * q'.den) =
          (p.num * p'.den) * (q.den * q'.den) :=
        mul_reorder_four p.num q.den p'.den q'.den
      _ = (p'.num * p.den) * (q.den * q'.den) := by rw [hp]
      _ = (p'.num * p.den) * (q'.den * q.den) := by
        rw [Nat.mul_comm q.den q'.den]
      _ = p'.num * q'.den * (p.den * q.den) :=
        mul_reorder_four p'.num p.den q'.den q.den
  have hright :
      q.num * p.den * (p'.den * q'.den) =
        q'.num * p'.den * (p.den * q.den) := by
    calc
      q.num * p.den * (p'.den * q'.den) =
          (q.num * q'.den) * (p.den * p'.den) := by
        rw [Nat.mul_comm p'.den q'.den]
        exact mul_reorder_four q.num p.den q'.den p'.den
      _ = (q'.num * q.den) * (p.den * p'.den) := by rw [hq]
      _ = (q'.num * q.den) * (p'.den * p.den) := by
        rw [Nat.mul_comm p.den p'.den]
      _ = q'.num * p'.den * (q.den * p.den) :=
        mul_reorder_four q'.num q.den p'.den p.den
      _ = q'.num * p'.den * (p.den * q.den) := by
        rw [Nat.mul_comm q.den p.den]
  rw [Nat.add_mul, Nat.add_mul, hleft, hright]

/-- Addition of presentations is commutative up to cross multiplication. -/
theorem add_comm (p q : QProb) :
    Equiv (add p q) (add q p) := by
  simp [Equiv, add, Nat.mul_comm, Nat.add_comm]

/-- Adding the canonical zero presentation does not change a value. -/
theorem add_zero (p : QProb) :
    Equiv (add p zero) p := by
  simp [Equiv, add, zero, Nat.mul_comm]

/-- Addition of presentations is associative up to cross multiplication. -/
theorem add_assoc (p q r : QProb) :
    Equiv (add (add p q) r) (add p (add q r)) := by
  simp only [Equiv, add]
  simp only [Nat.add_mul]
  ac_rfl

/--
Cross-multiplication order on nonnegative rational presentations.
This is the relation used by the displayed inequality \(P(E)\le P(F)\) in the
finite monotonicity corollary: numerators are compared after clearing
denominators, so the comparison does not depend on writing a probability as a
reduced fraction.
-/
def LE (p q : QProb) : Prop :=
  p.num * q.den ≤ q.num * p.den

/--
Strict cross-multiplication order on nonnegative rational presentations.
As with `LE`, this compares represented fractions without choosing reduced
representatives.
-/
def LT (p q : QProb) : Prop :=
  p.num * q.den < q.num * p.den

/-- No rational presentation is strictly below itself. -/
theorem lt_irrefl (p : QProb) : LT p p → False := by
  simp [LT]

/-- Strict cross-multiplication order is transitive. -/
theorem lt_trans {p q r : QProb} (hpq : LT p q) (hqr : LT q r) :
    LT p r := by
  have hcleared :
      p.num * r.den * q.den < r.num * p.den * q.den := by
    calc
      p.num * r.den * q.den = p.num * q.den * r.den := by ac_rfl
      _ < q.num * p.den * r.den :=
        Nat.mul_lt_mul_of_pos_right hpq r.den_pos
      _ = q.num * r.den * p.den := by ac_rfl
      _ < r.num * q.den * p.den :=
        Nat.mul_lt_mul_of_pos_right hqr p.den_pos
      _ = r.num * p.den * q.den := by ac_rfl
  rcases Nat.lt_or_ge (p.num * r.den) (r.num * p.den) with h | h
  · exact h
  · exact False.elim
      ((Nat.not_lt_of_ge (Nat.mul_le_mul_right q.den h)) hcleared)

/-- Same-denominator strict comparison reduces to numerator comparison. -/
theorem lt_of_same_den {p q : QProb}
    (hden : p.den = q.den) (hnum : p.num < q.num) :
    LT p q := by
  unfold LT
  rw [hden]
  exact Nat.mul_lt_mul_of_pos_right hnum q.den_pos

/-- Strict cross-multiplication order respects presentation equivalence. -/
theorem lt_congr {p p' q q' : QProb}
    (hp : Equiv p p') (hq : Equiv q q') (hlt : LT p q) :
    LT p' q' := by
  have hscaled :
      p.num * q.den * (p'.den * q'.den) <
        q.num * p.den * (p'.den * q'.den) :=
    Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos p'.den_pos q'.den_pos)
  have left :
      p.num * q.den * (p'.den * q'.den) =
        p'.num * q'.den * (p.den * q.den) := by
    calc
      p.num * q.den * (p'.den * q'.den) =
          (p.num * p'.den) * (q.den * q'.den) :=
        mul_reorder_four p.num q.den p'.den q'.den
      _ = (p'.num * p.den) * (q.den * q'.den) := by rw [hp]
      _ = (p'.num * p.den) * (q'.den * q.den) := by
        rw [Nat.mul_comm q.den q'.den]
      _ = p'.num * q'.den * (p.den * q.den) :=
        mul_reorder_four p'.num p.den q'.den q.den
  have right :
      q.num * p.den * (p'.den * q'.den) =
        q'.num * p'.den * (p.den * q.den) := by
    calc
      q.num * p.den * (p'.den * q'.den) =
          (q.num * q'.den) * (p.den * p'.den) := by
        rw [Nat.mul_comm p'.den q'.den]
        exact mul_reorder_four q.num p.den q'.den p'.den
      _ = (q'.num * q.den) * (p.den * p'.den) := by rw [hq]
      _ = (q'.num * q.den) * (p'.den * p.den) := by
        rw [Nat.mul_comm p.den p'.den]
      _ = q'.num * p'.den * (q.den * p.den) :=
        mul_reorder_four q'.num q.den p'.den p.den
      _ = q'.num * p'.den * (p.den * q.den) := by
        rw [Nat.mul_comm q.den p.den]
  have hcleared :
      p'.num * q'.den * (p.den * q.den) <
        q'.num * p'.den * (p.den * q.den) := by
    rw [← left, ← right]
    exact hscaled
  rcases Nat.lt_or_ge (p'.num * q'.den) (q'.num * p'.den) with h | h
  · exact h
  · exact False.elim
      ((Nat.not_lt_of_ge (Nat.mul_le_mul_right (p.den * q.den) h)) hcleared)

/-- Every nonnegative rational presentation is above the canonical zero. -/
theorem zero_le (p : QProb) : LE zero p := by
  simp [LE, zero]

/--
Same-denominator comparison reduces to a comparison of numerators.  Urn
probabilities always share the urn size as denominator, so this is the step
from a selected-cell inequality to a rational inequality.
-/
theorem le_of_same_den {p q : QProb}
    (hden : p.den = q.den) (hnum : p.num ≤ q.num) :
    LE p q := by
  unfold LE
  rw [hden]
  exact Nat.mul_le_mul_right q.den hnum

/-- The cross-multiplication order respects presentation equivalence. -/
theorem le_congr {p p' q q' : QProb}
    (hp : Equiv p p') (hq : Equiv q q') (hle : LE p q) :
    LE p' q' := by
  have hscaled :
      p.num * q.den * (p'.den * q'.den) ≤
        q.num * p.den * (p'.den * q'.den) :=
    Nat.mul_le_mul_right (p'.den * q'.den) hle
  have left :
      p.num * q.den * (p'.den * q'.den) =
        p'.num * q'.den * (p.den * q.den) := by
    calc
      p.num * q.den * (p'.den * q'.den) =
          (p.num * p'.den) * (q.den * q'.den) :=
        mul_reorder_four p.num q.den p'.den q'.den
      _ = (p'.num * p.den) * (q.den * q'.den) := by rw [hp]
      _ = (p'.num * p.den) * (q'.den * q.den) := by
        rw [Nat.mul_comm q.den q'.den]
      _ = p'.num * q'.den * (p.den * q.den) :=
        mul_reorder_four p'.num p.den q'.den q.den
  have right :
      q.num * p.den * (p'.den * q'.den) =
        q'.num * p'.den * (p.den * q.den) := by
    calc
      q.num * p.den * (p'.den * q'.den) =
          (q.num * q'.den) * (p.den * p'.den) := by
        rw [Nat.mul_comm p'.den q'.den]
        exact mul_reorder_four q.num p.den q'.den p'.den
      _ = (q'.num * q.den) * (p.den * p'.den) := by rw [hq]
      _ = (q'.num * q.den) * (p'.den * p.den) := by
        rw [Nat.mul_comm p.den p'.den]
      _ = q'.num * p'.den * (q.den * p.den) :=
        mul_reorder_four q'.num q.den p'.den p.den
      _ = q'.num * p'.den * (p.den * q.den) := by
        rw [Nat.mul_comm q.den p.den]
  have hcleared :
      p'.num * q'.den * (p.den * q.den) ≤
        q'.num * p'.den * (p.den * q.den) := by
    rw [← left, ← right]
    exact hscaled
  exact Nat.le_of_mul_le_mul_right hcleared (Nat.mul_pos p.den_pos q.den_pos)

/-- Finite addition of rational probability values. -/
def listSum : List QProb -> QProb
  | [] => zero
  | value :: values => add value (listSum values)

/-- Division by a common positive denominator distributes over addition. -/
theorem div_add_same_denominator (first second denominator : QProb)
    (positive : 0 < denominator.num) :
    Equiv (div (add first second) denominator positive)
      (add (div first denominator positive) (div second denominator positive)) := by
  simp only [Equiv, div, add, Nat.add_mul]
  ac_rfl

/-- Division by a common positive denominator distributes over a finite sum. -/
theorem div_listSum_same_denominator (values : List QProb)
    (denominator : QProb) (positive : 0 < denominator.num) :
    Equiv (div (listSum values) denominator positive)
      (listSum (values.map (fun value => div value denominator positive))) := by
  induction values with
  | nil =>
      simp [listSum, div, Equiv, zero]
  | cons value values ih =>
      exact equiv_trans
        (div_add_same_denominator value (listSum values) denominator positive)
        (add_congr (equiv_refl _) ih)

/-- Pointwise fraction equivalence is preserved by a finite sum. -/
theorem listSum_map_congr (values : List X) (left right : X -> QProb)
    (pointwise : forall value, Equiv (left value) (right value)) :
    Equiv (listSum (values.map left)) (listSum (values.map right)) := by
  induction values with
  | nil => exact equiv_refl zero
  | cons value values ih =>
      exact add_congr (pointwise value) ih

/-- A finite rational sum over an appended list is the sum of the two
component sums. -/
theorem listSum_append (left right : List QProb) :
    Equiv (listSum (left ++ right))
      (add (listSum left) (listSum right)) := by
  induction left with
  | nil => simp [listSum, Equiv, add, zero]
  | cons value values ih =>
      exact equiv_trans (add_congr (equiv_refl _) ih)
        (equiv_symm (add_assoc value (listSum values) (listSum right)))

/-- The canonical zero is equivalent to a zero numerator on any positive
denominator. -/
theorem equiv_zero_mk (D : Nat) (hD : 0 < D) :
    Equiv zero ⟨0, D, hD⟩ := by
  simp [Equiv, zero]

/-- Adding two presentations that already share a denominator adds the
numerators and keeps that denominator, up to `Equiv`. -/
theorem add_mk_same_den (D : Nat) (hD : 0 < D) (a b : Nat) :
    Equiv (add ⟨a, D, hD⟩ ⟨b, D, hD⟩) ⟨a + b, D, hD⟩ := by
  simp [Equiv, add]
  rw [← Nat.add_mul]
  ac_rfl

/-- A finite sum of common-denominator presentations is the sum of the
numerators on that denominator. -/
theorem listSum_mk_same_den (D : Nat) (hD : 0 < D) :
    forall nums : List Nat,
      Equiv (listSum (nums.map fun n => (⟨n, D, hD⟩ : QProb)))
        ⟨List.sum nums, D, hD⟩
  | [] => by
      simp [listSum]
      exact equiv_zero_mk D hD
  | n :: ns => by
      simp [listSum]
      refine equiv_trans
        (add_congr (equiv_refl _) (listSum_mk_same_den D hD ns)) ?_
      simpa [List.sum_cons] using add_mk_same_den D hD n (List.sum ns)

/-- Flattening a finite family of lists does not change its iterated rational
sum. -/
theorem listSum_flatMap (values : List X) (family : X -> List QProb) :
    Equiv (listSum (values.flatMap family))
      (listSum (values.map (fun value => listSum (family value)))) := by
  induction values with
  | nil => exact equiv_refl zero
  | cons value values ih =>
      exact equiv_trans (listSum_append (family value)
        (values.flatMap family)) (add_congr (equiv_refl _) ih)

theorem mul_congr {p p' q q' : QProb}
    (hp : Equiv p p') (hq : Equiv q q') :
    Equiv (mul p q) (mul p' q') := by
  change
    p.num * q.num * (p'.den * q'.den) =
      p'.num * q'.num * (p.den * q.den)
  calc
    p.num * q.num * (p'.den * q'.den) =
        (p.num * p'.den) * (q.num * q'.den) :=
      mul_reorder_four p.num q.num p'.den q'.den
    _ = (p'.num * p.den) * (q'.num * q.den) := by rw [hp, hq]
    _ = p'.num * q'.num * (p.den * q.den) :=
      (mul_reorder_four p'.num q'.num p.den q.den).symm

/-- Scaling by a natural factor preserves cross-multiplication equivalence. -/
theorem scale_congr (w : Nat) {p q : QProb} (hpq : Equiv p q) :
    Equiv (scale w p) (scale w q) := by
  change w * p.num * q.den = w * q.num * p.den
  calc
    w * p.num * q.den = w * (p.num * q.den) := by
      ac_rfl
    _ = w * (q.num * p.den) := by
      rw [hpq]
    _ = w * q.num * p.den := by
      ac_rfl

theorem mul_comm (left right : QProb) :
    Equiv (mul left right) (mul right left) := by
  simp only [Equiv, mul]
  ac_rfl

theorem mul_assoc (first second third : QProb) :
    Equiv (mul (mul first second) third)
      (mul first (mul second third)) := by
  simp only [Equiv, mul]
  ac_rfl

theorem mul_one (value : QProb) :
    Equiv (mul value one) value := by
  simp [Equiv, mul, one]

theorem one_mul (value : QProb) :
    Equiv (mul one value) value := by
  exact equiv_trans (mul_comm one value) (mul_one value)

theorem mul_add_distrib (factor left right : QProb) :
    Equiv (mul factor (add left right))
      (add (mul factor left) (mul factor right)) := by
  simp only [Equiv, mul, add, Nat.mul_add, Nat.add_mul]
  ac_rfl

theorem add_mul_distrib (left right factor : QProb) :
    Equiv (mul (add left right) factor)
      (add (mul left factor) (mul right factor)) := by
  simp only [Equiv, mul, add, Nat.add_mul]
  ac_rfl

theorem mul_listSum (factor : QProb) (values : List QProb) :
    Equiv (mul factor (listSum values))
      (listSum (values.map (fun value => mul factor value))) := by
  induction values with
  | nil => simp [listSum, Equiv, mul, zero]
  | cons value values ih =>
      exact equiv_trans (mul_add_distrib factor value (listSum values))
        (add_congr (equiv_refl _) ih)

theorem listSum_mul (values : List QProb) (factor : QProb) :
    Equiv (mul (listSum values) factor)
      (listSum (values.map (fun value => mul value factor))) := by
  induction values with
  | nil => simp [listSum, Equiv, mul, zero]
  | cons value values ih =>
      exact equiv_trans (add_mul_distrib value (listSum values) factor)
        (add_congr (equiv_refl _) ih)

theorem listSum_mul_listSum (left right : List QProb) :
    Equiv (mul (listSum left) (listSum right))
      (listSum (left.map (fun leftValue =>
        listSum (right.map (fun rightValue =>
          mul leftValue rightValue))))) := by
  induction left with
  | nil => simp [listSum, Equiv, mul, zero]
  | cons value values ih =>
      exact equiv_trans
        (add_mul_distrib value (listSum values) (listSum right))
        (add_congr (mul_listSum value right) ih)

theorem div_congr {p p' q q' : QProb}
    (hp : Equiv p p') (hq : Equiv q q')
    (hqPos : 0 < q.num) (hqPos' : 0 < q'.num) :
    Equiv (div p q hqPos) (div p' q' hqPos') := by
  change
    p.num * q.den * (p'.den * q'.num) =
      p'.num * q'.den * (p.den * q.num)
  have hq' : q.den * q'.num = q'.den * q.num := by
    calc
      q.den * q'.num = q'.num * q.den := Nat.mul_comm q.den q'.num
      _ = q.num * q'.den := hq.symm
      _ = q'.den * q.num := Nat.mul_comm q.num q'.den
  calc
    p.num * q.den * (p'.den * q'.num) =
        (p.num * p'.den) * (q.den * q'.num) :=
      mul_reorder_four p.num q.den p'.den q'.num
    _ = (p'.num * p.den) * (q.den * q'.num) := by rw [hp]
    _ = (p'.num * p.den) * (q'.den * q.num) := by rw [hq']
    _ = p'.num * q'.den * (p.den * q.num) :=
      mul_reorder_four p'.num p.den q'.den q.num

/-- A denominator-free cross-product identity yields equality of two ratios. -/
theorem div_equiv_of_cross {leftNumerator leftDenominator
    rightNumerator rightDenominator : QProb}
    (leftPositive : 0 < leftDenominator.num)
    (rightPositive : 0 < rightDenominator.num)
    (cross : Equiv
      (mul leftNumerator rightDenominator)
      (mul rightNumerator leftDenominator)) :
    Equiv
      (div leftNumerator leftDenominator leftPositive)
      (div rightNumerator rightDenominator rightPositive) := by
  change
    leftNumerator.num * leftDenominator.den *
        (rightNumerator.den * rightDenominator.num) =
      rightNumerator.num * rightDenominator.den *
        (leftNumerator.den * leftDenominator.num)
  change
    leftNumerator.num * rightDenominator.num *
        (rightNumerator.den * leftDenominator.den) =
      rightNumerator.num * leftDenominator.num *
        (leftNumerator.den * rightDenominator.den) at cross
  calc
    leftNumerator.num * leftDenominator.den *
        (rightNumerator.den * rightDenominator.num) =
      leftNumerator.num * rightDenominator.num *
        (rightNumerator.den * leftDenominator.den) := by ac_rfl
    _ = rightNumerator.num * leftDenominator.num *
        (leftNumerator.den * rightDenominator.den) := cross
    _ = rightNumerator.num * rightDenominator.den *
        (leftNumerator.den * leftDenominator.num) := by ac_rfl

theorem div_equiv_of_den_equiv_one (numerator denominator : QProb)
    (positive : 0 < denominator.num) (normalized : Equiv denominator one) :
    Equiv (div numerator denominator positive) numerator := by
  have equalParts : denominator.num = denominator.den := by
    simpa [Equiv, one] using normalized
  simp only [Equiv, div, equalParts]
  exact (mul_reorder_three numerator.num denominator.den numerator.den).trans
    (Nat.mul_assoc numerator.num numerator.den denominator.den)

theorem scale_forced_unit {N : Nat} (hN : 0 < N)
    (cell : QProb)
    (hwhole : Equiv (scale N cell) one) :
    Equiv cell { num := 1, den := N, den_pos := hN } := by
  simp [Equiv, scale, one] at hwhole ⊢
  calc
    cell.num * N = N * cell.num := by
      exact Nat.mul_comm cell.num N
    _ = cell.den := hwhole

theorem scale_forced_ratio {N k : Nat} (hN : 0 < N)
    (cell : QProb)
    (hwhole : Equiv (scale N cell) one) :
    Equiv (scale k cell) { num := k, den := N, den_pos := hN } := by
  simp [Equiv, scale, one] at hwhole ⊢
  calc
    k * cell.num * N = k * (cell.num * N) := by
      rw [Nat.mul_assoc]
    _ = k * (N * cell.num) := by
      rw [Nat.mul_comm cell.num N]
    _ = k * cell.den := by
      rw [hwhole]

/-- A natural number as a rational presentation with denominator one. -/
def ofNat (n : Nat) : QProb where
  num := n
  den := 1
  den_pos := Nat.succ_pos 0

/-- Addition of whole-number presentations is addition of the numbers. -/
theorem ofNat_add (a b : Nat) :
    Equiv (add (ofNat a) (ofNat b)) (ofNat (a + b)) := by
  simp [add, ofNat, Equiv]

/-- Reflexivity of the cross-multiplication order. -/
theorem le_refl (p : QProb) : LE p p := by
  simp [LE]

/-- Transitivity of the cross-multiplication order. -/
theorem le_trans {p q r : QProb} (hpq : LE p q) (hqr : LE q r) :
    LE p r := by
  have hcleared :
      p.num * r.den * q.den ≤ r.num * p.den * q.den := by
    calc
      p.num * r.den * q.den = p.num * q.den * r.den := by ac_rfl
      _ ≤ q.num * p.den * r.den :=
        Nat.mul_le_mul_right r.den hpq
      _ = q.num * r.den * p.den := by ac_rfl
      _ ≤ r.num * q.den * p.den :=
        Nat.mul_le_mul_right p.den hqr
      _ = r.num * p.den * q.den := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hcleared q.den_pos

/--
Difference of presentations, defined only when `LE q p`.  The numerator is
the cleared-denominator natural subtraction, so no signed rationals are
introduced.  Callers retain the inequality witness; the operation is not a
total inverse of `add` on raw presentations, only up to `Equiv`.
-/
def sub (p q : QProb) (_hle : LE q p) : QProb where
  num := p.num * q.den - q.num * p.den
  den := p.den * q.den
  den_pos := Nat.mul_pos p.den_pos q.den_pos

/-- Adding the subtracted presentation recovers the original value. -/
theorem sub_add (p q : QProb) (hle : LE q p) :
    Equiv (add (sub p q hle) q) p := by
  have hle_scaled :
      q.num * p.den * q.den ≤ p.num * q.den * q.den :=
    Nat.mul_le_mul_right q.den hle
  simp only [Equiv, add, sub]
  calc
    ((p.num * q.den - q.num * p.den) * q.den + q.num * (p.den * q.den)) *
        p.den
        =
      ((p.num * q.den * q.den - q.num * p.den * q.den) +
          q.num * p.den * q.den) * p.den := by
      have hdistrib :
          (p.num * q.den - q.num * p.den) * q.den =
            p.num * q.den * q.den - q.num * p.den * q.den :=
        Nat.mul_sub_right_distrib (p.num * q.den) (q.num * p.den) q.den
      rw [hdistrib, Nat.mul_assoc q.num p.den q.den]
    _ = (p.num * q.den * q.den) * p.den := by
      rw [Nat.sub_add_cancel hle_scaled]
    _ = p.num * (p.den * q.den * q.den) := by ac_rfl

/-- Witnessed subtraction respects presentation equivalence. -/
theorem sub_congr {p p' q q' : QProb}
    (hp : Equiv p p') (hq : Equiv q q')
    (hle : LE q p) (hle' : LE q' p') :
    Equiv (sub p q hle) (sub p' q' hle') := by
  have hA :
      p.num * q.den * (p'.den * q'.den) =
        p'.num * q'.den * (p.den * q.den) := by
    calc
      p.num * q.den * (p'.den * q'.den) =
          (p.num * p'.den) * (q.den * q'.den) :=
        mul_reorder_four p.num q.den p'.den q'.den
      _ = (p'.num * p.den) * (q.den * q'.den) := by rw [hp]
      _ = (p'.num * p.den) * (q'.den * q.den) := by
        rw [Nat.mul_comm q.den q'.den]
      _ = p'.num * q'.den * (p.den * q.den) :=
        mul_reorder_four p'.num p.den q'.den q.den
  have hB :
      q.num * p.den * (p'.den * q'.den) =
        q'.num * p'.den * (p.den * q.den) := by
    calc
      q.num * p.den * (p'.den * q'.den) =
          (q.num * q'.den) * (p.den * p'.den) := by
        rw [Nat.mul_comm p'.den q'.den]
        exact mul_reorder_four q.num p.den q'.den p'.den
      _ = (q'.num * q.den) * (p.den * p'.den) := by rw [hq]
      _ = (q'.num * q.den) * (p'.den * p.den) := by
        rw [Nat.mul_comm p.den p'.den]
      _ = q'.num * p'.den * (q.den * p.den) :=
        mul_reorder_four q'.num q.den p'.den p.den
      _ = q'.num * p'.den * (p.den * q.den) := by
        rw [Nat.mul_comm q.den p.den]
  have hle_scaled :
      q.num * p.den * (p'.den * q'.den) ≤
        p.num * q.den * (p'.den * q'.den) :=
    Nat.mul_le_mul_right (p'.den * q'.den) hle
  simp only [Equiv, sub]
  have hdistrib_left :
      (p.num * q.den - q.num * p.den) * (p'.den * q'.den) =
        p.num * q.den * (p'.den * q'.den) -
          q.num * p.den * (p'.den * q'.den) :=
    Nat.mul_sub_right_distrib (p.num * q.den) (q.num * p.den)
      (p'.den * q'.den)
  have hdistrib_right :
      (p'.num * q'.den - q'.num * p'.den) * (p.den * q.den) =
        p'.num * q'.den * (p.den * q.den) -
          q'.num * p'.den * (p.den * q.den) :=
    Nat.mul_sub_right_distrib (p'.num * q'.den) (q'.num * p'.den)
      (p.den * q.den)
  rw [hdistrib_left, hdistrib_right, hA, hB]

/-- Scaling by a natural factor preserves the cross-multiplication order. -/
theorem scale_le_scale (k : Nat) {p q : QProb} (hle : LE p q) :
    LE (scale k p) (scale k q) := by
  simp only [LE, scale]
  calc
    (k * p.num) * q.den = k * (p.num * q.den) := by ac_rfl
    _ ≤ k * (q.num * p.den) := Nat.mul_le_mul_left k hle
    _ = (k * q.num) * p.den := by ac_rfl

end QProb

end Probability
end Thesis
