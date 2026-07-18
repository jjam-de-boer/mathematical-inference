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

abbrev Event (X : Type u) := X → Bool

def topEvent : Event X :=
  fun _ => true

def union (E F : Event X) : Event X :=
  fun x => E x || F x

def inter (E F : Event X) : Event X :=
  fun x => E x && F x

def disjoint (E F : Event X) : Prop :=
  ∀ x, E x = true → F x = true → False

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
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have ih' : List.countP topEvent xs = xs.length := by
        simpa [count] using ih
      change List.countP topEvent (x :: xs) = (x :: xs).length
      rw [List.countP_cons, ih']
      simp [topEvent]

theorem count_congr {xs : List X} {E F : Event X}
    (h : ∀ x, E x = F x) :
    count xs E = count xs F := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have ih' : List.countP E xs = List.countP F xs := by
        simpa [count] using ih
      change List.countP E (x :: xs) = List.countP F (x :: xs)
      rw [List.countP_cons, List.countP_cons, ih', h x]

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

theorem count_mono {xs : List X} {E F : Event X}
    (h : ∀ x, E x = true → F x = true) :
    count xs E ≤ count xs F := by
  induction xs with
  | nil =>
      simp [count]
  | cons x xs ih =>
      have ih' : List.countP E xs ≤ List.countP F xs := by
        simpa [count] using ih
      change List.countP E (x :: xs) ≤ List.countP F (x :: xs)
      rw [List.countP_cons, List.countP_cons]
      cases hE : E x with
      | true =>
          have hF : F x = true := h x hE
          simp [hF]
          omega
      | false =>
          cases hF : F x with
          | true =>
              simp
              omega
          | false =>
              simp
              exact ih'

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

def toRat (p : QProb) : Rat :=
  (p.num : Rat) / (p.den : Rat)

theorem equiv_refl (p : QProb) :
    Equiv p p := by
  rfl

theorem equiv_symm {p q : QProb} (h : Equiv p q) :
    Equiv q p := by
  exact h.symm

/-- Reassociate four natural factors while exchanging the middle pair. -/
theorem mul_reorder_four (a b c d : Nat) :
    a * b * (c * d) = a * c * (b * d) := by
  calc
    a * b * (c * d) = a * (b * (c * d)) := Nat.mul_assoc a b (c * d)
    _ = a * ((b * c) * d) :=
      congrArg (fun value => a * value) (Nat.mul_assoc b c d).symm
    _ = a * ((c * b) * d) := by rw [Nat.mul_comm b c]
    _ = a * (c * (b * d)) :=
      congrArg (fun value => a * value) (Nat.mul_assoc c b d)
    _ = a * c * (b * d) := (Nat.mul_assoc a c (b * d)).symm

theorem mul_reorder_three (a b c : Nat) :
    a * b * c = a * c * b := by
  calc
    a * b * c = a * (b * c) := Nat.mul_assoc a b c
    _ = a * (c * b) :=
      congrArg (fun value => a * value) (Nat.mul_comm b c)
    _ = a * c * b := (Nat.mul_assoc a c b).symm

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

/-- Finite addition of rational probability values. -/
def listSum : List QProb -> QProb
  | [] => zero
  | value :: values => add value (listSum values)

/-- Pointwise fraction equivalence is preserved by a finite sum. -/
theorem listSum_map_congr (values : List X) (left right : X -> QProb)
    (pointwise : forall value, Equiv (left value) (right value)) :
    Equiv (listSum (values.map left)) (listSum (values.map right)) := by
  induction values with
  | nil => exact equiv_refl zero
  | cons value values ih =>
      exact add_congr (pointwise value) ih

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

end QProb

/--
An urn-generated probability assignment over `X`.

The finite urn is `Fin n`; `draw` pushes the equipossible cells forward into
the value type.
-/
structure UrnProb (X : Type u) where
  n : Nat
  pos : 0 < n
  draw : Fin n → X

namespace UrnProb

def support (μ : UrnProb X) : List X :=
  List.ofFn μ.draw

theorem support_length (μ : UrnProb X) :
    μ.support.length = μ.n := by
  simp [support]

def ofList (xs : List X) (h : 0 < xs.length) : UrnProb X where
  n := xs.length
  pos := h
  draw := fun i => xs.get i

theorem support_ofList (xs : List X) (h : 0 < xs.length) :
    (ofList xs h).support = xs := by
  simp [ofList, support]

def probNum (μ : UrnProb X) (E : Event X) : Nat :=
  count μ.support E

def probVal (μ : UrnProb X) (E : Event X) : QProb where
  num := μ.probNum E
  den := μ.n
  den_pos := μ.pos

def condVal (μ : UrnProb X) (E F : Event X)
    (hF : 0 < μ.probNum F) : QProb where
  num := μ.probNum (inter E F)
  den := μ.probNum F
  den_pos := hF

theorem probNum_nonneg (μ : UrnProb X) (E : Event X) :
    0 ≤ μ.probNum E := by
  exact Nat.zero_le _

theorem probNum_le_den (μ : UrnProb X) (E : Event X) :
    μ.probNum E ≤ μ.n := by
  rw [← μ.support_length]
  exact count_le_length μ.support E

theorem probNum_top (μ : UrnProb X) :
    μ.probNum topEvent = μ.n := by
  rw [probNum, count_top, support_length]

theorem normalization (μ : UrnProb X) :
    QProb.Equiv (μ.probVal topEvent) QProb.one := by
  simp [QProb.Equiv, QProb.one, probVal, probNum_top]

theorem finite_additivity_num (μ : UrnProb X) (E F : Event X)
    (h : disjoint E F) :
    μ.probNum (union E F) = μ.probNum E + μ.probNum F := by
  exact count_union_disjoint μ.support E F h

theorem finite_additivity (μ : UrnProb X) (E F : Event X)
    (h : disjoint E F) :
    QProb.Equiv (μ.probVal (union E F))
      (QProb.add (μ.probVal E) (μ.probVal F)) := by
  have hcount := μ.finite_additivity_num E F h
  simp [QProb.Equiv, QProb.add, probVal, hcount,
    Nat.left_distrib, Nat.mul_assoc, Nat.mul_comm]

theorem status_partition_num (μ : UrnProb S) (I : Inspection S A) :
    μ.probNum I.provedEvent +
      μ.probNum I.refutedEvent +
      μ.probNum I.unresolvedEvent =
      μ.n := by
  have h :=
    Inspection.status_count_partition μ.support I.status
  simpa [probNum, Inspection.provedEvent, Inspection.refutedEvent,
    Inspection.unresolvedEvent, support_length] using h

theorem status_partition (μ : UrnProb S) (I : Inspection S A) :
    QProb.Equiv
      (QProb.add
        (QProb.add (μ.probVal I.provedEvent) (μ.probVal I.refutedEvent))
        (μ.probVal I.unresolvedEvent))
      QProb.one := by
  have hsum := μ.status_partition_num I
  simp [QProb.Equiv, QProb.add, QProb.one, probVal]
  rw [← Nat.add_mul]
  calc
    (μ.probNum I.provedEvent + μ.probNum I.refutedEvent) * μ.n * μ.n +
        μ.probNum I.unresolvedEvent * (μ.n * μ.n)
        =
        (μ.probNum I.provedEvent + μ.probNum I.refutedEvent) *
            (μ.n * μ.n) +
          μ.probNum I.unresolvedEvent * (μ.n * μ.n) := by
          rw [Nat.mul_assoc]
    _ =
        (μ.probNum I.provedEvent + μ.probNum I.refutedEvent +
            μ.probNum I.unresolvedEvent) *
          (μ.n * μ.n) := by
          rw [← Nat.add_mul]
    _ = μ.n * (μ.n * μ.n) := by
          rw [hsum]
    _ = μ.n * μ.n * μ.n := by
          rw [← Nat.mul_assoc]

theorem product_rule_for_conditioning (μ : UrnProb X) (E F : Event X)
    (hF : 0 < μ.probNum F) :
    QProb.Equiv
      (QProb.mul (μ.condVal E F hF) (μ.probVal F))
      (μ.probVal (inter E F)) := by
  simp [QProb.Equiv, QProb.mul, condVal, probVal,
    Nat.mul_assoc, Nat.mul_comm]

theorem bayes_product_rule (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) (hF : 0 < μ.probNum F) :
    QProb.Equiv
      (QProb.mul (μ.condVal E F hF) (μ.probVal F))
      (QProb.mul (μ.condVal F E hE) (μ.probVal E)) := by
  have hInter :
      μ.probNum (inter F E) = μ.probNum (inter E F) := by
    exact (count_inter_comm μ.support E F).symm
  simp [QProb.Equiv, QProb.mul, condVal, probVal, hInter,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem bayes_formula (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) (hF : 0 < μ.probNum F) :
    QProb.Equiv
      (μ.condVal E F hF)
      (QProb.div
        (QProb.mul (μ.condVal F E hE) (μ.probVal E))
        (μ.probVal F)
        hF) := by
  have hInter :
      μ.probNum (inter F E) = μ.probNum (inter E F) := by
    exact (count_inter_comm μ.support E F).symm
  simp [QProb.Equiv, QProb.div, QProb.mul, condVal, probVal, hInter,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/--
Monotonicity of finite urn probability: a sub-event has at most the same urn
count as the larger event. This is the integer counterpart of the standard
`E ⊆ F ⇒ P(E) ≤ P(F)` rule, used implicitly by inclusion–exclusion arguments.
-/
theorem monotonicity (μ : UrnProb X) {E F : Event X}
    (h : ∀ x, E x = true → F x = true) :
    μ.probNum E ≤ μ.probNum F :=
  count_mono h

/--
Two-event count form of inclusion–exclusion: the sum of cells in `E ∪ F` and in
`E ∩ F` equals the sum of cells in `E` and in `F`. This generalises
`finite_additivity_num` to events that need not be disjoint.
-/
theorem probNum_union_inter (μ : UrnProb X) (E F : Event X) :
    μ.probNum (union E F) + μ.probNum (inter E F) =
      μ.probNum E + μ.probNum F :=
  count_union_inter μ.support E F

/--
Two-event inclusion–exclusion as an equivalence of `QProb` values. The sum of
the `E ∪ F` and `E ∩ F` probabilities equals the sum of the `E` and `F`
probabilities. This is the form used implicitly by the tenure-track example
calculation in the main text.
-/
theorem inclusion_exclusion (μ : UrnProb X) (E F : Event X) :
    QProb.Equiv
      (QProb.add (μ.probVal (union E F)) (μ.probVal (inter E F)))
      (QProb.add (μ.probVal E) (μ.probVal F)) := by
  have hcount := μ.probNum_union_inter E F
  unfold QProb.Equiv QProb.add probVal
  simp only [← Nat.add_mul]
  rw [hcount]

/--
The Bayesian update probability of `F` given conditioning event `E`, computed
directly from the formula `p_E(ω) := 𝟙_E(ω)·p(ω) / P(E)` of the appendix
definition `def:bayesian-update`. In the urn presentation this is the count of
cells satisfying both `E` and `F`, divided by the count of cells satisfying `E`.
-/
def bayesianUpdateProb (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) : QProb where
  num := μ.probNum (inter E F)
  den := μ.probNum E
  den_pos := hE

/--
Consistency of Bayesian update with conditional probability: when the
conditioning event has positive count, the update value `P_E(F)` equals
`P(F | E)`. This is the lemma the main text uses implicitly when treating
`P_E` and `P(- | E)` as interchangeable.
-/
theorem bayesian_update_consistency (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv (μ.bayesianUpdateProb E F hE) (μ.condVal F E hE) := by
  have hcomm : μ.probNum (inter E F) = μ.probNum (inter F E) :=
    count_inter_comm μ.support E F
  simp [QProb.Equiv, bayesianUpdateProb, condVal, hcomm]

/--
The Bayesian update induced by a positive event is normalized: the updated
probability of the total event is one.
-/
theorem bayesian_update_normalization (μ : UrnProb X) (E : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv (μ.bayesianUpdateProb E topEvent hE) QProb.one := by
  have htop : μ.probNum (inter E topEvent) = μ.probNum E := by
    unfold probNum
    apply count_congr
    intro x
    cases h : E x <;> simp [inter, topEvent, h]
  simp [QProb.Equiv, bayesianUpdateProb, QProb.one, htop]

end UrnProb

namespace FiniteProbRecord

def totalMass : List (Ω × Nat) → Nat
  | [] => 0
  | (_, w) :: atoms => w + totalMass atoms

def eventMass : List (Ω × Nat) → Event Ω → Nat
  | [], _ => 0
  | (ω, w) :: atoms, E =>
      if E ω then w + eventMass atoms E else eventMass atoms E

theorem eventMass_congr (atoms : List (Ω × Nat)) (E F : Event Ω)
    (h : forall value, E value = F value) :
    eventMass atoms E = eventMass atoms F := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      cases atom with
      | mk value weight =>
          change
            (if E value then weight + eventMass atoms E else eventMass atoms E) =
              (if F value then weight + eventMass atoms F else eventMass atoms F)
          rw [h value, ih]

def expand : List (Ω × Nat) → List Ω
  | [] => []
  | (ω, w) :: atoms => List.replicate w ω ++ expand atoms

theorem length_expand (atoms : List (Ω × Nat)) :
    (expand atoms).length = totalMass atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons a atoms ih =>
      cases a with
      | mk ω w =>
          simp [expand, totalMass, ih]

theorem count_expand (atoms : List (Ω × Nat)) (E : Event Ω) :
    count (expand atoms) E = eventMass atoms E := by
  induction atoms with
  | nil =>
      simp [expand, eventMass, count]
  | cons a atoms ih =>
      cases a with
      | mk ω w =>
          simp [expand, eventMass, count, List.countP_append,
            List.countP_replicate]
          have ihc :
              List.countP E (expand atoms) = eventMass atoms E := by
            simpa [count] using ih
          rw [ihc]
          cases E ω <;> simp

theorem totalMass_unit (xs : List Ω) :
    totalMass (xs.map (fun ω => (ω, 1))) = xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [totalMass, ih]
      omega

theorem eventMass_unit (xs : List Ω) (E : Event Ω) :
    eventMass (xs.map (fun ω => (ω, 1))) E = count xs E := by
  induction xs with
  | nil =>
      simp [eventMass, count]
  | cons x xs ih =>
      change
        (if E x then
            1 + eventMass (xs.map (fun ω => (ω, 1))) E
          else
            eventMass (xs.map (fun ω => (ω, 1))) E) =
          List.countP E (x :: xs)
      rw [List.countP_cons, ih]
      cases E x <;> simp [count]
      omega

theorem eventMass_top (atoms : List (Ω × Nat)) :
    eventMass atoms topEvent = totalMass atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      simp [eventMass, totalMass, topEvent, ih]

theorem totalMass_filter_event (atoms : List (Ω × Nat))
    (evidence : Event Ω) :
    totalMass (atoms.filter (fun atom => evidence atom.1)) =
      eventMass atoms evidence := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases h : evidence ω <;>
        simp [totalMass, eventMass, h, ih]

theorem eventMass_filter_event (atoms : List (Ω × Nat))
    (evidence event : Event Ω) :
    eventMass (atoms.filter (fun atom => evidence atom.1)) event =
      eventMass atoms (fun ω => evidence ω && event ω) := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases hEvidence : evidence ω <;> cases hEvent : event ω <;>
        simp [eventMass, hEvidence, hEvent, ih]

theorem totalMass_map_labels (atoms : List (Ω × Nat)) (f : Ω → X) :
    totalMass (atoms.map (fun atom => (f atom.1, atom.2))) =
      totalMass atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      change weight +
          totalMass (atoms.map (fun atom => (f atom.1, atom.2))) =
        weight + totalMass atoms
      exact congrArg (fun mass => weight + mass) ih

theorem eventMass_map_labels (atoms : List (Ω × Nat))
    (f : Ω → X) (event : Event X) :
    eventMass (atoms.map (fun atom => (f atom.1, atom.2))) event =
      eventMass atoms (fun ω => event (f ω)) := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases h : event (f ω) <;>
        simp [eventMass, h, ih]

theorem eventMass_scale (atoms : List (Ω × Nat)) (factor : Nat)
    (event : Event Ω) :
    eventMass
        (atoms.map (fun atom => (atom.1, factor * atom.2))) event =
      factor * eventMass atoms event := by
  induction atoms with
  | nil =>
      simp [eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases h : event ω <;>
        simp [eventMass, h, ih, Nat.mul_add]

theorem totalMass_append (left right : List (Ω × Nat)) :
    totalMass (left ++ right) = totalMass left + totalMass right := by
  induction left with
  | nil =>
      simp [totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      simp [totalMass, ih, Nat.add_assoc]

theorem eventMass_append (left right : List (Ω × Nat))
    (event : Event Ω) :
    eventMass (left ++ right) event =
      eventMass left event + eventMass right event := by
  induction left with
  | nil =>
      simp [eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases h : event value <;>
        simp [eventMass, h, ih, Nat.add_assoc]

theorem eventMass_false (atoms : List (Ω × Nat)) :
    eventMass atoms (fun _ => false) = 0 := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      simp [eventMass, ih]

theorem totalMass_map_weight (atoms : List (Ω × Nat))
    (label : Ω -> X) (factor : Nat) :
    totalMass (atoms.map (fun atom => (label atom.1, factor * atom.2))) =
      factor * totalMass atoms := by
  induction atoms with
  | nil =>
      simp [totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      simp [totalMass, ih, Nat.mul_add]

theorem eventMass_map_weight (atoms : List (Ω × Nat))
    (label : Ω -> X) (factor : Nat) (event : Event X) :
    eventMass (atoms.map (fun atom => (label atom.1, factor * atom.2))) event =
      factor * eventMass atoms (fun value => event (label value)) := by
  induction atoms with
  | nil =>
      simp [eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases h : event (label value) <;>
        simp [eventMass, h, ih, Nat.mul_add]

def weightedCartesian (left : List (Ω × Nat))
    (right : List (X × Nat)) : List ((Ω × X) × Nat) :=
  left.flatMap (fun leftAtom =>
    right.map (fun rightAtom =>
      ((leftAtom.1, rightAtom.1), leftAtom.2 * rightAtom.2)))

theorem totalMass_weightedCartesian (left : List (Ω × Nat))
    (right : List (X × Nat)) :
    totalMass (weightedCartesian left right) =
      totalMass left * totalMass right := by
  induction left with
  | nil =>
      simp [weightedCartesian, totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      change
        totalMass
            (right.map (fun rightAtom =>
              ((value, rightAtom.1), weight * rightAtom.2)) ++
              weightedCartesian atoms right) = _
      rw [totalMass_append,
        totalMass_map_weight right (fun rightValue => (value, rightValue)) weight,
        ih]
      simp [totalMass, Nat.add_mul]

theorem eventMass_weightedCartesian (left : List (Ω × Nat))
    (right : List (X × Nat)) (leftEvent : Event Ω)
    (rightEvent : Event X) :
    eventMass (weightedCartesian left right)
        (fun pair => leftEvent pair.1 && rightEvent pair.2) =
      eventMass left leftEvent * eventMass right rightEvent := by
  induction left with
  | nil =>
      simp [weightedCartesian, eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      change
        eventMass
            (right.map (fun rightAtom =>
              ((value, rightAtom.1), weight * rightAtom.2)) ++
              weightedCartesian atoms right)
            (fun pair => leftEvent pair.1 && rightEvent pair.2) = _
      rw [eventMass_append,
        eventMass_map_weight right
          (fun rightValue => (value, rightValue)) weight, ih]
      cases h : leftEvent value <;>
        simp [eventMass, eventMass_false, h, Nat.add_mul]

end FiniteProbRecord

/--
A finite rational probability record in common-denominator form.

The list `atoms` is a finite list of weighted outcomes.  Its weights sum to
the positive denominator `den`.  This is the constructive finite-support
version of a rational probability record after a common denominator has been
chosen.
-/
structure FiniteProbRecord (Ω : Type u) where
  atoms : List (Ω × Nat)
  den : Nat
  den_pos : 0 < den
  total_mass : FiniteProbRecord.totalMass atoms = den

namespace FiniteProbRecord

def probVal (R : FiniteProbRecord Ω) (E : Event Ω) : QProb where
  num := eventMass R.atoms E
  den := R.den
  den_pos := R.den_pos

theorem probVal_congr (R : FiniteProbRecord Ω) (E F : Event Ω)
    (pointwise : forall value, E value = F value) :
    QProb.Equiv (R.probVal E) (R.probVal F) := by
  have sameMass := eventMass_congr R.atoms E F pointwise
  simp [QProb.Equiv, probVal, sameMass]

theorem probVal_false (R : FiniteProbRecord Ω) :
    QProb.Equiv (R.probVal (fun _ => false)) QProb.zero := by
  simp [QProb.Equiv, probVal, eventMass_false, QProb.zero]

def singletonEvent [DecidableEq Ω] (value : Ω) : Event Ω :=
  fun candidate => decide (candidate = value)

def membershipEvent [DecidableEq Ω] (values : List Ω) : Event Ω :=
  fun candidate => decide (candidate ∈ values)

theorem probVal_union_disjoint (R : FiniteProbRecord Ω) (E F : Event Ω)
    (h : disjoint E F) :
    QProb.Equiv (R.probVal (union E F))
      (QProb.add (R.probVal E) (R.probVal F)) := by
  have hMass : eventMass R.atoms (union E F) =
      eventMass R.atoms E + eventMass R.atoms F := by
    induction R.atoms with
    | nil => rfl
    | cons atom atoms ih =>
        rcases atom with ⟨value, weight⟩
        cases hE : E value <;> cases hF : F value
        · simp [eventMass, union, hE, hF, ih]
        · simp [eventMass, union, hE, hF, ih]
          omega
        · simp [eventMass, union, hE, hF, ih]
          omega
        · exact False.elim (h value hE hF)
  simp [QProb.Equiv, QProb.add, probVal, hMass, Nat.add_mul,
    Nat.mul_assoc]

theorem membershipEvent_cons [DecidableEq Ω] (value : Ω) (values : List Ω) :
    membershipEvent (value :: values) =
      union (singletonEvent value) (membershipEvent values) := by
  funext candidate
  simp [membershipEvent, singletonEvent, union]

theorem singleton_membership_disjoint [DecidableEq Ω]
    {value : Ω} {values : List Ω} (fresh : value ∉ values) :
    disjoint (singletonEvent value) (membershipEvent values) := by
  intro candidate hSingleton hMembership
  have same : candidate = value := by
    simpa [singletonEvent] using hSingleton
  have member : candidate ∈ values := by
    simpa [membershipEvent] using hMembership
  exact fresh (same ▸ member)

theorem probVal_membership_equiv_listSum [DecidableEq Ω]
    (R : FiniteProbRecord Ω) (values : List Ω) (nodup : values.Nodup) :
    QProb.Equiv (R.probVal (membershipEvent values))
      (QProb.listSum (values.map (fun value =>
        R.probVal (singletonEvent value)))) := by
  induction values with
  | nil =>
      have emptyEvent : membershipEvent ([] : List Ω) = fun _ => false := by
        funext value
        simp [membershipEvent]
      rw [emptyEvent]
      simp [QProb.listSum, probVal, eventMass_false,
        QProb.Equiv, QProb.zero]
  | cons value values ih =>
      have fresh : value ∉ values := (List.nodup_cons.mp nodup).1
      have tailNodup : values.Nodup := (List.nodup_cons.mp nodup).2
      rw [membershipEvent_cons]
      exact QProb.equiv_trans
        (probVal_union_disjoint R _ _
          (singleton_membership_disjoint fresh))
        (QProb.add_congr (QProb.equiv_refl _)
          (ih tailNodup))

theorem membershipEvent_filter [DecidableEq Ω]
    (values : List Ω) (complete : forall value, value ∈ values)
    (event : Event Ω) :
    membershipEvent (values.filter event) = event := by
  funext value
  cases hEvent : event value with
  | false => simp [membershipEvent, hEvent]
  | true => simp [membershipEvent, hEvent, complete value]

theorem probVal_equiv_listSum_singletons [DecidableEq Ω]
    (R : FiniteProbRecord Ω) (values : List Ω)
    (nodup : values.Nodup) (complete : forall value, value ∈ values)
    (event : Event Ω) :
    QProb.Equiv (R.probVal event)
      (QProb.listSum ((values.filter event).map
        (fun value => R.probVal (singletonEvent value)))) := by
  have h := probVal_membership_equiv_listSum R (values.filter event)
    (List.Sublist.nodup List.filter_sublist nodup)
  rw [membershipEvent_filter values complete event] at h
  exact h

/-- On a finite enumerated type, singleton masses determine every event. -/
theorem probVal_extensional_of_singletons [DecidableEq Ω]
    (left right : FiniteProbRecord Ω) (values : List Ω)
    (nodup : values.Nodup) (complete : forall value, value ∈ values)
    (singletons : forall value,
      QProb.Equiv (left.probVal (singletonEvent value))
        (right.probVal (singletonEvent value)))
    (event : Event Ω) :
    QProb.Equiv (left.probVal event) (right.probVal event) := by
  exact QProb.equiv_trans
    (probVal_equiv_listSum_singletons left values nodup complete event)
    (QProb.equiv_trans
      (QProb.listSum_map_congr (values.filter event)
        (fun value => left.probVal (singletonEvent value))
        (fun value => right.probVal (singletonEvent value)) singletons)
      (QProb.equiv_symm
        (probVal_equiv_listSum_singletons right values nodup complete event)))

def probRat (R : FiniteProbRecord Ω) (E : Event Ω) : Rat :=
  (R.probVal E).toRat

theorem eventMass_pos_of_probRat_pos (R : FiniteProbRecord Ω)
    (event : Event Ω) (h : 0 < R.probRat event) :
    0 < eventMass R.atoms event := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hProbZero : R.probRat event = 0 := by
    simp [probRat, probVal, QProb.toRat, Rat.div_def, hzero]
  rw [hProbZero] at h
  simp at h

def map (R : FiniteProbRecord Ω) (f : Ω → X) : FiniteProbRecord X where
  atoms := R.atoms.map (fun atom => (f atom.1, atom.2))
  den := R.den
  den_pos := R.den_pos
  total_mass := by
    rw [totalMass_map_labels, R.total_mass]

theorem map_probVal (R : FiniteProbRecord Ω) (f : Ω → X)
    (event : Event X) :
    QProb.Equiv ((R.map f).probVal event)
      (R.probVal (fun omega => event (f omega))) := by
  simp [QProb.Equiv, map, probVal, eventMass_map_labels]

def condition (R : FiniteProbRecord Ω) (evidence : Event Ω)
    (hEvidence : 0 < R.probRat evidence) : FiniteProbRecord Ω where
  atoms := R.atoms.filter (fun atom => evidence atom.1)
  den := eventMass R.atoms evidence
  den_pos := R.eventMass_pos_of_probRat_pos evidence hEvidence
  total_mass := totalMass_filter_event R.atoms evidence

theorem normalization (R : FiniteProbRecord Ω) :
    QProb.Equiv (R.probVal topEvent) QProb.one := by
  simp [QProb.Equiv, probVal, QProb.one, eventMass_top, R.total_mass]

theorem probRat_top (R : FiniteProbRecord Ω) :
    R.probRat topEvent = 1 := by
  simp [probRat, probVal, QProb.toRat, eventMass_top, R.total_mass,
    Rat.div_def]
  exact Rat.mul_inv_cancel _ (by
    exact_mod_cast Nat.ne_of_gt R.den_pos)

theorem map_probRat (R : FiniteProbRecord Ω) (f : Ω → X)
    (event : Event X) :
    (R.map f).probRat event = R.probRat (fun ω => event (f ω)) := by
  simp [map, probRat, probVal, QProb.toRat, eventMass_map_labels]

theorem condition_probRat (R : FiniteProbRecord Ω)
    (evidence event : Event Ω) (hEvidence : 0 < R.probRat evidence) :
    (R.condition evidence hEvidence).probRat event =
      R.probRat (fun ω => evidence ω && event ω) / R.probRat evidence := by
  have hDenRat : (R.den : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt R.den_pos
  simp [probRat, condition, probVal, QProb.toRat, eventMass_filter_event,
    Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.mul_assoc]
  have hCancel :
      (R.den : Rat)⁻¹ *
          ((R.den : Rat) * (eventMass R.atoms evidence : Rat)⁻¹) =
        (eventMass R.atoms evidence : Rat)⁻¹ := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel _ hDenRat, Rat.one_mul]
  rw [hCancel]

def toUrn (R : FiniteProbRecord Ω) : UrnProb Ω :=
  UrnProb.ofList (expand R.atoms) (by
    rw [length_expand, R.total_mass]
    exact R.den_pos)

def ofUrn (μ : UrnProb Ω) : FiniteProbRecord Ω where
  atoms := μ.support.map (fun ω => (ω, 1))
  den := μ.n
  den_pos := μ.pos
  total_mass := by
    rw [totalMass_unit, μ.support_length]

def AgreesWith (R : FiniteProbRecord Ω) (μ : UrnProb Ω) : Prop :=
  ∀ E : Event Ω, QProb.Equiv (R.probVal E) (μ.probVal E)

theorem toUrn_agrees (R : FiniteProbRecord Ω) :
    AgreesWith R R.toUrn := by
  intro E
  have hsupport : R.toUrn.support = expand R.atoms := by
    simp [toUrn, UrnProb.support_ofList]
  have hcount : R.toUrn.probNum E = eventMass R.atoms E := by
    rw [UrnProb.probNum, hsupport, count_expand]
  have hn : R.toUrn.n = R.den := by
    simp [toUrn, UrnProb.ofList, length_expand, R.total_mass]
  simp [probVal, UrnProb.probVal, QProb.Equiv, hcount, hn]

theorem ofUrn_agrees (μ : UrnProb Ω) :
    AgreesWith (ofUrn μ) μ := by
  intro E
  simp [ofUrn, probVal, UrnProb.probVal, UrnProb.probNum,
    QProb.Equiv, eventMass_unit]

theorem record_to_urn_extensional (R : FiniteProbRecord Ω) :
    ∀ E : Event Ω, QProb.Equiv (R.probVal E) (R.toUrn.probVal E) :=
  R.toUrn_agrees

theorem urn_to_record_extensional (μ : UrnProb Ω) :
    ∀ E : Event Ω, QProb.Equiv ((ofUrn μ).probVal E) (μ.probVal E) :=
  ofUrn_agrees μ

end FiniteProbRecord

/-!
## Products of finite rational records

This constructor is used twice by causal functionalisation: first to sample a
complete response table for one CPT, and then to assemble the independent
response-table seeds of all observed variables.
-/

/-- Constructively remove repetitions while retaining finite coverage. -/
def deduplicate [DecidableEq X] : List X -> List X
  | [] => []
  | value :: values =>
      let tail := deduplicate values
      if value ∈ tail then tail else value :: tail

theorem mem_deduplicate [DecidableEq X] (value : X) (values : List X) :
    value ∈ deduplicate values <-> value ∈ values := by
  induction values with
  | nil => simp [deduplicate]
  | cons head tail ih =>
      simp only [deduplicate]
      by_cases duplicate : head ∈ deduplicate tail
      · rw [if_pos duplicate]
        constructor
        · intro member
          exact List.mem_cons.mpr (Or.inr (ih.mp member))
        · intro member
          rcases List.mem_cons.mp member with same | member
          · exact same ▸ duplicate
          · exact ih.mpr member
      · rw [if_neg duplicate]
        simp [ih]

theorem deduplicate_nodup [DecidableEq X] (values : List X) :
    (deduplicate values).Nodup := by
  induction values with
  | nil => simp [deduplicate]
  | cons head tail ih =>
      simp only [deduplicate]
      by_cases duplicate : head ∈ deduplicate tail
      · rw [if_pos duplicate]
        exact ih
      · rw [if_neg duplicate]
        exact List.nodup_cons.mpr ⟨duplicate, ih⟩

namespace FiniteProduct

abbrev Assignment (n : Nat) (Value : Fin n -> Type u) :=
  (i : Fin n) -> Value i

def assignmentDecidableEq : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> DecidableEq (Value i)) ->
    DecidableEq (Assignment n Value)
  | 0, _, _ => fun left right =>
      isTrue (by
        funext i
        exact Fin.elim0 i)
  | n + 1, Value, decEq => fun left right =>
      match decEq (Fin.last n) (left (Fin.last n)) (right (Fin.last n)) with
      | isFalse differentLast =>
          isFalse (fun equal => differentLast (congrFun equal (Fin.last n)))
      | isTrue equalLast =>
          match assignmentDecidableEq n (fun i => Value i.castSucc)
              (fun i => decEq i.castSucc)
              (fun i => left i.castSucc) (fun i => right i.castSucc) with
          | isFalse differentInitial =>
              isFalse (fun equal => differentInitial (by
                funext i
                exact congrFun equal i.castSucc))
          | isTrue equalInitial =>
              isTrue (by
                funext i
                refine Fin.lastCases ?_ (fun earlier => ?_) i
                · exact equalLast
                · exact congrFun equalInitial earlier)

def snocCases {n : Nat} {motive : Fin (n + 1) -> Sort u}
    (last : motive (Fin.last n))
    (initial : (i : Fin n) -> motive i.castSucc)
    (i : Fin (n + 1)) : motive i :=
  if h : i.val < n then
    let earlier : Fin n := ⟨i.val, h⟩
    have same : earlier.castSucc = i := Fin.ext (Eq.refl i.val)
    same ▸ initial earlier
  else
    have atLast : i.val = n := Nat.eq_of_lt_succ_of_not_lt i.isLt h
    have same : Fin.last n = i := Fin.ext atLast.symm
    same ▸ last

def extend {n : Nat} {Value : Fin (n + 1) -> Type u}
    (last : Value (Fin.last n))
    (initial : (i : Fin n) -> Value i.castSucc) : Assignment (n + 1) Value :=
  fun i => snocCases last initial i

@[simp] theorem extend_last {n : Nat} {Value : Fin (n + 1) -> Type u}
    (last : Value (Fin.last n))
    (initial : (i : Fin n) -> Value i.castSucc) :
    extend last initial (Fin.last n) = last := by
  unfold extend snocCases
  have hnot : Not ((Fin.last n).val < n) := Nat.lt_irrefl n
  rw [dif_neg hnot]

@[simp] theorem extend_castSucc {n : Nat} {Value : Fin (n + 1) -> Type u}
    (last : Value (Fin.last n))
    (initial : (i : Fin n) -> Value i.castSucc) (i : Fin n) :
    extend last initial i.castSucc = initial i := by
  unfold extend snocCases
  have hpos : i.castSucc.val < n := i.isLt
  rw [dif_pos hpos]
  let earlier : Fin n := ⟨i.castSucc.val, hpos⟩
  have hearlier : earlier = i := Fin.ext (Eq.refl i.val)
  cases hearlier
  rfl

theorem castSucc_ne_last {n : Nat} (i : Fin n) :
    i.castSucc ≠ Fin.last n :=
  Fin.ne_of_lt i.castSucc_lt_last

theorem last_ne_castSucc {n : Nat} (i : Fin n) :
    Fin.last n ≠ i.castSucc :=
  Ne.symm (castSucc_ne_last i)

def denominator : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> FiniteProbRecord (Value i)) -> Nat
  | 0, _, _ => 1
  | n + 1, Value, factors =>
      (factors (Fin.last n)).den *
        denominator n (fun i => Value i.castSucc)
          (fun i => factors i.castSucc)

def atoms : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) ->
    List (Assignment n Value × Nat)
  | 0, _, _ => [(fun i => Fin.elim0 i, 1)]
  | n + 1, Value, factors =>
      let prefixAtoms :=
        atoms n (fun i => Value i.castSucc) (fun i => factors i.castSucc)
      (FiniteProbRecord.weightedCartesian
          (factors (Fin.last n)).atoms prefixAtoms).map (fun atom =>
        (extend atom.1.1 atom.1.2, atom.2))

def enumeration : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> List (Value i)) -> List (Assignment n Value)
  | 0, _, _ => [fun i => Fin.elim0 i]
  | n + 1, Value, values =>
      (values (Fin.last n)).flatMap (fun last =>
        (enumeration n (fun i => Value i.castSucc)
          (fun i => values i.castSucc)).map (fun initial =>
            extend last initial))

theorem enumeration_complete (n : Nat) (Value : Fin n -> Type u)
    (values : (i : Fin n) -> List (Value i))
    (complete : forall i value, value ∈ values i)
    (assignment : Assignment n Value) :
    assignment ∈ enumeration n Value values := by
  induction n with
  | zero =>
      have hAssignment : assignment = fun i => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      rw [hAssignment]
      exact List.mem_cons_self
  | succ n ih =>
      rw [enumeration]
      let last := assignment (Fin.last n)
      let initial : (i : Fin n) -> Value i.castSucc :=
        fun i => assignment i.castSucc
      have hLast : last ∈ values (Fin.last n) :=
        complete (Fin.last n) last
      have hInitial :
          initial ∈ enumeration n (fun i => Value i.castSucc)
            (fun i => values i.castSucc) :=
        ih (fun i => Value i.castSucc) (fun i => values i.castSucc)
          (fun i value => complete i.castSucc value) initial
      have hMapped :
          extend last initial ∈
            (enumeration n (fun i => Value i.castSucc)
              (fun i => values i.castSucc)).map (fun initialAssignment =>
                extend last initialAssignment) :=
        List.mem_map_of_mem hInitial
      have hFlat :
          extend last initial ∈
            (values (Fin.last n)).flatMap (fun final =>
              (enumeration n (fun i => Value i.castSucc)
                (fun i => values i.castSucc)).map (fun initialAssignment =>
                  extend final initialAssignment)) :=
        List.mem_flatMap_of_mem hLast hMapped
      have hAssignment : extend last initial = assignment := by
        funext i
        refine Fin.lastCases ?_ (fun earlier => ?_) i
        · change extend last initial (Fin.last n) = last
          exact extend_last last initial
        · change extend last initial earlier.castSucc = initial earlier
          exact extend_castSucc last initial earlier
      exact hAssignment ▸ hFlat

def natProduct : (n : Nat) -> (Fin n -> Nat) -> Nat
  | 0, _ => 1
  | n + 1, values =>
      values (Fin.last n) * natProduct n (fun i => values i.castSucc)

def qProduct : (n : Nat) -> (Fin n -> QProb) -> QProb
  | 0, _ => QProb.one
  | n + 1, values =>
      QProb.mul (values (Fin.last n))
        (qProduct n (fun i => values i.castSucc))

def ratProduct : (n : Nat) -> (Fin n -> Rat) -> Rat
  | 0, _ => 1
  | n + 1, values =>
      values (Fin.last n) * ratProduct n (fun i => values i.castSucc)

def rectangularEvent : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> Value i -> Bool) -> Event (Assignment n Value)
  | 0, _, _, _ => true
  | n + 1, Value, events, assignment =>
      events (Fin.last n) (assignment (Fin.last n)) &&
      rectangularEvent n (fun i => Value i.castSucc)
          (fun i => events i.castSucc) (fun i => assignment i.castSucc)

theorem rectangularEvent_assignment_congr (n : Nat)
    (Value : Fin n -> Type u) (events : (i : Fin n) -> Value i -> Bool)
    (left right : Assignment n Value)
    (h : forall i, left i = right i) :
    rectangularEvent n Value events left =
      rectangularEvent n Value events right := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (events (Fin.last n) (left (Fin.last n)) &&
          rectangularEvent n (fun i => Value i.castSucc)
            (fun i => events i.castSucc) (fun i => left i.castSucc)) =
        (events (Fin.last n) (right (Fin.last n)) &&
          rectangularEvent n (fun i => Value i.castSucc)
            (fun i => events i.castSucc) (fun i => right i.castSucc))
      rw [h (Fin.last n)]
      exact congrArg (fun suffix =>
        events (Fin.last n) (right (Fin.last n)) && suffix)
        (ih (fun i => Value i.castSucc) (fun i => events i.castSucc)
          (fun i => left i.castSucc) (fun i => right i.castSucc)
          (fun i => h i.castSucc))

theorem denominator_pos (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) :
    0 < denominator n Value factors := by
  induction n with
  | zero =>
      simp [denominator]
  | succ n ih =>
      exact Nat.mul_pos (factors (Fin.last n)).den_pos
        (ih (fun i => Value i.castSucc) (fun i => factors i.castSucc))

theorem totalMass_atoms (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) :
    FiniteProbRecord.totalMass (atoms n Value factors) =
      denominator n Value factors := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      let productAtoms :=
        FiniteProbRecord.weightedCartesian
          (factors (Fin.last n)).atoms
          (atoms n (fun i => Value i.castSucc)
            (fun i => factors i.castSucc))
      calc
        FiniteProbRecord.totalMass (atoms (n + 1) Value factors) =
            FiniteProbRecord.totalMass productAtoms := by
              simpa [atoms, productAtoms] using
                FiniteProbRecord.totalMass_map_labels productAtoms
                  (fun pair => extend pair.1 pair.2)
        _ = FiniteProbRecord.totalMass (factors (Fin.last n)).atoms *
              FiniteProbRecord.totalMass
                (atoms n (fun i => Value i.castSucc)
                  (fun i => factors i.castSucc)) := by
              exact FiniteProbRecord.totalMass_weightedCartesian _ _
        _ = denominator (n + 1) Value factors := by
              rw [(factors (Fin.last n)).total_mass,
                ih (fun i => Value i.castSucc)
                  (fun i => factors i.castSucc)]
              rfl

theorem eventMass_atoms (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i))
    (events : (i : Fin n) -> Value i -> Bool) :
    FiniteProbRecord.eventMass (atoms n Value factors)
        (rectangularEvent n Value events) =
      natProduct n (fun i =>
        FiniteProbRecord.eventMass (factors i).atoms (events i)) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      let productAtoms :=
        FiniteProbRecord.weightedCartesian
          (factors (Fin.last n)).atoms
          (atoms n (fun i => Value i.castSucc)
            (fun i => factors i.castSucc))
      have hMap := FiniteProbRecord.eventMass_map_labels productAtoms
        (fun pair : Value (Fin.last n) ×
            Assignment n (fun i => Value i.castSucc) =>
          extend pair.1 pair.2)
        (rectangularEvent (n + 1) Value events)
      have hEvent (pair : Value (Fin.last n) ×
          Assignment n (fun i => Value i.castSucc)) :
          rectangularEvent (n + 1) Value events
              (extend pair.1 pair.2) =
            (events (Fin.last n) pair.1 &&
              rectangularEvent n (fun i => Value i.castSucc)
                (fun i => events i.castSucc) pair.2) := by
        change
          (events (Fin.last n) (extend pair.1 pair.2 (Fin.last n)) &&
            rectangularEvent n (fun i => Value i.castSucc)
              (fun i => events i.castSucc)
              (fun i => extend pair.1 pair.2 i.castSucc)) =
          (events (Fin.last n) pair.1 &&
            rectangularEvent n (fun i => Value i.castSucc)
              (fun i => events i.castSucc) pair.2)
        rw [extend_last]
        exact congrArg (fun suffix =>
          events (Fin.last n) pair.1 && suffix)
          (rectangularEvent_assignment_congr n
            (fun i => Value i.castSucc) (fun i => events i.castSucc)
            (fun i => extend pair.1 pair.2 i.castSucc) pair.2
            (fun i => extend_castSucc pair.1 pair.2 i))
      calc
        FiniteProbRecord.eventMass (atoms (n + 1) Value factors)
            (rectangularEvent (n + 1) Value events) =
            FiniteProbRecord.eventMass productAtoms
              (fun pair => rectangularEvent (n + 1) Value events
                (extend pair.1 pair.2)) := by
              change
                FiniteProbRecord.eventMass
                    (productAtoms.map (fun atom =>
                      (extend atom.1.1 atom.1.2, atom.2)))
                    (rectangularEvent (n + 1) Value events) =
                  FiniteProbRecord.eventMass productAtoms
                    (fun pair => rectangularEvent (n + 1) Value events
                      (extend pair.1 pair.2))
              exact hMap
        _ = FiniteProbRecord.eventMass productAtoms
              (fun pair =>
                events (Fin.last n) pair.1 &&
                  rectangularEvent n (fun i => Value i.castSucc)
                    (fun i => events i.castSucc) pair.2) := by
              exact FiniteProbRecord.eventMass_congr productAtoms _ _ hEvent
        _ = _ := by
              rw [FiniteProbRecord.eventMass_weightedCartesian,
                ih (fun i => Value i.castSucc)
                  (fun i => factors i.castSucc)
                  (fun i => events i.castSucc)]
              rfl

/-- The exact independent product of finitely many probability records. -/
def record (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) :
    FiniteProbRecord (Assignment n Value) where
  atoms := atoms n Value factors
  den := denominator n Value factors
  den_pos := denominator_pos n Value factors
  total_mass := totalMass_atoms n Value factors

/-- The product record satisfies its rectangular-event law constructively. -/
theorem record_rectangular_probVal (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i))
    (events : (i : Fin n) -> Value i -> Bool) :
    QProb.Equiv
      ((record n Value factors).probVal
        (rectangularEvent n Value events))
      (qProduct n (fun i => (factors i).probVal (events i))) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      let prefixValue := fun i : Fin n => Value i.castSucc
      let prefixFactors := fun i : Fin n => factors i.castSucc
      let prefixEvents := fun i : Fin n => events i.castSucc
      let lastValue := (factors (Fin.last n)).probVal (events (Fin.last n))
      let prefixValueProb :=
        (record n prefixValue prefixFactors).probVal
          (rectangularEvent n prefixValue prefixEvents)
      have hStep :
          QProb.Equiv
            ((record (n + 1) Value factors).probVal
              (rectangularEvent (n + 1) Value events))
            (QProb.mul lastValue prefixValueProb) := by
        simp only [record, FiniteProbRecord.probVal, eventMass_atoms,
          denominator, natProduct, QProb.Equiv, QProb.mul, lastValue,
          prefixValueProb, prefixValue, prefixFactors, prefixEvents]
      exact QProb.equiv_trans hStep
        (QProb.mul_congr (QProb.equiv_refl lastValue)
          (ih prefixValue prefixFactors prefixEvents))

theorem record_rectangular_probRat (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i))
    (events : (i : Fin n) -> Value i -> Bool) :
    (record n Value factors).probRat (rectangularEvent n Value events) =
      ratProduct n (fun i => (factors i).probRat (events i)) := by
  induction n with
  | zero =>
      have hInvOne : (1 : Rat)⁻¹ = 1 := by
        simpa only [Rat.one_mul] using
          Rat.mul_inv_cancel (1 : Rat) (by decide)
      simp [record, rectangularEvent, ratProduct,
        FiniteProbRecord.probRat, FiniteProbRecord.probVal,
        QProb.toRat, atoms, denominator, FiniteProbRecord.eventMass,
        Rat.div_def, hInvOne]
  | succ n ih =>
      rw [ratProduct]
      rw [← ih (fun i => Value i.castSucc) (fun i => factors i.castSucc)
        (fun i => events i.castSucc)]
      simp [record, FiniteProbRecord.probRat,
        FiniteProbRecord.probVal, QProb.toRat, eventMass_atoms,
        denominator, natProduct, Rat.div_def,
        Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm]
      congr 1
      let prefixNumerator : Rat :=
        (natProduct n (fun i =>
          FiniteProbRecord.eventMass (factors i.castSucc).atoms
            (events i.castSucc)) : Nat)
      let prefixInverse : Rat :=
        (denominator n (fun i => Value i.castSucc)
          (fun i => factors i.castSucc) : Rat)⁻¹
      let lastNumerator : Rat :=
        (FiniteProbRecord.eventMass (factors (Fin.last n)).atoms
          (events (Fin.last n)) : Nat)
      change prefixInverse * (lastNumerator * prefixNumerator) =
        lastNumerator * (prefixInverse * prefixNumerator)
      calc
        prefixInverse * (lastNumerator * prefixNumerator) =
            (prefixInverse * lastNumerator) * prefixNumerator := by
              rw [Rat.mul_assoc]
        _ = (lastNumerator * prefixInverse) * prefixNumerator := by
              rw [Rat.mul_comm prefixInverse lastNumerator]
        _ = lastNumerator * (prefixInverse * prefixNumerator) := by
              rw [Rat.mul_assoc]

theorem rectangularEvent_true (n : Nat) (Value : Fin n -> Type u)
    (assignment : Assignment n Value) :
    rectangularEvent n Value (fun _ _ => true) assignment = true := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [rectangularEvent,
        ih (fun i => Value i.castSucc) (fun i => assignment i.castSucc)]

theorem rectangularEvent_singleton (n : Nat) (Outcome : Type u)
    (chosen : Fin n) (event : Outcome -> Bool)
    (assignment : Fin n -> Outcome) :
    rectangularEvent n (fun _ => Outcome)
        (fun i value => if i = chosen then event value else true) assignment =
      event (assignment chosen) := by
  induction n with
  | zero =>
      exact Fin.elim0 chosen
  | succ n ih =>
      refine Fin.lastCases ?_ (fun earlier => ?_) chosen
      · have hInitialEvents :
            (fun (i : Fin n) (value : Outcome) =>
              if i.castSucc = Fin.last n then event value else true) =
            (fun _ _ => true) := by
          funext i value
          simp [castSucc_ne_last]
        rw [rectangularEvent]
        rw [if_pos rfl]
        change
          (event (assignment (Fin.last n)) &&
              rectangularEvent n (fun _ => Outcome)
                (fun i value =>
                  if i.castSucc = Fin.last n then event value else true)
                (fun i => assignment i.castSucc)) =
            event (assignment (Fin.last n))
        rw [hInitialEvents, rectangularEvent_true]
        simp
      · have hInitialEvents :
            (fun (i : Fin n) (value : Outcome) =>
              if i.castSucc = earlier.castSucc then event value else true) =
            (fun i value => if i = earlier then event value else true) := by
          funext i value
          simp [Fin.ext_iff]
        rw [rectangularEvent]
        change
          ((if Fin.last n = earlier.castSucc then
              event (assignment (Fin.last n)) else true) &&
              rectangularEvent n (fun _ => Outcome)
                (fun i value =>
                  if i.castSucc = earlier.castSucc then event value else true)
                (fun i => assignment i.castSucc)) =
            event (assignment earlier.castSucc)
        rw [if_neg (last_ne_castSucc earlier), hInitialEvents,
          ih earlier (fun i => assignment i.castSucc)]
        simp

theorem ratProduct_one (n : Nat) :
    ratProduct n (fun _ => (1 : Rat)) = 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [ratProduct, ih]

theorem ratProduct_singleton (n : Nat) (chosen : Fin n)
    (selected : Rat) :
    ratProduct n (fun i => if i = chosen then selected else 1) = selected := by
  induction n with
  | zero =>
      exact Fin.elim0 chosen
  | succ n ih =>
      refine Fin.lastCases ?_ (fun earlier => ?_) chosen
      · have hInitial :
            (fun i : Fin n =>
              if i.castSucc = Fin.last n then selected else 1) =
            (fun _ => 1) := by
          funext i
          simp [castSucc_ne_last]
        rw [ratProduct]
        rw [if_pos rfl]
        change selected *
          ratProduct n (fun i =>
            if i.castSucc = Fin.last n then selected else 1) = selected
        rw [hInitial, ratProduct_one, Rat.mul_one]
      · have hInitial :
            (fun i : Fin n =>
              if i.castSucc = earlier.castSucc then selected else 1) =
            (fun i => if i = earlier then selected else 1) := by
          funext i
          simp [Fin.ext_iff]
        rw [ratProduct]
        change
          (if Fin.last n = earlier.castSucc then selected else 1) *
              ratProduct n (fun i =>
                if i.castSucc = earlier.castSucc then selected else 1) =
            selected
        rw [if_neg (last_ne_castSucc earlier), hInitial, ih earlier,
          Rat.one_mul]

/-- A coordinate of the independent product has its declared marginal law. -/
theorem record_coordinate_probRat (n : Nat) (Outcome : Type u)
    (factors : Fin n -> FiniteProbRecord Outcome)
    (chosen : Fin n) (event : Outcome -> Bool) :
    (record n (fun _ => Outcome) factors).probRat
        (fun assignment => event (assignment chosen)) =
      (factors chosen).probRat event := by
  let events : (i : Fin n) -> Outcome -> Bool :=
    fun i value => if i = chosen then event value else true
  have hRectangular :=
    record_rectangular_probRat n (fun _ => Outcome) factors events
  have hEvent :
      rectangularEvent n (fun _ => Outcome) events =
        (fun assignment => event (assignment chosen)) := by
    funext assignment
    exact rectangularEvent_singleton n Outcome chosen event assignment
  have hFactors :
      (fun i => (factors i).probRat (events i)) =
        (fun i => if i = chosen then (factors i).probRat event else 1) := by
    funext i
    by_cases h : i = chosen
    · simp [events, h]
    · have hTop : (fun value => if i = chosen then event value else true) =
          topEvent := by
        funext value
        simp [h, topEvent]
      rw [show events i = topEvent by exact hTop]
      simpa [h] using (factors i).probRat_top
  rw [hEvent, hFactors] at hRectangular
  have hSingle :
      (fun i => if i = chosen then (factors i).probRat event else 1) =
        (fun i => if i = chosen then (factors chosen).probRat event else 1) := by
    funext i
    by_cases h : i = chosen
    · subst i
      simp
    · simp [h]
  rw [hSingle] at hRectangular
  exact hRectangular.trans
    (ratProduct_singleton n chosen ((factors chosen).probRat event))

end FiniteProduct

/-!
## Generic common-denominator conversion

The finite probability records above store one common denominator.  The
following construction shows that this is not an additional restriction: an
arbitrary normalized family of nonnegative rational masses on a finite type
can be converted to that representation constructively.
-/

namespace CommonDenominator

private def zeroWithDenominator (p : QProb) : QProb where
  num := 0
  den := p.den
  den_pos := p.den_pos

/-- The product of all denominators in a finite rational mass table. -/
def denominator (values : List Ω) (mass : Ω → QProb) : Nat :=
  values.foldr (fun ω den => (mass ω).den * den) 1

theorem denominator_pos (values : List Ω) (mass : Ω → QProb) :
    0 < denominator values mass := by
  induction values with
  | nil =>
      simp [denominator]
  | cons ω values ih =>
      exact Nat.mul_pos (mass ω).den_pos ih

/--
Integer weights obtained by putting every row over `denominator values mass`.
Earlier weights are multiplied whenever a new denominator is introduced.
-/
def atoms : (values : List Ω) → (mass : Ω → QProb) → List (Ω × Nat)
  | [], _ => []
  | ω :: values, mass =>
      (ω, (mass ω).num * denominator values mass) ::
        (atoms values mass).map
          (fun atom => (atom.1, (mass ω).den * atom.2))

/--
The sum of the selected masses.  A non-selected entry contributes a zero with
the entry's own denominator, so the resulting denominator is definitionally
the product of all denominators, independently of the event.
-/
def eventSum : (values : List Ω) → (mass : Ω → QProb) → Event Ω → QProb
  | [], _, _ => QProb.zero
  | ω :: values, mass, event =>
      QProb.add
        (if event ω then mass ω
          else zeroWithDenominator (mass ω))
        (eventSum values mass event)

theorem eventSum_den (values : List Ω) (mass : Ω → QProb)
    (event : Event Ω) :
    (eventSum values mass event).den = denominator values mass := by
  induction values with
  | nil =>
      rfl
  | cons ω values ih =>
      cases hEvent : event ω <;>
        simp [eventSum, denominator, QProb.add, zeroWithDenominator,
          hEvent, ih]

theorem eventMass_atoms (values : List Ω) (mass : Ω → QProb)
    (event : Event Ω) :
    FiniteProbRecord.eventMass (atoms values mass) event =
      (eventSum values mass event).num := by
  induction values with
  | nil =>
      rfl
  | cons ω values ih =>
      rw [atoms]
      simp only [FiniteProbRecord.eventMass]
      rw [FiniteProbRecord.eventMass_scale, ih]
      cases hEvent : event ω <;>
        simp [eventSum, QProb.add, zeroWithDenominator, hEvent,
          eventSum_den, Nat.mul_comm]

/--
A finite rational mass assignment before a common denominator has been chosen.
`values` explicitly witnesses finiteness and exhausts the outcome type.
-/
structure FiniteQMass (Ω : Type u) where
  values : List Ω
  nodup : values.Nodup
  complete : ∀ ω, ω ∈ values
  mass : Ω → QProb
  normalized : QProb.Equiv (eventSum values mass topEvent) QProb.one

namespace FiniteQMass

def probVal (M : FiniteQMass Ω) (event : Event Ω) : QProb :=
  eventSum M.values M.mass event

theorem common_total_mass (M : FiniteQMass Ω) :
    FiniteProbRecord.totalMass (atoms M.values M.mass) =
      denominator M.values M.mass := by
  have hEvent := eventMass_atoms M.values M.mass topEvent
  rw [FiniteProbRecord.eventMass_top] at hEvent
  have hDen := eventSum_den M.values M.mass topEvent
  have hNorm := M.normalized
  simp [QProb.Equiv, QProb.one] at hNorm
  calc
    FiniteProbRecord.totalMass (atoms M.values M.mass) =
        (eventSum M.values M.mass topEvent).num := hEvent
    _ = (eventSum M.values M.mass topEvent).den := hNorm
    _ = denominator M.values M.mass := hDen

/-- Construct the common-denominator probability record. -/
def toRecord (M : FiniteQMass Ω) : FiniteProbRecord Ω where
  atoms := atoms M.values M.mass
  den := denominator M.values M.mass
  den_pos := denominator_pos M.values M.mass
  total_mass := M.common_total_mass

/-- Every decidable event has the same rational probability after conversion. -/
theorem toRecord_preserves (M : FiniteQMass Ω) (event : Event Ω) :
    QProb.Equiv (M.toRecord.probVal event) (M.probVal event) := by
  simp [QProb.Equiv, toRecord, probVal, FiniteProbRecord.probVal,
    eventMass_atoms, eventSum_den]

/-- The resulting urn also preserves every event probability. -/
theorem toUrn_preserves (M : FiniteQMass Ω) (event : Event Ω) :
    QProb.Equiv (M.toRecord.toUrn.probVal event) (M.probVal event) := by
  exact QProb.equiv_trans
    (QProb.equiv_symm (M.toRecord.toUrn_agrees event))
    (M.toRecord_preserves event)

end FiniteQMass
end CommonDenominator

namespace ClaytonWaddington

/-!
Finite urn events as the Lean counterpart of the Clayton--Waddington-style
appendix argument.  An event in a symmetric urn is represented only by the
number of selected cells `k` in an urn of positive size `N`; relabelling
invariance is therefore built into the representation.
-/

structure UrnRatio where
  N : Nat
  k : Nat
  pos : 0 < N
  le : k ≤ N

namespace UrnRatio

def toQProb (u : UrnRatio) : QProb where
  num := u.k
  den := u.N
  den_pos := u.pos

def sameRatio (u v : UrnRatio) : Prop :=
  u.k * v.N = v.k * u.N

theorem sameRatio_toQProb {u v : UrnRatio}
    (h : sameRatio u v) :
    QProb.Equiv u.toQProb v.toQProb := by
  exact h

def refine (u : UrnRatio) (c : Nat) (hc : 0 < c) : UrnRatio where
  N := c * u.N
  k := c * u.k
  pos := Nat.mul_pos hc u.pos
  le := Nat.mul_le_mul_left c u.le

theorem refinement_preserves_ratio (u : UrnRatio)
    (c : Nat) (hc : 0 < c) :
    QProb.Equiv (u.refine c hc).toQProb u.toQProb := by
  simp [QProb.Equiv, toQProb, refine, Nat.mul_comm, Nat.mul_left_comm]

def complement (u : UrnRatio) : UrnRatio where
  N := u.N
  k := u.N - u.k
  pos := u.pos
  le := Nat.sub_le u.N u.k

theorem complement_rule (u : UrnRatio) :
    QProb.Equiv (QProb.add u.toQProb u.complement.toQProb) QProb.one := by
  have hsum : u.k + (u.N - u.k) = u.N := by
    rw [Nat.add_comm, Nat.sub_add_cancel u.le]
  simp [QProb.Equiv, QProb.add, QProb.one, toQProb, complement]
  rw [← Nat.add_mul, hsum]

def product (u v : UrnRatio) : UrnRatio where
  N := u.N * v.N
  k := u.k * v.k
  pos := Nat.mul_pos u.pos v.pos
  le := Nat.mul_le_mul u.le v.le

theorem product_rule (u v : UrnRatio) :
    QProb.Equiv (u.product v).toQProb
      (QProb.mul u.toQProb v.toQProb) := by
  simp [QProb.Equiv, QProb.mul, toQProb, product,
    Nat.mul_comm, Nat.mul_left_comm]

theorem rescaling_is_k_over_N (u : UrnRatio) :
    QProb.Equiv u.toQProb
      { num := u.k, den := u.N, den_pos := u.pos } := by
  rfl

/--
A primitive qualitative plausibility scale for finite symmetric urn events.

The scale does not start with numerical probabilities.  It starts with a type
of plausibility values, an equivalence relation on those values, and a strict
comparison.  The assumptions say that only the number of selected cells matters,
refining every cell into the same positive number of subcells preserves
plausibility, and larger selected subsets in a fixed urn are strictly more
plausible.
-/
structure QualitativeUrnScale where
  Plaus : Type u
  plaus : UrnRatio → Plaus
  eqv : Plaus → Plaus → Prop
  lt : Plaus → Plaus → Prop
  eqv_refl : ∀ a, eqv a a
  eqv_symm : ∀ {a b}, eqv a b → eqv b a
  eqv_trans : ∀ {a b c}, eqv a b → eqv b c → eqv a c
  same_counts_eqv :
    ∀ u v, u.N = v.N → u.k = v.k → eqv (plaus u) (plaus v)
  refinement_eqv :
    ∀ u (c : Nat) (hc : 0 < c),
      eqv (plaus (u.refine c hc)) (plaus u)
  strict_mono_same_urn :
    ∀ (N : Nat) (hN : 0 < N) {k l : Nat}
      (hk : k ≤ N) (hl : l ≤ N),
      k < l →
      lt
        (plaus { N := N, k := k, pos := hN, le := hk })
        (plaus { N := N, k := l, pos := hN, le := hl })
  lt_respects_eqv :
    ∀ {a b c d}, eqv a c → eqv b d → lt a b → lt c d
  eqv_lt_false :
    ∀ {a b}, eqv a b → lt a b → False

namespace QualitativeUrnScale

def commonLeft (u v : UrnRatio) : UrnRatio where
  N := v.N * u.N
  k := v.N * u.k
  pos := Nat.mul_pos v.pos u.pos
  le := Nat.mul_le_mul_left v.N u.le

def commonRight (u v : UrnRatio) : UrnRatio where
  N := v.N * u.N
  k := v.k * u.N
  pos := Nat.mul_pos v.pos u.pos
  le := Nat.mul_le_mul_right u.N v.le

theorem commonLeft_eqv (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.plaus (commonLeft u v)) (Q.plaus u) := by
  let refined := u.refine v.N v.pos
  have hsame :
      Q.eqv (Q.plaus (commonLeft u v)) (Q.plaus refined) := by
    apply Q.same_counts_eqv
    · rfl
    · rfl
  exact Q.eqv_trans hsame (Q.refinement_eqv u v.N v.pos)

theorem commonRight_eqv (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.plaus (commonRight u v)) (Q.plaus v) := by
  let refined := v.refine u.N u.pos
  have hsame :
      Q.eqv (Q.plaus (commonRight u v)) (Q.plaus refined) := by
    apply Q.same_counts_eqv
    · simp [commonRight, refined, refine, Nat.mul_comm]
    · simp [commonRight, refined, refine, Nat.mul_comm]
  exact Q.eqv_trans hsame (Q.refinement_eqv v u.N u.pos)

theorem sameRatio_implies_eqv (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : sameRatio u v) :
    Q.eqv (Q.plaus u) (Q.plaus v) := by
  have hcommon :
      Q.eqv (Q.plaus (commonLeft u v)) (Q.plaus (commonRight u v)) := by
    apply Q.same_counts_eqv
    · rfl
    · simp [commonLeft, commonRight, sameRatio] at h ⊢
      calc
        v.N * u.k = u.k * v.N := by
          exact Nat.mul_comm v.N u.k
        _ = v.k * u.N := h
  exact Q.eqv_trans
    (Q.eqv_symm (Q.commonLeft_eqv u v))
    (Q.eqv_trans hcommon (Q.commonRight_eqv u v))

theorem ratio_lt_implies_lt (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : u.k * v.N < v.k * u.N) :
    Q.lt (Q.plaus u) (Q.plaus v) := by
  have hcommon :
      Q.lt (Q.plaus (commonLeft u v)) (Q.plaus (commonRight u v)) := by
    apply Q.strict_mono_same_urn (v.N * u.N)
      (Nat.mul_pos v.pos u.pos)
      (commonLeft u v).le
      (commonRight u v).le
    simpa [commonLeft, commonRight, Nat.mul_comm] using h
  exact Q.lt_respects_eqv
    (Q.commonLeft_eqv u v)
    (Q.commonRight_eqv u v)
    hcommon

theorem eqv_implies_sameRatio (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.eqv (Q.plaus u) (Q.plaus v)) :
    sameRatio u v := by
  by_cases heq : u.k * v.N = v.k * u.N
  · exact heq
  · by_cases hlt : u.k * v.N < v.k * u.N
    · exact False.elim (Q.eqv_lt_false h (Q.ratio_lt_implies_lt hlt))
    · have hgt : v.k * u.N < u.k * v.N := by
        omega
      have hvu : Q.lt (Q.plaus v) (Q.plaus u) :=
        Q.ratio_lt_implies_lt hgt
      exact False.elim (Q.eqv_lt_false (Q.eqv_symm h) hvu)

theorem eqv_iff_sameRatio (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.plaus u) (Q.plaus v) ↔ sameRatio u v :=
  ⟨Q.eqv_implies_sameRatio, Q.sameRatio_implies_eqv⟩

/--
The qualitative representation theorem: the rational value `k/N` is a
well-defined rescaling of primitive qualitative plausibility classes.
-/
theorem rational_rescaling_well_defined (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.eqv (Q.plaus u) (Q.plaus v)) :
    QProb.Equiv u.toQProb v.toQProb := by
  exact sameRatio_toQProb (Q.eqv_implies_sameRatio h)

/--
The same rescaling is order-preserving: strict qualitative increase follows
from strict increase of the represented rational urn ratio.
-/
theorem rational_rescaling_order_preserving (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : u.k * v.N < v.k * u.N) :
    Q.lt (Q.plaus u) (Q.plaus v) := by
  exact Q.ratio_lt_implies_lt h

end QualitativeUrnScale

/--
The primitive finite-urn representation step.

Read `cell` as the common value of one equipossible cell.  Finite additivity
says that an event with `k` such cells has value `scale k cell`, while
normalization says that all `N` cells together have value one.  Under those
assumptions, the value forced for the event is `k/N`.
-/
theorem equal_cells_force_ratio (u : UrnRatio) (cell : QProb)
    (hwhole : QProb.Equiv (QProb.scale u.N cell) QProb.one) :
    QProb.Equiv (QProb.scale u.k cell) u.toQProb := by
  exact QProb.scale_forced_ratio u.pos cell hwhole

/--
An explicit packaging of the primitive assumptions used by the finite
Clayton--Waddington urn argument.

`whole_is_all_cells` is normalization plus equipossibility of the `N` cells.
`event_is_selected_cells` is the finite-additivity consequence that the event
made of `k` selected cells has the sum of `k` equal cell-values.
-/
structure PrimitiveUrnAssignment (u : UrnRatio) where
  cell : QProb
  value : QProb
  whole_is_all_cells :
    QProb.Equiv (QProb.scale u.N cell) QProb.one
  event_is_selected_cells :
    QProb.Equiv value (QProb.scale u.k cell)

theorem PrimitiveUrnAssignment.forces_ratio
    {u : UrnRatio} (A : PrimitiveUrnAssignment u) :
    QProb.Equiv A.value u.toQProb := by
  exact QProb.equiv_trans A.event_is_selected_cells
    (equal_cells_force_ratio u A.cell A.whole_is_all_cells)

end UrnRatio

end ClaytonWaddington

end Probability
end Thesis
