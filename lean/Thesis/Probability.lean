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

theorem equiv_trans {p q r : QProb}
    (hpq : Equiv p q) (hqr : Equiv q r) :
    Equiv p r := by
  apply Nat.eq_of_mul_eq_mul_right q.den_pos
  calc
    p.num * r.den * q.den = (p.num * q.den) * r.den := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    _ = (q.num * p.den) * r.den := by
      rw [hpq]
    _ = (q.num * r.den) * p.den := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    _ = (r.num * q.den) * p.den := by
      rw [hqr]
    _ = r.num * p.den * q.den := by
      simp [Nat.mul_comm, Nat.mul_left_comm]

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

end UrnProb

namespace FiniteProbRecord

def totalMass : List (Ω × Nat) → Nat
  | [] => 0
  | (_, w) :: atoms => w + totalMass atoms

def eventMass : List (Ω × Nat) → Event Ω → Nat
  | [], _ => 0
  | (ω, w) :: atoms, E =>
      if E ω then w + eventMass atoms E else eventMass atoms E

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
