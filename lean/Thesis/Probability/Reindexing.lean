import Thesis.Probability.Core

namespace Thesis
namespace Probability

/-!
# Finite-sum reindexing

The appendix treats a finite sum as a recursive fold over `Fin n`, taken in
an additive carrier whose equality is an explicit equivalence relation rather
than judgemental identity.  The carrier records exactly the data used in the
adjacent-swap argument: addition respects the equivalence, and it is
associative, commutative and unital up to that equivalence.

No result here is a statement about infinite series, unordered sums over
arbitrary types, or quotient types.  The sum is the finite fold of the
supplied addition, and a permutation is an explicitly inverted bijection of
`Fin n`.  The count-form instance used by urn invariance remains
`count_reindex` in `Core.lean`; this module supplies the named abstract
theorem and its `Nat` and `QProb` specializations.
-/

/--
An additive carrier is a type with an equivalence, a binary addition and a
zero, such that addition respects the equivalence and satisfies the finite
commutative-monoid laws up to that equivalence.

This is not a Lean typeclass hierarchy and is not a claim that `M` is a
quotient.  Callers retain the original presentations and transport equalities
by `Equiv`.
-/
structure AdditiveCarrier (M : Type u) where
  Equiv : M → M → Prop
  equiv_refl : ∀ x, Equiv x x
  equiv_symm : ∀ {x y}, Equiv x y → Equiv y x
  equiv_trans : ∀ {x y z}, Equiv x y → Equiv y z → Equiv x z
  add : M → M → M
  zero : M
  add_congr :
    ∀ {x x' y y'}, Equiv x x' → Equiv y y' → Equiv (add x y) (add x' y')
  add_assoc : ∀ x y z, Equiv (add (add x y) z) (add x (add y z))
  add_comm : ∀ x y, Equiv (add x y) (add y x)
  add_zero : ∀ x, Equiv (add x zero) x

namespace AdditiveCarrier

variable {M : Type u}

/-- Recursive finite sum, beginning at zero and adding one coordinate at a time. -/
def listSum (C : AdditiveCarrier M) : List M → M
  | [] => C.zero
  | value :: values => C.add value (listSum C values)

/-- An adjacent transposition changes the sum only by commutativity. -/
theorem listSum_swap (C : AdditiveCarrier M) (x y : M) (values : List M) :
    C.Equiv
      (listSum C (x :: y :: values))
      (listSum C (y :: x :: values)) := by
  have assoc_xy :
      C.Equiv
        (C.add x (C.add y (listSum C values)))
        (C.add (C.add x y) (listSum C values)) :=
    C.equiv_symm (C.add_assoc x y (listSum C values))
  have comm_xy :
      C.Equiv
        (C.add (C.add x y) (listSum C values))
        (C.add (C.add y x) (listSum C values)) :=
    C.add_congr (C.add_comm x y) (C.equiv_refl _)
  have assoc_yx :
      C.Equiv
        (C.add (C.add y x) (listSum C values))
        (C.add y (C.add x (listSum C values))) :=
    C.add_assoc y x (listSum C values)
  exact C.equiv_trans assoc_xy (C.equiv_trans comm_xy assoc_yx)

/--
Reordering a finite list does not change its sum.  The `Perm.swap` case is
exactly the adjacent-swap step used in the prose argument; transitivity
assembles a finite sequence of such swaps.
-/
theorem listSum_perm (C : AdditiveCarrier M) {xs ys : List M}
    (h : xs.Perm ys) :
    C.Equiv (listSum C xs) (listSum C ys) := by
  induction h with
  | nil => exact C.equiv_refl C.zero
  | cons _ _ ih => exact C.add_congr (C.equiv_refl _) ih
  | swap x y values => exact C.equiv_symm (listSum_swap C x y values)
  | trans _ _ ih ih' => exact C.equiv_trans ih ih'

/-- The finite fold of a `Fin n`-indexed family, in canonical index order. -/
def finSum (C : AdditiveCarrier M) (n : Nat) (u : Fin n → M) : M :=
  listSum C ((List.finRange n).map u)

/-!
The following constructive permutation reconstruction is copied in spirit
from `FiniteCellProduct`: the standard `List.perm_iff_count` proof in Lean's
library inherits `Classical.choice`.  Here both lists are finite enumerations
of `Fin n`, so decidable occurrence counts suffice.
-/

private theorem perm_cons_erase_constructive {A : Type u}
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

/-- Reconstruct a list permutation from matching decidable occurrence counts. -/
theorem perm_of_count_eq_constructive {A : Type u}
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
      have front := perm_cons_erase_constructive member
      have tailCounts : ∀ other,
          List.count other rest = List.count other (right.erase value) :=
        fun other => cancel_front_counts (countsEqual other) front
      exact ((ih tailCounts).cons value).trans front.symm

/-- Pointwise Boolean agreement, without function extensionality. -/
private theorem countP_eq_of_pointwise {A : Type u}
    (p q : A → Bool) : ∀ (values : List A),
    (∀ value, p value = q value) →
      values.countP p = values.countP q
  | [], _ => rfl
  | value :: values, h => by
      simp [List.countP_cons, h value, countP_eq_of_pointwise p q values h]

/-- Mapping preserves an already constructed list permutation. -/
private theorem perm_map_constructive {A : Type u} {B : Type v}
    (f : A → B) {xs ys : List A} (h : xs.Perm ys) :
    (xs.map f).Perm (ys.map f) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons _ _ ih => exact ih.cons (f _)
  | swap x y values => exact List.Perm.swap (f x) (f y) (values.map f)
  | trans _ _ ih ih' => exact ih.trans ih'

theorem mem_finRange_self {n : Nat} (j : Fin n) :
    j ∈ List.finRange n :=
  List.mem_finRange j

theorem count_finRange (n : Nat) (j : Fin n) :
    (List.finRange n).count j = 1 := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.finRange_succ_last, List.count_append]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · have hleft :
            ((List.finRange n).map Fin.castSucc).count (Fin.last n) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          rcases List.mem_map.mp hmem with ⟨k, _, hk⟩
          have hlt : k.castSucc.val < n := Fin.castSucc_lt_last k
          have heq : k.castSucc.val = n := by
            rw [hk]
            rfl
          exact (Nat.ne_of_lt hlt) heq
        have hright : [Fin.last n].count (Fin.last n) = 1 :=
          List.count_singleton_self
        simp [hleft, hright]
      · have hright : [Fin.last n].count i.castSucc = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          have heq : i.castSucc = Fin.last n := List.mem_singleton.mp hmem
          have hlt : i.castSucc.val < n := Fin.castSucc_lt_last i
          have hval : i.castSucc.val = n := by
            rw [heq]
            rfl
          exact (Nat.ne_of_lt hlt) hval
        have hleft :
            ((List.finRange n).map Fin.castSucc).count i.castSucc = 1 := by
          rw [List.count_eq_countP, List.countP_map]
          change (List.finRange n).countP (fun k => k.castSucc == i.castSucc) = 1
          have hpoint :
              (fun k : Fin n => k.castSucc == i.castSucc) =
                fun k => k == i := by
            funext k
            apply Bool.eq_iff_iff.mpr
            constructor
            · intro h
              exact beq_iff_eq.mpr
                (Fin.castSucc_inj.mp (beq_iff_eq.mp h))
            · intro h
              exact beq_iff_eq.mpr
                (Fin.castSucc_inj.mpr (beq_iff_eq.mp h))
          rw [hpoint, ← List.count_eq_countP]
          exact ih i
        simp [hleft, hright]

/-- Mapping a list and then counting a value is counting the preimage predicate. -/
private theorem count_map_eq_countP {A : Type u} {B : Type v} [BEq B]
    (f : A → B) (target : B) :
    ∀ values : List A,
      (values.map f).count target = values.countP (fun value => f value == target)
  | [] => rfl
  | value :: values => by
      simp [List.count_cons, List.countP_cons,
        count_map_eq_countP f target values]

/-- A bijection of `Fin n` merely reorders the canonical enumeration. -/
private theorem fin_beq_of_bijective {n : Nat}
    (σ τ : Fin n → Fin n)
    (left_inv : ∀ i, τ (σ i) = i)
    (right_inv : ∀ i, σ (τ i) = i)
    (j i : Fin n) :
    (σ i == j) = (i == τ j) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hσ
    have equal : σ i = j := beq_iff_eq.mp hσ
    apply beq_iff_eq.mpr
    calc
      i = τ (σ i) := (left_inv i).symm
      _ = τ j := congrArg τ equal
  · intro hi
    have equal : i = τ j := beq_iff_eq.mp hi
    apply beq_iff_eq.mpr
    calc
      σ i = σ (τ j) := congrArg σ equal
      _ = j := right_inv j

theorem finRange_map_bijective_perm {n : Nat}
    (σ τ : Fin n → Fin n)
    (left_inv : ∀ i, τ (σ i) = i)
    (right_inv : ∀ i, σ (τ i) = i) :
    ((List.finRange n).map σ).Perm (List.finRange n) := by
  apply perm_of_count_eq_constructive
  intro j
  have hpoint : ∀ i, (σ i == j) = (i == τ j) :=
    fun i => fin_beq_of_bijective σ τ left_inv right_inv j i
  calc
    ((List.finRange n).map σ).count j
        = (List.finRange n).countP (fun i => σ i == j) :=
          count_map_eq_countP σ j _
    _ = (List.finRange n).countP (fun i => i == τ j) :=
        countP_eq_of_pointwise _ _ _ hpoint
    _ = (List.finRange n).count (τ j) := List.count_eq_countP.symm
    _ = 1 := count_finRange n (τ j)
    _ = (List.finRange n).count j := (count_finRange n j).symm

/--
Finite-sum reindexing: if `σ` is an explicitly inverted permutation of
`Fin n`, then summing `u ∘ σ` agrees with summing `u`.

The argument packages the adjacent-swap reasoning as a list permutation of
the canonical enumeration and then applies `listSum_perm`.  It does not
quotient the carrier or identify `u` with `u ∘ σ` as functions.
-/
theorem finSum_reindex (C : AdditiveCarrier M) (n : Nat) (u : Fin n → M)
    (σ τ : Fin n → Fin n)
    (left_inv : ∀ i, τ (σ i) = i)
    (right_inv : ∀ i, σ (τ i) = i) :
    C.Equiv (finSum C n (u ∘ σ)) (finSum C n u) := by
  have hperm :
      ((List.finRange n).map (u ∘ σ)).Perm ((List.finRange n).map u) := by
    have hσ := finRange_map_bijective_perm σ τ left_inv right_inv
    have hmap := perm_map_constructive u hσ
    rwa [List.map_map] at hmap
  exact listSum_perm C hperm

end AdditiveCarrier

/-- Natural-number addition with judgemental equality as the carrier equivalence. -/
def AdditiveCarrier.nat : AdditiveCarrier Nat where
  Equiv := Eq
  equiv_refl := fun _ => rfl
  equiv_symm := fun h => h.symm
  equiv_trans := fun h h' => h.trans h'
  add := Nat.add
  zero := 0
  add_congr := by
    intro x x' y y' hx hy
    simp [hx, hy]
  add_assoc := fun x y z => (Nat.add_assoc x y z)
  add_comm := fun x y => Nat.add_comm x y
  add_zero := fun x => Nat.add_zero x

/--
Nonnegative rational presentations with cross-multiplication equivalence.
The addition is the ordinary fraction addition already used by `QProb.listSum`.
-/
def AdditiveCarrier.qprob : AdditiveCarrier QProb where
  Equiv := QProb.Equiv
  equiv_refl := QProb.equiv_refl
  equiv_symm := fun h => QProb.equiv_symm h
  equiv_trans := fun h h' => QProb.equiv_trans h h'
  add := QProb.add
  zero := QProb.zero
  add_congr := fun hp hq => QProb.add_congr hp hq
  add_assoc := QProb.add_assoc
  add_comm := QProb.add_comm
  add_zero := QProb.add_zero

/-- The `Nat` specialization of finite-sum reindexing. -/
theorem nat_finSum_reindex (n : Nat) (u : Fin n → Nat)
    (σ τ : Fin n → Fin n)
    (left_inv : ∀ i, τ (σ i) = i)
    (right_inv : ∀ i, σ (τ i) = i) :
    AdditiveCarrier.nat.finSum n (u ∘ σ) =
      AdditiveCarrier.nat.finSum n u :=
  AdditiveCarrier.nat.finSum_reindex n u σ τ left_inv right_inv

theorem qprob_listSum_eq (values : List QProb) :
    AdditiveCarrier.qprob.listSum values = QProb.listSum values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change AdditiveCarrier.qprob.add value (AdditiveCarrier.qprob.listSum values) =
        QProb.add value (QProb.listSum values)
      rw [ih]
      rfl

/--
The `QProb` specialization used by finite rational sums: a permutation of a
finite list of presentations does not change the summed value up to
cross multiplication.
-/
theorem QProb.listSum_perm {xs ys : List QProb} (h : xs.Perm ys) :
    QProb.Equiv (QProb.listSum xs) (QProb.listSum ys) := by
  rw [← qprob_listSum_eq, ← qprob_listSum_eq]
  exact AdditiveCarrier.qprob.listSum_perm h

/-- The `QProb` specialization of `Fin n`-indexed reindexing. -/
theorem QProb.finSum_reindex (n : Nat) (u : Fin n → QProb)
    (σ τ : Fin n → Fin n)
    (left_inv : ∀ i, τ (σ i) = i)
    (right_inv : ∀ i, σ (τ i) = i) :
    QProb.Equiv
      (AdditiveCarrier.qprob.finSum n (u ∘ σ))
      (AdditiveCarrier.qprob.finSum n u) :=
  AdditiveCarrier.qprob.finSum_reindex n u σ τ left_inv right_inv

end Probability
end Thesis
