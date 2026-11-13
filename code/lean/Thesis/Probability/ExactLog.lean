import Thesis.Probability.PositiveRatio

namespace Thesis.Probability

/-- An exact symbolic value `log₂(argument) / degree`. Arguments and all
comparisons are rational; this type does not claim that logarithms are rational.
Equivalent presentations are compared by raising to a common positive degree. -/
structure ExactLog where
  argument : PositiveRatio
  degree : Nat
  degree_pos : 0 < degree

namespace ExactLog

def LE (x y : ExactLog) : Prop :=
  PositiveRatio.LE (x.argument.pow y.degree) (y.argument.pow x.degree)
def Equiv (x y : ExactLog) : Prop :=
  PositiveRatio.Equiv (x.argument.pow y.degree) (y.argument.pow x.degree)
instance (x y : ExactLog) : Decidable (LE x y) := inferInstanceAs (Decidable (PositiveRatio.LE _ _))
instance (x y : ExactLog) : Decidable (Equiv x y) := inferInstanceAs (Decidable (PositiveRatio.Equiv _ _))

def zero : ExactLog := ⟨PositiveRatio.one, 1, Nat.zero_lt_one⟩
def log (argument : PositiveRatio) : ExactLog := ⟨argument, 1, Nat.zero_lt_one⟩
def add (x y : ExactLog) : ExactLog :=
  ⟨PositiveRatio.mul (x.argument.pow y.degree) (y.argument.pow x.degree),
    x.degree * y.degree, Nat.mul_pos x.degree_pos y.degree_pos⟩
def neg (x : ExactLog) : ExactLog := ⟨x.argument.inv, x.degree, x.degree_pos⟩
def sub (x y : ExactLog) : ExactLog := add x (neg y)
def scaleNat (n : Nat) (x : ExactLog) : ExactLog := ⟨x.argument.pow n, x.degree, x.degree_pos⟩
def divideNat (x : ExactLog) (n : Nat) (positive : 0 < n) : ExactLog :=
  ⟨x.argument, x.degree * n, Nat.mul_pos x.degree_pos positive⟩

/-- A computationally harmless change of presentation. -/
def rescale (x : ExactLog) (n : Nat) (positive : 0 < n) : ExactLog :=
  ⟨x.argument.pow n, x.degree * n, Nat.mul_pos x.degree_pos positive⟩

theorem le_refl (x : ExactLog) : LE x x := PositiveRatio.le_refl _
theorem equiv_refl (x : ExactLog) : Equiv x x := PositiveRatio.equiv_refl _
theorem equiv_symm {x y : ExactLog} (same : Equiv x y) : Equiv y x := PositiveRatio.equiv_symm same

theorem equiv_iff_le (x y : ExactLog) : Equiv x y ↔ LE x y ∧ LE y x := by
  constructor
  · intro same
    exact ⟨Nat.le_of_eq same, Nat.le_of_eq same.symm⟩
  · rintro ⟨forward, backward⟩
    exact PositiveRatio.le_antisymm forward backward

theorem le_total (x y : ExactLog) : LE x y ∨ LE y x := PositiveRatio.le_total _ _

theorem le_trans {x y z : ExactLog} (first : LE x y) (second : LE y z) : LE x z := by
  have left := (PositiveRatio.pow_le_pow_iff _ _ z.degree z.degree_pos).mpr first
  have right := (PositiveRatio.pow_le_pow_iff _ _ x.degree x.degree_pos).mpr second
  rw [PositiveRatio.pow_comm y.argument x.degree z.degree] at left
  have combined := PositiveRatio.le_trans left right
  rw [PositiveRatio.pow_comm x.argument y.degree z.degree,
    PositiveRatio.pow_comm z.argument y.degree x.degree] at combined
  exact (PositiveRatio.pow_le_pow_iff _ _ y.degree y.degree_pos).mp combined

theorem equiv_trans {x y z : ExactLog} (first : Equiv x y) (second : Equiv y z) : Equiv x z := by
  have a := (equiv_iff_le x y).mp first
  have b := (equiv_iff_le y z).mp second
  exact (equiv_iff_le x z).mpr ⟨le_trans a.1 b.1, le_trans b.2 a.2⟩

theorem le_congr {x x' y y' : ExactLog} (first : Equiv x x') (second : Equiv y y') :
    LE x y ↔ LE x' y' := by
  have a := (equiv_iff_le x x').mp first
  have b := (equiv_iff_le y y').mp second
  exact ⟨fun h => le_trans a.2 (le_trans h b.1), fun h => le_trans a.1 (le_trans h b.2)⟩

theorem rescale_equiv (x : ExactLog) (n : Nat) (positive : 0 < n) : Equiv (rescale x n positive) x := by
  change PositiveRatio.Equiv ((x.argument.pow n).pow x.degree) (x.argument.pow (x.degree * n))
  rw [PositiveRatio.pow_mul, PositiveRatio.pow_comm]
  exact PositiveRatio.equiv_refl _

theorem log_le_log_iff (x y : PositiveRatio) : LE (log x) (log y) ↔ PositiveRatio.LE x y := by
  simp only [LE, log, PositiveRatio.pow_one]

theorem log_equiv_log_iff (x y : PositiveRatio) : Equiv (log x) (log y) ↔ PositiveRatio.Equiv x y := by
  simp only [Equiv, log, PositiveRatio.pow_one]

theorem neg_neg (x : ExactLog) : neg (neg x) = x := by
  cases x
  simp only [neg, PositiveRatio.inv_inv]

theorem neg_le_neg_iff (x y : ExactLog) : LE (neg x) (neg y) ↔ LE y x := by
  change PositiveRatio.LE (x.argument.inv.pow y.degree) (y.argument.inv.pow x.degree) ↔ LE y x
  rw [← PositiveRatio.inv_pow, ← PositiveRatio.inv_pow, PositiveRatio.inv_le_inv_iff]
  rfl

theorem neg_congr {x y : ExactLog} (same : Equiv x y) : Equiv (neg x) (neg y) := by
  have bounds := (equiv_iff_le x y).mp same
  exact (equiv_iff_le _ _).mpr ⟨(neg_le_neg_iff x y).mpr bounds.2, (neg_le_neg_iff y x).mpr bounds.1⟩

theorem add_comm (x y : ExactLog) : Equiv (add x y) (add y x) := by
  have equal : add x y = add y x := by
    cases x; cases y
    simp only [add, Nat.mul_comm, PositiveRatio.mul_comm]
  rw [equal]
  exact equiv_refl _

theorem add_zero (x : ExactLog) : add x zero = x := by
  cases x
  simp only [add, zero, PositiveRatio.pow_one, PositiveRatio.one_pow,
    PositiveRatio.mul_one, Nat.mul_one]

theorem zero_add (x : ExactLog) : add zero x = x := by
  cases x
  simp only [add, zero, PositiveRatio.pow_one, PositiveRatio.one_pow,
    PositiveRatio.one_mul, Nat.one_mul]

theorem add_assoc (x y z : ExactLog) : add (add x y) z = add x (add y z) := by
  have arguments : (add (add x y) z).argument = (add x (add y z)).argument := by
    apply PositiveRatio.ext <;>
      simp only [add, PositiveRatio.mul, PositiveRatio.pow, Nat.mul_pow, ← Nat.pow_mul] <;> ac_rfl
  have degrees : (add (add x y) z).degree = (add x (add y z)).degree := Nat.mul_assoc _ _ _
  cases left : add (add x y) z
  cases right : add x (add y z)
  simp_all

theorem add_neg (x : ExactLog) : Equiv (add x (neg x)) zero := by
  change PositiveRatio.Equiv
    ((PositiveRatio.mul (x.argument.pow x.degree) (x.argument.inv.pow x.degree)).pow 1)
    (PositiveRatio.one.pow (x.degree * x.degree))
  rw [PositiveRatio.pow_one, PositiveRatio.one_pow, ← PositiveRatio.inv_pow]
  exact PositiveRatio.mul_inv _

/-- Adding the same value preserves and reflects the exact comparison. -/
theorem add_le_add_right_iff (x y z : ExactLog) : LE (add x z) (add y z) ↔ LE x y := by
  change PositiveRatio.LE
    ((PositiveRatio.mul (x.argument.pow z.degree) (z.argument.pow x.degree)).pow (y.degree * z.degree))
    ((PositiveRatio.mul (y.argument.pow z.degree) (z.argument.pow y.degree)).pow (x.degree * z.degree)) ↔ LE x y
  rw [PositiveRatio.mul_pow, PositiveRatio.mul_pow]
  have first : (x.argument.pow z.degree).pow (y.degree * z.degree) =
      (x.argument.pow y.degree).pow (z.degree * z.degree) := by
    simp only [← PositiveRatio.pow_mul]; congr 1; ac_rfl
  have second : (y.argument.pow z.degree).pow (x.degree * z.degree) =
      (y.argument.pow x.degree).pow (z.degree * z.degree) := by
    simp only [← PositiveRatio.pow_mul]; congr 1; ac_rfl
  have common : (z.argument.pow x.degree).pow (y.degree * z.degree) =
      (z.argument.pow y.degree).pow (x.degree * z.degree) := by
    simp only [← PositiveRatio.pow_mul]; congr 1; ac_rfl
  rw [first, second, common]
  rw [PositiveRatio.mul_comm _ ((z.argument.pow y.degree).pow (x.degree * z.degree)),
    PositiveRatio.mul_comm _ ((z.argument.pow y.degree).pow (x.degree * z.degree)),
    PositiveRatio.mul_le_mul_left_iff]
  exact PositiveRatio.pow_le_pow_iff _ _ _ (Nat.mul_pos z.degree_pos z.degree_pos)

theorem add_congr {x x' y y' : ExactLog} (first : Equiv x x') (second : Equiv y y') :
    Equiv (add x y) (add x' y') := by
  have a := (equiv_iff_le x x').mp first
  have b := (equiv_iff_le y y').mp second
  have forward : LE (add x y) (add x' y') := by
    apply le_trans ((add_le_add_right_iff x x' y).mpr a.1)
    exact (le_congr (add_comm x' y) (add_comm x' y')).mpr ((add_le_add_right_iff y y' x').mpr b.1)
  have backward : LE (add x' y') (add x y) := by
    apply le_trans ((add_le_add_right_iff x' x y').mpr a.2)
    exact (le_congr (add_comm x y') (add_comm x y)).mpr ((add_le_add_right_iff y' y x).mpr b.2)
  exact (equiv_iff_le _ _).mpr ⟨forward, backward⟩

theorem scaleNat_congr (n : Nat) {x y : ExactLog} (same : Equiv x y) :
    Equiv (scaleNat n x) (scaleNat n y) := by
  change PositiveRatio.Equiv ((x.argument.pow n).pow y.degree) ((y.argument.pow n).pow x.degree)
  rw [PositiveRatio.pow_comm x.argument n y.degree, PositiveRatio.pow_comm y.argument n x.degree]
  exact PositiveRatio.pow_congr same n

theorem scaleNat_le_scaleNat_iff (n : Nat) (positive : 0 < n) (x y : ExactLog) :
    LE (scaleNat n x) (scaleNat n y) ↔ LE x y := by
  change PositiveRatio.LE ((x.argument.pow n).pow y.degree) ((y.argument.pow n).pow x.degree) ↔ LE x y
  rw [PositiveRatio.pow_comm x.argument n y.degree, PositiveRatio.pow_comm y.argument n x.degree]
  exact PositiveRatio.pow_le_pow_iff _ _ n positive

theorem divideNat_le_divideNat_iff (n : Nat) (positive : 0 < n) (x y : ExactLog) :
    LE (divideNat x n positive) (divideNat y n positive) ↔ LE x y := by
  change PositiveRatio.LE (x.argument.pow (y.degree * n)) (y.argument.pow (x.degree * n)) ↔ LE x y
  rw [PositiveRatio.pow_mul, PositiveRatio.pow_mul]
  exact PositiveRatio.pow_le_pow_iff _ _ n positive

theorem log_mul (x y : PositiveRatio) : add (log x) (log y) = log (PositiveRatio.mul x y) := by
  simp only [add, log, PositiveRatio.pow_one, Nat.mul_one]

theorem log_inv (x : PositiveRatio) : log x.inv = neg (log x) := rfl

theorem log_pow (x : PositiveRatio) (n : Nat) : log (x.pow n) = scaleNat n (log x) := rfl

theorem scaleNat_degree (x : ExactLog) : Equiv (scaleNat x.degree x) (log x.argument) := by
  change PositiveRatio.Equiv ((x.argument.pow x.degree).pow 1) (x.argument.pow x.degree)
  rw [PositiveRatio.pow_one]
  exact PositiveRatio.equiv_refl _

theorem scaleNat_zero (x : ExactLog) : Equiv (scaleNat 0 x) zero := by
  change PositiveRatio.Equiv ((x.argument.pow 0).pow 1) (PositiveRatio.one.pow x.degree)
  rw [PositiveRatio.pow_zero, PositiveRatio.pow_one, PositiveRatio.one_pow]
  exact PositiveRatio.equiv_refl _

theorem scaleNat_one (x : ExactLog) : scaleNat 1 x = x := by
  cases x
  simp only [scaleNat, PositiveRatio.pow_one]

theorem scaleNat_mul (m n : Nat) (x : ExactLog) : scaleNat m (scaleNat n x) = scaleNat (n * m) x := by
  cases x
  simp only [scaleNat, PositiveRatio.pow_mul]

theorem scaleNat_add (n : Nat) (x y : ExactLog) :
    scaleNat n (add x y) = add (scaleNat n x) (scaleNat n y) := by
  have arguments : (scaleNat n (add x y)).argument = (add (scaleNat n x) (scaleNat n y)).argument := by
    change (PositiveRatio.mul (x.argument.pow y.degree) (y.argument.pow x.degree)).pow n =
      PositiveRatio.mul ((x.argument.pow n).pow y.degree) ((y.argument.pow n).pow x.degree)
    rw [PositiveRatio.mul_pow, PositiveRatio.pow_comm x.argument y.degree n,
      PositiveRatio.pow_comm y.argument x.degree n]
  cases left : scaleNat n (add x y)
  cases right : add (scaleNat n x) (scaleNat n y)
  simp_all [scaleNat, add]

theorem divideNat_congr (n : Nat) (positive : 0 < n) {x y : ExactLog} (same : Equiv x y) :
    Equiv (divideNat x n positive) (divideNat y n positive) := by
  have bounds := (equiv_iff_le x y).mp same
  exact (equiv_iff_le _ _).mpr ⟨(divideNat_le_divideNat_iff n positive x y).mpr bounds.1,
    (divideNat_le_divideNat_iff n positive y x).mpr bounds.2⟩

theorem divideNat_scaleNat (n : Nat) (positive : 0 < n) (x : ExactLog) :
    Equiv (divideNat (scaleNat n x) n positive) x := rescale_equiv x n positive

end ExactLog
end Thesis.Probability
