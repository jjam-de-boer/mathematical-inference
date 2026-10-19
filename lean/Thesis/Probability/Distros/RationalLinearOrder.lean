import Thesis.Probability.Distros.ConditionalProjection
import Thesis.Probability.Distros.RationalConcentration

namespace Thesis.Probability.SignedRatio

/-- Order laws on unreduced rational presentations. These compare finite
integer cross-products and do not choose normalized rational representatives. -/
theorem le_refl (value : SignedRatio) : LE value value :=
  nonnegative_of_equiv_zero ((sub_equiv_zero_iff _ _).mpr (equiv_refl _))

theorem le_trans {a b c : SignedRatio} (first : LE a b) (second : LE b c) : LE a c :=
  (nonnegative_congr (sub_split c b a)).mpr (nonnegative_add second first)

theorem le_total (a b : SignedRatio) : LE a b ∨ LE b a := by
  by_cases forward : LE a b
  · exact Or.inl forward
  · apply Or.inr
    rw [le_iff_cross] at forward ⊢
    omega

theorem equiv_of_le_of_le {a b : SignedRatio} (first : LE a b) (second : LE b a) : Equiv a b :=
  Int.le_antisymm ((le_iff_cross a b).mp first) ((le_iff_cross b a).mp second)

theorem add_le_add {a b c d : SignedRatio} (first : LE a b) (second : LE c d) : LE (add a c) (add b d) :=
  (nonnegative_congr (sub_add_sub b d a c)).mpr (nonnegative_add first second)

theorem mul_le_mul_nonnegative {a b factor : SignedRatio} (positive : Nonnegative factor) (compared : LE a b) :
    LE (mul factor a) (mul factor b) :=
  (nonnegative_congr (mul_sub factor b a)).mp (nonnegative_mul positive compared)

def scaleInt (factor : Int) (value : SignedRatio) : SignedRatio := mul ⟨factor, 1, Nat.zero_lt_one⟩ value

theorem scaleInt_congr (factor : Int) {a b : SignedRatio} (same : Equiv a b) : Equiv (scaleInt factor a) (scaleInt factor b) :=
  mul_congr (equiv_refl _) same

theorem scaleInt_add (factor : Int) (a b : SignedRatio) :
    Equiv (scaleInt factor (add a b)) (add (scaleInt factor a) (scaleInt factor b)) := mul_add _ _ _

theorem scaleInt_scaleInt (first second : Int) (value : SignedRatio) :
    Equiv (scaleInt first (scaleInt second value)) (scaleInt (first * second) value) := by
  simp only [Equiv, scaleInt, mul, Nat.one_mul, Int.natCast_one, Int.one_mul]
  ac_rfl

theorem scaleInt_nonnegative {factor : Int} (positive : 0 ≤ factor) {value : SignedRatio} (bounded : Nonnegative value) :
    Nonnegative (scaleInt factor value) := Int.mul_nonneg positive bounded

theorem scaleInt_le_iff (factor : Int) (positive : 0 < factor) (a b : SignedRatio) :
    LE (scaleInt factor a) (scaleInt factor b) ↔ LE a b := by
  rw [le_iff_cross, le_iff_cross]
  simp only [scaleInt, mul, Nat.one_mul]
  simpa only [Int.mul_assoc] using (Int.mul_le_mul_left (b := a.num * (b.den : Int)) (c := b.num * (a.den : Int)) positive)

theorem scaleInt_divideNat (value : SignedRatio) (den : Nat) (positive : 0 < den) :
    Equiv (scaleInt (den : Int) (divideNat value den positive)) value := by
  simp only [Equiv, scaleInt, divideNat, mul, Nat.one_mul, Int.natCast_mul]
  ac_rfl

theorem scaleInt_divide_le_iff (factor : Nat) (positive : 0 < factor) (value bound : SignedRatio) :
    LE (scaleInt (factor : Int) value) bound ↔ LE value (divideNat bound factor positive) := by
  rw [le_iff_cross, le_iff_cross]
  simp only [scaleInt, mul, divideNat, Nat.one_mul, Int.natCast_mul]
  have same : (factor : Int) * value.num * (bound.den : Int) = value.num * ((bound.den : Int) * factor) := by ac_rfl
  rw [same]

def selectMin (initial : SignedRatio) : List SignedRatio → SignedRatio
  | [] => initial
  | value :: values => if LE value initial then selectMin value values else selectMin initial values

theorem selectMin_mem (initial : SignedRatio) (values : List SignedRatio) : selectMin initial values ∈ initial :: values := by
  induction values generalizing initial with
  | nil => exact List.mem_cons_self ..
  | cons value values ih =>
      by_cases better : LE value initial
      · rw [selectMin, if_pos better]
        exact List.mem_cons_of_mem initial (ih value)
      · rw [selectMin, if_neg better]
        rcases List.mem_cons.mp (ih initial) with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem initial (List.mem_cons_of_mem value member)

theorem selectMin_bounds (initial : SignedRatio) (values : List SignedRatio) :
    ∀ value ∈ initial :: values, LE (selectMin initial values) value := by
  induction values generalizing initial with
  | nil => intro value member; have same := List.mem_singleton.mp member; subst value; exact le_refl _
  | cons value values ih =>
      by_cases better : LE value initial
      · rw [selectMin, if_pos better]
        intro other member
        rcases List.mem_cons.mp member with same | listed
        · subst other; exact le_trans (ih value value (List.mem_cons_self ..)) better
        · exact ih value other listed
      · rw [selectMin, if_neg better]
        have reversed : LE initial value := (le_total value initial).resolve_left better
        intro other member
        rcases List.mem_cons.mp member with same | listed
        · subst other; exact ih initial initial (List.mem_cons_self ..)
        · rcases List.mem_cons.mp listed with same | later
          · subst other; exact le_trans (ih initial initial (List.mem_cons_self ..)) reversed
          · exact ih initial other (List.mem_cons_of_mem initial later)

def selectMax (initial : SignedRatio) : List SignedRatio → SignedRatio
  | [] => initial
  | value :: values => if LE initial value then selectMax value values else selectMax initial values

theorem selectMax_mem (initial : SignedRatio) (values : List SignedRatio) : selectMax initial values ∈ initial :: values := by
  induction values generalizing initial with
  | nil => exact List.mem_cons_self ..
  | cons value values ih =>
      by_cases better : LE initial value
      · rw [selectMax, if_pos better]
        exact List.mem_cons_of_mem initial (ih value)
      · rw [selectMax, if_neg better]
        rcases List.mem_cons.mp (ih initial) with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem initial (List.mem_cons_of_mem value member)

theorem selectMax_bounds (initial : SignedRatio) (values : List SignedRatio) :
    ∀ value ∈ initial :: values, LE value (selectMax initial values) := by
  induction values generalizing initial with
  | nil => intro value member; have same := List.mem_singleton.mp member; subst value; exact le_refl _
  | cons value values ih =>
      by_cases better : LE initial value
      · rw [selectMax, if_pos better]
        intro other member
        rcases List.mem_cons.mp member with same | listed
        · subst other; exact le_trans better (ih value value (List.mem_cons_self ..))
        · exact ih value other listed
      · rw [selectMax, if_neg better]
        have reversed : LE value initial := (le_total initial value).resolve_left better
        intro other member
        rcases List.mem_cons.mp member with same | listed
        · subst other; exact ih initial initial (List.mem_cons_self ..)
        · rcases List.mem_cons.mp listed with same | later
          · subst other; exact le_trans reversed (ih initial initial (List.mem_cons_self ..))
          · exact ih initial other (List.mem_cons_of_mem initial later)

end Thesis.Probability.SignedRatio
