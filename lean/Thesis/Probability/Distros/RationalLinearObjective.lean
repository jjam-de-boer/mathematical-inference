import Thesis.Probability.Distros.RationalLinearBounds
import Thesis.Probability.Distros.FiniteGridMoments

namespace Thesis.Probability.SignedRatio

theorem neg_add_le_zero_iff (a b : SignedRatio) : LE (add (neg a) b) zero ↔ LE b a :=
  (le_congr (add_comm _ _) (equiv_refl _)).trans
    ((add_le_iff_le_sub b (neg a) zero).trans
      (le_congr (equiv_refl _) (equiv_trans (zero_add _) (neg_neg a))))

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.Distros.RationalLinear

/-- Explicit first-coordinate extension, without selecting from a proposition. -/
def prepend (first : A) (tail : Fin n → A) : Fin (n + 1) → A :=
  fun i => if zero : i.val = 0 then first else tail ⟨i.val - 1, by have bound := i.isLt; omega⟩

theorem prepend_zero (first : A) (tail : Fin n → A) : prepend first tail 0 = first := by
  simp only [prepend, Fin.val_zero, dif_pos rfl]

theorem prepend_succ (first : A) (tail : Fin n → A) (i : Fin n) : prepend first tail i.succ = tail i := by
  simp only [prepend, Fin.val_succ, Nat.add_one_ne_zero, dif_neg, Nat.add_sub_cancel]

theorem prepend_restrict (values : Fin (n + 1) → A) : prepend (values 0) (fun i => values i.succ) = values := by
  funext i
  by_cases zero : i.val = 0
  · have same : i = 0 := Fin.ext zero
    rw [same, prepend_zero]
  · let earlier : Fin n := ⟨i.val - 1, by have bound := i.isLt; omega⟩
    have same : earlier.succ = i := Fin.ext (by simp only [Fin.val_succ]; dsimp [earlier]; omega)
    rw [← same, prepend_succ]

theorem dot_head (n : Nat) (coefficients : Fin (n + 1) → Int) (values : Fin (n + 1) → SignedRatio) :
    SignedRatio.Equiv (dot (n + 1) coefficients values)
      (SignedRatio.add (SignedRatio.scaleInt (coefficients 0) (values 0))
        (dot n (fun i => coefficients i.succ) (fun i => values i.succ))) := by
  refine SignedRatio.equiv_trans (dot_sum (n + 1) coefficients values) ?_
  rw [List.finRange_succ, List.map_cons, List.map_map]
  exact SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (dot_sum n _ _))

theorem dot_prepend (first : Int) (tail : Fin n → Int) (values : Fin (n + 1) → SignedRatio) :
    SignedRatio.Equiv (dot (n + 1) (prepend first tail) values)
      (SignedRatio.add (SignedRatio.scaleInt first (values 0)) (dot n tail (fun i => values i.succ))) := by
  simpa only [prepend_zero, prepend_succ] using dot_head n (prepend first tail) values

def Inequality.weaken (row : Inequality n) : Inequality (n + 1) := ⟨prepend 0 row.coefficients, row.bound⟩

theorem Inequality.holds_weaken_iff (row : Inequality n) (values : Fin (n + 1) → SignedRatio) :
    row.weaken.Holds values ↔ row.Holds (fun i => values i.succ) :=
  SignedRatio.le_congr (SignedRatio.equiv_trans (dot_prepend 0 row.coefficients values)
    (SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.zero_scaleInt _) (SignedRatio.equiv_refl _))
      (SignedRatio.zero_add _))) (SignedRatio.equiv_refl _)

/-- Two rows identify the retained first coordinate with the requested
integer linear objective in the remaining coordinates. -/
def objectiveRows (coefficients : Fin n → Int) : List (Inequality (n + 1)) :=
  [⟨prepend (-1) coefficients, SignedRatio.zero⟩,
    ⟨prepend 1 (fun i => -coefficients i), SignedRatio.zero⟩]

theorem objectiveRows_iff (coefficients : Fin n → Int) (values : Fin (n + 1) → SignedRatio) :
    Satisfies (objectiveRows coefficients) values ↔
      SignedRatio.Equiv (values 0) (dot n coefficients (fun i => values i.succ)) := by
  have first : (⟨prepend (-1) coefficients, SignedRatio.zero⟩ : Inequality (n + 1)).Holds values ↔
      SignedRatio.LE (dot n coefficients (fun i => values i.succ)) (values 0) :=
    (SignedRatio.le_congr (SignedRatio.equiv_trans (dot_prepend (-1) coefficients values)
      (SignedRatio.add_congr (minus_one_scaleInt _) (SignedRatio.equiv_refl _))) (SignedRatio.equiv_refl _)).trans
      (SignedRatio.neg_add_le_zero_iff _ _)
  have second : (⟨prepend 1 (fun i => -coefficients i), SignedRatio.zero⟩ : Inequality (n + 1)).Holds values ↔
      SignedRatio.LE (values 0) (dot n coefficients (fun i => values i.succ)) :=
    (SignedRatio.le_congr (SignedRatio.equiv_trans (dot_prepend 1 _ values)
      (SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.one_scaleInt _) (dot_neg_coefficients n coefficients _))
        (SignedRatio.add_comm _ _))) (SignedRatio.equiv_refl _)).trans (SignedRatio.neg_add_le_zero_iff _ _)
  constructor
  · intro valid
    exact SignedRatio.equiv_of_le_of_le (second.mp (valid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
      (first.mp (valid _ (List.mem_cons_self ..)))
  · intro same row member
    have upper : SignedRatio.LE (values 0) (dot n coefficients (fun i => values i.succ)) :=
      (SignedRatio.le_congr (SignedRatio.equiv_refl _) same).mp (SignedRatio.le_refl _)
    have lower : SignedRatio.LE (dot n coefficients (fun i => values i.succ)) (values 0) :=
      (SignedRatio.le_congr same (SignedRatio.equiv_refl _)).mp (SignedRatio.le_refl _)
    rcases List.mem_cons.mp member with equal | later
    · cases equal; exact first.mpr lower
    · have equal := List.mem_singleton.mp later
      cases equal; exact second.mpr upper

theorem headRow_holds_iff (others : Nat) (coefficient : Int) (bound : SignedRatio)
    (values : Fin (others + 1) → SignedRatio) :
    (headRow others coefficient bound).Holds values ↔ SignedRatio.LE (SignedRatio.scaleInt coefficient (values 0)) bound := by
  have coefficients : (headRow others coefficient bound).coefficients = prepend coefficient (fun _ => 0) := by
    funext i
    by_cases zero : i.val = 0 <;> simp only [headRow, prepend, zero, if_true, if_false, dif_pos, dif_neg]
  change SignedRatio.LE (dot (others + 1) (headRow others coefficient bound).coefficients values) bound ↔ _
  rw [coefficients]
  exact SignedRatio.le_congr (SignedRatio.equiv_trans (dot_prepend coefficient (fun _ => 0) values)
    (SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _) (dot_zero others _)) (SignedRatio.add_zero _)))
    (SignedRatio.equiv_refl _)

end Thesis.Probability.Distros.RationalLinear
