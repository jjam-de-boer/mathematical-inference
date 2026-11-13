import Thesis.Probability.Distros.FiniteGridMoments

namespace Thesis.Probability.Distros.RationalLinear

def nonnegativeRow (variables : Nat) (index : Fin variables) : Inequality variables :=
  ⟨fun i => if i = index then -1 else 0, SignedRatio.zero⟩

def upperMassRow (variables : Nat) : Inequality variables := ⟨fun _ => 1, SignedRatio.one⟩
def lowerMassRow (variables : Nat) : Inequality variables := ⟨fun _ => -1, SignedRatio.neg SignedRatio.one⟩

/-- Nonnegative masses summing to one, expressed as finite linear rows. -/
def simplexRows (variables : Nat) : List (Inequality variables) :=
  (List.finRange variables).map (nonnegativeRow variables) ++ [upperMassRow variables, lowerMassRow variables]

def Simplex (values : Fin variables → SignedRatio) : Prop :=
  (∀ i, SignedRatio.Nonnegative (values i)) ∧ SignedRatio.Equiv (dot variables (fun _ => 1) values) SignedRatio.one

theorem nonnegativeRow_iff (variables : Nat) (index : Fin variables) (values : Fin variables → SignedRatio) :
    (nonnegativeRow variables index).Holds values ↔ SignedRatio.Nonnegative (values index) :=
  (SignedRatio.le_congr (dot_negative_unit variables index values) (SignedRatio.equiv_refl _)).trans
    ((SignedRatio.neg_le_iff_nonnegative_add _ _).trans (SignedRatio.nonnegative_congr (SignedRatio.zero_add _)))

theorem satisfies_simplex_iff (variables : Nat) (values : Fin variables → SignedRatio) :
    Satisfies (simplexRows variables) values ↔ Simplex values := by
  constructor
  · intro valid
    refine ⟨fun i => (nonnegativeRow_iff variables i values).mp
      (valid _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))), ?_⟩
    have upper : SignedRatio.LE (dot variables (fun _ => 1) values) SignedRatio.one :=
      valid (upperMassRow variables) (List.mem_append_right _ (List.mem_cons_self ..))
    have lower : SignedRatio.LE (dot variables (fun _ => -1) values) (SignedRatio.neg SignedRatio.one) :=
      valid (lowerMassRow variables) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    have moved := (SignedRatio.le_congr (dot_neg_coefficients variables (fun _ => 1) values) (SignedRatio.equiv_refl _)).mp lower
    exact SignedRatio.equiv_of_le_of_le upper ((SignedRatio.neg_le_neg_iff _ _).mp moved)
  · rintro ⟨nonnegative, normalized⟩ row member
    rcases List.mem_append.mp member with listed | mass
    · rcases List.mem_map.mp listed with ⟨i, _, same⟩
      cases same
      exact (nonnegativeRow_iff variables i values).mpr (nonnegative i)
    · rcases List.mem_cons.mp mass with same | later
      · cases same
        exact (SignedRatio.le_congr normalized (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl _)
      · have same := List.mem_singleton.mp later
        cases same
        exact (SignedRatio.le_congr (SignedRatio.equiv_trans (dot_neg_coefficients variables (fun _ => 1) values)
          (SignedRatio.neg_congr normalized)) (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl _)

end Thesis.Probability.Distros.RationalLinear
