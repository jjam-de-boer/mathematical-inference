import Thesis.Probability.Distros.RationalIntervalCheck

namespace Thesis.Probability.Distros.RationalLinear

/-- Integer coefficient rows act on explicit signed rational assignments.
The recursion exposes the final variable for fraction-free elimination. -/
def dot : (variables : Nat) → (Fin variables → Int) → (Fin variables → SignedRatio) → SignedRatio
  | 0, _, _ => SignedRatio.zero
  | variables + 1, coefficients, values =>
      SignedRatio.add (SignedRatio.scaleInt (coefficients (Fin.last variables)) (values (Fin.last variables)))
        (dot variables (fun i => coefficients i.castSucc) (fun i => values i.castSucc))

def extend (values : Fin variables → SignedRatio) (last : SignedRatio) : Fin (variables + 1) → SignedRatio :=
  Fin.lastCases last values

theorem dot_extend (coefficients : Fin (variables + 1) → Int) (values : Fin variables → SignedRatio) (last : SignedRatio) :
    dot (variables + 1) coefficients (extend values last) =
      SignedRatio.add (SignedRatio.scaleInt (coefficients (Fin.last variables)) last)
        (dot variables (fun i => coefficients i.castSucc) values) := by
  simp only [dot, extend, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem dot_zero (variables : Nat) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (dot variables (fun _ => 0) values) SignedRatio.zero := by
  induction variables with
  | zero => exact SignedRatio.equiv_refl _
  | succ variables ih =>
      exact SignedRatio.equiv_trans
        (SignedRatio.add_congr (SignedRatio.zero_scaleInt _) (ih (fun i => values i.castSucc))) (SignedRatio.add_zero _)

theorem dot_congr (variables : Nat) (coefficients : Fin variables → Int) (values other : Fin variables → SignedRatio)
    (same : ∀ i, SignedRatio.Equiv (values i) (other i)) :
    SignedRatio.Equiv (dot variables coefficients values) (dot variables coefficients other) := by
  induction variables with
  | zero => exact SignedRatio.equiv_refl _
  | succ variables ih =>
      exact SignedRatio.add_congr
        (SignedRatio.scaleInt_congr _ (same (Fin.last variables)))
        (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc) (fun i => other i.castSucc) (fun i => same i.castSucc))

theorem dot_add_coefficients (variables : Nat) (first second : Fin variables → Int) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (dot variables (fun i => first i + second i) values)
      (SignedRatio.add (dot variables first values) (dot variables second values)) := by
  induction variables with
  | zero => exact SignedRatio.equiv_symm (SignedRatio.add_zero _)
  | succ variables ih =>
      exact SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.scaleInt_add_factor _ _ _)
        (ih (fun i => first i.castSucc) (fun i => second i.castSucc) (fun i => values i.castSucc)))
        (SignedRatio.add_interchange _ _ _ _)

theorem dot_scale_coefficients (variables : Nat) (factor : Int) (coefficients : Fin variables → Int) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (dot variables (fun i => factor * coefficients i) values)
      (SignedRatio.scaleInt factor (dot variables coefficients values)) := by
  induction variables with
  | zero => exact SignedRatio.equiv_symm (SignedRatio.scaleInt_zero _)
  | succ variables ih =>
      exact SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_symm (SignedRatio.scaleInt_scaleInt _ _ _))
        (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))
        (SignedRatio.equiv_symm (SignedRatio.scaleInt_add _ _ _))

structure Inequality (variables : Nat) where
  coefficients : Fin variables → Int
  bound : SignedRatio

def Inequality.Holds (row : Inequality variables) (values : Fin variables → SignedRatio) : Prop :=
  SignedRatio.LE (dot variables row.coefficients values) row.bound

instance (row : Inequality variables) (values : Fin variables → SignedRatio) : Decidable (row.Holds values) :=
  inferInstanceAs (Decidable (SignedRatio.LE (dot variables row.coefficients values) row.bound))

def Satisfies (rows : List (Inequality variables)) (values : Fin variables → SignedRatio) : Prop :=
  ∀ row ∈ rows, row.Holds values

instance (rows : List (Inequality variables)) (values : Fin variables → SignedRatio) : Decidable (Satisfies rows values) :=
  inferInstanceAs (Decidable (∀ row ∈ rows, row.Holds values))

def Inequality.pivot (row : Inequality (variables + 1)) : Int := row.coefficients (Fin.last variables)

def Inequality.trim (row : Inequality (variables + 1)) : Inequality variables :=
  ⟨fun i => row.coefficients i.castSucc, row.bound⟩

def Inequality.residual (row : Inequality (variables + 1)) (values : Fin variables → SignedRatio) : SignedRatio :=
  SignedRatio.sub row.bound (dot variables row.trim.coefficients values)

theorem Inequality.holds_extend_iff (row : Inequality (variables + 1)) (values : Fin variables → SignedRatio) (last : SignedRatio) :
    row.Holds (extend values last) ↔ SignedRatio.LE (SignedRatio.scaleInt row.pivot last) (row.residual values) := by
  unfold Holds
  rw [dot_extend, SignedRatio.add_le_iff_le_sub]
  rfl

/-- A projected pair combines an upper row and a lower row using positive
integer multipliers. No rational division or normalization enters elimination. -/
def combine (upper lower : Inequality (variables + 1)) : Inequality variables :=
  ⟨fun i => -lower.pivot * upper.coefficients i.castSucc + upper.pivot * lower.coefficients i.castSucc,
    SignedRatio.add (SignedRatio.scaleInt (-lower.pivot) upper.bound) (SignedRatio.scaleInt upper.pivot lower.bound)⟩

def project (rows : List (Inequality (variables + 1))) : List (Inequality variables) :=
  ((rows.filter (fun row => decide (row.pivot = 0))).map Inequality.trim) ++
    (rows.filter (fun row => decide (0 < row.pivot))).flatMap (fun upper =>
      (rows.filter (fun row => decide (row.pivot < 0))).map (fun lower => combine upper lower))

theorem project_zero_mem (rows : List (Inequality (variables + 1))) (row : Inequality (variables + 1))
    (member : row ∈ rows) (zero : row.pivot = 0) : row.trim ∈ project rows :=
  List.mem_append_left _ (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true zero⟩, rfl⟩)

theorem project_pair_mem (rows : List (Inequality (variables + 1))) (upper lower : Inequality (variables + 1))
    (upperMember : upper ∈ rows) (lowerMember : lower ∈ rows) (positive : 0 < upper.pivot) (negative : lower.pivot < 0) :
    combine upper lower ∈ project rows :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨upper, List.mem_filter.mpr ⟨upperMember, decide_eq_true positive⟩,
    List.mem_map.mpr ⟨lower, List.mem_filter.mpr ⟨lowerMember, decide_eq_true negative⟩, rfl⟩⟩)

end Thesis.Probability.Distros.RationalLinear
