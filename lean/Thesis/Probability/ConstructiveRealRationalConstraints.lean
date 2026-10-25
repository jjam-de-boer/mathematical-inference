import Thesis.Probability.ConstructiveRealFeasibleApproximation
import Thesis.Probability.ConstructiveRealReciprocal
import Thesis.Probability.FiniteDenominatorClearing

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- Finite linear rows may have arbitrary signed rational coefficients.
Denominators are cleared constructively before the existing integer-row
solver is called; probability weights remain in the original rational type. -/
structure RationalConstraint (variables : Nat) where
  coefficients : Fin variables → SignedRatio
  bound : SignedRatio

def rationalDot : (variables : Nat) → (Fin variables → SignedRatio) → (Fin variables → SignedRatio) → SignedRatio
  | 0, _, _ => SignedRatio.zero
  | variables + 1, coefficients, values =>
      SignedRatio.add (SignedRatio.mul (coefficients (Fin.last variables)) (values (Fin.last variables)))
        (rationalDot variables (fun i => coefficients i.castSucc) (fun i => values i.castSucc))

def realRationalDot : (variables : Nat) → (Fin variables → SignedRatio) → (Fin variables → ConstructiveReal) → ConstructiveReal
  | 0, _, _ => zero
  | variables + 1, coefficients, values =>
      add (mul (ofSignedRatio (coefficients (Fin.last variables))) (values (Fin.last variables)))
        (realRationalDot variables (fun i => coefficients i.castSucc) (fun i => values i.castSucc))

def RationalConstraint.Holds (row : RationalConstraint variables) (values : Fin variables → SignedRatio) : Prop :=
  SignedRatio.LE (rationalDot variables row.coefficients values) row.bound

instance (row : RationalConstraint variables) (values : Fin variables → SignedRatio) : Decidable (row.Holds values) :=
  inferInstanceAs (Decidable (SignedRatio.LE (rationalDot variables row.coefficients values) row.bound))

def RationalConstraint.RealHolds (row : RationalConstraint variables) (values : Fin variables → ConstructiveReal) : Prop :=
  LE (realRationalDot variables row.coefficients values) (ofSignedRatio row.bound)

def RationalConstraint.clear (row : RationalConstraint variables) : Inequality variables :=
  let coefficients := FiniteDenominatorClearing.clear row.coefficients
  ⟨coefficients.numerator, SignedRatio.scaleInt (coefficients.denominator : Int) row.bound⟩

private theorem realRationalDot_ofSignedRatio (variables : Nat) (coefficients values : Fin variables → SignedRatio) :
    Equiv (realRationalDot variables coefficients (fun i => ofSignedRatio (values i)))
      (ofSignedRatio (rationalDot variables coefficients values)) := by
  induction variables with
  | zero => exact equiv_refl zero
  | succ variables ih => exact equiv_trans (add_congr (ofSignedRatio_mul _ _)
      (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc))) (ofSignedRatio_add _ _)

private theorem cleared_coefficient (coefficient : SignedRatio) (numerator : Int) (denominator : Nat) (positive : 0 < denominator)
    (represents : SignedRatio.Equiv ⟨numerator, denominator, positive⟩ coefficient) :
    Equiv (mul (realInteger (denominator : Int)) (ofSignedRatio coefficient)) (realInteger numerator) :=
  equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by
    simp only [SignedRatio.Equiv, SignedRatio.mul, Nat.one_mul, Int.natCast_one, Int.mul_one]
    change (denominator : Int) * coefficient.num = numerator * (coefficient.den : Int)
    exact (Int.mul_comm _ _).trans represents.symm))

private theorem realRationalDot_clear (variables : Nat) (coefficients : Fin variables → SignedRatio)
    (numerators : Fin variables → Int) (denominator : Nat) (positive : 0 < denominator)
    (represents : ∀ i, SignedRatio.Equiv ⟨numerators i, denominator, positive⟩ (coefficients i))
    (values : Fin variables → ConstructiveReal) :
    Equiv (mul (realInteger (denominator : Int)) (realRationalDot variables coefficients values))
      (realDot variables numerators values) := by
  induction variables with
  | zero => exact mul_zero _
  | succ variables ih =>
      have head : Equiv (mul (realInteger (denominator : Int))
          (mul (ofSignedRatio (coefficients (Fin.last variables))) (values (Fin.last variables))))
          (mul (realInteger (numerators (Fin.last variables))) (values (Fin.last variables))) :=
        equiv_trans (equiv_symm (mul_assoc _ _ _))
          (mul_congr (cleared_coefficient _ _ denominator positive (represents (Fin.last variables))) (equiv_refl _))
      exact equiv_trans (mul_add _ _ _) (add_congr head
        (ih (fun i => coefficients i.castSucc) (fun i => numerators i.castSucc) (fun i => represents i.castSucc) (fun i => values i.castSucc)))

/-- Positive denominator clearing preserves and reflects the original real
inequality. The common denominator is computed, with no chosen normal form. -/
theorem RationalConstraint.clear_real_iff (row : RationalConstraint variables) (values : Fin variables → ConstructiveReal) :
    row.clear.RealHolds values ↔ row.RealHolds values := by
  let coefficients := FiniteDenominatorClearing.clear row.coefficients
  let positive : PositiveRatio := ⟨coefficients.denominator, 1, coefficients.positive, Nat.zero_lt_one⟩
  have left := realRationalDot_clear variables row.coefficients coefficients.numerator coefficients.denominator coefficients.positive coefficients.represents values
  have right : Equiv (mul (realInteger (coefficients.denominator : Int)) (ofSignedRatio row.bound))
      (ofSignedRatio (SignedRatio.scaleInt (coefficients.denominator : Int) row.bound)) := ofSignedRatio_mul _ _
  exact (le_congr (equiv_symm left) (equiv_symm right)).trans
    (mul_le_mul_positive_iff (realInteger (coefficients.denominator : Int)) positive (le_refl _) _ _)

/-- The same equivalence holds in the actual rational constraint semantics. -/
theorem RationalConstraint.clear_iff (row : RationalConstraint variables) (values : Fin variables → SignedRatio) :
    row.clear.Holds values ↔ row.Holds values := by
  have integer : row.clear.RealHolds (fun i => ofSignedRatio (values i)) ↔ row.clear.Holds values :=
    (le_congr (realDot_ofSignedRatio variables row.clear.coefficients values) (equiv_refl (ofSignedRatio row.clear.bound))).trans
      (ofSignedRatio_le_iff _ row.clear.bound)
  have rational : row.RealHolds (fun i => ofSignedRatio (values i)) ↔ row.Holds values :=
    (le_congr (realRationalDot_ofSignedRatio variables row.coefficients values) (equiv_refl (ofSignedRatio row.bound))).trans
      (ofSignedRatio_le_iff _ row.bound)
  exact integer.symm.trans ((row.clear_real_iff (fun i => ofSignedRatio (values i))).trans rational)

/-- Exact-feasible density for arbitrary rational linear data. Each original
row, including equality pairs or redundant inequalities, is preserved in its
original rational semantics; clearing is only an internal solver step. -/
def approximateRationalConstraints (rows : List (RationalConstraint variables)) (values : Fin variables → ConstructiveReal)
    (valid : ∀ row ∈ rows, row.RealHolds values) (precision : PositiveRatio) :
    {rational : Fin variables → SignedRatio // (∀ row ∈ rows, row.Holds rational) ∧
      ∀ index, Within precision.toQProb (values index) (ofSignedRatio (rational index))} := by
  let cleared := rows.map RationalConstraint.clear
  have clearedValid : RealSatisfies cleared values := by
    intro row member
    rcases List.mem_map.mp member with ⟨original, listed, same⟩
    cases same
    exact (original.clear_real_iff values).mpr (valid original listed)
  let approximation := approximateFeasible cleared values clearedValid precision
  refine ⟨approximation.val, ?_, approximation.property.2⟩
  intro row member
  exact (row.clear_iff approximation.val).mp
    (approximation.property.1 row.clear (List.mem_map.mpr ⟨row, member, rfl⟩))

end Thesis.Probability.Distros.RationalLinear
