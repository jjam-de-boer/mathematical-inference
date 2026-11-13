import Thesis.Probability.ConstructiveRealLinear
import Thesis.Probability.ConstructiveRealProductLimits
import Thesis.Probability.ConstructiveRealCauchyOrder

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- A finite linear row on effective coordinate sequences is itself an
effective sequence. Coefficient signs do not affect closed-limit validity. -/
def realDotSequence : (variables : Nat) → (Fin variables → Int) → (Fin variables → RealCauchySequence) → RealCauchySequence
  | 0, _, _ => RealCauchySequence.constant zero
  | variables + 1, coefficients, values =>
      ((RealCauchySequence.constant (realInteger (coefficients (Fin.last variables)))).mul (values (Fin.last variables))).add
        (realDotSequence variables (fun i => coefficients i.castSucc) (fun i => values i.castSucc))

theorem realDotSequence_value (variables : Nat) (coefficients : Fin variables → Int)
    (values : Fin variables → RealCauchySequence) (n : Nat) :
    Equiv ((realDotSequence variables coefficients values).value n)
      (realDot variables coefficients (fun i => (values i).value n)) := by
  induction variables with
  | zero => exact equiv_refl zero
  | succ variables ih =>
      exact add_congr (equiv_refl _)
        (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc))

theorem realDotSequence_limit (variables : Nat) (coefficients : Fin variables → Int)
    (values : Fin variables → RealCauchySequence) :
    Equiv (realDotSequence variables coefficients values).limit
      (realDot variables coefficients (fun i => (values i).limit)) := by
  induction variables with
  | zero => exact RealCauchySequence.constant_limit zero
  | succ variables ih =>
      exact equiv_trans (RealCauchySequence.add_limit _ _)
        (add_congr (equiv_trans (RealCauchySequence.mul_limit _ _)
          (mul_congr (RealCauchySequence.constant_limit _) (equiv_refl _)))
          (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))

/-- Every original closed row survives the effective coordinate limit. -/
theorem realSatisfies_limits (rows : List (Inequality variables)) (values : Fin variables → RealCauchySequence)
    (valid : ∀ n, RealSatisfies rows (fun i => (values i).value n)) :
    RealSatisfies rows (fun i => (values i).limit) := by
  intro row member
  have bounded : LE (realDotSequence variables row.coefficients values).limit (ofSignedRatio row.bound) := by
    apply RealCauchySequence.limit_le
    intro n
    exact (le_congr (realDotSequence_value variables row.coefficients values n) (equiv_refl _)).mpr (valid n row member)
  exact (le_congr (realDotSequence_limit variables row.coefficients values) (equiv_refl _)).mp bounded

end Thesis.Probability.Distros.RationalLinear
