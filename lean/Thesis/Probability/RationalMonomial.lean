import Thesis.Probability.SignedRatioAlgebra
import Thesis.Probability.Construction

namespace Thesis
namespace Probability
namespace RationalMonomial

open SignedRatio

/-!
# Exact monomials in finitely many signed rational variables

A monomial is its vector of natural exponents.  This presentation identifies
commuting variable products without sorting arbitrary expression trees or
choosing a quotient representative.  Equality of exponent vectors is decided
by the existing constructive finite-assignment comparison.

Evaluation and its product theorem work for all signed rational assignments,
including zero and negative variables.  The later bound-certificate checker
must separately justify nonnegativity of its constrained expressions; nothing
in this syntax silently assumes that every polynomial term is positive.
-/

abbrev Powers (variables : Nat) := Fin variables → Nat

instance (variables : Nat) : DecidableEq (Powers variables) :=
  FiniteProduct.assignmentDecidableEq variables (fun _ => Nat) (fun _ => inferInstance)

def unit (variables : Nat) : Powers variables := fun _ => 0
def combine {variables : Nat} (left right : Powers variables) : Powers variables := fun index => left index + right index
def variable {variables : Nat} (chosen : Fin variables) : Powers variables := fun index => if index = chosen then 1 else 0

def power (value : SignedRatio) : Nat → SignedRatio
  | 0 => one
  | exponent + 1 => mul value (power value exponent)

theorem power_add (value : SignedRatio) (first second : Nat) :
    Equiv (power value (first + second)) (mul (power value first) (power value second)) := by
  induction first with
  | zero => exact equiv_symm (one_mul _)
  | succ first inductionHypothesis =>
      simpa only [Nat.succ_add, power] using
        equiv_trans (mul_congr (equiv_refl value) inductionHypothesis)
          (equiv_symm (mul_assoc value (power value first) (power value second)))

def product : (variables : Nat) → (Fin variables → SignedRatio) → SignedRatio
  | 0, _ => one
  | variables + 1, values => mul (values (Fin.last variables)) (product variables (fun index => values index.castSucc))

theorem product_congr (variables : Nat) (left right : Fin variables → SignedRatio)
    (same : forall index, Equiv (left index) (right index)) : Equiv (product variables left) (product variables right) := by
  induction variables with
  | zero => exact equiv_refl one
  | succ variables inductionHypothesis =>
      exact mul_congr (same (Fin.last variables))
        (inductionHypothesis (fun index => left index.castSucc) (fun index => right index.castSucc) (fun index => same index.castSucc))

theorem product_one (variables : Nat) : Equiv (product variables (fun _ => one)) one := by
  induction variables with
  | zero => exact equiv_refl one
  | succ variables inductionHypothesis =>
      exact equiv_trans (mul_congr (equiv_refl one) inductionHypothesis) (mul_one one)

theorem product_pointwise_mul (variables : Nat) (left right : Fin variables → SignedRatio) :
    Equiv (product variables (fun index => mul (left index) (right index))) (mul (product variables left) (product variables right)) := by
  induction variables with
  | zero => exact equiv_symm (mul_one one)
  | succ variables inductionHypothesis =>
      exact equiv_trans (mul_congr (equiv_refl _) (inductionHypothesis (fun index => left index.castSucc) (fun index => right index.castSucc)))
        (mul_interchange (left (Fin.last variables)) (right (Fin.last variables)) _ _)

theorem product_singleton (variables : Nat) (chosen : Fin variables) (selected : SignedRatio) :
    Equiv (product variables (fun index => if index = chosen then selected else one)) selected := by
  induction variables with
  | zero => exact Fin.elim0 chosen
  | succ variables inductionHypothesis =>
      refine Fin.lastCases ?_ (fun earlier => ?_) chosen
      · have initial : (fun index : Fin variables => if index.castSucc = Fin.last variables then selected else one) =
            (fun _ => one) := by
          funext index
          rw [if_neg (FiniteProduct.castSucc_ne_last index)]
        rw [product, if_pos rfl, initial]
        exact equiv_trans (mul_congr (equiv_refl selected) (product_one variables)) (mul_one selected)
      · have initial : (fun index : Fin variables => if index.castSucc = earlier.castSucc then selected else one) =
            (fun index => if index = earlier then selected else one) := by
          funext index
          simp only [Fin.ext_iff, Fin.val_castSucc]
        rw [product, if_neg (FiniteProduct.last_ne_castSucc earlier), initial]
        exact equiv_trans (mul_congr (equiv_refl one) (inductionHypothesis earlier)) (one_mul selected)

def evaluate {variables : Nat} (powers : Powers variables) (values : Fin variables → SignedRatio) : SignedRatio :=
  product variables (fun index => power (values index) (powers index))

theorem evaluate_unit (variables : Nat) (values : Fin variables → SignedRatio) : Equiv (evaluate (unit variables) values) one :=
  product_one variables

theorem evaluate_combine {variables : Nat} (left right : Powers variables) (values : Fin variables → SignedRatio) :
    Equiv (evaluate (combine left right) values) (mul (evaluate left values) (evaluate right values)) :=
  equiv_trans (product_congr variables _ _ (fun index => power_add (values index) (left index) (right index)))
    (product_pointwise_mul variables _ _)

theorem evaluate_variable {variables : Nat} (chosen : Fin variables) (values : Fin variables → SignedRatio) :
    Equiv (evaluate (variable chosen) values) (values chosen) := by
  refine equiv_trans (product_congr variables _ (fun index => if index = chosen then values chosen else one) (fun index => ?_))
    (product_singleton variables chosen (values chosen))
  by_cases same : index = chosen
  · subst index
    rw [variable, if_pos rfl]
    exact mul_one (values chosen)
  · rw [variable, if_neg same, if_neg same]
    exact equiv_refl one

end RationalMonomial
end Probability
end Thesis
