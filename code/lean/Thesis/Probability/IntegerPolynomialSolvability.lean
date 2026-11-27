import Thesis.Probability.SignedRatioOrder

namespace Thesis.Probability

/-!
# Integer polynomials evaluated over explicit rationals

A polynomial expression has integer constants and the ring operations.
Its variable count is part of a solvability instance. This presentation
keeps products and sums in their supplied form, so outputting a single
polynomial does not require expanding a large sum of squares. Evaluation
uses the same signed rational presentations as the other exact algebra
modules. Existence of a zero has the usual meaning because rational values
and polynomial equality are interpreted by cross multiplication.
-/

inductive IntegerPolynomial (Variable : Type) where
  | constant (value : Int)
  | variable (index : Variable)
  | add (left right : IntegerPolynomial Variable)
  | mul (left right : IntegerPolynomial Variable)
  | neg (value : IntegerPolynomial Variable)

namespace IntegerPolynomial

variable {V W : Type}

/-- Explicit evaluation over rational representatives. -/
def evaluate (valuation : V → SignedRatio) : IntegerPolynomial V → SignedRatio
  | .constant n => ⟨n, 1, by decide⟩
  | .variable i => valuation i
  | .add p q => (p.evaluate valuation).add (q.evaluate valuation)
  | .mul p q => (p.evaluate valuation).mul (q.evaluate valuation)
  | .neg p => (p.evaluate valuation).neg

/-- An equation between expressions is represented by their difference. -/
def sub (left right : IntegerPolynomial V) : IntegerPolynomial V := .add left (.neg right)

def square (value : IntegerPolynomial V) : IntegerPolynomial V := .mul value value

/-- A change of variable names preserves evaluation at the pulled-back
valuation. It is used to keep the source, rates and arithmetic witnesses in
explicit finite index sets. -/
def rename (index : V → W) : IntegerPolynomial V → IntegerPolynomial W
  | .constant n => .constant n
  | .variable i => .variable (index i)
  | .add p q => .add (p.rename index) (q.rename index)
  | .mul p q => .mul (p.rename index) (q.rename index)
  | .neg p => .neg (p.rename index)

theorem evaluate_rename (polynomial : IntegerPolynomial V) (index : V → W)
    (valuation : W → SignedRatio) :
    (polynomial.rename index).evaluate valuation = polynomial.evaluate (valuation ∘ index) := by
  induction polynomial <;> simp_all [rename, evaluate, Function.comp_def]

/-- Assembly into one polynomial. Order is inherited from the input list. -/
def sum : List (IntegerPolynomial V) → IntegerPolynomial V
  | [] => .constant 0
  | term :: rest => .add term (sum rest)

/-- Polynomial summation evaluates by the same explicit rational fold. -/
theorem evaluate_sum (terms : List (IntegerPolynomial V)) (valuation : V → SignedRatio) :
    (sum terms).evaluate valuation = SignedRatio.listSum (terms.map (evaluate valuation)) := by
  induction terms <;> simp_all [sum, evaluate, SignedRatio.listSum, SignedRatio.zero]

/-- A system of equations is represented by the sum of the squared residuals. -/
def sumSquares (equations : List (IntegerPolynomial V)) : IntegerPolynomial V :=
  sum (equations.map square)

theorem sumSquares_nonnegative (equations : List (IntegerPolynomial V))
    (valuation : V → SignedRatio) : ((sumSquares equations).evaluate valuation).Nonnegative := by
  induction equations with
  | nil => exact SignedRatio.nonnegative_zero
  | cons equation rest ih =>
    exact SignedRatio.nonnegative_add (SignedRatio.nonnegative_square (equation.evaluate valuation)) ih

private theorem add_zero_iff_of_nonnegative {a b : SignedRatio}
    (positiveA : a.Nonnegative) (positiveB : b.Nonnegative) :
    (a.add b).Equiv .zero ↔ a.Equiv .zero ∧ b.Equiv .zero := by
  rw [SignedRatio.equiv_zero_iff, SignedRatio.equiv_zero_iff, SignedRatio.equiv_zero_iff]
  change a.num * (b.den : Int) + b.num * (a.den : Int) = 0 ↔ a.num = 0 ∧ b.num = 0
  constructor
  · intro vanishes
    have aProduct : 0 ≤ a.num * (b.den : Int) := Int.mul_nonneg positiveA (Int.natCast_nonneg _)
    have bProduct : 0 ≤ b.num * (a.den : Int) := Int.mul_nonneg positiveB (Int.natCast_nonneg _)
    have aDen := a.den_pos
    have bDen := b.den_pos
    exact ⟨Int.eq_of_mul_eq_mul_right (by omega) (show a.num * (b.den : Int) = 0 * _ by
      rw [Int.zero_mul]; omega),
      Int.eq_of_mul_eq_mul_right (by omega) (show b.num * (a.den : Int) = 0 * _ by
      rw [Int.zero_mul]; omega)⟩
  · rintro ⟨h, k⟩
    simp [h, k]

private theorem square_zero_iff (value : SignedRatio) : (value.mul value).Equiv .zero ↔ value.Equiv .zero := by
  rw [SignedRatio.equiv_zero_iff, SignedRatio.equiv_zero_iff]
  change value.num * value.num = 0 ↔ value.num = 0
  exact ⟨fun zero => (Int.mul_eq_zero.mp zero).elim id id, fun zero => by rw [zero]; decide⟩

/-- The system and the single polynomial have exactly the same rational
solutions. Nonnegative squares prevent cancellation even for signed
residuals and arbitrary positive denominators. -/
theorem sumSquares_zero_iff (equations : List (IntegerPolynomial V))
    (valuation : V → SignedRatio) :
    ((sumSquares equations).evaluate valuation).Equiv .zero ↔
      ∀ equation ∈ equations, (equation.evaluate valuation).Equiv .zero := by
  induction equations with
  | nil => simp [sumSquares, sum, evaluate, SignedRatio.Equiv, SignedRatio.zero]
  | cons equation rest ih =>
    let value := equation.evaluate valuation
    change ((value.mul value).add ((sumSquares rest).evaluate valuation)).Equiv .zero ↔ _
    rw [add_zero_iff_of_nonnegative (SignedRatio.nonnegative_square _) (sumSquares_nonnegative rest valuation),
      square_zero_iff, ih]
    simp [value]

end IntegerPolynomial

/-- The arithmetic problem takes a single integer polynomial with finitely
many named variables. -/
structure RationalZeroProblem where
  count : Nat
  polynomial : IntegerPolynomial (Fin count)

/-- Solvability over the rationals, using explicit signed representatives. -/
def RationalZeroProblem.Solvable (problem : RationalZeroProblem) : Prop :=
  ∃ valuation : Fin problem.count → SignedRatio, (problem.polynomial.evaluate valuation).Equiv .zero

end Thesis.Probability
