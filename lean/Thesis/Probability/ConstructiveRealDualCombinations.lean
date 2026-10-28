import Thesis.Probability.ConstructiveRealFarkas
import Thesis.Probability.FiniteDenominatorClearing

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear
open IntegerLinearAlgebra

/-- Integral data retained by combinations of multiplier-system rows.
`direction` and `total` are free signed coefficients; `cone` records the
nonnegative coefficients of the multiplier sign constraints. -/
structure DualSignature (rows columns : Nat) where
  direction : Fin columns → Int
  total : Int
  cone : Fin rows → Nat

/-- Rendering a signature as an actual dual inequality. The last unknown
is the free normalization offset; all preceding unknowns are multipliers.
Only the objective and attained value are analytic right-hand sides. -/
def DualSignature.row (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (signature : DualSignature rows columns) : Inequality (rows + 1) where
  coefficients := FiniteDenominatorClearing.extendNumerator
    (fun r => dot signature.direction (matrix r) + signature.total * bounds r - (signature.cone r : Int))
    (dot signature.direction (fun _ => 1) + signature.total)
  bound := add (realDot columns signature.direction gradient) (mul (realInteger signature.total) target)

/-- Nonnegative integral row operations also combine their explicit signed
normalization/direction data and their nonnegative cone coefficients. -/
def DualSignature.addScaled (left : DualSignature rows columns) (first second : Nat) (right : DualSignature rows columns) : DualSignature rows columns where
  direction i := (first : Int) * left.direction i + (second : Int) * right.direction i
  total := (first : Int) * left.total + (second : Int) * right.total
  cone r := first * left.cone r + second * right.cone r

theorem DualSignature.addScaled_coefficients (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (first second : Nat) (left right : DualSignature rows columns) (column : Fin (rows + 1)) :
    ((left.addScaled first second right).row matrix bounds gradient target).coefficients column =
      (first : Int) * (left.row matrix bounds gradient target).coefficients column +
        (second : Int) * (right.row matrix bounds gradient target).coefficients column := by
  refine Fin.lastCases ?_ (fun r => ?_) column
  · simp only [DualSignature.row, FiniteDenominatorClearing.extendNumerator_last, DualSignature.addScaled,
      dot_add_left, dot_scale_left, Int.mul_add]
    omega
  · simp only [DualSignature.row, FiniteDenominatorClearing.extendNumerator_castSucc, DualSignature.addScaled,
      dot_add_left, dot_scale_left, Int.natCast_add, Int.natCast_mul, Int.add_mul, Int.mul_add,
      Int.mul_sub, Int.mul_assoc]
    omega

theorem DualSignature.addScaled_bound (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (first second : Nat) (left right : DualSignature rows columns) :
    Equiv ((left.addScaled first second right).row matrix bounds gradient target).bound
      (add (mul (realInteger (first : Int)) (left.row matrix bounds gradient target).bound)
        (mul (realInteger (second : Int)) (right.row matrix bounds gradient target).bound)) := by
  have directions := equiv_trans (realDot_add_coefficients columns _ _ gradient)
    (add_congr (realDot_scale_coefficients columns (first : Int) left.direction gradient)
      (realDot_scale_coefficients columns (second : Int) right.direction gradient))
  have total : Equiv (realInteger ((first : Int) * left.total + (second : Int) * right.total))
      (add (mul (realInteger (first : Int)) (realInteger left.total))
        (mul (realInteger (second : Int)) (realInteger right.total))) :=
    equiv_trans (equiv_symm (realInteger_add _ _))
      (add_congr (equiv_symm (realInteger_mul _ _)) (equiv_symm (realInteger_mul _ _)))
  have totals := equiv_trans (mul_congr total (equiv_refl target))
    (equiv_trans (add_mul _ _ _) (add_congr (mul_assoc _ _ _) (mul_assoc _ _ _)))
  exact equiv_trans (add_congr directions totals)
    (equiv_trans (add_four _ _ _ _) (add_congr (equiv_symm (mul_add _ _ _)) (equiv_symm (mul_add _ _ _))))

/-- Erasing signatures gives the finite system accepted by `solveFarkas`.
The original list positions, including repetitions, remain explicit. -/
def dualRows (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (signatures : List (DualSignature rows columns)) : List (Inequality (rows + 1)) :=
  signatures.map (DualSignature.row matrix bounds gradient target)

/-- Trace any actual nonnegative row combination back to signed direction
and normalization data. No signature is extracted from an existential proof. -/
def Combination.signature {matrix : Matrix rows columns} {bounds : Fin rows → Int}
    {gradient : Fin columns → ConstructiveReal} {target : ConstructiveReal}
    {signatures : List (DualSignature rows columns)} :
    Combination (dualRows matrix bounds gradient target signatures) → DualSignature rows columns
  | .input index => signatures[index.val]'(by simpa only [dualRows, List.length_map] using index.isLt)
  | .addScaled first second left right => left.signature.addScaled first second right.signature

theorem Combination.signature_coefficients {matrix : Matrix rows columns} {bounds : Fin rows → Int}
    {gradient : Fin columns → ConstructiveReal} {target : ConstructiveReal}
    {signatures : List (DualSignature rows columns)}
    (combination : Combination (dualRows matrix bounds gradient target signatures)) (column : Fin (rows + 1)) :
    combination.coefficients column = (combination.signature.row matrix bounds gradient target).coefficients column := by
  induction combination with
  | input index => simp only [Combination.coefficients, Combination.signature, dualRows, List.getElem_map]
  | addScaled first second left right ihLeft ihRight =>
      change (first : Int) * left.coefficients column + (second : Int) * right.coefficients column = _
      rw [ihLeft, ihRight]
      exact (DualSignature.addScaled_coefficients matrix bounds gradient target first second left.signature right.signature column).symm

theorem Combination.signature_bound {matrix : Matrix rows columns} {bounds : Fin rows → Int}
    {gradient : Fin columns → ConstructiveReal} {target : ConstructiveReal}
    {signatures : List (DualSignature rows columns)}
    (combination : Combination (dualRows matrix bounds gradient target signatures)) :
    Equiv combination.bound (combination.signature.row matrix bounds gradient target).bound := by
  induction combination with
  | input index => simp only [Combination.bound, Combination.signature, dualRows, List.getElem_map]; exact equiv_refl _
  | addScaled first second left right ihLeft ihRight =>
      exact equiv_trans (add_congr (mul_congr (equiv_refl _) ihLeft) (mul_congr (equiv_refl _) ihRight))
        (equiv_symm (DualSignature.addScaled_bound matrix bounds gradient target first second left.signature right.signature))

/-- Vanishing dual coefficients give exact integral cancellation identities.
These imply primal feasible perturbations without deciding analytic slack. -/
theorem Combination.signature_cancellation {matrix : Matrix rows columns} {bounds : Fin rows → Int}
    {gradient : Fin columns → ConstructiveReal} {target : ConstructiveReal}
    {signatures : List (DualSignature rows columns)}
    (combination : Combination (dualRows matrix bounds gradient target signatures))
    (vanished : ∀ column, combination.coefficients column = 0) :
    dot combination.signature.direction (fun _ => 1) + combination.signature.total = 0 ∧
      ∀ r, dot combination.signature.direction (matrix r) + combination.signature.total * bounds r = (combination.signature.cone r : Int) := by
  constructor
  · have same := (combination.signature_coefficients (Fin.last rows)).symm.trans (vanished (Fin.last rows))
    simpa only [DualSignature.row, FiniteDenominatorClearing.extendNumerator_last] using same
  · intro r
    have same := (combination.signature_coefficients r.castSucc).symm.trans (vanished r.castSucc)
    simp only [DualSignature.row, FiniteDenominatorClearing.extendNumerator_castSucc] at same
    omega

/-- A sign proof for the explicit canceled signatures suffices for the
actual finite dual system. Provenance supplies the signature for each
combination, rather than asking the caller to guess one. -/
theorem farkas_of_signature_nonnegative (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal)
    (signatures : List (DualSignature rows columns))
    (nonnegative : ∀ signature : DualSignature rows columns,
      dot signature.direction (fun _ => 1) + signature.total = 0 →
      (∀ r, dot signature.direction (matrix r) + signature.total * bounds r = (signature.cone r : Int)) →
      LE zero (signature.row matrix bounds gradient target).bound) :
    FarkasCondition (dualRows matrix bounds gradient target signatures) := by
  intro combination vanished
  have canceled := combination.signature_cancellation vanished
  exact (le_congr (equiv_refl _) (equiv_symm combination.signature_bound)).mp
    (nonnegative combination.signature canceled.1 canceled.2)

end Thesis.Probability.AnalyticLinear
