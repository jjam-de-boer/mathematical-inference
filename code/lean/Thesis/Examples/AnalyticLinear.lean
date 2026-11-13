import Thesis.Probability.ConstructiveRealFarkas
import Thesis.Probability.ConstructiveRealPolynomialExpression
import Thesis.Probability.ConstructiveRealNaturalLog

namespace Thesis.Examples.AnalyticLinear
open Probability ConstructiveReal
open Probability.Distros.RationalLinear
open Probability.AnalyticLinear

private abbrev Expr := RationalPolynomial.Expression 2
private def a : Expr := .coordinate 0
private def b : Expr := .coordinate 1
private def half : Expr := .constant ⟨1, 2, by decide⟩
private def xExpr : Expr := .mul (.add a b) half
private def yExpr : Expr := .mul (.sub a b) half
private def sumExpr (x y : Expr) : Expr := .add (.mul (.constant SignedRatio.one) y)
  (.add (.mul (.constant SignedRatio.one) x) (.constant SignedRatio.zero))
private def differenceExpr (x y : Expr) : Expr := .add (.mul (.constant ⟨-1, 1, by decide⟩) y)
  (.add (.mul (.constant SignedRatio.one) x) (.constant SignedRatio.zero))

private def plus (alpha : ConstructiveReal) : Probability.AnalyticLinear.Inequality 2 := ⟨fun _ => 1, alpha⟩
private def minus (alpha : ConstructiveReal) : Probability.AnalyticLinear.Inequality 2 := ⟨fun _ => -1, neg alpha⟩
private def difference (beta : ConstructiveReal) : Probability.AnalyticLinear.Inequality 2 := ⟨fun i => if i = 0 then 1 else -1, beta⟩
private def reverseDifference (beta : ConstructiveReal) : Probability.AnalyticLinear.Inequality 2 := ⟨fun i => -(if i = 0 then 1 else -1), neg beta⟩
private def nullRow : Probability.AnalyticLinear.Inequality 2 := ⟨fun _ => 0, zero⟩
private def rows (alpha beta : ConstructiveReal) := [plus alpha, minus alpha, difference beta, reverseDifference beta, nullRow, plus alpha]
private def reference (alpha beta : ConstructiveReal) (i : Fin 2) : ConstructiveReal :=
  if i = 0 then mul (add alpha beta) (ofSignedRatio ⟨1, 2, by decide⟩) else mul (sub alpha beta) (ofSignedRatio ⟨1, 2, by decide⟩)

private theorem sum_reference (alpha beta : ConstructiveReal) :
    Equiv (realDot 2 (fun _ => 1) (reference alpha beta)) alpha :=
  RationalPolynomial.Expression.equalityCheck_sound_real (sumExpr xExpr yExpr) a (by decide +kernel)
    (fun i => if i = 0 then alpha else beta)

private theorem difference_reference (alpha beta : ConstructiveReal) :
    Equiv (realDot 2 (fun i => if i = 0 then 1 else -1) (reference alpha beta)) beta :=
  RationalPolynomial.Expression.equalityCheck_sound_real (differenceExpr xExpr yExpr) b (by decide +kernel)
    (fun i => if i = 0 then alpha else beta)

private theorem reference_valid (alpha beta : ConstructiveReal) :
    Probability.AnalyticLinear.Satisfies (rows alpha beta) (reference alpha beta) := by
  intro row member
  change row ∈ [plus alpha, minus alpha, difference beta, reverseDifference beta, nullRow, plus alpha] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (sum_reference alpha beta).1
  · exact (le_congr (equiv_trans (realDot_negated_coefficients 2 (fun _ => 1) _) (neg_congr (sum_reference alpha beta))) (equiv_refl _)).mpr (le_refl _)
  · exact (difference_reference alpha beta).1
  · exact (le_congr (equiv_trans (realDot_negated_coefficients 2 (fun i => if i = 0 then 1 else -1) _)
      (neg_congr (difference_reference alpha beta))) (equiv_refl _)).mpr (le_refl _)
  · exact (realDot_zero 2 _).1
  · exact (sum_reference alpha beta).1

/-- Two unknown analytic right-hand sides, redundant and zero rows, and
opposite pivot signs all pass through the actual constructive solver. -/
private def solution (alpha beta : ConstructiveReal) : Fin 2 → ConstructiveReal :=
  (solveFarkas (rows alpha beta) (farkas_of_satisfies _ _ (reference_valid alpha beta))).val

private theorem solution_valid (alpha beta : ConstructiveReal) : Probability.AnalyticLinear.Satisfies (rows alpha beta) (solution alpha beta) :=
  (solveFarkas (rows alpha beta) (farkas_of_satisfies _ _ (reference_valid alpha beta))).property

private theorem solution_sum (alpha beta : ConstructiveReal) : Equiv (realDot 2 (fun _ => 1) (solution alpha beta)) alpha := by
  have upper := solution_valid alpha beta (plus alpha) (List.mem_cons_self ..)
  have lower := solution_valid alpha beta (minus alpha) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have negative := (le_congr (realDot_negated_coefficients 2 (fun _ => 1) _) (equiv_refl _)).mp lower
  exact ⟨upper, (neg_le_neg_iff _ _).mp negative⟩

private theorem solution_difference (alpha beta : ConstructiveReal) : Equiv (realDot 2 (fun i => if i = 0 then 1 else -1) (solution alpha beta)) beta := by
  have upper := solution_valid alpha beta (difference beta) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have lower := solution_valid alpha beta (reverseDifference beta) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have negative := (le_congr (realDot_negated_coefficients 2 (fun i => if i = 0 then 1 else -1) _) (equiv_refl _)).mp lower
  exact ⟨upper, (neg_le_neg_iff _ _).mp negative⟩

private theorem recover_first (values : Fin 2 → ConstructiveReal) :
    Equiv (mul (add (realDot 2 (fun _ => 1) values) (realDot 2 (fun i => if i = 0 then 1 else -1) values))
      (ofSignedRatio ⟨1, 2, by decide⟩)) (values 0) :=
  RationalPolynomial.Expression.equalityCheck_sound_real (.mul (.add (sumExpr a b) (differenceExpr a b)) half) a
    (by decide +kernel) values

private theorem recover_second (values : Fin 2 → ConstructiveReal) :
    Equiv (mul (sub (realDot 2 (fun _ => 1) values) (realDot 2 (fun i => if i = 0 then 1 else -1) values))
      (ofSignedRatio ⟨1, 2, by decide⟩)) (values 1) :=
  RationalPolynomial.Expression.equalityCheck_sound_real (.mul (.sub (sumExpr a b) (differenceExpr a b)) half) b
    (by decide +kernel) values

/-- The returned coordinates are checked against the expected solution,
not merely against the solver's own output interface. -/
example (alpha beta : ConstructiveReal) : Equiv (solution alpha beta 0)
    (mul (add alpha beta) (ofSignedRatio ⟨1, 2, by decide⟩)) :=
  equiv_trans (equiv_symm (recover_first (solution alpha beta)))
    (mul_congr (add_congr (solution_sum alpha beta) (solution_difference alpha beta)) (equiv_refl _))

example (alpha beta : ConstructiveReal) : Equiv (solution alpha beta 1)
    (mul (sub alpha beta) (ofSignedRatio ⟨1, 2, by decide⟩)) :=
  equiv_trans (equiv_symm (recover_second (solution alpha beta)))
    (mul_congr (add_congr (solution_sum alpha beta) (neg_congr (solution_difference alpha beta))) (equiv_refl _))

/-- Existing analytic constants are permitted as bounds without introducing
new rational probability weights or asking for their exact ordering. -/
example : Probability.AnalyticLinear.Satisfies (rows lnTwo one.exp) (solution lnTwo one.exp) := solution_valid lnTwo one.exp

example (precision : PositiveRatio) : LE (ofSignedRatio ((solution lnTwo one.exp 0).enclose precision).lower) (solution lnTwo one.exp 0) ∧
    LE (solution lnTwo one.exp 0) (ofSignedRatio ((solution lnTwo one.exp 0).enclose precision).upper) :=
  (solution lnTwo one.exp 0).enclosure_bounds precision

private def oneSidedRow (alpha : ConstructiveReal) : Probability.AnalyticLinear.Inequality 1 :=
  ⟨fun _ => 2, mul (realInteger 2) alpha⟩
private theorem oneSided_valid (alpha : ConstructiveReal) :
    Probability.AnalyticLinear.Satisfies [oneSidedRow alpha] (fun _ => alpha) := by
  intro row member
  have same := List.mem_singleton.mp member
  cases same
  exact (add_zero _).1

/-- An upper-only system with an unknown signed analytic endpoint is solved
without assuming the endpoint is nonnegative or giving a finite lower bound. -/
example (alpha : ConstructiveReal) : LE
    ((solveFarkas [oneSidedRow alpha] (farkas_of_satisfies _ _ (oneSided_valid alpha))).val 0) alpha := by
  let solved := solveFarkas [oneSidedRow alpha] (farkas_of_satisfies _ _ (oneSided_valid alpha))
  have bound := solved.property (oneSidedRow alpha) (List.mem_singleton_self _)
  change LE (add (mul (realInteger 2) (solved.val 0)) zero) (mul (realInteger 2) alpha) at bound
  exact (mul_le_mul_positive_iff (realInteger 2) (integerLower 2 (by decide)) (integerLower_le 2 (by decide)) _ _).mp
    ((le_congr (add_zero _) (equiv_refl _)).mp bound)

private def impossibleRow : Probability.AnalyticLinear.Inequality 1 := ⟨fun _ => 0, ofSignedRatio ⟨-1, 1, by decide⟩⟩

/-- A negative projected constant is rejected; provenance cannot manufacture
a satisfying assignment for an inconsistent analytic system. -/
example : ¬ ∃ values, Probability.AnalyticLinear.Satisfies [impossibleRow] values := by
  intro feasible
  have condition := (farkas_iff_feasible [impossibleRow]).mpr feasible
  have impossible := condition (.input 0) (fun _ => rfl)
  have rational := (ofSignedRatio_le_iff SignedRatio.zero ⟨-1, 1, by decide⟩).mp impossible
  exact (by decide +kernel : ¬ SignedRatio.LE SignedRatio.zero ⟨-1, 1, by decide⟩) rational

end Thesis.Examples.AnalyticLinear
