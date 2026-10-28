import Thesis.Probability.ConstructiveRealEntropyGibbsForm
import Thesis.Probability.ConstructiveRealEntropyInterior

namespace Thesis.Examples.EntropyGibbsForm
open Probability Probability.Distros ConstructiveReal
open RationalLinear RationalEntropyProblem

private def upper : RationalConstraint 2 :=
  ⟨fun i => if i = 1 then SignedRatio.one else SignedRatio.zero, ⟨2, 3, by decide⟩⟩
private def lower : RationalConstraint 2 :=
  ⟨fun i => SignedRatio.neg (upper.coefficients i), ⟨-2, 3, by decide⟩⟩
private def problem : RationalEntropyProblem 2 := ⟨by decide, [upper, lower, upper]⟩
private def vector : Fin 2 → SignedRatio := fun i => if i = 0 then ⟨2, 6, by decide⟩ else ⟨4, 6, by decide⟩
private def anchor : problem.RealLaw :=
  .ofRationalVector problem vector ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
private def floor : PositiveRatio := ⟨1, 6, by decide, by decide⟩

private theorem two_cases (index : Fin 2) : index = 0 ∨ index = 1 := by
  by_cases first : index.val = 0
  · exact Or.inl (Fin.ext first)
  · exact Or.inr (Fin.ext (by have bounded := index.isLt; omega))

private theorem upper_coefficients : upper.clear.coefficients = (fun i : Fin 2 => if i = 1 then 1 else 0) := by
  funext i
  rcases two_cases i with rfl | rfl <;> decide +kernel
private theorem lower_coefficients : lower.clear.coefficients = (fun i : Fin 2 => -(if i = 1 then 1 else 0)) := by
  funext i
  rcases two_cases i with rfl | rfl <;> decide +kernel

private theorem second_fixed (law : problem.RealLaw) : Equiv (law.mass 1).value (anchor.mass 1).value := by
  let values := fun i => (law.mass i).value
  let target := ofSignedRatio (⟨2, 3, by decide⟩ : SignedRatio)
  have above := (upper.clear_real_iff values).mpr (law.valid upper (List.mem_cons_self ..))
  change LE (realDot 2 upper.clear.coefficients values) target at above
  rw [upper_coefficients] at above
  have upperBound := (le_congr (realDot_unit 2 1 values) (equiv_refl _)).mp above
  have below := (lower.clear_real_iff values).mpr (law.valid lower (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  change LE (realDot 2 lower.clear.coefficients values) (neg target) at below
  rw [lower_coefficients] at below
  have negative := equiv_trans (realDot_negated_coefficients 2 (fun i : Fin 2 => if i = 1 then 1 else 0) values)
    (neg_congr (realDot_unit 2 1 values))
  have lowerBound := (neg_le_neg_iff target (values 1)).mp ((le_congr negative (equiv_refl _)).mp below)
  have represented : Equiv target (anchor.mass 1).value := (ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)
  exact equiv_trans ⟨upperBound, lowerBound⟩ represented

private theorem pair_normalized (law : problem.RealLaw) : Equiv (add (law.mass 0).value (law.mass 1).value) one := by
  have evaluation : Equiv (realDot 2 (fun _ => 1) (fun i => (law.mass i).value)) (add (law.mass 0).value (law.mass 1).value) := by
    change Equiv (add (mul one (law.mass 1).value) (add (mul one (law.mass 0).value) zero)) _
    exact equiv_trans (add_congr (one_mul _) (equiv_trans (add_congr (one_mul _) (equiv_refl zero)) (add_zero _))) (add_comm _ _)
  exact equiv_trans (equiv_symm evaluation) law.normalized

private theorem first_fixed (law : problem.RealLaw) : Equiv (law.mass 0).value (anchor.mass 0).value := by
  have sums := equiv_trans (pair_normalized law) (equiv_symm (pair_normalized anchor))
  have aligned := equiv_trans (add_congr (equiv_refl _) (equiv_symm (second_fixed law))) sums
  exact ⟨(add_le_add_right_iff _ _ (anchor.mass 1).value).mp aligned.1,
    (add_le_add_right_iff _ _ (anchor.mass 1).value).mp aligned.2⟩

private theorem maximal : anchor.Maximal := by
  intro law
  have first := realEntropyTerm_congr (first_fixed law) (law.mass 0).nonnegative (anchor.mass 0).nonnegative
    (law.mass 0).bounded (anchor.mass 0).bounded
  have second := realEntropyTerm_congr (second_fixed law) (law.mass 1).nonnegative (anchor.mass 1).nonnegative
    (law.mass 1).bounded (anchor.mass 1).bounded
  change LE (add _ (add _ zero)) (add _ (add _ zero))
  exact (add_congr first (add_congr second (equiv_refl zero))).1

private theorem positive (i : Fin 2) : LE (ofSignedRatio floor.toSignedRatio) (anchor.mass i).value := by
  apply (ofSignedRatio_le_iff _ _).mpr
  rcases two_cases i with rfl | rfl <;> decide +kernel

/-- The maximum and positive domain data are proved above. Its multipliers
are then constructed; no log-linear parameter solution is supplied. -/
private opaque certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (anchor.mass i).value floor (positive i)) :=
  anchor.naturalLagrangeMultipliers maximal (fun _ => floor) positive

/-- This is an actual nonuniform feasible law with unreduced rational
probability presentations, rather than an assumed ideal maximizing law. -/
example : ¬ Equiv (anchor.mass 0).value (anchor.mass 1).value := by
  intro same
  have rational := (ofSignedRatio_equiv_iff (vector 0) (vector 1)).mp same
  exact (by decide +kernel : ¬ SignedRatio.Equiv (vector 0) (vector 1)) rational

example (column : Fin 2) : Equiv (anchor.mass column).value
    (mul (neg (certificate.score column)).exp certificate.partitionInverse) :=
  gibbsForm_of_coefficients anchor (fun _ => floor) positive certificate column

example : Equiv (certificate.partition.positiveLn certificate.partitionLower certificate.partition_positive)
    (add one certificate.offset) := partition_log_offset anchor (fun _ => floor) positive certificate

example : LE (ofSignedRatio certificate.partitionLower.toSignedRatio) certificate.partition := certificate.partition_positive

/-- Only positive feasibility is supplied here. The optimizer's positivity
and its multipliers are obtained by the constructive maximum algorithm;
the independently proved `maximal` certificate above is not an input. -/
private opaque fitted : problem.LagrangeCoefficients (fun i =>
    entropyNaturalGradient (anchor.maximize.mass i).value (interiorLower 2 floor)
      (anchor.maximize_positive (fun _ => floor) positive i)) :=
  anchor.fittedNaturalMultipliers (fun _ => floor) positive

example (index : Fin 2) : LE (ofSignedRatio (interiorLower 2 floor).toSignedRatio)
    (anchor.maximize.mass index).value := anchor.maximize_positive (fun _ => floor) positive index

example (index : Fin 2) : Equiv (anchor.maximize.mass index).value
    (mul (neg (fitted.score index)).exp fitted.partitionInverse) :=
  gibbsForm_of_coefficients anchor.maximize (fun _ => interiorLower 2 floor)
    (anchor.maximize_positive (fun _ => floor) positive) fitted index

/-- The fitted analytic coefficients expose certified rational enclosures
at any requested precision; no exact rational multiplier is asserted. -/
example (row : Fin problem.rows.length) (precision : PositiveRatio) :
    LE (ofSignedRatio ((fitted.coefficient row).enclose precision).lower) (fitted.coefficient row) ∧
      LE (fitted.coefficient row) (ofSignedRatio ((fitted.coefficient row).enclose precision).upper) :=
  (fitted.coefficient row).enclosure_bounds precision

/-- The automatically constructed ideal law agrees with the independently
verified nonuniform candidate. The original probabilities remain rational. -/
example (index : Fin 2) : Equiv (anchor.maximize.mass index).value (anchor.mass index).value :=
  anchor.maximize.maximal_unique anchor anchor.maximize_maximal maximal index

end Thesis.Examples.EntropyGibbsForm
