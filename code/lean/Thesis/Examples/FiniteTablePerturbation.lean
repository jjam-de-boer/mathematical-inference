import Thesis.Causality.LatentTableCounterexample

namespace Thesis
namespace Causality
namespace Examples
namespace FiniteTablePerturbation

open Probability

/-!
# Boundary checks for balanced finite table construction

These small algebraic regressions use three values, a repeated middle label,
zero direction weights, and an intervened environment with zero coefficients.
They check that the normalized record construction and response criterion
agree with literal rational calculations.  No surrogate law is called an SCM,
and no isolated graph example is substituted for universal completeness.

Repeated labels belong to the raw atom presentation only: the response list
below enumerates each distinct value once.  The actual middle-label mass is
therefore two baseline units, not one; both perturbation directions remain
zero there.  Factual cancellation need not survive a changed environment.
-/

private def first : Fin 3 := ⟨0, by decide⟩
private def middle : Fin 3 := ⟨1, by decide⟩
private def last : Fin 3 := ⟨2, by decide⟩

def perturbation : FiniteRecordPerturbation (Fin 3) where
  values := [first, middle, last, middle]
  complete := by
    intro value
    rcases value with ⟨index, bound⟩
    match index with
    | 0 => simp [first]
    | 1 => simp [middle]
    | 2 => simp [last]
    | _ + 3 => exact False.elim (by omega)
  anchor := first
  baseline := 1
  baselinePositive := by decide
  decrease := fun value => if value = first then 2 else 0
  increase := fun value => if value = last then 2 else 0
  massBalanced := by decide +kernel

/-- Full-alphabet positivity follows from the generated baseline, not a
positivity assumption about either perturbation direction. -/
theorem profiles_positive (value : Fin 3) :
    perturbation.leftRecord.EventPositive (FiniteProbRecord.singletonEvent value) ∧
      perturbation.rightRecord.EventPositive (FiniteProbRecord.singletonEvent value) :=
  ⟨perturbation.left_positive value, perturbation.right_positive value⟩

/-- The repeated label is accumulated in both actual record presentations. -/
theorem middle_probability :
    QProb.Equiv (perturbation.leftRecord.probVal (FiniteProbRecord.singletonEvent middle))
      ⟨1, 3, by decide⟩ ∧
    QProb.Equiv (perturbation.rightRecord.probVal (FiniteProbRecord.singletonEvent middle))
      ⟨1, 3, by decide⟩ := by decide +kernel

private def leftCells (value : Fin 3) : QProb :=
  perturbation.leftRecord.probVal (FiniteProbRecord.singletonEvent value)

private def rightCells (value : Fin 3) : QProb :=
  perturbation.rightRecord.probVal (FiniteProbRecord.singletonEvent value)

private def factualEnvironment (_value : Fin 3) : QProb := QProb.one

private def intervenedEnvironment (value : Fin 3) : QProb :=
  if value = first then QProb.one else QProb.zero

/-- Equal factual direction responses imply equal profile responses by
the general balance theorem.  This checks its cancellation orientation. -/
theorem factual_responses_equal :
    QProb.Equiv
      (FiniteLinearResponse.applyWith (List.finRange 3) factualEnvironment leftCells)
      (FiniteLinearResponse.applyWith (List.finRange 3) factualEnvironment rightCells) :=
  (FiniteLinearResponse.applyWith_equiv_iff_of_balance (List.finRange 3) factualEnvironment
    leftCells rightCells perturbation.decreaseCell perturbation.increaseCell
    perturbation.cells_balanced).mpr (by decide +kernel)

/-- Zero environment coefficients are not cancelled or divided out.
The direction gap yields a profile response gap constructively. -/
theorem intervened_responses_separated :
    Not (QProb.Equiv
      (FiniteLinearResponse.applyWith (List.finRange 3) intervenedEnvironment leftCells)
      (FiniteLinearResponse.applyWith (List.finRange 3) intervenedEnvironment rightCells)) := by
  intro equal
  have directions := (FiniteLinearResponse.applyWith_equiv_iff_of_balance
    (List.finRange 3) intervenedEnvironment leftCells rightCells
    perturbation.decreaseCell perturbation.increaseCell perturbation.cells_balanced).mp equal
  have distinct : Not (QProb.Equiv
      (FiniteLinearResponse.applyWith (List.finRange 3) intervenedEnvironment perturbation.decreaseCell)
      (FiniteLinearResponse.applyWith (List.finRange 3) intervenedEnvironment perturbation.increaseCell)) :=
    by decide +kernel
  exact distinct directions

end FiniteTablePerturbation
end Examples
end Causality
end Thesis
