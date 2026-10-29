import Thesis.Probability.Distros.PartialMomentConditionalBounds
import Thesis.Examples.RationalConditionalNormalization

namespace Thesis.Probability.Examples.PartialMomentConditionalBounds

open Distros RationalLinear

/-!
# Actual laws attaining every supported conditional probability

On the declared grid `{0,1,2}`, condition on the proper event `{0,1}` and
ask for `{0}`. The uniform reference has evidence probability `2/3` and
conditional value `1/2`. Explicit endpoint laws force any sharp certificate
to have endpoints zero and one, and the computed certificate constructs
an actual law for every rational value in that interval.

The additional occurrence at label nine has weight zero and lies outside
the grid. It is admissible almost surely, so the universal bounds cover it
without rewriting its record. No closed optimizer result is normalized in
these proofs and no runtime result is used as evidence.
-/

def problem : PartialMomentProblem Nat :=
  ⟨[0, 1, 2], 0, by decide, by decide, []⟩

def evidence : Event Nat := fun value => decide (value < 2)
def event : Event Nat := fun value => decide (value = 0)

def law : Distro Nat := ⟨⟨[(0, 1), (1, 1), (2, 1), (9, 0)], 3, by decide, rfl⟩⟩

def reference : problem.ConditionalLaw evidence where
  distro := law
  support := by
    intro atom member positive
    simp only [law, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same | same
    all_goals cases same
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · cases positive
  moments := by intro constraint member; cases member
  positive := by decide +kernel

theorem reference_evidence : QProb.Equiv (law.record.probVal evidence) ⟨2, 3, by decide⟩ := by decide +kernel
theorem reference_value : QProb.Equiv (reference.value event) ⟨1, 2, by decide⟩ := by decide +kernel

def endpoint (upper : Bool) : problem.ConditionalLaw evidence where
  distro := ⟨⟨[(if upper then 0 else 1, 1)], 1, Nat.zero_lt_one, rfl⟩⟩
  support := by
    intro atom member _positive
    have same := List.mem_singleton.mp member
    cases same
    cases upper <;> decide +kernel
  moments := by intro constraint member; cases member
  positive := by cases upper <;> decide +kernel

def computed : problem.ConditionalRange evidence event := problem.conditionalRange evidence event reference

/-- This checks the actual-law range, including containment for records
with null labels outside the declared grid, without executing elimination. -/
theorem endpoints (sharp : problem.ConditionalRange evidence event) :
    QProb.Equiv (sharp.lower.value event) QProb.zero ∧ QProb.Equiv (sharp.upper.value event) QProb.one := by
  have zero : QProb.Equiv ((endpoint false).value event) QProb.zero := by decide +kernel
  have one : QProb.Equiv ((endpoint true).value event) QProb.one := by decide +kernel
  have lower := QProb.le_congr (QProb.equiv_refl _) zero (sharp.bounds (endpoint false)).1
  have upper := QProb.le_congr one (QProb.equiv_refl _) (sharp.bounds (endpoint true)).2
  exact ⟨(QProb.toSignedRatio_equiv_iff _ _).mp (SignedRatio.equiv_of_le_of_le
    ((SignedRatio.toSignedRatio_le_iff _ _).mpr lower) ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le _))),
    (QProb.toSignedRatio_equiv_iff _ _).mp (SignedRatio.equiv_of_le_of_le
      ((SignedRatio.toSignedRatio_le_iff _ _).mpr ((sharp.upper.distro.record.conditionOn evidence sharp.upper.positive).probVal_le_one event))
      ((SignedRatio.toSignedRatio_le_iff _ _).mpr upper))⟩

/-- All rational values, with no denominator cap, return actual supported
law data. The endpoints are included, not only strictly interior values. -/
def realizingLaw (value : QProb) (bounded : QProb.LE value QProb.one) :
    {original : problem.ConditionalLaw evidence // QProb.Equiv (original.value event) value} :=
  computed.pointBetween value
    (QProb.le_congr (QProb.equiv_symm (endpoints computed).1) (QProb.equiv_refl _) (QProb.zero_le _))
    (QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm (endpoints computed).2) bounded)

end Thesis.Probability.Examples.PartialMomentConditionalBounds
