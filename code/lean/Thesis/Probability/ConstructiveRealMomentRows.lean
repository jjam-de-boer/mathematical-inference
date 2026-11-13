import Thesis.Probability.ConstructiveRealSimplexResponseBounds

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- Nonnegative coordinates and exact normalization satisfy precisely the
original closed simplex rows. No sign of an analytic value is decided. -/
theorem real_simplex_of_nonnegative (values : Fin variables → ConstructiveReal)
    (nonnegative : ∀ i, LE zero (values i))
    (normalized : Equiv (realDot variables (fun _ => 1) values) one) :
    RealSatisfies (simplexRows variables) values := by
  intro row member
  rcases List.mem_append.mp member with coordinate | mass
  · obtain ⟨i, _, same⟩ := List.mem_map.mp coordinate
    cases same
    exact (le_congr (realDot_negative_unit variables i values) (ofSignedRatio_neg SignedRatio.zero)).mpr
      ((neg_le_neg_iff zero (values i)).mpr (nonnegative i))
  · rcases List.mem_cons.mp mass with same | later
    · cases same; exact normalized.1
    · have same := List.mem_singleton.mp later
      cases same
      exact (le_congr (realDot_negated_coefficients variables (fun _ => 1) values)
        (ofSignedRatio_neg SignedRatio.one)).mpr ((neg_le_neg_iff one _).mpr normalized.2)

end Thesis.Probability.Distros.RationalLinear

namespace Thesis.Probability.Distros
open ConstructiveReal

/-- Analytic semantics of the two original rows of a closed moment band. -/
theorem MomentInterval.real_rows_iff (constraint : MomentInterval A) (cells : List A) (default : A)
    (values : Fin cells.length → ConstructiveReal) :
    RationalLinear.RealSatisfies (constraint.rows cells default) values ↔
      LE (ofSignedRatio constraint.lower) (RationalLinear.realDot cells.length (constraint.coefficients cells default) values) ∧
      LE (RationalLinear.realDot cells.length (constraint.coefficients cells default) values) (ofSignedRatio constraint.upper) := by
  constructor
  · intro valid
    have upper := valid _ (List.mem_cons_self ..)
    have lower := valid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have moved := (le_congr (RationalLinear.realDot_negated_coefficients cells.length _ values)
      (ofSignedRatio_neg constraint.lower)).mp lower
    exact ⟨(neg_le_neg_iff _ _).mp moved, upper⟩
  · rintro ⟨lower, upper⟩ row member
    rcases List.mem_cons.mp member with same | later
    · cases same; exact upper
    · have same := List.mem_singleton.mp later
      cases same
      exact (le_congr (RationalLinear.realDot_negated_coefficients cells.length _ values)
        (ofSignedRatio_neg constraint.lower)).mpr ((neg_le_neg_iff _ _).mpr lower)

end Thesis.Probability.Distros
