import Thesis.Probability.ConstructiveRealLinear
import Thesis.Probability.ConstructiveRealDistance
import Thesis.Probability.Distros.FiniteGridMoments

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

theorem realDot_negative_unit (variables : Nat) (index : Fin variables) (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables (fun i => if i = index then -1 else 0) values) (neg (values index)) := by
  have coefficients : (fun i : Fin variables => if i = index then (-1 : Int) else 0) =
      (fun i => (-1 : Int) * (if i = index then 1 else 0)) := by
    funext i
    by_cases same : i = index
    · simp only [if_pos same, Int.mul_one]
    · simp only [if_neg same, Int.mul_zero]
  rw [coefficients]
  exact equiv_trans (realDot_scale_coefficients variables (-1) _ values)
    (equiv_trans (mul_congr (ofSignedRatio_neg SignedRatio.one) (realDot_unit variables index values))
      (equiv_trans (neg_mul one _) (neg_congr (one_mul _))))

/-- Rational box rows use the real presentation's certified endpoints. The
original constraints will be retained as additional, unchanged rows. -/
def enclosureUpperRow (values : Fin variables → ConstructiveReal) (precision : PositiveRatio) (index : Fin variables) : Inequality variables :=
  ⟨fun i => if i = index then 1 else 0, ((values index).enclose precision).upper⟩

def enclosureLowerRow (values : Fin variables → ConstructiveReal) (precision : PositiveRatio) (index : Fin variables) : Inequality variables :=
  ⟨fun i => if i = index then -1 else 0, SignedRatio.neg ((values index).enclose precision).lower⟩

def enclosureRows (values : Fin variables → ConstructiveReal) (precision : PositiveRatio) : List (Inequality variables) :=
  (List.finRange variables).map (enclosureUpperRow values precision) ++
    (List.finRange variables).map (enclosureLowerRow values precision)

theorem enclosureRows_real_valid (values : Fin variables → ConstructiveReal) (precision : PositiveRatio) :
    RealSatisfies (enclosureRows values precision) values := by
  intro row member
  rcases List.mem_append.mp member with upper | lower
  · rcases List.mem_map.mp upper with ⟨index, _, same⟩
    cases same
    exact (le_congr (realDot_unit variables index values) (equiv_refl _)).mpr ((values index).upper_bound precision)
  · rcases List.mem_map.mp lower with ⟨index, _, same⟩
    cases same
    exact (le_congr (realDot_negative_unit variables index values) (equiv_symm (ofSignedRatio_neg _))).mpr
      ((neg_le_neg_iff _ _).mpr ((values index).lower_bound precision))

/-- Rational solutions of the enclosure rows lie in every original box. -/
theorem enclosureRows_bounds (values : Fin variables → ConstructiveReal) (precision : PositiveRatio)
    (rational : Fin variables → SignedRatio) (valid : Satisfies (enclosureRows values precision) rational) (index : Fin variables) :
    SignedRatio.LE ((values index).enclose precision).lower (rational index) ∧
      SignedRatio.LE (rational index) ((values index).enclose precision).upper := by
  have upper := valid (enclosureUpperRow values precision index)
    (List.mem_append_left _ (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩))
  have lower := valid (enclosureLowerRow values precision index)
    (List.mem_append_right _ (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩))
  exact ⟨(SignedRatio.neg_le_neg_iff _ _).mp
      ((SignedRatio.le_congr (dot_negative_unit variables index rational) (SignedRatio.equiv_refl _)).mp lower),
    (SignedRatio.le_congr (dot_unit variables index rational) (SignedRatio.equiv_refl _)).mp upper⟩

/-- Any rational in a certified enclosure is close to the real it encloses. -/
theorem within_enclosure (value : ConstructiveReal) (precision : PositiveRatio) (rational : SignedRatio)
    (lower : SignedRatio.LE (value.enclose precision).lower rational)
    (upper : SignedRatio.LE rational (value.enclose precision).upper) :
    Within precision.toQProb value (ofSignedRatio rational) := by
  have width : LE (ofSignedRatio (value.enclose precision).upper)
      (add (ofSignedRatio (value.enclose precision).lower) (ofSignedRatio precision.toSignedRatio)) :=
    (le_congr (equiv_refl _) (ofSignedRatio_add _ _)).mpr ((ofSignedRatio_le_iff _ _).mpr (value.enclose precision).width)
  have lowerReal := (ofSignedRatio_le_iff _ _).mpr lower
  have upperReal := (ofSignedRatio_le_iff _ _).mpr upper
  exact ⟨le_trans (value.upper_bound precision) (le_trans width (add_le_add lowerReal (le_refl _))),
    le_trans upperReal (le_trans width (add_le_add (value.lower_bound precision) (le_refl _)))⟩

/-- Effective exact-feasible rational density for every finite system of
integer-coefficient, rational-bound linear inequalities. Equalities are pairs
of opposite rows, so equalities, closed intervals, forced zeros and redundant
constraints are all retained verbatim. No independent coordinate rounding is
used: the rational solver handles the original rows and the enclosure rows
simultaneously. A real solution rules out its infeasible return branch. -/
def approximateFeasible (rows : List (Inequality variables)) (values : Fin variables → ConstructiveReal)
    (valid : RealSatisfies rows values) (precision : PositiveRatio) :
    {rational : Fin variables → SignedRatio // Satisfies rows rational ∧
      ∀ index, Within precision.toQProb (values index) (ofSignedRatio (rational index))} :=
  match solve variables (rows ++ enclosureRows values precision) with
  | .feasible rational satisfies => ⟨rational,
      (fun row member => satisfies row (List.mem_append_left _ member)),
      fun index =>
        let bounds := enclosureRows_bounds values precision rational
          (fun row member => satisfies row (List.mem_append_right _ member)) index
        within_enclosure (values index) precision (rational index) bounds.1 bounds.2⟩
  | .infeasible certificate => False.elim (certificate.not_real ⟨values, by
      intro row member
      rcases List.mem_append.mp member with original | enclosure
      · exact valid row original
      · exact enclosureRows_real_valid values precision row enclosure⟩)

end Thesis.Probability.Distros.RationalLinear
