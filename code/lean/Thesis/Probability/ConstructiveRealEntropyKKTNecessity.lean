import Thesis.Probability.ConstructiveRealNormalComplementarity
import Thesis.Probability.ConstructiveRealFullRowClearing
import Thesis.Probability.ConstructiveRealEntropyVariational

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal
open RationalLinear

/-- Integral coefficients and bounds obtained by positive clearing of every
original row. Simplex coordinate inequalities are not added to this matrix. -/
def fullMatrix (problem : RationalEntropyProblem variables) : IntegerLinearAlgebra.Matrix problem.rows.length variables :=
  fun r => (problem.rows[r.val]).fullCoefficient

def fullBounds (problem : RationalEntropyProblem variables) : Fin problem.rows.length → Int :=
  fun r => (problem.rows[r.val]).fullBound

theorem RealLaw.fullValid {problem : RationalEntropyProblem variables} (law : problem.RealLaw) (r : Fin problem.rows.length) :
    LE (realDot variables (problem.fullMatrix r) (fun i => (law.mass i).value)) (realInteger (problem.fullBounds r)) :=
  ((problem.rows[r.val]).fullHolds_iff _).mpr (law.valid _ (List.getElem_mem r.isLt))

/-- Every analytic competitor of the exactly cleared system is an original
feasible law. Thus the original variational theorem supplies the normal-cone
premise of the constructive dual solver. -/
theorem RealLaw.fullVariational {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (gradient : Fin variables → ConstructiveReal)
    (variational : ∀ observed : problem.RealLaw, LE (FiniteLinear.pair variables
      (fun i => sub (observed.mass i).value (law.mass i).value) gradient) zero) :
    AnalyticLinear.SimplexVariational problem.fullMatrix problem.fullBounds (fun i => (law.mass i).value) gradient := by
  intro values nonnegative normalized valid
  let observed := RealLaw.ofVector problem values (real_simplex_of_nonnegative values nonnegative normalized) (by
    intro row member
    obtain ⟨index, within, same⟩ := List.getElem_of_mem member
    have actual := valid (⟨index, within⟩ : Fin problem.rows.length)
    change LE (realDot variables (problem.rows[index]).fullCoefficient values) (realInteger (problem.rows[index]).fullBound) at actual
    rw [same] at actual
    exact (row.fullHolds_iff values).mp actual)
  exact variational observed

/-- Compute signed coefficients for the original rational rows from the
full variational inequality. All denominator scales are positive, so signs
and complementary products survive transport. Redundant, zero and paired
equality rows remain in their original positions. -/
def RealLaw.coefficientsOfVariational {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (gradient : Fin variables → ConstructiveReal)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value)
    (variational : ∀ observed : problem.RealLaw, LE (FiniteLinear.pair variables
      (fun i => sub (observed.mass i).value (law.mass i).value) gradient) zero) :
    {certificate : problem.LagrangeCoefficients gradient // certificate.KKTAt law} := by
  let found := AnalyticLinear.normalMultipliers problem.fullMatrix problem.fullBounds
    (fun i => (law.mass i).value) gradient lower positive law.normalized law.fullValid (law.fullVariational gradient variational)
  let certificate : problem.LagrangeCoefficients gradient := {
    offset := found.offset
    coefficient r := mul (problem.rows[r.val]).fullScale (found.coefficient r)
    represents i := by
      have reweighted : Equiv (FiniteLinear.pair problem.rows.length
          (fun r => realInteger (problem.fullMatrix r i)) found.coefficient)
          (FiniteLinear.pair problem.rows.length (fun r => ofSignedRatio ((problem.rows[r.val]).coefficients i))
            (fun r => mul (problem.rows[r.val]).fullScale (found.coefficient r))) :=
        listSum_map_congr (List.finRange problem.rows.length) _ _ (fun r _ =>
          equiv_trans (mul_congr (equiv_symm ((problem.rows[r.val]).fullCoefficient_scaled i)) (equiv_refl _))
            (equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _)) (mul_assoc _ _ _)))
      exact equiv_trans (found.represents i) (add_congr (equiv_refl _)
        (equiv_trans (FiniteLinear.realDot_pair problem.rows.length (fun r => problem.fullMatrix r i) found.coefficient)
          (equiv_trans reweighted (equiv_symm (realRationalDot_pair problem.rows.length _ _))))) }
  refine ⟨certificate, ?_⟩
  constructor
  · intro r
    exact mul_nonnegative (problem.rows[r.val]).fullScale_nonnegative (found.nonnegative r)
  · intro r
    exact equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _))
      (equiv_trans (mul_assoc _ _ _) (equiv_trans
        (mul_congr (equiv_refl _) (equiv_symm ((problem.rows[r.val]).fullSlack_scaled (fun i => (law.mass i).value))))
        (found.complementary law.normalized law.fullValid r)))

/-- Necessary signed bit-unit KKT coefficients at every quantitatively
positive entropy maximum. This returns actual coefficients; the caller
supplies neither their existence nor an active set or row-rank condition. -/
def RealLaw.kktMultipliers {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value) :
    {certificate : problem.LagrangeCoefficients (fun i => entropyBitGradient (law.mass i).value (lower i) (positive i)) // certificate.KKTAt law} :=
  law.coefficientsOfVariational _ lower positive (law.maximum_variational maximal lower positive)

/-- Both directions of signed KKT optimality, including all original closed
rational rows and boundary competitors. Positivity concerns the reference
law; it is obtained automatically on the feasible face in the fitting API. -/
theorem RealLaw.maximal_iff_kkt {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value) :
    law.Maximal ↔ ∃ certificate : problem.LagrangeCoefficients
      (fun i => entropyBitGradient (law.mass i).value (lower i) (positive i)), certificate.KKTAt law :=
  ⟨fun maximal => ⟨(law.kktMultipliers maximal lower positive).val, (law.kktMultipliers maximal lower positive).property⟩,
    fun ⟨certificate, kkt⟩ => law.maximal_of_kkt lower positive certificate kkt⟩

/-- The constructed signed coefficients in natural entropy units, with
normalization and signs converted together by the proved `ln(2)` factor. -/
def RealLaw.naturalKKTMultipliers {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value) :
    {certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)) // certificate.KKTAt law} := by
  let bits := law.kktMultipliers maximal lower positive
  have scaleNonnegative : LE zero lnTwo := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr RationalLogSecant.limit.positiveInverseLower.signed_nonnegative)) lnTwo_lower
  exact ⟨bits.val.scale lnTwo _ (fun i => entropyGradient_units _ _ _),
    bits.property.scale lnTwo scaleNonnegative _ (fun i => entropyGradient_units _ _ _)⟩

/-- Natural-unit necessity and global sufficiency use the same signs and
complementary products as the bit-unit theorem. -/
theorem RealLaw.maximal_iff_natural_kkt {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value) :
    law.Maximal ↔ ∃ certificate : problem.LagrangeCoefficients
      (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)), certificate.KKTAt law :=
  ⟨fun maximal => ⟨(law.naturalKKTMultipliers maximal lower positive).val, (law.naturalKKTMultipliers maximal lower positive).property⟩,
    fun ⟨certificate, kkt⟩ => law.maximal_of_natural_kkt lower positive certificate kkt⟩

end Thesis.Probability.Distros.RationalEntropyProblem
