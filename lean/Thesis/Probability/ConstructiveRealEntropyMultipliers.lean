import Thesis.Probability.ConstructiveRealRowSpaceDuality
import Thesis.Probability.ConstructiveRealEntropyStationarity

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

/-- All original rational constraint rows, followed by normalization.
Denominator clearing changes their coefficient presentation only. -/
def constraintMatrix (problem : RationalEntropyProblem variables) : IntegerRowSpace.Matrix (problem.rows.length + 1) variables :=
  fun row column => FiniteDenominatorClearing.extendNumerator
    (fun index => (problem.rows[index.val]).clear.coefficients column) 1 row

theorem constraintMatrix_last (problem : RationalEntropyProblem variables) :
    problem.constraintMatrix (Fin.last problem.rows.length) = (fun _ => 1) := by
  funext column
  exact FiniteDenominatorClearing.extendNumerator_last _ _

theorem constraintMatrix_castSucc (problem : RationalEntropyProblem variables) (row : Fin problem.rows.length) :
    problem.constraintMatrix row.castSucc = (problem.rows[row.val]).clear.coefficients := by
  funext column
  exact FiniteDenominatorClearing.extendNumerator_castSucc _ _ row

theorem constraintMatrix_kernel_iff (problem : RationalEntropyProblem variables) (directions : Fin variables → ConstructiveReal) :
    IntegerRowSpace.Kernel problem.constraintMatrix directions ↔ problem.ConstraintKernel directions := by
  constructor
  · intro valid
    refine ⟨?_, ?_⟩
    · simpa only [constraintMatrix_last] using valid (Fin.last problem.rows.length)
    · intro row member
      obtain ⟨index, within, same⟩ := List.getElem_of_mem member
      have actual := valid (⟨index, within⟩ : Fin problem.rows.length).castSucc
      simpa only [constraintMatrix_castSucc, same] using actual
  · intro valid row
    refine Fin.lastCases ?_ (fun index => ?_) row
    · simpa only [constraintMatrix_last] using valid.1
    · simpa only [constraintMatrix_castSucc] using
        valid.2 (problem.rows[index.val]) (List.getElem_mem index.isLt)

/-- Multipliers of the original rational coefficients, with a separate
normalization coefficient. Repeated rows remain separate positions. These
are unrestricted equality multipliers; inequality signs/complementarity
are additional KKT obligations, not fields silently assumed here. -/
structure LagrangeCoefficients (problem : RationalEntropyProblem variables) (gradient : Fin variables → ConstructiveReal) where
  offset : ConstructiveReal
  coefficient : Fin problem.rows.length → ConstructiveReal
  represents : ∀ column, Equiv (gradient column)
    (add offset (RationalLinear.realRationalDot problem.rows.length
      (fun row => (problem.rows[row.val]).coefficients column) coefficient))

private def rowScale (row : RationalLinear.RationalConstraint variables) : ConstructiveReal :=
  RationalLinear.realInteger ((FiniteDenominatorClearing.clear row.coefficients).denominator : Int)

private theorem rowScale_coefficient (row : RationalLinear.RationalConstraint variables) (column : Fin variables) :
    Equiv (mul (rowScale row) (ofSignedRatio (row.coefficients column))) (RationalLinear.realInteger (row.clear.coefficients column)) := by
  let cleared := FiniteDenominatorClearing.clear row.coefficients
  have represents := cleared.represents column
  apply equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr ?_)
  simp only [SignedRatio.Equiv, SignedRatio.mul, Nat.one_mul, Int.natCast_one, Int.mul_one]
  change (cleared.denominator : Int) * (row.coefficients column).num = cleared.numerator column * ((row.coefficients column).den : Int)
  exact (Int.mul_comm _ _).trans represents.symm

private theorem realDot_reweight (size : Nat) (first : Fin size → Int) (second : Fin size → SignedRatio)
    (scales values : Fin size → ConstructiveReal)
    (same : ∀ i, Equiv (RationalLinear.realInteger (first i)) (mul (ofSignedRatio (second i)) (scales i))) :
    Equiv (RationalLinear.realDot size first values)
      (RationalLinear.realRationalDot size second (fun i => mul (scales i) (values i))) := by
  induction size with
  | zero => exact equiv_refl zero
  | succ size ih =>
      exact add_congr (equiv_trans (mul_congr (same (Fin.last size)) (equiv_refl _)) (mul_assoc _ _ _))
        (ih (fun i => first i.castSucc) (fun i => second i.castSucc) (fun i => scales i.castSucc) (fun i => values i.castSucc) (fun i => same i.castSucc))

private theorem constraintMatrix_combination (problem : RationalEntropyProblem variables)
    (values : Fin (problem.rows.length + 1) → ConstructiveReal) (column : Fin variables) :
    Equiv (RationalLinear.realDot (problem.rows.length + 1) (fun row => problem.constraintMatrix row column) values)
      (add (values (Fin.last problem.rows.length))
        (RationalLinear.realDot problem.rows.length (fun row => (problem.rows[row.val]).clear.coefficients column) (fun row => values row.castSucc))) := by
  rw [RationalLinear.realDot]
  simp only [constraintMatrix_last, constraintMatrix_castSucc]
  exact add_congr (one_mul _) (equiv_refl _)

/-- Construct actual multipliers of the original rational rows from the
proved kernel condition. No independent-row assumption or row-span witness
is supplied by the caller; both zero and redundant rows are handled by the
finite integer elimination algorithm. -/
def coefficientsOfAnnihilator (problem : RationalEntropyProblem variables) (gradient : Fin variables → ConstructiveReal)
    (annihilates : IntegerRowSpace.AnnihilatesKernel problem.constraintMatrix gradient) : problem.LagrangeCoefficients gradient := by
  let found := IntegerRowSpace.ofAnnihilator (problem.rows.length + 1) variables problem.constraintMatrix gradient annihilates
  refine ⟨found.value (Fin.last problem.rows.length),
    (fun row => mul (rowScale (problem.rows[row.val])) (found.value row.castSucc)), ?_⟩
  intro column
  have evaluation := constraintMatrix_combination problem found.value column
  have reweighted := realDot_reweight problem.rows.length
    (fun row => (problem.rows[row.val]).clear.coefficients column) (fun row => (problem.rows[row.val]).coefficients column)
    (fun row => rowScale (problem.rows[row.val])) (fun row => found.value row.castSucc)
    (fun row => equiv_trans (equiv_symm (rowScale_coefficient _ column)) (mul_comm _ _))
  exact equiv_trans (found.represents column) (equiv_trans evaluation (add_congr (equiv_refl _) reweighted))

/-- Necessary bit-unit multipliers at every supplied quantitatively
positive maximum. Positivity is explicit; existence of a maximum is already
proved independently. This gives no full-grid finite multipliers at forced
zeros and does not assert inequality KKT signs. -/
def RealLaw.lagrangeMultipliers {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value) :
    problem.LagrangeCoefficients (fun i => entropyBitGradient (law.mass i).value (lower i) (positive i)) := by
  apply problem.coefficientsOfAnnihilator _
  intro directions valid
  exact equiv_trans (FiniteLinear.pair_comm variables _ directions)
    (law.maximum_stationary maximal lower positive directions ((problem.constraintMatrix_kernel_iff directions).mp valid))

private theorem realRationalDot_mul_values (size : Nat) (coefficients : Fin size → SignedRatio)
    (values : Fin size → ConstructiveReal) (factor : ConstructiveReal) :
    Equiv (RationalLinear.realRationalDot size coefficients (fun i => mul (values i) factor))
      (mul (RationalLinear.realRationalDot size coefficients values) factor) := by
  induction size with
  | zero => exact equiv_symm (zero_mul factor)
  | succ size ih =>
      exact equiv_trans (add_congr (equiv_symm (mul_assoc _ _ _))
        (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc))) (equiv_symm (add_mul _ _ _))

/-- Unit conversion transforms the computed coefficients as well as the
gradient; it is not an assertion that separately chosen multipliers agree. -/
def LagrangeCoefficients.scale {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (factor : ConstructiveReal) (converted : Fin variables → ConstructiveReal)
    (same : ∀ i, Equiv (mul (gradient i) factor) (converted i)) : problem.LagrangeCoefficients converted where
  offset := mul certificate.offset factor
  coefficient row := mul (certificate.coefficient row) factor
  represents column :=
    equiv_trans (equiv_symm (same column))
      (equiv_trans (mul_congr (certificate.represents column) (equiv_refl _))
        (equiv_trans (add_mul _ _ _) (add_congr (equiv_refl _)
          (equiv_symm (realRationalDot_mul_values _ _ _ factor)))))

def RealLaw.naturalLagrangeMultipliers {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (law.mass i).value) :
    problem.LagrangeCoefficients (fun i => entropyNaturalGradient (law.mass i).value (lower i) (positive i)) :=
  (law.lagrangeMultipliers maximal lower positive).scale lnTwo _ (fun _ => entropyGradient_units _ _ _)

end Thesis.Probability.Distros.RationalEntropyProblem
