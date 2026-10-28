import Thesis.Probability.ConstructiveRealEntropyKKT
import Thesis.Probability.ConstructiveRealEntropyPositivePath

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

private theorem line_zero {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (directions : Fin variables → ConstructiveReal) (lower : Fin variables → PositiveRatio)
    (inside : entropyLineDomain (fun i => (law.mass i).value) directions lower zero) :
    Equiv (entropyLine (fun i => (law.mass i).value) directions lower zero inside) law.entropy := by
  unfold entropyLine RealLaw.entropy realEntropySum
  simp only [List.map_map, Function.comp_def]
  exact listSum_map_congr (List.finRange variables) _ _ (fun i _ =>
    realEntropyTerm_congr (affineCoordinate_zero _ _) _ (law.mass i).nonnegative _ (law.mass i).bounded)

/-- Necessary variational inequality at a positive entropy maximum, for
all feasible competitors, including boundary laws and directions that
change interval expectations. Feasibility comes from constructed dyadic
mixtures, not from a supplied active-set or tangent-space assumption. -/
theorem RealLaw.maximum_variational {problem : RationalEntropyProblem variables} (reference : problem.RealLaw)
    (maximal : reference.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (observed : problem.RealLaw) :
    LE (FiniteLinear.pair variables (fun i => sub (observed.mass i).value (reference.mass i).value)
      (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i))) zero := by
  let masses := fun i => (reference.mass i).value
  let directions := fun i => sub (observed.mass i).value (reference.mass i).value
  let slope := FiniteLinear.pair variables directions (fun i => entropyBitGradient (masses i) (lower i) (positive i))
  have inside (i : Fin variables) : entropyPositiveDomain (lower i).half (masses i) :=
    ⟨positive_half_lower (masses i) (masses i) (lower i) (positive i) (within_refl _ _), (reference.mass i).bounded⟩
  have sameSlope : Equiv (listSum ((List.finRange variables).map (fun i =>
      mul (directions i) (entropyBitGradient (masses i) (lower i).half (inside i).1)))) slope :=
    listSum_map_congr _ _ _ (fun i _ => mul_congr (equiv_refl _) (neg_congr (add_congr
      (positiveLog2_congr (equiv_refl (masses i)) (lower i).half (lower i) (inside i).1 (positive i)) (equiv_refl _))))
  let derivative := (entropyLine_hasDerivativeWithinAt masses directions (fun i => (lower i).half) inside).slope_congr sameSlope
  apply le_of_forall_rational_error
  intro epsilon
  let n := (derivative.modulus epsilon).den
  let radius := dyadicPrecision n
  let parameter := ofSignedRatio radius.toSignedRatio
  let sample := reference.towards observed n
  have affineSame (i : Fin variables) : Equiv (affineCoordinate (masses i) (directions i) parameter) (sample.mass i).value := by
    rw [reference.towards_mass observed n i]
    exact equiv_trans (add_comm _ _) (equiv_symm ((reference.mass i).towards_affine (observed.mass i) n))
  have admitted (i : Fin variables) : entropyPositiveDomain (lower i).half (affineCoordinate (masses i) (directions i) parameter) := by
    have floor : LE (ofSignedRatio (lower i).half.toSignedRatio) (sample.mass i).value := by
      rw [reference.towards_mass observed n i]
      exact (reference.mass i).towards_positive (observed.mass i) (lower i) (positive i) n (derivative.modulus epsilon).den_pos
    exact ⟨(le_congr (equiv_refl _) (affineSame i)).mpr floor,
      (le_congr (affineSame i) (equiv_refl _)).mpr (sample.mass i).bounded⟩
  have lineSample : Equiv (entropyLine masses directions (fun i => (lower i).half) parameter admitted) sample.entropy := by
    unfold entropyLine RealLaw.entropy realEntropySum
    simp only [List.map_map, Function.comp_def]
    exact listSum_map_congr (List.finRange variables) _ _ (fun i _ =>
      realEntropyTerm_congr (affineSame i) _ (sample.mass i).nonnegative _ (sample.mass i).bounded)
  have close : Within radius.toQProb zero parameter :=
    (within_congr (equiv_refl _) (zero_add parameter)).mp (within_positive_shift zero radius)
  have remainder := (derivative.remainder epsilon radius (dyadicPrecision_small (derivative.modulus epsilon)) parameter admitted close).2
  have increment : Equiv (sub parameter zero) parameter :=
    equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _)
  have errorProduct : Equiv (ofSignedRatio (QProb.mul epsilon.toQProb radius.toQProb).toSignedRatio)
      (mul parameter (ofSignedRatio epsilon.toSignedRatio)) := by
    rw [QProb.toSignedRatio_mul]
    exact equiv_trans (equiv_symm (ofSignedRatio_mul _ _)) (mul_comm _ _)
  have transported := (le_congr (add_congr (line_zero reference directions (fun i => (lower i).half) _) (mul_congr increment (equiv_refl slope)))
    (add_congr lineSample errorProduct)).mp remainder
  have compared := le_trans transported (add_le_add (maximal sample) (le_refl _))
  have canceled := (add_le_add_right_iff _ _ reference.entropy).mp
    ((le_congr (add_comm _ _) (add_comm _ _)).mp compared)
  have reduced := (mul_le_mul_positive_iff parameter radius (le_refl _) slope (ofSignedRatio epsilon.toSignedRatio)).mp canceled
  exact (le_congr (equiv_refl _) (equiv_symm (zero_add _))).mp reduced

/-- Necessary and sufficient variational characterization of the entropy
maximum for every original rational closed-row problem. This is a full
normal-cone inequality; extracting signed KKT coefficients from it requires
an additional constructive duality theorem. -/
theorem RealLaw.maximal_iff_variational {problem : RationalEntropyProblem variables} (reference : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value) :
    reference.Maximal ↔ ∀ observed : problem.RealLaw,
      LE (FiniteLinear.pair variables (fun i => sub (observed.mass i).value (reference.mass i).value)
        (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i))) zero := by
  constructor
  · intro maximal
    exact reference.maximum_variational maximal lower positive
  · intro variational observed
    have tangent := realEntropy_tangent_eq_crossEntropy observed.mass reference.mass observed.normalized reference.normalized lower positive
    have crossBound : LE (realCrossEntropySum observed.mass reference.mass lower positive) reference.entropy :=
      (le_congr tangent (add_zero reference.entropy)).mp (add_le_add (le_refl _) (variational observed))
    exact le_trans (realEntropySum_le_crossEntropy observed.mass reference.mass observed.normalized reference.normalized lower positive) crossBound

end Thesis.Probability.Distros.RationalEntropyProblem
