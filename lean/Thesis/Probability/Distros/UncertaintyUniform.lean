import Thesis.Probability.Distros.UncertaintyMeasure
import Thesis.Probability.ExactLogRoots

namespace Thesis.Probability.UncertaintyMeasure
open ProbabilityVector

/-- Uniform product additivity follows from the grouping axiom. No
logarithmic formula for uniform uncertainty is used in this argument. -/
theorem uniform_mul (measure : UncertaintyMeasure) (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    ExactLog.Equiv (measure.value (uniform (m * n) (Nat.mul_pos hm hn)))
      (ExactLog.add (measure.value (uniform m hm)) (measure.value (uniform n hn))) := by
  let choice : Compound := ⟨List.replicate m (⟨1, m, hm⟩, uniform n hn), by
    simpa only [List.map_replicate] using (uniform m hm).normalized⟩
  have outer : choice.outer = uniform m hm := by
    apply ProbabilityVector.ext
    simp only [Compound.outer, choice, uniform, List.map_replicate]
  have refined : choice.refined = uniform (m * n) (Nat.mul_pos hm hn) := by
    apply ProbabilityVector.ext
    simp only [Compound.refined, choice, uniform, List.flatMap_replicate,
      List.map_replicate, List.flatten_replicate_replicate, QProb.mul, Nat.one_mul]
  have grouped := measure.grouping choice
  rw [outer, refined] at grouped
  have constant := ExactLog.scaleRatio_weight_congr (uniform m hm).normalized (measure.value (uniform n hn))
  rw [ExactLog.scaleRatio_one] at constant
  have weighted := ExactLog.equiv_trans
    (ExactLog.listSum_scaleRatio_weights (uniform m hm).masses (measure.value (uniform n hn))) constant
  have matching : ExactLog.Equiv (ExactLog.listSum (choice.branches.map
      (fun branch => ExactLog.scaleRatio branch.1 (measure.value branch.2)))) (measure.value (uniform n hn)) := by
    simpa only [choice, uniform, List.map_replicate] using weighted
  exact ExactLog.equiv_trans grouped (ExactLog.add_congr (ExactLog.equiv_refl _) matching)

/-- Certainty has zero uncertainty, derived rather than added as an axiom. -/
theorem uniform_one (measure : UncertaintyMeasure) :
    ExactLog.Equiv (measure.value (uniform 1 (by decide))) ExactLog.zero := by
  let x := measure.value (uniform 1 (by decide))
  have doubled : ExactLog.Equiv x (ExactLog.add x x) := measure.uniform_mul 1 1 (by decide) (by decide)
  have compared : ExactLog.Equiv (ExactLog.add x x) (ExactLog.add ExactLog.zero x) := by
    rw [ExactLog.zero_add]
    exact ExactLog.equiv_symm doubled
  have bounds := (ExactLog.equiv_iff_le _ _).mp compared
  exact (ExactLog.equiv_iff_le _ _).mpr
    ⟨(ExactLog.add_le_add_right_iff x ExactLog.zero x).mp bounds.1,
      (ExactLog.add_le_add_right_iff ExactLog.zero x x).mp bounds.2⟩

private theorem scale_succ (x : ExactLog) (n : Nat) :
    ExactLog.Equiv (ExactLog.add (ExactLog.scaleNat n x) x) (ExactLog.scaleNat (n + 1) x) := by
  have roots := ExactLog.root_add_equiv (x.argument.pow n) x.argument x.degree x.degree_pos
  have power : PositiveRatio.mul (x.argument.pow n) x.argument = x.argument.pow (n + 1) := by
    rw [PositiveRatio.pow_add, PositiveRatio.pow_one]
  rw [power] at roots
  exact roots

/-- Repeated uniform choices give the natural power law needed by the
number-theoretic uniqueness argument. The exponent may be zero. -/
theorem uniform_pow (measure : UncertaintyMeasure) (n k : Nat) (positive : 0 < n) :
    ExactLog.Equiv (measure.value (uniform (n ^ k) (Nat.pow_pos positive)))
      (ExactLog.scaleNat k (measure.value (uniform n positive))) := by
  induction k with
  | zero => exact ExactLog.equiv_trans measure.uniform_one (ExactLog.equiv_symm (ExactLog.scaleNat_zero _))
  | succ k ih =>
      have product : ExactLog.Equiv (measure.value (uniform (n ^ (k + 1)) (Nat.pow_pos positive)))
          (ExactLog.add (measure.value (uniform (n ^ k) (Nat.pow_pos positive))) (measure.value (uniform n positive))) := by
        simpa only [Nat.pow_succ] using measure.uniform_mul (n ^ k) n (Nat.pow_pos positive) positive
      exact ExactLog.equiv_trans product
        (ExactLog.equiv_trans (ExactLog.add_congr ih (ExactLog.equiv_refl _)) (scale_succ _ k))

end Thesis.Probability.UncertaintyMeasure
