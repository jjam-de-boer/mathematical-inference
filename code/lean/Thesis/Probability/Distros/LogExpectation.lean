import Thesis.Probability.Distros.CrossEntropy
import Thesis.Probability.Distros.FiniteGridMoments

namespace Thesis.Probability.ExactLog

theorem scaleRatio_ofNat (n : Nat) (x : ExactLog) : scaleRatio (QProb.ofNat n) x = scaleNat n x := by
  apply ext
  · rfl
  · exact Nat.mul_one _

end Thesis.Probability.ExactLog

namespace Thesis.Probability.Distros

private theorem signed_sum (values : List QProb) : (QProb.listSum values).toSignedRatio =
    SignedRatio.listSum (values.map QProb.toSignedRatio) := by
  induction values with
  | nil => rfl
  | cons head rest ih => rw [QProb.listSum, QProb.toSignedRatio_add, List.map_cons, SignedRatio.listSum, ih]

/-- Natural expectations integrate the aggregated PMF on any supported
distinct grid, with no restriction on null atom labels. -/
theorem Distro.expectNat_grid_pmf [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (f : A → Nat) :
    QProb.Equiv (μ.expectNat f) (QProb.listSum (grid.cells.map (fun value => QProb.mul (μ.pmf value) (QProb.ofNat (f value))))) := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.rationalExpectation_ofNat f)) ?_
  refine SignedRatio.equiv_trans
    (μ.rationalExpectation_grid_pmf grid.cells grid.distinct support (fun value => (QProb.ofNat (f value)).toSignedRatio)) ?_
  rw [signed_sum, List.map_map]
  apply SignedRatio.listSum_map_congr
  intro value
  change SignedRatio.Equiv (SignedRatio.mul (μ.pmf value).toSignedRatio (QProb.ofNat (f value)).toSignedRatio)
    (QProb.mul (μ.pmf value) (QProb.ofNat (f value))).toSignedRatio
  rw [QProb.toSignedRatio_mul]
  exact SignedRatio.equiv_refl _

/-- Expectation of an exact logarithmic observable against the original
aggregated grid probabilities. The values can have either sign. -/
def Distro.logExpectation [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (_support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (f : A → ExactLog) : ExactLog :=
  ExactLog.listSum (grid.cells.map (fun value => ExactLog.scaleRatio (μ.pmf value) (f value)))

theorem Distro.logExpectation_congr [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (f g : A → ExactLog)
    (same : ∀ value ∈ grid.cells, ExactLog.Equiv (f value) (g value)) :
    ExactLog.Equiv (μ.logExpectation grid support f) (μ.logExpectation grid support g) :=
  ExactLog.listSum_map_congr grid.cells _ _ (fun value member => ExactLog.scaleRatio_value_congr _ (same value member))

theorem Distro.logExpectation_constant [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (constant : ExactLog) :
    ExactLog.Equiv (μ.logExpectation grid support (fun _ => constant)) constant := by
  have distributed := ExactLog.listSum_scaleRatio_weights (grid.cells.map μ.pmf) constant
  rw [List.map_map] at distributed
  have normalized := ExactLog.scaleRatio_weight_congr (μ.pmf_grid_normalization grid support) constant
  rw [ExactLog.scaleRatio_one] at normalized
  exact ExactLog.equiv_trans distributed normalized

theorem Distro.logExpectation_add [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (f g : A → ExactLog) :
    ExactLog.Equiv (μ.logExpectation grid support (fun value => ExactLog.add (f value) (g value)))
      (ExactLog.add (μ.logExpectation grid support f) (μ.logExpectation grid support g)) :=
  ExactLog.equiv_trans (ExactLog.listSum_map_congr grid.cells _ _ (fun _ _ => ExactLog.scaleRatio_add_value _ _ _))
    (ExactLog.listSum_map_add grid.cells _ _)

theorem Distro.logExpectation_listSum [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (indices : List I) (f : I → A → ExactLog) :
    ExactLog.Equiv (μ.logExpectation grid support (fun value => ExactLog.listSum (indices.map (fun i => f i value))))
      (ExactLog.listSum (indices.map (fun i => μ.logExpectation grid support (f i)))) := by
  induction indices with
  | nil => exact μ.logExpectation_constant grid support ExactLog.zero
  | cons head rest ih =>
      exact ExactLog.equiv_trans (μ.logExpectation_add grid support (f head) _)
        (ExactLog.add_congr (ExactLog.equiv_refl _) ih)

theorem Distro.logExpectation_nat [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (f : A → Nat) (coefficient : ExactLog) :
    ExactLog.Equiv (μ.logExpectation grid support (fun value => ExactLog.scaleNat (f value) coefficient))
      (ExactLog.scaleRatio (μ.expectNat f) coefficient) := by
  have terms := ExactLog.listSum_map_congr grid.cells
    (fun value => ExactLog.scaleRatio (μ.pmf value) (ExactLog.scaleNat (f value) coefficient))
    (fun value => ExactLog.scaleRatio (QProb.mul (μ.pmf value) (QProb.ofNat (f value))) coefficient)
    (fun value _ => by
      change ExactLog.Equiv (ExactLog.scaleRatio (μ.pmf value) (ExactLog.scaleNat (f value) coefficient))
        (ExactLog.scaleRatio (QProb.mul (μ.pmf value) (QProb.ofNat (f value))) coefficient)
      rw [← ExactLog.scaleRatio_ofNat, ExactLog.scaleRatio_mul]
      exact ExactLog.equiv_refl _)
  have distributed := ExactLog.listSum_scaleRatio_weights
    (grid.cells.map (fun value => QProb.mul (μ.pmf value) (QProb.ofNat (f value)))) coefficient
  rw [List.map_map] at distributed
  exact ExactLog.equiv_trans terms (ExactLog.equiv_trans distributed
    (ExactLog.scaleRatio_weight_congr (QProb.equiv_symm (μ.expectNat_grid_pmf grid support f)) coefficient))

/-- Integrating an affine logarithmic score depends only on the selected
natural moments; each logarithmic coefficient may itself be negative. -/
theorem Distro.logExpectation_affine [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (indices : List I)
    (feature : I → A → Nat) (coefficient : I → ExactLog) (offset : ExactLog) :
    ExactLog.Equiv (μ.logExpectation grid support (fun value => ExactLog.add offset
      (ExactLog.listSum (indices.map (fun i => ExactLog.scaleNat (feature i value) (coefficient i))))))
      (ExactLog.add offset (ExactLog.listSum (indices.map (fun i => ExactLog.scaleRatio (μ.expectNat (feature i)) (coefficient i))))) := by
  exact ExactLog.equiv_trans (μ.logExpectation_add grid support _ _)
    (ExactLog.add_congr (μ.logExpectation_constant grid support offset)
      (ExactLog.equiv_trans (μ.logExpectation_listSum grid support indices _)
        (ExactLog.listSum_map_congr indices _ _ (fun i _ => μ.logExpectation_nat grid support (feature i) (coefficient i)))))

theorem Distro.crossEntropy_eq_logExpectation [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) (score : A → ExactLog)
    (represented : ∀ value (member : value ∈ grid.cells), ExactLog.Equiv
      (ExactLog.log ⟨(reference.pmf value).den, (reference.pmf value).num,
        (reference.pmf value).den_pos, positive value member⟩) (score value)) :
    ExactLog.Equiv (μ.crossEntropy reference grid support referenceSupport positive) (μ.logExpectation grid support score) := by
  have terms := ExactLog.listSum_map_congr grid.cells.attach
    (fun cell => crossEntropyTerm (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property))
    (fun cell => ExactLog.scaleRatio (μ.pmf cell.val) (score cell.val))
    (fun cell _ => ExactLog.scaleRatio_value_congr _ (represented cell.val cell.property))
  rw [List.attach_map_val (f := fun value => ExactLog.scaleRatio (μ.pmf value) (score value))] at terms
  exact terms

end Thesis.Probability.Distros
