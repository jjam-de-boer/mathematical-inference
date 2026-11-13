import Thesis.Probability.Distros.CrossEntropy

namespace Thesis.Probability.Distros

private theorem unit_total (values : List A) :
    FiniteProbRecord.totalMass (values.map (fun value => (value, 1))) = values.length := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, FiniteProbRecord.totalMass, List.length_cons, ih, Nat.add_comm]

private theorem unit_singleton [DecidableEq A] (values : List A) (distinct : values.Nodup) (value : A) :
    FiniteProbRecord.eventMass (values.map (fun value => (value, 1))) (FiniteProbRecord.singletonEvent value) =
      if value ∈ values then 1 else 0 := by
  induction values with
  | nil => simp only [List.map_nil, FiniteProbRecord.eventMass, List.not_mem_nil, if_false]
  | cons head rest ih =>
      by_cases same : head = value
      · subst head
        have fresh := (List.nodup_cons.mp distinct).1
        simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent, ih (List.nodup_cons.mp distinct).2, fresh]
      · simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent, same, Ne.symm same,
          ih (List.nodup_cons.mp distinct).2]

/-- Uniform reference on the declared observable grid. Every cell is retained
with weight one, so the constructor preserves the declared domain. -/
def EntropyGrid.uniform (grid : EntropyGrid A) (positive : 0 < grid.cells.length) : Distro A :=
  ⟨⟨grid.cells.map (fun value => (value, 1)), grid.cells.length, positive, unit_total grid.cells⟩⟩

theorem EntropyGrid.uniform_support (grid : EntropyGrid A) (positive : 0 < grid.cells.length) :
    (grid.uniform positive).AlmostSurely (fun value => value ∈ grid.cells) := by
  intro atom member _
  rcases List.mem_map.mp member with ⟨value, listed, rfl⟩
  exact listed

theorem EntropyGrid.uniform_pmf [DecidableEq A] (grid : EntropyGrid A) (positive : 0 < grid.cells.length)
    (value : A) (listed : value ∈ grid.cells) :
    (grid.uniform positive).pmf value = (⟨1, grid.cells.length, positive⟩ : QProb) := by
  change (⟨FiniteProbRecord.eventMass (grid.cells.map (fun value => (value, 1)))
    (FiniteProbRecord.singletonEvent value), grid.cells.length, positive⟩ : QProb) = _
  rw [unit_singleton grid.cells grid.distinct value, if_pos listed]

theorem EntropyGrid.uniform_positive [DecidableEq A] (grid : EntropyGrid A) (positive : 0 < grid.cells.length) :
    (grid.uniform positive).GridPositive grid := by
  intro value listed
  rw [grid.uniform_pmf positive value listed]
  exact Nat.zero_lt_one

/-- A normalized law cannot be supported on an empty declared grid. -/
theorem EntropyGrid.nonempty_of_support [DecidableEq A] (grid : EntropyGrid A) (μ : Distro A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) : 0 < grid.cells.length := by
  by_cases positive : 0 < grid.cells.length
  · exact positive
  · have empty := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_not_pos positive)
    have normalized := μ.pmf_grid_numerator_sum grid support
    rw [empty, List.map_nil, List.sum_nil] at normalized
    exact False.elim (Nat.ne_of_gt μ.record.den_pos normalized.symm)

theorem Distro.crossEntropy_uniform [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (positive : 0 < grid.cells.length) :
    ExactLog.Equiv (μ.crossEntropy (grid.uniform positive) grid support (grid.uniform_support positive) (grid.uniform_positive positive))
      (ExactLog.log (PositiveRatio.ofNat grid.cells.length positive)) := by
  apply μ.crossEntropy_constant (grid.uniform positive) grid support (grid.uniform_support positive) (grid.uniform_positive positive)
    (⟨1, grid.cells.length, positive⟩ : QProb) Nat.zero_lt_one
  intro value listed
  rw [grid.uniform_pmf positive value listed]
  exact QProb.equiv_refl _

/-- Uniform entropy is exactly the logarithm of the declared cardinality. -/
theorem EntropyGrid.uniform_entropy [DecidableEq A] (grid : EntropyGrid A) (positive : 0 < grid.cells.length) :
    ExactLog.Equiv ((grid.uniform positive).entropy grid (grid.uniform_support positive))
      (ExactLog.log (PositiveRatio.ofNat grid.cells.length positive)) :=
  ExactLog.equiv_trans
    (ExactLog.equiv_symm ((grid.uniform positive).crossEntropy_self grid (grid.uniform_support positive) (grid.uniform_positive positive)))
    ((grid.uniform positive).crossEntropy_uniform grid (grid.uniform_support positive) positive)

/-- The complete finite Shannon bound in bits, with retained null cells. -/
theorem Distro.entropy_le_log_card [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (positive : 0 < grid.cells.length) :
    ExactLog.LE (μ.entropy grid support) (ExactLog.log (PositiveRatio.ofNat grid.cells.length positive)) := by
  have bound := μ.entropy_le_crossEntropy (grid.uniform positive) grid support (grid.uniform_support positive) (grid.uniform_positive positive)
  exact (ExactLog.le_congr (ExactLog.equiv_refl _) (μ.crossEntropy_uniform grid support positive)).mp bound

/-- Equality in the finite entropy upper bound holds exactly for the uniform
law, independent of atom splitting, denominators and zero-weight outliers. -/
theorem Distro.entropy_eq_log_card_iff [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (positive : 0 < grid.cells.length) :
    ExactLog.Equiv (μ.entropy grid support) (ExactLog.log (PositiveRatio.ofNat grid.cells.length positive)) ↔
      μ.SameLaw (grid.uniform positive) := by
  have fixed := ExactLog.equiv_trans (μ.crossEntropy_uniform grid support positive)
    (ExactLog.equiv_symm ((grid.uniform positive).crossEntropy_uniform grid (grid.uniform_support positive) positive))
  have criterion := μ.entropy_eq_of_crossEntropy_eq_iff (grid.uniform positive) grid support
    (grid.uniform_support positive) (grid.uniform_positive positive) fixed
  constructor
  · intro equal
    apply criterion.mp
    exact ExactLog.equiv_trans equal (ExactLog.equiv_symm (grid.uniform_entropy positive))
  · intro same
    exact ExactLog.equiv_trans (criterion.mpr same) (grid.uniform_entropy positive)

end Thesis.Probability.Distros
