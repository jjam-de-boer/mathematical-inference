import Thesis.Probability.EntropyContinuity

namespace Thesis.Probability.ExactLog

private theorem constant_roots (values : List A) (argument : PositiveRatio) (degree : Nat) (positive : 0 < degree) :
    Equiv (listSum (values.map (fun _ => root argument degree positive)))
      (root (argument.pow values.length) degree positive) := by
  induction values with
  | nil =>
      rw [List.map_nil, listSum, List.length_nil, PositiveRatio.pow_zero]
      exact equiv_symm (root_one_equiv_zero degree positive)
  | cons head rest ih =>
      have split := root_add_equiv argument (argument.pow rest.length) degree positive
      have power : PositiveRatio.mul argument (argument.pow rest.length) = argument.pow (rest.length + 1) := by
        apply PositiveRatio.ext <;> simp only [PositiveRatio.mul, PositiveRatio.pow, Nat.pow_succ, Nat.mul_comm]
      rw [power] at split
      exact equiv_trans (add_congr (equiv_refl _) ih) split

private theorem rational_root (num den : Nat) (positive : 0 < den) :
    ofSignedRatio ⟨(num : Int), den, positive⟩ = root ((PositiveRatio.ofNat 2 (by decide)).pow num) den positive := by
  apply ext
  · apply PositiveRatio.ext <;> simp only [ofSignedRatio, root, PositiveRatio.pow, PositiveRatio.ofNat,
      Int.toNat_natCast, Int.toNat_neg_natCast, Nat.pow_zero, Nat.one_pow]
  · rfl

theorem listSum_constant_bits (values : List A) (den : Nat) (positive : 0 < den) :
    Equiv (listSum (values.map (fun _ => ofSignedRatio ⟨1, den, positive⟩)))
      (ofSignedRatio ⟨(values.length : Int), den, positive⟩) := by
  have unit : ofSignedRatio ⟨1, den, positive⟩ = root (PositiveRatio.ofNat 2 (by decide)) den positive := rfl
  rw [unit, rational_root values.length den positive]
  exact constant_roots values (PositiveRatio.ofNat 2 (by decide)) den positive

theorem listSum_map_le (values : List A) (f g : A → ExactLog) (compared : ∀ value ∈ values, LE (f value) (g value)) :
    LE (listSum (values.map f)) (listSum (values.map g)) := by
  induction values with
  | nil => exact le_refl _
  | cons head rest ih =>
      exact add_le_add (compared head (List.mem_cons_self ..))
        (ih (fun value member => compared value (List.mem_cons_of_mem _ member)))

end Thesis.Probability.ExactLog

namespace Thesis.Probability.Distros

/-- A uniform coordinate tolerance sufficient for a requested total entropy
error on the entire declared grid, including retained zero-mass cells. -/
def EntropyGrid.continuityThreshold (grid : EntropyGrid A) (tolerance : QProb) : QProb :=
  ⟨1, 2 ^ (3 * ((grid.cells.length * tolerance.den).log2 + 1) + 6), Nat.pow_pos (by decide)⟩

/-- Uniform entropy continuity for all rational laws on a declared finite
grid. Neither input denominators nor positive supports are restricted. -/
theorem Distro.entropy_uniform_continuity [DecidableEq A] (μ ν : Distro A) (grid : EntropyGrid A)
    (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (tolerance : QProb) (positive : 0 < tolerance.num)
    (leftClose : ∀ value ∈ grid.cells, QProb.LE (μ.pmf value) (QProb.add (ν.pmf value) (grid.continuityThreshold tolerance)))
    (rightClose : ∀ value ∈ grid.cells, QProb.LE (ν.pmf value) (QProb.add (μ.pmf value) (grid.continuityThreshold tolerance))) :
    ExactLog.LE (μ.entropy grid first) (ExactLog.add (ν.entropy grid second) (ExactLog.ofSignedRatio tolerance.toSignedRatio)) ∧
    ExactLog.LE (ν.entropy grid second) (ExactLog.add (μ.entropy grid first) (ExactLog.ofSignedRatio tolerance.toSignedRatio)) := by
  let n := (grid.cells.length * tolerance.den).log2 + 1
  let error := ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩
  have coordinates (value : A) (member : value ∈ grid.cells) : EntropyWithin (μ.pmf value) (ν.pmf value) error := by
    have pBound := (μ.probVal_bounds (FiniteProbRecord.singletonEvent value)).2
    have qBound := (ν.probVal_bounds (FiniteProbRecord.singletonEvent value)).2
    exact entropyTerm_continuity _ _
      (by simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using pBound)
      (by simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using qBound)
      n (leftClose value member) (rightClose value member)
  have totalError : ExactLog.LE (ExactLog.listSum (grid.cells.map (fun _ => error)))
      (ExactLog.ofSignedRatio tolerance.toSignedRatio) := by
    have represented := ExactLog.listSum_constant_bits grid.cells (2 ^ n) (Nat.pow_pos (by decide))
    apply (ExactLog.le_congr represented (ExactLog.equiv_refl _)).mpr
    apply (ExactLog.ofSignedRatio_le_iff _ _).mpr
    have power : grid.cells.length * tolerance.den ≤ 2 ^ n := Nat.le_of_lt Nat.lt_log2_self
    have scaled : 2 ^ n ≤ tolerance.num * 2 ^ n := Nat.le_mul_of_pos_left _ positive
    simpa only [QProb.toSignedRatio, ← Int.natCast_mul, Int.ofNat_le] using Nat.le_trans power scaled
  have bound (ρ σ : Distro A)
      (supportρ : ρ.AlmostSurely (fun value => value ∈ grid.cells))
      (supportσ : σ.AlmostSurely (fun value => value ∈ grid.cells))
      (pointwise : ∀ value ∈ grid.cells, ExactLog.LE (entropyTerm (ρ.pmf value)) (ExactLog.add (entropyTerm (σ.pmf value)) error)) :
      ExactLog.LE (ρ.entropy grid supportρ) (ExactLog.add (σ.entropy grid supportσ) (ExactLog.ofSignedRatio tolerance.toSignedRatio)) := by
    have terms := ExactLog.listSum_map_le grid.cells (fun value => entropyTerm (ρ.pmf value))
      (fun value => ExactLog.add (entropyTerm (σ.pmf value)) error) pointwise
    have distributed := ExactLog.listSum_map_add grid.cells (fun value => entropyTerm (σ.pmf value)) (fun _ => error)
    have combined := (ExactLog.le_congr (ExactLog.equiv_refl _) distributed).mp terms
    exact ExactLog.le_trans combined ((ExactLog.add_le_add_left_iff _ _ (σ.entropy grid supportσ)).mpr totalError)
  exact ⟨bound μ ν first second (fun value member => (coordinates value member).1),
    bound ν μ second first (fun value member => (coordinates value member).2)⟩

end Thesis.Probability.Distros
