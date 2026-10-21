import Thesis.Probability.Distros.EntropyMixture

namespace Thesis.Probability.Distros

private theorem comparison_positive [DecidableEq A] (μ ν : Distro A) (grid : EntropyGrid A)
    (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (left right : Nat) (positive : 0 < left + right) (leftPositive : 0 < left) (rightPositive : 0 < right)
    (referencePositive : (μ.mixture ν left right positive).GridPositive grid) :
    ExactLog.LE
      (ExactLog.add (ExactLog.scaleRatio ⟨left, left + right, positive⟩ (μ.entropy grid first))
        (ExactLog.scaleRatio ⟨right, left + right, positive⟩ (ν.entropy grid second)))
      ((μ.mixture ν left right positive).entropy grid (μ.mixture_support ν left right positive _ first second)) ∧
    (ExactLog.Equiv
      (ExactLog.add (ExactLog.scaleRatio ⟨left, left + right, positive⟩ (μ.entropy grid first))
        (ExactLog.scaleRatio ⟨right, left + right, positive⟩ (ν.entropy grid second)))
      ((μ.mixture ν left right positive).entropy grid (μ.mixture_support ν left right positive _ first second)) ↔ μ.SameLaw ν) := by
  let m := μ.mixture ν left right positive
  have supported := μ.mixture_support ν left right positive _ first second
  let t : QProb := ⟨left, left + right, positive⟩
  let u : QProb := ⟨right, left + right, positive⟩
  let a := μ.entropy grid first
  let b := ν.entropy grid second
  let c := μ.crossEntropy m grid first supported referencePositive
  let d := ν.crossEntropy m grid second supported referencePositive
  have boundFirst : ExactLog.LE a c := μ.entropy_le_crossEntropy m grid first supported referencePositive
  have boundSecond : ExactLog.LE b d := ν.entropy_le_crossEntropy m grid second supported referencePositive
  have weightedFirst := ExactLog.scaleRatio_mono t boundFirst
  have weightedSecond := ExactLog.scaleRatio_mono u boundSecond
  have identity : ExactLog.Equiv (ExactLog.add (ExactLog.scaleRatio t c) (ExactLog.scaleRatio u d))
      (m.entropy grid supported) :=
    ExactLog.equiv_trans (ExactLog.equiv_symm (μ.crossEntropy_mixture ν m grid first second supported referencePositive left right positive))
      (m.crossEntropy_self grid supported referencePositive)
  refine ⟨(ExactLog.le_congr (ExactLog.equiv_refl _) identity).mp (ExactLog.add_le_add weightedFirst weightedSecond), ?_⟩
  constructor
  · intro equal
    have sums := ExactLog.equiv_trans equal (ExactLog.equiv_symm identity)
    have equalFirst := (ExactLog.scaleRatio_equiv_iff t leftPositive a c).mp
      (ExactLog.equiv_of_add_equiv weightedFirst weightedSecond sums)
    have equalSecond := (ExactLog.scaleRatio_equiv_iff u rightPositive b d).mp
      (ExactLog.equiv_of_add_equiv weightedSecond weightedFirst
        (ExactLog.equiv_trans (ExactLog.add_comm _ _) (ExactLog.equiv_trans sums (ExactLog.add_comm _ _))))
    have firstZero := ExactLog.equiv_trans (μ.relativeEntropy_cross_sub m grid first supported referencePositive)
      ((ExactLog.sub_equiv_zero_iff c a).mpr (ExactLog.equiv_symm equalFirst))
    have secondZero := ExactLog.equiv_trans (ν.relativeEntropy_cross_sub m grid second supported referencePositive)
      ((ExactLog.sub_equiv_zero_iff d b).mpr (ExactLog.equiv_symm equalSecond))
    exact (μ.sameLaw_of_relativeEntropy_zero m grid first supported referencePositive firstZero).trans
      (ν.sameLaw_of_relativeEntropy_zero m grid second supported referencePositive secondZero).symm
  · intro same
    have equalFirst := μ.entropy_sameLaw same grid first second
    have equalMixture := m.entropy_sameLaw (μ.mixture_sameLaw_of_sameLaw ν left right positive same) grid supported first
    have normalized : QProb.Equiv (QProb.add t u) QProb.one := by
      change (left * (left + right) + right * (left + right)) * 1 = 1 * ((left + right) * (left + right))
      rw [← Nat.add_mul, Nat.mul_one, Nat.one_mul]
    have combined := ExactLog.equiv_trans
      (ExactLog.add_congr (ExactLog.equiv_refl _) (ExactLog.scaleRatio_value_congr u (ExactLog.equiv_symm equalFirst)))
      (ExactLog.equiv_symm (ExactLog.scaleRatio_add_weight t u a))
    have constant := ExactLog.scaleRatio_weight_congr normalized a
    rw [ExactLog.scaleRatio_one] at constant
    exact ExactLog.equiv_trans combined (ExactLog.equiv_trans constant (ExactLog.equiv_symm equalMixture))

/-- Shannon entropy is concave, with strict equality criterion for a mixture
using two positive rational coefficients. Input and mixture laws may have zero
masses anywhere on the declared grid. -/
theorem Distro.entropy_mixture_comparison [DecidableEq A] (μ ν : Distro A) (grid : EntropyGrid A)
    (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (left right : Nat) (positive : 0 < left + right) (leftPositive : 0 < left) (rightPositive : 0 < right) :
    ExactLog.LE
      (ExactLog.add (ExactLog.scaleRatio ⟨left, left + right, positive⟩ (μ.entropy grid first))
        (ExactLog.scaleRatio ⟨right, left + right, positive⟩ (ν.entropy grid second)))
      ((μ.mixture ν left right positive).entropy grid (μ.mixture_support ν left right positive _ first second)) ∧
    (ExactLog.Equiv
      (ExactLog.add (ExactLog.scaleRatio ⟨left, left + right, positive⟩ (μ.entropy grid first))
        (ExactLog.scaleRatio ⟨right, left + right, positive⟩ (ν.entropy grid second)))
      ((μ.mixture ν left right positive).entropy grid (μ.mixture_support ν left right positive _ first second)) ↔ μ.SameLaw ν) := by
  let m := μ.mixture ν left right positive
  let selected := fun value => decide (0 < (m.pmf value).num)
  let active := grid.restrict selected
  have restrictSupport (ρ : Distro A) (support : ρ.AlmostSurely (fun value => value ∈ grid.cells))
      (dominates : ∀ value, 0 < (ρ.pmf value).num → 0 < (m.pmf value).num) :
      ρ.AlmostSurely (fun value => value ∈ active.cells) := by
    intro atom member weight
    exact List.mem_filter.mpr ⟨support atom member weight, by
      exact (decide_eq_true_eq).mpr (dominates atom.1 (ρ.pmf_pos_of_atom atom member weight))⟩
  have supported := μ.mixture_support ν left right positive _ first second
  have firstActive := restrictSupport μ first (μ.mixture_positive_left ν left right positive leftPositive)
  have secondActive := restrictSupport ν second (μ.mixture_positive_right ν left right positive rightPositive)
  have mixActive := restrictSupport m supported (fun _ mass => mass)
  have activePositive : m.GridPositive active := by
    intro value member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have erased (ρ : Distro A) (support : ρ.AlmostSurely (fun value => value ∈ grid.cells))
      (restricted : ρ.AlmostSurely (fun value => value ∈ active.cells))
      (dominates : ∀ value, 0 < (ρ.pmf value).num → 0 < (m.pmf value).num) :
      ExactLog.Equiv (ρ.entropy active restricted) (ρ.entropy grid support) := by
    apply ρ.entropy_restrict grid selected support restricted
    intro value _ absent
    apply Nat.eq_zero_of_not_pos
    intro mass
    have chosen : selected value = true := (decide_eq_true_eq).mpr (dominates value mass)
    rw [absent] at chosen
    cases chosen
  have firstEqual := erased μ first firstActive (μ.mixture_positive_left ν left right positive leftPositive)
  have secondEqual := erased ν second secondActive (μ.mixture_positive_right ν left right positive rightPositive)
  have mixtureEqual := erased m supported mixActive (fun _ mass => mass)
  have weightedEqual := ExactLog.add_congr (ExactLog.scaleRatio_value_congr ⟨left, left + right, positive⟩ firstEqual)
    (ExactLog.scaleRatio_value_congr ⟨right, left + right, positive⟩ secondEqual)
  have comparison := comparison_positive μ ν active firstActive secondActive left right positive leftPositive rightPositive activePositive
  refine ⟨(ExactLog.le_congr weightedEqual mixtureEqual).mp comparison.1, ?_⟩
  constructor
  · intro equal
    exact comparison.2.mp (ExactLog.equiv_trans weightedEqual (ExactLog.equiv_trans equal (ExactLog.equiv_symm mixtureEqual)))
  · intro same
    exact ExactLog.equiv_trans (ExactLog.equiv_symm weightedEqual)
      (ExactLog.equiv_trans (comparison.2.mpr same) mixtureEqual)

/-- Different laws give strictly larger mixture entropy than the weighted
input entropy: the reverse inequality is impossible. -/
theorem Distro.entropy_strict_concave [DecidableEq A] (μ ν : Distro A) (grid : EntropyGrid A)
    (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (left right : Nat) (positive : 0 < left + right) (leftPositive : 0 < left) (rightPositive : 0 < right)
    (different : ¬ μ.SameLaw ν) :
    ¬ ExactLog.LE ((μ.mixture ν left right positive).entropy grid (μ.mixture_support ν left right positive _ first second))
      (ExactLog.add (ExactLog.scaleRatio ⟨left, left + right, positive⟩ (μ.entropy grid first))
        (ExactLog.scaleRatio ⟨right, left + right, positive⟩ (ν.entropy grid second))) := by
  intro reverse
  have comparison := μ.entropy_mixture_comparison ν grid first second left right positive leftPositive rightPositive
  exact different (comparison.2.mp ((ExactLog.equiv_iff_le _ _).mpr ⟨comparison.1, reverse⟩))

/-- Every attained entropy maximum in a class closed under midpoints is
unique as a probability law. The theorem does not assert that a rational
maximum exists in every feasible class. -/
theorem Distro.entropy_maximum_unique [DecidableEq A] (grid : EntropyGrid A) (admissible : Distro A → Prop)
    (support : ∀ ρ, admissible ρ → ρ.AlmostSurely (fun value => value ∈ grid.cells))
    (midpoints : ∀ μ ν, admissible μ → admissible ν → admissible (μ.mixture ν 1 1 (by decide)))
    (μ ν : Distro A) (first : admissible μ) (second : admissible ν)
    (maxFirst : ∀ ρ (valid : admissible ρ), ExactLog.LE (ρ.entropy grid (support ρ valid)) (μ.entropy grid (support μ first)))
    (maxSecond : ∀ ρ (valid : admissible ρ), ExactLog.LE (ρ.entropy grid (support ρ valid)) (ν.entropy grid (support ν second))) :
    μ.SameLaw ν := by
  have endpointEqual := (ExactLog.equiv_iff_le _ _).mpr ⟨maxSecond μ first, maxFirst ν second⟩
  have weightedEqual := ExactLog.equiv_trans
    (ExactLog.add_congr (ExactLog.equiv_refl _)
      (ExactLog.scaleRatio_value_congr (⟨1, 2, by decide⟩ : QProb) (ExactLog.equiv_symm endpointEqual)))
    (ExactLog.convexPair_constant 1 1 (by decide) (μ.entropy grid (support μ first)))
  have mixValid := midpoints μ ν first second
  have upper := maxFirst (μ.mixture ν 1 1 (by decide)) mixValid
  have reverse := (ExactLog.le_congr (ExactLog.equiv_refl _) (ExactLog.equiv_symm weightedEqual)).mp upper
  have comparison := μ.entropy_mixture_comparison ν grid (support μ first) (support ν second) 1 1 (by decide) (by decide) (by decide)
  exact comparison.2.mp ((ExactLog.equiv_iff_le _ _).mpr ⟨comparison.1, reverse⟩)

end Thesis.Probability.Distros
