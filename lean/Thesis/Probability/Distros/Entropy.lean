import Thesis.Probability.EntropyValue
import Thesis.Probability.Distros.LawBasics

namespace Thesis.Probability.Distros

/-- The distinct observable outcomes on which entropy is computed. The grid
retains null outcomes; it never treats repeated atom occurrences as new states. -/
structure EntropyGrid (A : Type u) where
  cells : List A
  distinct : cells.Nodup

/-- Shannon entropy in bits of a law supported almost surely on the declared
grid. Zero-weight atoms outside that grid remain valid record presentations. -/
def Distro.entropy [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (_support : μ.AlmostSurely (fun value => value ∈ grid.cells)) : ExactLog :=
  ExactLog.listSum (grid.cells.map (fun value => entropyTerm (μ.pmf value)))

theorem Distro.entropy_nonnegative [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) :
    ExactLog.LE ExactLog.zero (μ.entropy grid support) := by
  apply ExactLog.listSum_map_nonnegative
  intro value _
  exact entropyTerm_nonnegative _ (μ.probVal_bounds (FiniteProbRecord.singletonEvent value)).2

/-- Atom splitting, denominator rescaling, permutation and null outliers
cannot change entropy when they preserve the probability law. -/
theorem Distro.entropy_sameLaw [DecidableEq A] {μ ν : Distro A} (same : μ.SameLaw ν)
    (grid : EntropyGrid A) (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells)) :
    ExactLog.Equiv (μ.entropy grid first) (ν.entropy grid second) := by
  apply ExactLog.listSum_map_congr
  intro value _
  exact entropyTerm_congr (same (FiniteProbRecord.singletonEvent value))

theorem Distro.entropy_grid_perm [DecidableEq A] (μ : Distro A) (first second : EntropyGrid A)
    (permutation : first.cells.Perm second.cells)
    (supportedFirst : μ.AlmostSurely (fun value => value ∈ first.cells))
    (supportedSecond : μ.AlmostSurely (fun value => value ∈ second.cells)) :
    ExactLog.Equiv (μ.entropy first supportedFirst) (μ.entropy second supportedSecond) :=
  ExactLog.listSum_perm (permutation.map _)

/-- Declaring an additional zero-mass outcome does not change entropy. The
new cell remains present in the declared grid and in all subsequent interfaces. -/
theorem Distro.entropy_add_null_cell [DecidableEq A] (μ : Distro A) (grid extended : EntropyGrid A)
    (value : A) (cells : extended.cells = value :: grid.cells)
    (support : μ.AlmostSurely (fun x => x ∈ grid.cells))
    (supportExtended : μ.AlmostSurely (fun x => x ∈ extended.cells))
    (zero : QProb.Equiv (μ.pmf value) QProb.zero) :
    ExactLog.Equiv (μ.entropy extended supportExtended) (μ.entropy grid support) := by
  unfold entropy
  rw [cells, List.map_cons, ExactLog.listSum]
  have head := entropyTerm_congr zero
  rw [entropyTerm_zero_num QProb.zero rfl] at head
  refine ExactLog.equiv_trans (ExactLog.add_congr head (ExactLog.equiv_refl _)) ?_
  rw [ExactLog.zero_add]
  exact ExactLog.equiv_refl _

/-- Positive reference mass is required at every declared state. This is an
explicit hypothesis, including at states of zero observed mass. -/
def Distro.GridPositive [DecidableEq A] (reference : Distro A) (grid : EntropyGrid A) : Prop :=
  ∀ value ∈ grid.cells, 0 < (reference.pmf value).num

/-- KL divergence in bits on a declared finite grid with a positive reference
law. Both laws are supported almost surely, retaining null record outliers. -/
def Distro.relativeEntropy [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (_support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (_referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) : ExactLog :=
  ExactLog.listSum (grid.cells.attach.map (fun cell =>
    relativeEntropyTerm (μ.pmf cell.val) (reference.pmf cell.val) (positive cell.val cell.property)))

/-- KL depends only on the two laws, rather than either atom presentation. -/
theorem Distro.relativeEntropy_sameLaw [DecidableEq A] {μ ν reference reference' : Distro A}
    (observed : μ.SameLaw ν) (prior : reference.SameLaw reference') (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (support' : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport' : reference'.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) (positive' : reference'.GridPositive grid) :
    ExactLog.Equiv (μ.relativeEntropy reference grid support referenceSupport positive)
      (ν.relativeEntropy reference' grid support' referenceSupport' positive') := by
  apply ExactLog.listSum_map_congr
  intro cell _
  exact relativeEntropyTerm_congr (observed (FiniteProbRecord.singletonEvent cell.val))
    (prior (FiniteProbRecord.singletonEvent cell.val)) _ _

theorem Distro.relativeEntropy_self [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) (positive : μ.GridPositive grid) :
    ExactLog.Equiv (μ.relativeEntropy μ grid support support positive) ExactLog.zero := by
  refine ExactLog.equiv_trans (ExactLog.listSum_map_congr grid.cells.attach _ (fun _ => ExactLog.zero) ?_) ?_
  · intro cell _
    exact relativeEntropyTerm_self _ _
  · rw [ExactLog.listSum_map_zero]
    exact ExactLog.equiv_refl _

end Thesis.Probability.Distros
