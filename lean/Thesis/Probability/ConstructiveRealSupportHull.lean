import Thesis.Probability.ConstructiveRealMomentApproximation
import Thesis.Probability.Distros.PartialMomentBounds

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- Universal rational coordinate bounds extend to every analytic feasible
law through exactly feasible density, including equality and interval rows. -/
theorem RealCompatibleLaw.coordinate_le_of_rational_bound [DecidableEq A] {problem : PartialMomentProblem A}
    (law : problem.RealCompatibleLaw) (index : Fin problem.cells.length) (upper : ConstructiveReal)
    (bounded : ∀ rational : problem.CompatibleLaw,
      LE (ofSignedRatio (rational.distro.pmf (problem.cells.getD index.val problem.default)).toSignedRatio) upper) :
    LE (law.mass index).value upper := by
  apply le_of_forall_rational_error
  intro precision
  let approximation := law.approximate precision
  exact le_trans (approximation.property index).1 (add_le_add (bounded approximation.val) (le_refl _))

/-- The exact attained singleton bounds also constrain analytic laws. -/
theorem SharpBounds.real_coordinate_upper [DecidableEq A] {problem : PartialMomentProblem A}
    (index : Fin problem.cells.length)
    (sharp : problem.SharpBounds (eventResponse (FiniteProbRecord.singletonEvent (problem.cells.getD index.val problem.default))))
    (law : problem.RealCompatibleLaw) : LE (law.mass index).value (ofSignedRatio sharp.upper) := by
  apply law.coordinate_le_of_rational_bound index
  intro rational
  exact (ofSignedRatio_le_iff _ _).mpr (sharp.event_bounds rational.distro rational.support rational.moments).2

/-- An actual feasible midpoint retaining every original grid label. Null
records are still presentation choices; no positivity is assumed here. -/
def CompatibleLaw.midpoint [DecidableEq A] {problem : PartialMomentProblem A}
    (first second : problem.CompatibleLaw) : problem.CompatibleLaw := by
  let admissible := problem.admissible_mixture first.distro second.distro
    ⟨first.support, first.moments⟩ ⟨second.support, second.moments⟩ 1 1 (by decide)
  refine ⟨first.distro.mixture second.distro 1 1 (by decide), admissible.1, admissible.2, ?_⟩
  intro cell member
  obtain ⟨weight, listed⟩ := second.retains cell member
  exact ⟨(1 * first.distro.record.den) * weight,
    List.mem_append_right _ (List.mem_map.mpr ⟨(cell, weight), listed, rfl⟩)⟩

/-- Finite mixing combines support witnesses without a denominator bound. -/
def CompatibleLaw.mixList [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) : List problem.CompatibleLaw → problem.CompatibleLaw
  | [] => seed
  | first :: rest => first.midpoint (seed.mixList rest)

theorem CompatibleLaw.mixList_positive [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (laws : List problem.CompatibleLaw) (witness : problem.CompatibleLaw)
    (member : witness ∈ laws) (cell : A) (positive : 0 < (witness.distro.pmf cell).num) :
    0 < ((seed.mixList laws).distro.pmf cell).num := by
  induction laws with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · have firstPositive : 0 < (first.distro.pmf cell).num := by simpa only [same] using positive
        exact first.distro.mixture_positive_left (seed.mixList rest).distro 1 1 (by decide) (by decide) cell firstPositive
      · exact first.distro.mixture_positive_right (seed.mixList rest).distro 1 1 (by decide) (by decide) cell (ih later)

/-- Coordinate extrema are computed by the existing exact rational solver,
starting from an actual feasible law. -/
def CompatibleLaw.coordinateBounds [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (index : Fin problem.cells.length) :
    problem.SharpBounds (eventResponse (FiniteProbRecord.singletonEvent (problem.cells.getD index.val problem.default))) :=
  problem.boundsOfVector _ (gridMasses seed.distro problem.cells problem.default)
    (problem.vectorOfLaw seed.distro seed.support seed.moments)

/-- A single rational feasible law supports every state that can occur in
any feasible law. It mixes the finitely many attained coordinate maxima;
no comparison or choice of analytic probabilities is used. -/
def CompatibleLaw.supportHull [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) : problem.CompatibleLaw :=
  seed.mixList ((List.finRange problem.cells.length).map (fun index => (seed.coordinateBounds index).upperLaw))

private theorem attained_positive [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (index : Fin problem.cells.length)
    (positive : 0 < (seed.coordinateBounds index).upper.num) :
    0 < ((seed.coordinateBounds index).upperLaw.distro.pmf (problem.cells.getD index.val problem.default)).num := by
  let sharp := seed.coordinateBounds index
  let mass := sharp.upperLaw.distro.pmf (problem.cells.getD index.val problem.default)
  have same : (mass.num : Int) * (sharp.upper.den : Int) = sharp.upper.num * (mass.den : Int) := sharp.event_upper_attained
  by_cases nonzero : 0 < mass.num
  · exact nonzero
  · have vanished : mass.num = 0 := by omega
    rw [vanished, Int.natCast_zero, Int.zero_mul] at same
    have product : 0 < sharp.upper.num * (mass.den : Int) := Int.mul_pos positive (Int.natCast_pos.mpr mass.den_pos)
    omega

theorem CompatibleLaw.supportHull_positive_of_upper [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (index : Fin problem.cells.length)
    (positive : 0 < (seed.coordinateBounds index).upper.num) :
    0 < (seed.supportHull.distro.pmf (problem.cells.getD index.val problem.default)).num :=
  seed.mixList_positive _ (seed.coordinateBounds index).upperLaw
    (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩) _ (attained_positive seed index positive)

/-- Every analytic feasible law vanishes outside the computed rational
support hull. This proves presentation-invariant forced zeros, rather than
merely observing that a particular solver output contains null atoms. -/
theorem CompatibleLaw.supportHull_null [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : problem.RealCompatibleLaw) (index : Fin problem.cells.length)
    (absent : ¬ 0 < (seed.supportHull.distro.pmf (problem.cells.getD index.val problem.default)).num) :
    Equiv (law.mass index).value zero := by
  have nonpositive : (seed.coordinateBounds index).upper.num ≤ 0 := by
    by_cases positive : 0 < (seed.coordinateBounds index).upper.num
    · exact False.elim (absent (seed.supportHull_positive_of_upper index positive))
    · omega
  have bound : SignedRatio.LE (seed.coordinateBounds index).upper SignedRatio.zero := by
    rw [SignedRatio.le_iff_cross]
    simpa only [SignedRatio.zero, Int.natCast_one, Int.mul_one, Int.zero_mul] using nonpositive
  exact ⟨le_trans ((seed.coordinateBounds index).real_coordinate_upper index law)
    ((ofSignedRatio_le_iff _ _).mpr bound), (law.mass index).nonnegative⟩

private theorem cell_index (cells : List A) (default cell : A) (member : cell ∈ cells) :
    ∃ index : Fin cells.length, cells.getD index.val default = cell := by
  induction cells with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · cases same; exact ⟨0, rfl⟩
      · obtain ⟨index, represented⟩ := ih later
        exact ⟨index.succ, represented⟩

/-- The hull includes the support of every rational feasible law, regardless
of additional recorded zero weights or duplicate occurrences. -/
theorem CompatibleLaw.supportHull_dominates [DecidableEq A] {problem : PartialMomentProblem A}
    (seed other : problem.CompatibleLaw) (cell : A) (member : cell ∈ problem.cells)
    (positive : 0 < (other.distro.pmf cell).num) : 0 < (seed.supportHull.distro.pmf cell).num := by
  obtain ⟨index, represented⟩ := cell_index problem.cells problem.default cell member
  by_cases present : 0 < (seed.supportHull.distro.pmf cell).num
  · exact present
  · have vanished := seed.supportHull_null other.toReal index (by simpa only [represented] using present)
    have rational := (ofSignedRatio_equiv_iff _ _).mp vanished
    change (other.distro.pmf (problem.cells.getD index.val problem.default)).toSignedRatio.Equiv SignedRatio.zero at rational
    rw [represented] at rational
    change ((other.distro.pmf cell).num : Int) * 1 = 0 * ((other.distro.pmf cell).den : Int) at rational
    simp only [Int.mul_one, Int.zero_mul] at rational
    omega

/-- The support face is selected by an exact rational mass test on the
constructed witness, not by testing analytic masses for equality to zero. -/
def CompatibleLaw.supportFaceCells [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) : List A :=
  problem.cells.filter (fun cell => decide (0 < (seed.supportHull.distro.pmf cell).num))

private theorem supportFace_support [DecidableEq A] {problem : PartialMomentProblem A}
    (seed other : problem.CompatibleLaw) : other.distro.AlmostSurely (fun cell => cell ∈ seed.supportFaceCells) := by
  intro atom member positive
  have listed := other.support atom member positive
  exact List.mem_filter.mpr ⟨listed, decide_eq_true
    (seed.supportHull_dominates other atom.1 listed (other.distro.pmf_pos_of_atom atom member positive))⟩

/-- The active face depends only on the feasible problem, not on the
starting law, its presentation, or the solver's choice of support witness. -/
theorem CompatibleLaw.supportFaceCells_eq [DecidableEq A] {problem : PartialMomentProblem A}
    (first second : problem.CompatibleLaw) : first.supportFaceCells = second.supportFaceCells := by
  apply List.filter_congr
  intro cell member
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨fun positive => second.supportHull_dominates first.supportHull cell member positive,
    fun positive => first.supportHull_dominates second.supportHull cell member positive⟩

/-- The computed support face is nonempty because its actual feasible
witness has strictly positive total mass. -/
theorem CompatibleLaw.supportFaceCells_nonempty [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) : 0 < seed.supportFaceCells.length := by
  have total : 0 < FiniteProbRecord.eventMass seed.supportHull.distro.record.atoms topEvent := by
    rw [FiniteProbRecord.eventMass_top, seed.supportHull.distro.record.total_mass]
    exact seed.supportHull.distro.record.den_pos
  obtain ⟨atom, member, positive, _⟩ := (FiniteProbRecord.eventMass_pos_iff_exists_atom _ _).mp total
  have listed := supportFace_support seed seed.supportHull atom member positive
  cases empty : seed.supportFaceCells with
  | nil => rw [empty] at listed; exact False.elim (List.not_mem_nil listed)
  | cons first rest => exact Nat.zero_lt_succ _

/-- Restrict the declared states to the computed feasible face. Original
expectation intervals, including equalities and redundancy, are retained. -/
def CompatibleLaw.supportFace [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) : PartialMomentProblem A where
  cells := seed.supportFaceCells
  default := problem.default
  nonempty := seed.supportFaceCells_nonempty
  distinct := List.Sublist.nodup List.filter_sublist problem.distinct
  intervals := problem.intervals

/-- Every original rational feasible law is also feasible on this face;
retained null records outside the face do not prevent the conversion. -/
def CompatibleLaw.toSupportFace [DecidableEq A] {problem : PartialMomentProblem A}
    (seed other : problem.CompatibleLaw) : seed.supportFace.CompatibleLaw where
  distro := other.distro
  support := supportFace_support seed other
  moments := other.moments
  retains cell member := other.retains cell (List.mem_filter.mp member).1

/-- The constructed witness is strictly positive on the entire reduced
state grid, ready for the positive-interior multiplier development. -/
theorem CompatibleLaw.supportFace_positive [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) : seed.supportHull.distro.GridPositive seed.supportFace.entropyGrid := by
  intro cell member
  exact of_decide_eq_true (List.mem_filter.mp member).2

end Thesis.Probability.Distros.PartialMomentProblem
