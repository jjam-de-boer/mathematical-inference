import Thesis.Probability.ConstructiveRealSupportHull
import Thesis.Probability.ConstructiveRealMomentRows
import Thesis.Probability.ConstructiveRealFiniteLinear
import Thesis.Probability.ConstructiveRealEntropyOptimizer
import Thesis.Probability.Construction

namespace Thesis.Probability.ConstructiveReal

/-- A finite sum loses no value when only proved-zero summands are removed. -/
theorem listSum_filter_zero (values : List A) (selected : A → Bool) (terms : A → ConstructiveReal)
    (vanishes : ∀ value ∈ values, selected value = false → Equiv (terms value) zero) :
    Equiv (listSum ((values.filter selected).map terms)) (listSum (values.map terms)) := by
  induction values with
  | nil => exact equiv_refl zero
  | cons first rest ih =>
      have tail := ih (fun value member => vanishes value (List.mem_cons_of_mem _ member))
      cases kept : selected first with
      | true => simpa only [List.filter_cons, kept, List.map_cons, listSum] using add_congr (equiv_refl (terms first)) tail
      | false =>
          simp only [List.filter_cons, kept, List.map_cons, listSum]
          exact equiv_trans tail (equiv_symm (equiv_trans
            (add_congr (vanishes first (List.mem_cons_self ..) kept) (equiv_refl _)) (zero_add _)))

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal
open RationalLinear

/-- An explicitly computed original-grid index, used only with membership.
This is finite rational-label bookkeeping, not analytic support selection. -/
def cellIndex [DecidableEq A] (problem : PartialMomentProblem A) (cell : A) (member : cell ∈ problem.cells) : Fin problem.cells.length :=
  ⟨problem.cells.idxOf cell, List.idxOf_lt_length_of_mem member⟩

private theorem getD_get (cells : List A) (default : A) (index : Fin cells.length) :
    cells.getD index.val default = cells.get index := (List.getElem_eq_getD default).symm

theorem cellIndex_getD [DecidableEq A] (problem : PartialMomentProblem A) (index : Fin problem.cells.length)
    (member : problem.cells.getD index.val problem.default ∈ problem.cells) :
    problem.cellIndex (problem.cells.getD index.val problem.default) member = index := by
  apply Fin.ext
  change problem.cells.idxOf (problem.cells.getD index.val problem.default) = index.val
  rw [getD_get]
  exact idxOf_get_of_nodup problem.cells problem.distinct index

theorem getD_cellIndex [DecidableEq A] (problem : PartialMomentProblem A) (cell : A) (member : cell ∈ problem.cells) :
    problem.cells.getD (problem.cellIndex cell member).val problem.default = cell := by
  have found : (problem.cells[problem.cells.idxOf cell]'(List.idxOf_lt_length_of_mem member) == cell) = true := by
    simpa only [List.idxOf] using (List.findIdx_getElem (p := fun value => value == cell)
      (xs := problem.cells) (w := List.idxOf_lt_length_of_mem member))
  exact (List.getElem_eq_getD problem.default).symm.trans (beq_iff_eq.mp found)

private def zeroMass : UnitIntervalValue := .ofQProb QProb.zero (by decide)

/-- A finite label function for an analytic law, extended by zero away from
its declared grid. Lookup is on finite labels; no real equality is tested. -/
def RealCompatibleLaw.atCell [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw)
    (cell : A) : UnitIntervalValue :=
  if member : cell ∈ problem.cells then law.mass (problem.cellIndex cell member) else zeroMass

theorem RealCompatibleLaw.atCell_getD [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw)
    (index : Fin problem.cells.length) : law.atCell (problem.cells.getD index.val problem.default) = law.mass index := by
  have member : problem.cells.getD index.val problem.default ∈ problem.cells := by
    rw [getD_get]
    exact List.get_mem problem.cells index
  simp only [RealCompatibleLaw.atCell, dif_pos member, problem.cellIndex_getD index member]

/-- Integer observable integral on a finite declared grid. -/
def cellIntegral (problem : PartialMomentProblem A) (masses : A → UnitIntervalValue) (response : A → Int) : ConstructiveReal :=
  realDot problem.cells.length (fun i => response (problem.cells.getD i.val problem.default))
    (fun i => (masses (problem.cells.getD i.val problem.default)).value)

private theorem cellIntegral_sum (problem : PartialMomentProblem A) (masses : A → UnitIntervalValue) (response : A → Int) :
    Equiv (problem.cellIntegral masses response)
      (listSum (problem.cells.map (fun cell => mul (realInteger (response cell)) (masses cell).value))) := by
  apply equiv_trans (FiniteLinear.realDot_pair _ _ _) ?_
  unfold FiniteLinear.pair
  rw [finRange_getD_map problem.cells problem.default (fun cell => mul (realInteger (response cell)) (masses cell).value)]
  exact equiv_refl _

theorem RealCompatibleLaw.cellIntegral_eq [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw)
    (response : A → Int) : Equiv (problem.cellIntegral law.atCell response)
      (realDot problem.cells.length (fun i => response (problem.cells.getD i.val problem.default)) (fun i => (law.mass i).value)) := by
  unfold cellIntegral
  have same : (fun i : Fin problem.cells.length => (law.atCell (problem.cells.getD i.val problem.default)).value) =
      (fun i => (law.mass i).value) := by funext i; rw [law.atCell_getD i]
  rw [same]
  exact equiv_refl _

theorem RealCompatibleLaw.normalized {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw) :
    Equiv (realDot problem.cells.length (fun _ => 1) (fun i => (law.mass i).value)) one :=
  real_simplex_normalized _ (fun row member => law.valid row (List.mem_append_left _ member))

theorem RealCompatibleLaw.moment_bounds {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw)
    (constraint : MomentInterval A) (member : constraint ∈ problem.intervals) :
    LE (ofSignedRatio constraint.lower) (realDot problem.cells.length (constraint.coefficients problem.cells problem.default) (fun i => (law.mass i).value)) ∧
      LE (realDot problem.cells.length (constraint.coefficients problem.cells problem.default) (fun i => (law.mass i).value)) (ofSignedRatio constraint.upper) :=
  (MomentInterval.real_rows_iff constraint problem.cells problem.default _).mp
    (fun row listed => law.valid row (List.mem_append_right _ (List.mem_flatMap.mpr ⟨constraint, member, listed⟩)))

private def lawOfCells (problem : PartialMomentProblem A) (masses : A → UnitIntervalValue)
    (normalized : Equiv (problem.cellIntegral masses (fun _ => 1)) one)
    (moments : ∀ constraint ∈ problem.intervals,
      LE (ofSignedRatio constraint.lower) (problem.cellIntegral masses constraint.response) ∧
      LE (problem.cellIntegral masses constraint.response) (ofSignedRatio constraint.upper)) : problem.RealCompatibleLaw where
  mass i := masses (problem.cells.getD i.val problem.default)
  valid row member := by
    rcases List.mem_append.mp member with simplex | moment
    · exact real_simplex_of_nonnegative _ (fun i => (masses (problem.cells.getD i.val problem.default)).nonnegative) normalized row simplex
    · obtain ⟨constraint, listed, inside⟩ := List.mem_flatMap.mp moment
      exact (MomentInterval.real_rows_iff constraint problem.cells problem.default _).mpr (moments constraint listed) row inside

private def faceSelected [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw) (cell : A) : Bool :=
  decide (0 < (seed.supportHull.distro.pmf cell).num)

/-- Observable integrals are unchanged when proved-zero coordinates are
removed. The two grid sizes can differ and the observable can be signed. -/
private theorem integral_face [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw)
    (masses : A → UnitIntervalValue)
    (vanishes : ∀ cell ∈ problem.cells, faceSelected seed cell = false → Equiv (masses cell).value zero)
    (response : A → Int) : Equiv (seed.supportFace.cellIntegral masses response) (problem.cellIntegral masses response) :=
  equiv_trans (cellIntegral_sum seed.supportFace masses response)
    (equiv_trans (listSum_filter_zero problem.cells (faceSelected seed)
      (fun cell => mul (realInteger (response cell)) (masses cell).value)
      (fun cell member absent => equiv_trans (mul_congr (equiv_refl _) (vanishes cell member absent)) (mul_zero _)))
      (equiv_symm (cellIntegral_sum problem masses response)))

private theorem law_null [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw)
    (law : problem.RealCompatibleLaw) (cell : A) (member : cell ∈ problem.cells) (absent : faceSelected seed cell = false) :
    Equiv (law.atCell cell).value zero := by
  have vanished := seed.supportHull_null law (problem.cellIndex cell member) (by
    rw [problem.getD_cellIndex cell member]
    exact of_decide_eq_false absent)
  simpa only [RealCompatibleLaw.atCell, dif_pos member] using vanished

/-- Every original analytic feasible law restricts to the computed support
face. Equalities, signed intervals and redundant rows remain exact. -/
def RealCompatibleLaw.toSupportFace [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : problem.RealCompatibleLaw) : seed.supportFace.RealCompatibleLaw := by
  apply lawOfCells seed.supportFace law.atCell
  · exact equiv_trans (integral_face seed law.atCell (law_null seed law) (fun _ => 1))
      (equiv_trans (law.cellIntegral_eq (fun _ => 1)) law.normalized)
  · intro constraint member
    have same := equiv_trans (integral_face seed law.atCell (law_null seed law) constraint.response) (law.cellIntegral_eq constraint.response)
    exact ⟨(le_congr (equiv_refl _) same).mpr (law.moment_bounds constraint member).1,
      (le_congr same (equiv_refl _)).mpr (law.moment_bounds constraint member).2⟩

private theorem face_law_null [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : seed.supportFace.RealCompatibleLaw)
    (cell : A) (_member : cell ∈ problem.cells) (absent : faceSelected seed cell = false) : Equiv (law.atCell cell).value zero := by
  have outside : cell ∉ seed.supportFace.cells := by
    intro listed
    have kept := (List.mem_filter.mp listed).2
    change faceSelected seed cell = true at kept
    rw [absent] at kept
    cases kept
  simp only [RealCompatibleLaw.atCell, dif_neg outside]
  exact equiv_refl _

/-- A face law extends by zero to the original finite grid. Normalization
and every original rational expectation interval are preserved. -/
def RealCompatibleLaw.fromSupportFace [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : seed.supportFace.RealCompatibleLaw) : problem.RealCompatibleLaw := by
  have vanishes := face_law_null seed law
  apply lawOfCells problem law.atCell
  · exact equiv_trans (equiv_symm (integral_face seed law.atCell vanishes (fun _ => 1)))
      (equiv_trans (law.cellIntegral_eq (fun _ => 1)) law.normalized)
  · intro constraint member
    have same := equiv_trans (equiv_symm (integral_face seed law.atCell vanishes constraint.response)) (law.cellIntegral_eq constraint.response)
    exact ⟨(le_congr (equiv_refl _) same).mpr (law.moment_bounds constraint member).1,
      (le_congr same (equiv_refl _)).mpr (law.moment_bounds constraint member).2⟩

private theorem entropyGrid_sum (problem : PartialMomentProblem A) (masses : A → UnitIntervalValue) :
    Equiv (realEntropySum ((List.finRange problem.cells.length).map (fun i => masses (problem.cells.getD i.val problem.default))))
      (realEntropySum (problem.cells.map masses)) := by
  unfold realEntropySum
  simp only [List.map_map, Function.comp_def]
  rw [finRange_getD_map problem.cells problem.default (fun cell => (masses cell).entropy)]
  exact equiv_refl _

private theorem entropy_cells [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw) :
    Equiv (realEntropySum (problem.cells.map law.atCell)) law.entropy := by
  have represented := finRange_getD_map problem.cells problem.default (fun cell => (law.atCell cell).entropy)
  have same := listSum_map_congr (List.finRange problem.cells.length)
    (fun i => (law.atCell (problem.cells.getD i.val problem.default)).entropy) (fun i => (law.mass i).entropy)
    (fun i _ => by
      change Equiv (law.atCell (problem.cells.getD i.val problem.default)).entropy (law.mass i).entropy
      rw [law.atCell_getD i]
      exact equiv_refl _)
  simpa only [RealCompatibleLaw.entropy, realEntropySum, List.map_map, Function.comp_def, represented] using same

private theorem entropy_face [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw)
    (masses : A → UnitIntervalValue)
    (vanishes : ∀ cell ∈ problem.cells, faceSelected seed cell = false → Equiv (masses cell).value zero) :
    Equiv (realEntropySum (seed.supportFace.cells.map masses)) (realEntropySum (problem.cells.map masses)) := by
  unfold realEntropySum
  simp only [List.map_map, Function.comp_def]
  apply listSum_filter_zero problem.cells (faceSelected seed)
  intro cell member absent
  exact equiv_trans (realEntropyTerm_congr (vanishes cell member absent) (masses cell).nonnegative (le_refl zero)
    (masses cell).bounded ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel)))
    (realEntropyTerm_zero _ _)

/-- Deleting the forced-zero coordinates preserves analytic entropy exactly,
not merely its rational approximations. -/
theorem RealCompatibleLaw.toSupportFace_entropy [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : problem.RealCompatibleLaw) : Equiv (law.toSupportFace seed).entropy law.entropy :=
  equiv_trans (entropyGrid_sum seed.supportFace law.atCell)
    (equiv_trans (entropy_face seed law.atCell (law_null seed law)) (entropy_cells law))

/-- Zero extension likewise preserves entropy, so the two feasible problems
have the same optimization objective in both directions. -/
theorem RealCompatibleLaw.fromSupportFace_entropy [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : seed.supportFace.RealCompatibleLaw) : Equiv (law.fromSupportFace seed).entropy law.entropy :=
  equiv_trans (entropyGrid_sum problem law.atCell)
    (equiv_trans (equiv_symm (entropy_face seed law.atCell (face_law_null seed law))) (entropy_cells law))

/-- An attained face maximum is an attained original maximum, quantified
over every original analytic feasible law. -/
theorem RealCompatibleLaw.fromSupportFace_maximal [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : seed.supportFace.RealCompatibleLaw) (maximal : law.Maximal) :
    (law.fromSupportFace seed).Maximal := by
  intro other
  exact (le_congr (other.toSupportFace_entropy seed) (equiv_symm (law.fromSupportFace_entropy seed))).mp
    (maximal (other.toSupportFace seed))

/-- Conversely, original maxima restrict to face maxima. Together with the
zero-extension theorem, this justifies optimizing on the computed face. -/
theorem RealCompatibleLaw.toSupportFace_maximal [DecidableEq A] {problem : PartialMomentProblem A}
    (seed : problem.CompatibleLaw) (law : problem.RealCompatibleLaw) (maximal : law.Maximal) :
    (law.toSupportFace seed).Maximal := by
  intro other
  exact (le_congr (other.fromSupportFace_entropy seed) (equiv_symm (law.toSupportFace_entropy seed))).mp
    (maximal (other.fromSupportFace seed))

end Thesis.Probability.Distros.PartialMomentProblem
