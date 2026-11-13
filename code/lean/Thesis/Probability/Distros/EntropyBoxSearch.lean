import Thesis.Probability.Distros.EntropyBoxes

namespace Thesis.Probability.Distros.PartialMomentProblem

/-- Solve every finite box with the existing complete rational feasibility
solver. Witnesses satisfy all moment constraints exactly; infeasible boxes
produce no candidate. -/
def boxCandidates [DecidableEq A] (problem : PartialMomentProblem A) (size : Nat) (positive : 0 < size) :
    List problem.CompatibleLaw :=
  (ProbabilityBoxes.enumerate problem.cells.length size).filterMap (fun indices =>
    match (problem.withBox size positive indices).solve with
    | .feasible law => some (problem.forgetBox size positive indices law)
    | .infeasible _ => none)

/-- A feasible law always has a nearby exactly feasible candidate. This
uses box coverage and certified infeasibility, not a denominator search. -/
theorem boxCandidates_cover [DecidableEq A] (problem : PartialMomentProblem A) (size : Nat) (positive : 0 < size)
    (μ : Distro A) (valid : problem.Admissible μ) :
    ∃ law ∈ problem.boxCandidates size positive, ∀ value ∈ problem.cells,
      QProb.LE (μ.pmf value) (QProb.add (law.distro.pmf value) (ProbabilityBoxes.width size positive)) ∧
      QProb.LE (law.distro.pmf value) (QProb.add (μ.pmf value) (ProbabilityBoxes.width size positive)) := by
  obtain ⟨indices, listed, inside⟩ := problem.boxes_cover size positive μ valid
  cases result : (problem.withBox size positive indices).solve with
  | feasible law =>
      refine ⟨problem.forgetBox size positive indices law, ?_, ?_⟩
      · apply List.mem_filterMap.mpr
        refine ⟨indices, listed, ?_⟩
        rw [result]
      · exact problem.same_box_close size positive indices μ law.distro inside ⟨law.support, law.moments⟩
  | infeasible certificate =>
      exact False.elim ((problem.withBox size positive indices).refutation_not_realizable certificate
        ⟨μ, inside.1, inside.2⟩)

private def lawEntropy [DecidableEq A] (problem : PartialMomentProblem A) (law : problem.CompatibleLaw) : ExactLog :=
  law.distro.entropy problem.entropyGrid law.support

/-- A finite exact comparison selects an entropy maximum among the supplied
feasible candidates. The initial law makes the procedure total on empty lists. -/
def selectEntropyMaximum [DecidableEq A] (problem : PartialMomentProblem A) (initial : problem.CompatibleLaw) :
    List problem.CompatibleLaw → problem.CompatibleLaw
  | [] => initial
  | law :: rest => problem.selectEntropyMaximum
      (if ExactLog.LE (lawEntropy problem initial) (lawEntropy problem law) then law else initial) rest

theorem selectEntropyMaximum_bounds [DecidableEq A] (problem : PartialMomentProblem A)
    (initial : problem.CompatibleLaw) (laws : List problem.CompatibleLaw) :
    ExactLog.LE (lawEntropy problem initial) (lawEntropy problem (problem.selectEntropyMaximum initial laws)) ∧
    ∀ law ∈ laws, ExactLog.LE (lawEntropy problem law) (lawEntropy problem (problem.selectEntropyMaximum initial laws)) := by
  induction laws generalizing initial with
  | nil => exact ⟨ExactLog.le_refl _, fun _ member => False.elim (List.not_mem_nil member)⟩
  | cons law rest ih =>
      by_cases better : ExactLog.LE (lawEntropy problem initial) (lawEntropy problem law)
      · simp only [selectEntropyMaximum, if_pos better]
        have tail := ih law
        refine ⟨ExactLog.le_trans better tail.1, ?_⟩
        intro candidate member
        rcases List.mem_cons.mp member with rfl | later
        · exact tail.1
        · exact tail.2 candidate later
      · simp only [selectEntropyMaximum, if_neg better]
        have tail := ih initial
        have reverse := (ExactLog.le_total (lawEntropy problem initial) (lawEntropy problem law)).resolve_left better
        refine ⟨tail.1, ?_⟩
        intro candidate member
        rcases List.mem_cons.mp member with rfl | later
        · exact ExactLog.le_trans reverse tail.1
        · exact tail.2 candidate later

/-- Exactly feasible rational output with a global symbolic entropy gap.
Rational enclosures of this gap are a separate final certificate layer. -/
structure EntropyApproximation [DecidableEq A] (problem : PartialMomentProblem A) (tolerance : QProb) where
  law : problem.CompatibleLaw
  upper : ∀ μ (valid : problem.Admissible μ), ExactLog.LE (μ.entropy problem.entropyGrid valid.1)
    (ExactLog.add (law.distro.entropy problem.entropyGrid law.support) (ExactLog.ofSignedRatio tolerance.toSignedRatio))

/-- A total reference algorithm for symbolic epsilon optimality over every
rational feasible law. The finite box cover is independent of input or witness
denominators; no claim of efficient exhaustive enumeration is made. -/
def approximateEntropyByBoxes [DecidableEq A] (problem : PartialMomentProblem A) (initial : problem.CompatibleLaw)
    (tolerance : QProb) (positive : 0 < tolerance.num) : problem.EntropyApproximation tolerance := by
  let threshold := problem.entropyGrid.continuityThreshold tolerance
  let size := threshold.den
  have sizePositive : 0 < size := threshold.den_pos
  let candidates := problem.boxCandidates size sizePositive
  let best := problem.selectEntropyMaximum initial candidates
  refine ⟨best, ?_⟩
  intro μ valid
  obtain ⟨law, listed, close⟩ := problem.boxCandidates_cover size sizePositive μ valid
  have comparison := μ.entropy_uniform_continuity law.distro problem.entropyGrid valid.1 law.support tolerance positive
    (fun value member => (close value member).1)
    (fun value member => (close value member).2)
  have maximal := (problem.selectEntropyMaximum_bounds initial candidates).2 law listed
  exact ExactLog.le_trans comparison.1 ((ExactLog.add_le_add_right_iff _ _ _).mpr maximal)

/-- Skip exhaustive boxes whenever the existing universal entropy bound
already certifies the supplied feasible law to the requested error. -/
def approximateEntropy [DecidableEq A] (problem : PartialMomentProblem A) (initial : problem.CompatibleLaw)
    (tolerance : QProb) (positive : 0 < tolerance.num) : problem.EntropyApproximation tolerance :=
  if sufficient : ExactLog.LE (ExactLog.log (PositiveRatio.ofNat problem.cells.length problem.nonempty))
      (ExactLog.add (initial.distro.entropy problem.entropyGrid initial.support) (ExactLog.ofSignedRatio tolerance.toSignedRatio)) then
    ⟨initial, fun μ valid => ExactLog.le_trans
      (μ.entropy_le_log_card problem.entropyGrid valid.1 problem.nonempty) sufficient⟩
  else problem.approximateEntropyByBoxes initial tolerance positive

end Thesis.Probability.Distros.PartialMomentProblem
