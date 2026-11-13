import Thesis.Probability.Distros.PartialMomentProblem
import Thesis.Probability.Distros.RationalLinearObjective

namespace Thesis.Probability.Distros

theorem Distro.rationalExpectation_mono (μ : Distro A) (f g : A → SignedRatio)
    (bounded : μ.AlmostSurely (fun x => SignedRatio.LE (f x) (g x))) :
    SignedRatio.LE (μ.rationalExpectation f) (μ.rationalExpectation g) :=
  (SignedRatio.nonnegative_congr (μ.rationalExpectation_sub g f)).mp
    (μ.rationalExpectation_nonnegative _ bounded)

def integerResponse (response : A → Int) (x : A) : SignedRatio := ⟨response x, 1, Nat.zero_lt_one⟩

def responseLower (cells : List A) (response : A → Int) : SignedRatio :=
  SignedRatio.selectMin SignedRatio.zero (cells.map (integerResponse response))

def responseUpper (cells : List A) (response : A → Int) : SignedRatio :=
  SignedRatio.selectMax SignedRatio.zero (cells.map (integerResponse response))

/-- Finite response bounds require membership only for positive occurrences. -/
theorem response_expectation_bounds (μ : Distro A) (cells : List A) (response : A → Int)
    (support : μ.AlmostSurely (fun x => x ∈ cells)) :
    SignedRatio.LE (responseLower cells response) (μ.rationalExpectation (integerResponse response)) ∧
      SignedRatio.LE (μ.rationalExpectation (integerResponse response)) (responseUpper cells response) := by
  constructor
  · apply (SignedRatio.le_congr (μ.rationalExpectation_constant _) (SignedRatio.equiv_refl _)).mp
    apply μ.rationalExpectation_mono
    intro atom member weight
    exact SignedRatio.selectMin_bounds _ _ _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨atom.1, support atom member weight, rfl⟩))
  · apply (SignedRatio.le_congr (SignedRatio.equiv_refl _) (μ.rationalExpectation_constant _)).mp
    apply μ.rationalExpectation_mono
    intro atom member weight
    exact SignedRatio.selectMax_bounds _ _ _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨atom.1, support atom member weight, rfl⟩))

namespace PartialMomentProblem
open RationalLinear

def objectiveCoefficients (problem : PartialMomentProblem A) (response : A → Int) : Fin problem.cells.length → Int :=
  fun i => response (problem.cells.getD i.val problem.default)

/-- The original mass constraints, the objective equation, and redundant
finite response bounds. The latter ensure that both projected extrema exist. -/
def objectiveSystem (problem : PartialMomentProblem A) (response : A → Int) : List (Inequality (problem.cells.length + 1)) :=
  (problem.rows.map Inequality.weaken ++ objectiveRows (problem.objectiveCoefficients response)) ++
    [headRow problem.cells.length (-1) (SignedRatio.neg (responseLower problem.cells response)),
      headRow problem.cells.length 1 (responseUpper problem.cells response)]

theorem objectiveSystem_masses (problem : PartialMomentProblem A) (response : A → Int)
    (values : Fin (problem.cells.length + 1) → SignedRatio) (valid : Satisfies (problem.objectiveSystem response) values) :
    problem.VectorHolds (fun i => values i.succ) := by
  apply (problem.rows_iff _).mp
  intro row member
  apply (row.holds_weaken_iff values).mp
  exact valid row.weaken (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨row, member, rfl⟩)))

theorem objectiveSystem_response (problem : PartialMomentProblem A) (response : A → Int)
    (values : Fin (problem.cells.length + 1) → SignedRatio) (valid : Satisfies (problem.objectiveSystem response) values) :
    SignedRatio.Equiv (values 0) (dot problem.cells.length (problem.objectiveCoefficients response) (fun i => values i.succ)) :=
  (objectiveRows_iff _ values).mp (fun row member =>
    valid row (List.mem_append_left _ (List.mem_append_right _ member)))

def encodeObjective (problem : PartialMomentProblem A) (response : A → Int) (values : Fin problem.cells.length → SignedRatio) :
    Fin (problem.cells.length + 1) → SignedRatio :=
  prepend (dot problem.cells.length (problem.objectiveCoefficients response) values) values

theorem encodeObjective_valid (problem : PartialMomentProblem A) (response : A → Int)
    (values : Fin problem.cells.length → SignedRatio) (valid : problem.VectorHolds values) :
    Satisfies (problem.objectiveSystem response) (problem.encodeObjective response values) := by
  let encoded := problem.encodeObjective response values
  have tail : (fun i => encoded i.succ) = values := by funext i; exact prepend_succ _ _ i
  have head : encoded 0 = dot problem.cells.length (problem.objectiveCoefficients response) values := prepend_zero _ _
  let μ := simplexGrid problem.cells problem.default values valid.1 problem.nonempty
  have integral := simplexGrid_integer_expectation problem.cells problem.default values valid.1 problem.nonempty response
  have bounded := response_expectation_bounds μ problem.cells response
    (simplexGrid_supported problem.cells problem.default values valid.1 problem.nonempty)
  have lower : SignedRatio.LE (responseLower problem.cells response) (encoded 0) := by
    rw [head]
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) integral).mp bounded.1
  have upper : SignedRatio.LE (encoded 0) (responseUpper problem.cells response) := by
    rw [head]
    exact (SignedRatio.le_congr integral (SignedRatio.equiv_refl _)).mp bounded.2
  intro row member
  rcases List.mem_append.mp member with original | bounds
  · rcases List.mem_append.mp original with mass | equation
    · rcases List.mem_map.mp mass with ⟨source, listed, same⟩
      cases same
      apply (source.holds_weaken_iff encoded).mpr
      rw [tail]
      exact (problem.rows_iff values).mpr valid source listed
    · apply (objectiveRows_iff _ encoded).mpr ?_ row equation
      rw [head, tail]
      exact SignedRatio.equiv_refl _
  · rcases List.mem_cons.mp bounds with same | later
    · cases same
      apply (headRow_holds_iff _ _ _ encoded).mpr
      exact (SignedRatio.le_congr (minus_one_scaleInt _) (SignedRatio.equiv_refl _)).mpr
        ((SignedRatio.neg_le_neg_iff _ _).mpr lower)
    · have same := List.mem_singleton.mp later
      cases same
      apply (headRow_holds_iff _ _ _ encoded).mpr
      exact (SignedRatio.le_congr (SignedRatio.one_scaleInt _) (SignedRatio.equiv_refl _)).mpr upper

/-- A sharp bound includes universal inequalities and compatible laws
attaining both endpoints. Multiple compatible laws need not be identified. -/
structure SharpBounds (problem : PartialMomentProblem A) (response : A → Int) where
  lower : SignedRatio
  upper : SignedRatio
  lowerLaw : problem.CompatibleLaw
  upperLaw : problem.CompatibleLaw
  lower_attained : SignedRatio.Equiv (lowerLaw.distro.rationalExpectation (integerResponse response)) lower
  upper_attained : SignedRatio.Equiv (upperLaw.distro.rationalExpectation (integerResponse response)) upper
  bounds : ∀ μ : Distro A, μ.AlmostSurely (fun x => x ∈ problem.cells) →
    (∀ constraint ∈ problem.intervals, constraint.LawHolds μ) →
    SignedRatio.LE lower (μ.rationalExpectation (integerResponse response)) ∧
      SignedRatio.LE (μ.rationalExpectation (integerResponse response)) upper

/-- Optimize over all compatible rational laws, using no denominator cap. -/
def boundsOfVector [DecidableEq A] (problem : PartialMomentProblem A) (response : A → Int)
    (values : Fin problem.cells.length → SignedRatio) (valid : problem.VectorHolds values) : problem.SharpBounds response := by
  let rows := problem.objectiveSystem response
  let sharp := sharpRange problem.cells.length rows (problem.encodeObjective response values)
    (problem.encodeObjective_valid response values valid) (responseLower problem.cells response) (responseUpper problem.cells response)
    (List.mem_append_right _ (List.mem_cons_self ..))
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  let lowerValid := problem.objectiveSystem_masses response sharp.lower sharp.lower_valid
  let upperValid := problem.objectiveSystem_masses response sharp.upper sharp.upper_valid
  let lowerLaw := problem.lawOfVector (fun i => sharp.lower i.succ) lowerValid
  let upperLaw := problem.lawOfVector (fun i => sharp.upper i.succ) upperValid
  have lowerIntegral : SignedRatio.Equiv (lowerLaw.distro.rationalExpectation (integerResponse response)) (sharp.lower 0) :=
    SignedRatio.equiv_trans (simplexGrid_integer_expectation _ _ _ lowerValid.1 problem.nonempty response)
      (SignedRatio.equiv_symm (problem.objectiveSystem_response response sharp.lower sharp.lower_valid))
  have upperIntegral : SignedRatio.Equiv (upperLaw.distro.rationalExpectation (integerResponse response)) (sharp.upper 0) :=
    SignedRatio.equiv_trans (simplexGrid_integer_expectation _ _ _ upperValid.1 problem.nonempty response)
      (SignedRatio.equiv_symm (problem.objectiveSystem_response response sharp.upper sharp.upper_valid))
  refine ⟨sharp.lower 0, sharp.upper 0, lowerLaw, upperLaw, lowerIntegral, upperIntegral, ?_⟩
  intro μ support moments
  let masses := gridMasses μ problem.cells problem.default
  have massValid := problem.vectorOfLaw μ support moments
  have all := sharp.bounds (problem.encodeObjective response masses) (problem.encodeObjective_valid response masses massValid)
  have integral := gridMasses_integer_expectation μ problem.cells problem.default problem.distinct support response
  change SignedRatio.LE (sharp.lower 0) (dot problem.cells.length (problem.objectiveCoefficients response) masses) ∧
    SignedRatio.LE (dot problem.cells.length (problem.objectiveCoefficients response) masses) (sharp.upper 0) at all
  exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) integral).mpr all.1,
    (SignedRatio.le_congr integral (SignedRatio.equiv_refl _)).mpr all.2⟩

inductive BoundResult (problem : PartialMomentProblem A) (response : A → Int) where
  | bounded (sharp : problem.SharpBounds response)
  | infeasible (certificate : Infeasibility problem.cells.length problem.rows)

/-- Decide feasibility and, when feasible, return attained sharp bounds
for any integer response, including events and scalar or mixed moments. -/
def solveBounds [DecidableEq A] (problem : PartialMomentProblem A) (response : A → Int) : problem.BoundResult response :=
  match RationalLinear.solve problem.cells.length problem.rows with
  | .feasible values valid => .bounded (problem.boundsOfVector response values ((problem.rows_iff values).mp valid))
  | .infeasible certificate => .infeasible certificate

end PartialMomentProblem

def eventResponse (event : Event A) (x : A) : Int := if event x then 1 else 0

theorem eventResponse_expectation (μ : Distro A) (event : Event A) :
    SignedRatio.Equiv (μ.rationalExpectation (integerResponse (eventResponse event))) (μ.record.probVal event).toSignedRatio := by
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _ ?_) (μ.rationalExpectation_indicator event)
  intro x
  cases selected : event x <;>
    simp only [integerResponse, eventResponse, selected, Bool.false_eq_true, if_true, if_false] <;>
    exact SignedRatio.equiv_refl _

def PartialMomentProblem.solveEventBounds [DecidableEq A] (problem : PartialMomentProblem A) (event : Event A) :=
  problem.solveBounds (eventResponse event)

/-- Event-bound certificates speak directly about event probabilities. -/
theorem PartialMomentProblem.SharpBounds.event_bounds [DecidableEq A]
    {problem : PartialMomentProblem A} {event : Event A}
    (sharp : problem.SharpBounds (eventResponse event)) (μ : Distro A)
    (support : μ.AlmostSurely (fun x => x ∈ problem.cells))
    (moments : ∀ constraint ∈ problem.intervals, constraint.LawHolds μ) :
    SignedRatio.LE sharp.lower (μ.record.probVal event).toSignedRatio ∧
      SignedRatio.LE (μ.record.probVal event).toSignedRatio sharp.upper := by
  have bounded := sharp.bounds μ support moments
  exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) (eventResponse_expectation μ event)).mp bounded.1,
    (SignedRatio.le_congr (eventResponse_expectation μ event) (SignedRatio.equiv_refl _)).mp bounded.2⟩

theorem PartialMomentProblem.SharpBounds.event_lower_attained
    {problem : PartialMomentProblem A} {event : Event A} (sharp : problem.SharpBounds (eventResponse event)) :
    SignedRatio.Equiv (sharp.lowerLaw.distro.record.probVal event).toSignedRatio sharp.lower :=
  SignedRatio.equiv_trans (SignedRatio.equiv_symm (eventResponse_expectation sharp.lowerLaw.distro event)) sharp.lower_attained

theorem PartialMomentProblem.SharpBounds.event_upper_attained
    {problem : PartialMomentProblem A} {event : Event A} (sharp : problem.SharpBounds (eventResponse event)) :
    SignedRatio.Equiv (sharp.upperLaw.distro.record.probVal event).toSignedRatio sharp.upper :=
  SignedRatio.equiv_trans (SignedRatio.equiv_symm (eventResponse_expectation sharp.upperLaw.distro event)) sharp.upper_attained

end Thesis.Probability.Distros
