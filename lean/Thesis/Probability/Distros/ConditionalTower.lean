import Thesis.Probability.Distros.ConditionalObservable

namespace Thesis.Probability.Distros

private theorem event_and_eq_right (coarse fine : Event Ω)
    (included : ∀ x, fine x = true → coarse x = true) :
    (fun x => coarse x && fine x) = fine := by
  funext x
  cases selected : fine x with
  | false => exact Bool.and_false _
  | true => rw [included x selected]; rfl

/-- A supported finer event remains supported after its coarser event. -/
theorem Distro.conditionOn_eventPositive_of_imp (μ : Distro Ω) (coarse fine : Event Ω)
    (included : ∀ x, fine x = true → coarse x = true)
    (hc : μ.record.EventPositive coarse) (hf : μ.record.EventPositive fine) :
    (μ.conditionOn coarse hc).record.EventPositive fine := by
  change 0 < FiniteProbRecord.eventMass (μ.record.atoms.filter (fun atom => coarse atom.1)) fine
  rw [FiniteProbRecord.eventMass_filter_event, event_and_eq_right coarse fine included]
  exact hf

/-- Nested supported conditioning on an included event agrees as an actual
record with conditioning directly on the finer evidence. -/
theorem Distro.conditionOn_nested (μ : Distro Ω) (coarse fine : Event Ω)
    (included : ∀ x, fine x = true → coarse x = true)
    (hc : μ.record.EventPositive coarse) (hf : μ.record.EventPositive fine) :
    (μ.conditionOn coarse hc).conditionOn fine (μ.conditionOn_eventPositive_of_imp coarse fine included hc hf) =
      μ.conditionOn fine hf := by
  apply Distro.eq_of_atoms_den
  · change (μ.record.atoms.filter (fun atom => coarse atom.1)).filter (fun atom => fine atom.1) =
      μ.record.atoms.filter (fun atom => fine atom.1)
    rw [List.filter_filter]
    apply List.filter_congr
    intro atom _
    exact (Bool.and_comm _ _).trans (congrFun (event_and_eq_right coarse fine included) atom.1)
  · change FiniteProbRecord.eventMass (μ.record.atoms.filter (fun atom => coarse atom.1)) fine =
      FiniteProbRecord.eventMass μ.record.atoms fine
    rw [FiniteProbRecord.eventMass_filter_event, event_and_eq_right coarse fine included]

/-- A deterministic coarsening is explicit finite partition refinement.
The supplied map is data; no representative is chosen from a fibre. -/
structure ObservableRefinement (fine : Ω → Fin n) (coarse : Ω → Fin m) where
  merge : Fin n → Fin m
  agrees : ∀ x, coarse x = merge (fine x)

/-- Conditional expectation onto a coarser finite observable satisfies
E[E[f | fine] | merge(fine)] = E[f | merge(fine)]. The equality includes
unsupported coarse fibres, where both conditional means are explicitly zero. -/
theorem Distro.conditionalExpectation_tower (μ : Distro Ω) (fine : Ω → Fin n)
    (merge : Fin n → Fin m) (f : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv
      (μ.conditionalExpectation (fun y => merge (fine y)) (μ.conditionalExpectation fine f) x)
      (μ.conditionalExpectation (fun y => merge (fine y)) f x) := by
  let cell := μ.record.atoms.filter (fun atom => decide (merge (fine atom.1) = merge (fine x)))
  change SignedRatio.Equiv (conditionalBlockMean cell (μ.conditionalExpectation fine f)) (conditionalBlockMean cell f)
  by_cases supported : 0 < FiniteProbRecord.totalMass cell
  · let ν : Distro Ω := ⟨⟨cell, FiniteProbRecord.totalMass cell, supported, rfl⟩⟩
    have compatible : ∀ atom ∈ ν.record.atoms,
        SignedRatio.Equiv (μ.conditionalExpectation fine f atom.1) (ν.conditionalExpectation fine f atom.1) := by
      intro atom member
      have accepted := of_decide_eq_true (List.mem_filter.mp member).2
      have cells : cell.filter (fun other => decide (fine other.1 = fine atom.1)) =
          μ.record.atoms.filter (fun other => decide (fine other.1 = fine atom.1)) := by
        change (μ.record.atoms.filter (fun other => decide (merge (fine other.1) = merge (fine x)))).filter
          (fun other => decide (fine other.1 = fine atom.1)) = _
        rw [List.filter_filter]
        apply List.filter_congr
        intro other _
        by_cases same : fine other.1 = fine atom.1
        · simp only [same, accepted, decide_true, Bool.true_and]
        · simp only [same, decide_false, Bool.false_and]
      change SignedRatio.Equiv
        (conditionalBlockMean (μ.record.atoms.filter (fun other => decide (fine other.1 = fine atom.1))) f)
        (conditionalBlockMean (cell.filter (fun other => decide (fine other.1 = fine atom.1))) f)
      rw [cells]
      exact SignedRatio.equiv_refl _
    have total := SignedRatio.equiv_trans
      (ν.rationalExpectation_congr_on_support _ _ compatible) (ν.conditionalExpectation_total fine f)
    simpa only [conditionalBlockMean, dif_pos supported, Distro.rationalExpectation,
      FiniteProbRecord.rationalMean, ν] using total
  · simp only [conditionalBlockMean, dif_neg supported]
    exact SignedRatio.equiv_refl _

/-- The tower law stated with an explicit refinement certificate. -/
theorem Distro.conditionalExpectation_tower_refinement (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (refinement : ObservableRefinement fine coarse)
    (f : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation coarse (μ.conditionalExpectation fine f) x)
      (μ.conditionalExpectation coarse f x) := by
  have same : coarse = (fun y => refinement.merge (fine y)) := funext refinement.agrees
  rw [same]
  exact μ.conditionalExpectation_tower fine refinement.merge f x

end Thesis.Probability.Distros
