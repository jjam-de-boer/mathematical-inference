import Thesis.Probability.ConstructiveRealLinearCombinations

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal

/-- Erase only provenance; the projected analytic inequality remains exact. -/
def erase (traces : List (Traced rows retained)) : List (Inequality retained) := traces.map Traced.row

/-- Eliminate a variable while carrying its nonnegative original-row
combination. Every branch is on an integral pivot, with proof data retained. -/
def projectTraced (traces : List (Traced rows (retained + 1))) : List (Traced rows retained) :=
  ((traces.filter (fun trace => decide (trace.row.pivot = 0))).attach.map (fun trace =>
    trace.val.trim (of_decide_eq_true (List.mem_filter.mp trace.property).2))) ++
    (traces.filter (fun trace => decide (0 < trace.row.pivot))).attach.flatMap (fun upper =>
      (traces.filter (fun trace => decide (trace.row.pivot < 0))).attach.map (fun lower =>
        upper.val.combine lower.val (of_decide_eq_true (List.mem_filter.mp upper.property).2)
          (of_decide_eq_true (List.mem_filter.mp lower.property).2)))

private theorem attach_flatMap_val (values : List A) (function : A → List B) :
    values.attach.flatMap (fun value => function value.val) = values.flatMap function := by
  have rewritten := (List.flatMap_map Subtype.val function values.attach).symm
  simpa only [List.attach_map_subtype_val] using rewritten

/-- The traced program is exactly the ordinary projection, not a weakened
replacement with different rows or approximate analytic bounds. -/
theorem erase_projectTraced (traces : List (Traced rows (retained + 1))) :
    erase (projectTraced traces) = project (erase traces) := by
  simp only [erase, projectTraced, project, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def, Traced.trim, Traced.combine, List.filter_map, List.flatMap_map]
  congr 1
  · exact List.attach_map_val (f := fun trace : Traced rows (retained + 1) => trace.row.trim)
  · let upperRows := traces.filter (fun trace => decide (0 < trace.row.pivot))
    let lowerRows := traces.filter (fun trace => decide (trace.row.pivot < 0))
    change upperRows.attach.flatMap (fun upper => lowerRows.attach.map (fun lower => combine upper.val.row lower.val.row)) =
      upperRows.flatMap (fun upper => lowerRows.map (fun lower => combine upper.row lower.row))
    have inner : (fun upper : {value // value ∈ upperRows} => lowerRows.attach.map (fun lower => combine upper.val.row lower.val.row)) =
        (fun upper : {value // value ∈ upperRows} => lowerRows.map (fun lower => combine upper.val.row lower.row)) := by
      funext upper
      exact List.attach_map_val (f := fun lower : Traced rows (retained + 1) => combine upper.val.row lower.row)
    rw [inner]
    exact attach_flatMap_val upperRows (fun upper => lowerRows.map (fun lower => combine upper.row lower.row))

/-- Original input rows carry singleton source indices. `ofFn` makes this
finite indexing data explicit, including the empty constraint system. -/
def inputs (rows : List (Inequality variables)) : List (Traced rows variables) := List.ofFn (Traced.input rows)

theorem erase_inputs (rows : List (Inequality variables)) : erase (inputs rows) = rows := by
  simp only [erase, inputs, List.map_ofFn, Function.comp_def, Traced.input]
  exact List.ofFn_getElem

/-- The Farkas signs justify every projected constant by its actual
nonnegative source combination. No active analytic inequality is selected. -/
theorem constants_of_farkas (retained : Nat) (traces : List (Traced rows retained)) (condition : FarkasCondition rows) :
    constantConditions retained (erase traces) := by
  induction retained with
  | zero =>
      intro row member
      obtain ⟨trace, _, same⟩ := List.mem_map.mp member
      cases same
      exact trace.constant_nonnegative condition
  | succ retained ih =>
      change constantConditions retained (project (erase traces))
      rw [← erase_projectTraced]
      exact ih (projectTraced traces)

/-- Constructive Farkas solver for fixed integral coefficients and analytic
right-hand sides. The supplied combination condition is converted to the
proved finite projected constants, and the existing analytic lifting
program computes every variable. No real feasibility decision is claimed. -/
def solveFarkas (rows : List (Inequality variables)) (condition : FarkasCondition rows) :
    {values : Fin variables → ConstructiveReal // Satisfies rows values} :=
  solve variables rows (by
    have consistent := constants_of_farkas variables (inputs rows) condition
    simpa only [erase_inputs] using consistent)

/-- Exact feasibility equivalence, with a computational forward direction.
Every premise ranges over explicit nonnegative integral row combinations;
there is no assumed choice, separation oracle or real comparison decision. -/
theorem farkas_iff_feasible (rows : List (Inequality variables)) :
    FarkasCondition rows ↔ ∃ values, Satisfies rows values :=
  ⟨fun condition => ⟨(solveFarkas rows condition).val, (solveFarkas rows condition).property⟩,
    fun ⟨values, satisfies⟩ => farkas_of_satisfies rows values satisfies⟩

end Thesis.Probability.AnalyticLinear
