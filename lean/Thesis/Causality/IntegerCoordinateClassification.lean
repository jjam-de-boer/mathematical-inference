import Thesis.Causality.IntegerLargeSolution

namespace Thesis.Causality.IntegerEquations

open Probability.IntegerLinearAlgebra

/-!
# Exact coordinate classification for natural solutions

For a finite signed integer system A*x = b and a selected coordinate j,
the classifier distinguishes three possibilities: no natural solution;
a supplied solution and a bound valid for every solution; or a supplied
solution and a nonnegative homogeneous direction positive at j. The last
case computes solutions above every requested coordinate threshold.

Positivity needs no large right-hand side or extra search dimension.
Write h = u + e_j, with u natural. Then A*h = 0 and h_j > 0 are equivalent
to A*u = -A*e_j. The existing exact feasibility procedure decides this
shifted system and retains actual witness data. If it has no solution,
the large-coordinate bridge bounds every original solution below 2^N,
where N is the original system's finite carry enumeration length.

The base solution is essential: a positive homogeneous direction alone
does not make an infeasible system unbounded. Empty solution sets therefore
have their own result, rather than being reported as bounded by vacuity.
The returned bound need not be the smallest bound. Carry enumeration can
still be expensive; termination is not a practical runtime guarantee.
These are equation solutions, with no Petri firing-order or reachability
claim and no rational-polynomial feasibility claim.
-/

variable {rows variables : Nat}

private theorem rowValue_head (coefficients : Fin (variables + 1) → Int)
    (values : Fin (variables + 1) → Nat) :
    rowValue coefficients values = coefficients 0 * (values 0 : Int) +
      rowValue (fun index => coefficients index.succ) (fun index => values index.succ) := by
  simp only [rowValue, List.finRange_succ, List.map_cons, List.map_map, Function.comp_def]
  rfl

/-- The coordinate selector is a literal finite sum, including when the
selected coordinate is first or last. No infinite linear-space basis is used. -/
private theorem rowValue_unit (coefficients : Fin variables → Int) (selected : Fin variables) :
    rowValue coefficients (fun index => if index = selected then 1 else 0) = coefficients selected := by
  induction variables with
  | zero => exact Fin.elim0 selected
  | succ variables ih =>
      refine Fin.cases ?_ (fun selected => ?_) selected
      · rw [rowValue_head]
        have tailZero : (fun index : Fin variables => if index.succ = 0 then (1 : Nat) else 0) =
            (fun _ => 0) := by
          funext index
          exact if_neg (Fin.succ_ne_zero index)
        simp only [ite_true, Int.natCast_one, Int.mul_one, tailZero, rowValue_zero, Int.add_zero]
      · rw [rowValue_head]
        have away : (0 : Fin (variables + 1)) ≠ selected.succ := (Fin.succ_ne_zero selected).symm
        simp only [if_neg away, Int.natCast_zero, Int.mul_zero, Int.zero_add, Fin.succ_inj]
        exact ih (fun index => coefficients index.succ) selected

private def raiseCoordinate (values : Fin variables → Nat) (selected : Fin variables) : Fin variables → Nat :=
  fun index => values index + if index = selected then 1 else 0

private theorem rowValue_raiseCoordinate (coefficients : Fin variables → Int)
    (values : Fin variables → Nat) (selected : Fin variables) :
    rowValue coefficients (raiseCoordinate values selected) = rowValue coefficients values + coefficients selected := by
  exact (rowValue_add coefficients values _).trans (congrArg (rowValue coefficients values + ·)
    (rowValue_unit coefficients selected))

/-- The direction is natural data with its equation and selected-coordinate
certificates; it is not chosen from a propositional existence statement. -/
abbrev System.PositiveDirection (system : System rows variables) (index : Fin variables) :=
  {direction : Fin variables → Nat // system.homogeneous.Satisfies direction ∧ 0 < direction index}

/-- Shift the selected coordinate down by one before solving. Keeping the
same matrix and dimensions avoids encoding the much larger 2^N threshold. -/
def System.positiveDirectionSystem (system : System rows variables) (index : Fin variables) : System rows variables where
  coefficients := system.coefficients
  rhs := fun row => -(system.coefficients row index)

def System.directionOfPositiveSolution (system : System rows variables) (index : Fin variables)
    (values : Fin variables → Nat) (valid : (system.positiveDirectionSystem index).Satisfies values) :
    system.PositiveDirection index := by
  refine ⟨raiseCoordinate values index, ?_, ?_⟩
  · intro row
    have equation := valid row
    change rowValue (system.coefficients row) values = -(system.coefficients row index) at equation
    change rowValue (system.coefficients row) (raiseCoordinate values index) = 0
    rw [rowValue_raiseCoordinate, equation]
    omega
  · change 0 < values index + if index = index then 1 else 0
    rw [if_pos rfl]
    omega

/-- Conversely, positive natural h_j can be lowered by one without leaving
the natural domain. This supplies the missing-direction branch constructively. -/
def System.positiveSolutionOfDirection (system : System rows variables) (index : Fin variables)
    (direction : system.PositiveDirection index) :
    {values : Fin variables → Nat // (system.positiveDirectionSystem index).Satisfies values} := by
  let values := fun other => if other = index then direction.val other - 1 else direction.val other
  have raised : raiseCoordinate values index = direction.val := by
    funext other
    have positive := direction.property.2
    by_cases same : other = index
    · subst other
      simp only [raiseCoordinate, values, ite_true]
      omega
    · simp only [raiseCoordinate, values, if_neg same, Nat.add_zero]
  refine ⟨values, ?_⟩
  intro row
  have equation : rowValue (system.coefficients row) direction.val = 0 := direction.property.1 row
  rw [← raised, rowValue_raiseCoordinate] at equation
  change rowValue (system.coefficients row) values = -(system.coefficients row index)
  omega

/-- A computed bound, not an assumed cutoff on the unknowns. The bounded
branch below certifies this bound for every solution of the original system. -/
def System.coordinateBound (system : System rows variables) : Nat :=
  2 ^ system.carryWitness.enumeration.length

theorem System.boundOfNoPositiveDirection (system : System rows variables) (index : Fin variables)
    (missing : ¬ ∃ direction : Fin variables → Nat,
      system.homogeneous.Satisfies direction ∧ 0 < direction index) :
    ∀ values, system.Satisfies values → values index < system.coordinateBound := by
  intro values valid
  by_cases large : system.coordinateBound ≤ values index
  · let direction := system.directionOfLargeSolution values valid index large
    exact False.elim (missing ⟨direction.val, direction.property⟩)
  · omega

/-- Every requested threshold gets an actual solution, using the same
computed base and direction. All other coordinates stay natural as well. -/
def System.solutionAbove (system : System rows variables) (index : Fin variables)
    (base : Fin variables → Nat) (valid : system.Satisfies base)
    (direction : system.PositiveDirection index) (threshold : Nat) :
    {values : Fin variables → Nat // system.Satisfies values ∧ threshold ≤ values index} := by
  refine ⟨fun other => base other + threshold * direction.val other,
    system.satisfies_add_homogeneous valid direction.property.1 threshold, ?_⟩
  have positive : 1 ≤ direction.val index := direction.property.2
  have product := Nat.mul_le_mul_left threshold positive
  rw [Nat.mul_one] at product
  change threshold ≤ base index + threshold * direction.val index
  omega

/-- This property alone permits an empty solution set. The classifier's
bounded result additionally stores a solution, preventing that ambiguity. -/
def System.CoordinateBounded (system : System rows variables) (index : Fin variables) : Prop :=
  ∃ bound : Nat, ∀ values, system.Satisfies values → values index < bound

/-- Arbitrarily large coordinate values in actual natural solutions;
neither a rational relaxation nor arbitrary zero-padded encodings suffice. -/
def System.CoordinateUnbounded (system : System rows variables) (index : Fin variables) : Prop :=
  ∀ threshold : Nat, ∃ values, system.Satisfies values ∧ threshold ≤ values index

inductive CoordinateKind where
  | infeasible
  | bounded
  | unbounded
  deriving DecidableEq

/-- Every branch carries its justification. The unbounded branch stores
both base and direction; `solutionAbove` computes a witness at any threshold.
The bounded branch uses the original carry bound, without claiming optimality. -/
inductive CoordinateResult (system : System rows variables) (index : Fin variables) where
  | infeasible (missing : ¬ ∃ values, system.Satisfies values)
  | bounded (base : Fin variables → Nat) (valid : system.Satisfies base)
      (bounds : ∀ values, system.Satisfies values → values index < system.coordinateBound)
  | unbounded (base : Fin variables → Nat) (valid : system.Satisfies base)
      (direction : system.PositiveDirection index)

def CoordinateResult.kind {system : System rows variables} {index : Fin variables} :
    CoordinateResult system index → CoordinateKind
  | .infeasible _ => .infeasible
  | .bounded _ _ _ => .bounded
  | .unbounded _ _ _ => .unbounded

/-- Two exact feasibility calls suffice. Original infeasibility is checked
first; otherwise the shifted homogeneous problem either computes a direction
or excludes all such directions. The latter exclusion invokes the proved
large-coordinate implication, not an assumed finite search cutoff. -/
def System.classifyCoordinate (system : System rows variables) (index : Fin variables) :
    CoordinateResult system index :=
  match system.solve with
  | .infeasible missing => .infeasible missing
  | .feasible base valid =>
      match (system.positiveDirectionSystem index).solve with
      | .feasible values shifted =>
          .unbounded base valid (system.directionOfPositiveSolution index values shifted)
      | .infeasible missing =>
          .bounded base valid (system.boundOfNoPositiveDirection index (by
            rintro ⟨direction, null, positive⟩
            let shifted := system.positiveSolutionOfDirection index ⟨direction, null, positive⟩
            exact missing ⟨shifted.val, shifted.property⟩))

variable {system : System rows variables} {index : Fin variables}

/-- These exactness statements apply to every certified result, including
the result returned by `classifyCoordinate`; no particular solver output
or finite range of candidates is assumed. -/
theorem CoordinateResult.infeasible_iff (result : CoordinateResult system index) :
    result.kind = .infeasible ↔ ¬ ∃ values, system.Satisfies values := by
  cases result with
  | infeasible missing => exact ⟨fun _ => missing, fun _ => rfl⟩
  | bounded base valid bounds =>
      constructor
      · intro impossible; cases impossible
      · intro missing; exact False.elim (missing ⟨base, valid⟩)
  | unbounded base valid direction =>
      constructor
      · intro impossible; cases impossible
      · intro missing; exact False.elim (missing ⟨base, valid⟩)

theorem CoordinateResult.bounded_iff (result : CoordinateResult system index) :
    result.kind = .bounded ↔
      (∃ values, system.Satisfies values) ∧ system.CoordinateBounded index := by
  cases result with
  | infeasible missing =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨found, _⟩
        exact False.elim (missing found)
  | bounded base valid bounds =>
      exact ⟨fun _ => ⟨⟨base, valid⟩, system.coordinateBound, bounds⟩, fun _ => rfl⟩
  | unbounded base valid direction =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, bound, bounded⟩
        let above := system.solutionAbove index base valid direction bound
        have upper := bounded above.val above.property.1
        have lower := above.property.2
        exact False.elim (Nat.not_lt_of_ge lower upper)

theorem CoordinateResult.unbounded_iff (result : CoordinateResult system index) :
    result.kind = .unbounded ↔ system.CoordinateUnbounded index := by
  cases result with
  | infeasible missing =>
      constructor
      · intro impossible; cases impossible
      · intro growth
        obtain ⟨values, valid, _⟩ := growth 0
        exact False.elim (missing ⟨values, valid⟩)
  | bounded base valid bounds =>
      constructor
      · intro impossible; cases impossible
      · intro growth
        obtain ⟨values, valid, large⟩ := growth system.coordinateBound
        exact False.elim (Nat.not_lt_of_ge large (bounds values valid))
  | unbounded base valid direction =>
      constructor
      · intro _ threshold
        let above := system.solutionAbove index base valid direction threshold
        exact ⟨above.val, above.property⟩
      · intro _; rfl

end Thesis.Causality.IntegerEquations
