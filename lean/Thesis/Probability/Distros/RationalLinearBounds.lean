import Thesis.Probability.Distros.RationalLinearSolve

namespace Thesis.Probability.Distros.RationalLinear

/-- Keep the first coordinate and eliminate every remaining coordinate. -/
def projectToOne : (others : Nat) → List (Inequality (others + 1)) → List (Inequality 1)
  | 0, rows => rows
  | others + 1, rows => projectToOne others (project rows)

def oneValues (value : SignedRatio) : Fin 1 → SignedRatio := extend (fun i => Fin.elim0 i) value

theorem oneValues_zero (value : SignedRatio) : oneValues value 0 = value := extend_last _ _

theorem oneValues_restrict (values : Fin 1 → SignedRatio) : oneValues (values 0) = values := by
  funext i
  have same : i = 0 := Fin.ext (by have bound := i.isLt; omega)
  rw [same, oneValues_zero]

theorem projectToOne_sound (others : Nat) (rows : List (Inequality (others + 1)))
    (values : Fin (others + 1) → SignedRatio) (valid : Satisfies rows values) :
    Satisfies (projectToOne others rows) (oneValues (values 0)) := by
  induction others with
  | zero => simpa only [projectToOne, oneValues_restrict] using valid
  | succ others ih =>
      apply ih (project rows) (fun i => values i.castSucc)
      apply project_sound rows _ (values (Fin.last _))
      simpa only [extend_restrict] using valid

/-- Lift a retained objective value back to a complete satisfying assignment. -/
def liftFromOne : (others : Nat) → (rows : List (Inequality (others + 1))) →
    (value : SignedRatio) → Satisfies (projectToOne others rows) (oneValues value) →
    {values : Fin (others + 1) → SignedRatio // Satisfies rows values ∧ SignedRatio.Equiv (values 0) value}
  | 0, rows, value, valid => ⟨oneValues value, valid, by rw [oneValues_zero]; exact SignedRatio.equiv_refl _⟩
  | others + 1, rows, value, valid =>
      let previous := liftFromOne others (project rows) value valid
      let last := lift rows previous.val previous.property.1
      ⟨extend previous.val last.val, last.property, by
        change SignedRatio.Equiv (extend previous.val last.val (0 : Fin (others + 1)).castSucc) value
        rw [extend_castSucc]
        exact previous.property.2⟩

/-- A bound on the retained first coordinate survives all projections. -/
def headRow (others : Nat) (coefficient : Int) (bound : SignedRatio) : Inequality (others + 1) :=
  ⟨fun i => if i.val = 0 then coefficient else 0, bound⟩

theorem projectToOne_headRow_mem (others : Nat) (rows : List (Inequality (others + 1)))
    (coefficient : Int) (bound : SignedRatio) (member : headRow others coefficient bound ∈ rows) :
    headRow 0 coefficient bound ∈ projectToOne others rows := by
  induction others with
  | zero => exact member
  | succ others ih =>
      apply ih (project rows)
      have zero : (headRow (others + 1) coefficient bound).pivot = 0 := by
        simp only [headRow, Inequality.pivot, Fin.val_last, Nat.add_one_ne_zero, if_false]
      exact project_zero_mem rows _ member zero

private theorem one_lower_bound (rows : List (Inequality 1)) (value : SignedRatio)
    (valid : Satisfies rows (oneValues value)) :
    ∀ bound ∈ lowerBounds rows (fun i => Fin.elim0 i), SignedRatio.LE bound value := by
  intro bound member
  rcases List.mem_map.mp member with ⟨row, listed, same⟩
  rw [← same]
  exact (row.holds_lower_iff _ value (of_decide_eq_true (List.mem_filter.mp listed).2)).mp
    (valid row (List.mem_filter.mp listed).1)

private theorem one_upper_bound (rows : List (Inequality 1)) (value : SignedRatio)
    (valid : Satisfies rows (oneValues value)) :
    ∀ bound ∈ upperBounds rows (fun i => Fin.elim0 i), SignedRatio.LE value bound := by
  intro bound member
  rcases List.mem_map.mp member with ⟨row, listed, same⟩
  rw [← same]
  exact (row.holds_upper_iff _ value (of_decide_eq_true (List.mem_filter.mp listed).2)).mp
    (valid row (List.mem_filter.mp listed).1)

private theorem one_satisfies (rows : List (Inequality 1)) (old : SignedRatio)
    (valid : Satisfies rows (oneValues old)) (value : SignedRatio)
    (lows : ∀ bound ∈ lowerBounds rows (fun i => Fin.elim0 i), SignedRatio.LE bound value)
    (highs : ∀ bound ∈ upperBounds rows (fun i => Fin.elim0 i), SignedRatio.LE value bound) :
    Satisfies rows (oneValues value) := by
  intro row member
  by_cases positive : 0 < row.pivot
  · apply (row.holds_upper_iff _ value positive).mpr
    exact highs _ (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true positive⟩, rfl⟩)
  · by_cases negative : row.pivot < 0
    · apply (row.holds_lower_iff _ value negative).mpr
      exact lows _ (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true negative⟩, rfl⟩)
    · have zero : row.pivot = 0 := by omega
      exact (row.holds_zero_iff _ value zero).mpr ((row.holds_zero_iff _ old zero).mp (valid row member))

/-- Both endpoint assignments satisfy the original one-variable system,
and every satisfying value lies between them. -/
structure OneRange (rows : List (Inequality 1)) where
  lower : SignedRatio
  upper : SignedRatio
  lower_valid : Satisfies rows (oneValues lower)
  upper_valid : Satisfies rows (oneValues upper)
  bounds : ∀ value, Satisfies rows (oneValues value) → SignedRatio.LE lower value ∧ SignedRatio.LE value upper

/-- Finite endpoint selection computes the exact closed feasible interval.
An existing feasible assignment handles constant rows and rules out reversal. -/
def oneRange (rows : List (Inequality 1)) (value : SignedRatio) (valid : Satisfies rows (oneValues value))
    (lowerExists : lowerBounds rows (fun i => Fin.elim0 i) ≠ [])
    (upperExists : upperBounds rows (fun i => Fin.elim0 i) ≠ []) : OneRange rows := by
  cases lowerEq : lowerBounds rows (fun i => Fin.elim0 i) with
  | nil => exact False.elim (lowerExists lowerEq)
  | cons below lows =>
      cases upperEq : upperBounds rows (fun i => Fin.elim0 i) with
      | nil => exact False.elim (upperExists upperEq)
      | cons above highs =>
          let lo := SignedRatio.selectMax below lows
          let hi := SignedRatio.selectMin above highs
          have loMem : lo ∈ lowerBounds rows (fun i => Fin.elim0 i) := by
            rw [lowerEq]; exact SignedRatio.selectMax_mem below lows
          have hiMem : hi ∈ upperBounds rows (fun i => Fin.elim0 i) := by
            rw [upperEq]; exact SignedRatio.selectMin_mem above highs
          have ordered : SignedRatio.LE lo hi := SignedRatio.le_trans
            (one_lower_bound rows value valid lo loMem) (one_upper_bound rows value valid hi hiMem)
          have lowerAll : ∀ bound ∈ lowerBounds rows (fun i => Fin.elim0 i), SignedRatio.LE bound lo := by
            rw [lowerEq]; exact SignedRatio.selectMax_bounds below lows
          have upperAll : ∀ bound ∈ upperBounds rows (fun i => Fin.elim0 i), SignedRatio.LE hi bound := by
            rw [upperEq]; exact SignedRatio.selectMin_bounds above highs
          exact ⟨lo, hi,
            one_satisfies rows value valid lo lowerAll (fun bound member => SignedRatio.le_trans ordered (upperAll bound member)),
            one_satisfies rows value valid hi (fun bound member => SignedRatio.le_trans (lowerAll bound member) ordered) upperAll,
            fun other satisfies => ⟨one_lower_bound rows other satisfies lo loMem, one_upper_bound rows other satisfies hi hiMem⟩⟩

/-- Sharp bounds carry actual full assignments attaining both extrema. -/
structure SharpRange (others : Nat) (rows : List (Inequality (others + 1))) where
  lower : Fin (others + 1) → SignedRatio
  upper : Fin (others + 1) → SignedRatio
  lower_valid : Satisfies rows lower
  upper_valid : Satisfies rows upper
  bounds : ∀ values, Satisfies rows values → SignedRatio.LE (lower 0) (values 0) ∧ SignedRatio.LE (values 0) (upper 0)

def sharpRange (others : Nat) (rows : List (Inequality (others + 1)))
    (values : Fin (others + 1) → SignedRatio) (valid : Satisfies rows values)
    (lo hi : SignedRatio) (lowerMember : headRow others (-1) (SignedRatio.neg lo) ∈ rows)
    (upperMember : headRow others 1 hi ∈ rows) : SharpRange others rows := by
  let projected := projectToOne others rows
  have lowerRow := projectToOne_headRow_mem others rows (-1) (SignedRatio.neg lo) lowerMember
  have upperRow := projectToOne_headRow_mem others rows 1 hi upperMember
  have lowerExists : lowerBounds projected (fun i => Fin.elim0 i) ≠ [] := by
    intro empty
    have member : (headRow 0 (-1) (SignedRatio.neg lo)).lowerValue (fun i => Fin.elim0 i) ∈ lowerBounds projected (fun i => Fin.elim0 i) :=
      List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨lowerRow, by decide⟩, rfl⟩
    rw [empty] at member
    exact List.not_mem_nil member
  have upperExists : upperBounds projected (fun i => Fin.elim0 i) ≠ [] := by
    intro empty
    have member : (headRow 0 1 hi).upperValue (fun i => Fin.elim0 i) ∈ upperBounds projected (fun i => Fin.elim0 i) :=
      List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨upperRow, by decide⟩, rfl⟩
    rw [empty] at member
    exact List.not_mem_nil member
  let endpoints := oneRange projected (values 0) (projectToOne_sound others rows values valid) lowerExists upperExists
  let lower := liftFromOne others rows endpoints.lower endpoints.lower_valid
  let upper := liftFromOne others rows endpoints.upper endpoints.upper_valid
  refine ⟨lower.val, upper.val, lower.property.1, upper.property.1, ?_⟩
  intro other satisfies
  have bounds := endpoints.bounds (other 0) (projectToOne_sound others rows other satisfies)
  exact ⟨(SignedRatio.le_congr lower.property.2 (SignedRatio.equiv_refl _)).mpr bounds.1,
    (SignedRatio.le_congr (SignedRatio.equiv_refl _) upper.property.2).mpr bounds.2⟩

end Thesis.Probability.Distros.RationalLinear
