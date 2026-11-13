import Thesis.Probability.Distros.RationalConditionalNormalization

namespace Thesis.Probability.Distros.RationalLinear.Conditional

/-!
# Attained unit-interval fractional ranges from the existing linear solver

Normalize a positive denominator as in `RationalConditionalNormalization`,
retain a first objective coordinate, and bound that coordinate by zero and
one. These last rows describe the source domain explicitly: this module
optimizes probability-valued fractions, not every arbitrary signed ratio.
Probability-law clients must derive those bounds for their actual events.

The old exact linear solver now gives both endpoint assignments. Decoding
constructs original supported assignments, and the response-preservation
theorem identifies their conditional values. Finite projection lifting also
constructs an assignment for every rational value between the endpoints.
Thus no new optimization oracle, real scalar, denominator cap or selected
existential witness is introduced. Native causal coverage remains downstream.
-/

variable {variables : Nat}

private theorem satisfies_append_iff (first second : List (Inequality variables))
    (values : Fin variables → SignedRatio) :
    Satisfies (first ++ second) values ↔ Satisfies first values ∧ Satisfies second values := by
  constructor
  · intro valid
    exact ⟨fun row member => valid row (List.mem_append_left _ member),
      fun row member => valid row (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩ row member
    rcases List.mem_append.mp member with first | second
    · exact left row first
    · exact right row second

private theorem satisfies_weaken_iff (rows : List (Inequality variables))
    (values : Fin (variables + 1) → SignedRatio) :
    Satisfies (rows.map Inequality.weaken) values ↔ Satisfies rows (fun i => values i.succ) := by
  constructor
  · intro valid row member
    exact (row.holds_weaken_iff values).mp (valid row.weaken (List.mem_map.mpr ⟨row, member, rfl⟩))
  · intro valid row member
    rcases List.mem_map.mp member with ⟨original, listed, rfl⟩
    exact (original.holds_weaken_iff values).mpr (valid original listed)

def objectiveCoefficients (numerator : Fin variables → Int) : Fin (variables + 1) → Int :=
  (⟨numerator, SignedRatio.zero⟩ : Inequality variables).extendZero.coefficients

theorem objectiveCoefficients_dot (point : NormalizedAssignment rows denominator) (numerator : Fin variables → Int) :
    SignedRatio.Equiv (dot (variables + 1) (objectiveCoefficients numerator) point.values)
      (dot variables numerator point.masses) := by
  rw [← extend_restrict point.values]
  exact (⟨numerator, SignedRatio.zero⟩ : Inequality variables).extendZero_dot _ _

def unitRows (others : Nat) : List (Inequality (others + 1)) :=
  [headRow others (-1) SignedRatio.zero, headRow others 1 SignedRatio.one]

theorem unitRows_iff (others : Nat) (values : Fin (others + 1) → SignedRatio) :
    Satisfies (unitRows others) values ↔ SignedRatio.LE SignedRatio.zero (values 0) ∧ SignedRatio.LE (values 0) SignedRatio.one := by
  have lower : (headRow others (-1) SignedRatio.zero).Holds values ↔ SignedRatio.LE SignedRatio.zero (values 0) :=
    (headRow_holds_iff _ _ _ values).trans
      ((SignedRatio.le_congr (minus_one_scaleInt _) (by rfl)).trans
        (SignedRatio.neg_le_neg_iff _ _))
  have upper : (headRow others 1 SignedRatio.one).Holds values ↔ SignedRatio.LE (values 0) SignedRatio.one :=
    (headRow_holds_iff _ _ _ values).trans (SignedRatio.le_congr (SignedRatio.one_scaleInt _) (SignedRatio.equiv_refl _))
  constructor
  · intro valid
    exact ⟨lower.mp (valid _ (List.mem_cons_self ..)), upper.mp (valid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩
  · rintro ⟨low, high⟩ row member
    rcases List.mem_cons.mp member with same | later
    · cases same; exact lower.mpr low
    · have same := List.mem_singleton.mp later
      cases same; exact upper.mpr high

def program (rows : List (Inequality variables)) (denominator numerator : Fin variables → Int) :
    List (Inequality ((variables + 1) + 1)) :=
  (normalizedRows rows denominator).map Inequality.weaken ++
    (objectiveRows (objectiveCoefficients numerator) ++ unitRows (variables + 1))

theorem program_iff (rows : List (Inequality variables)) (denominator numerator : Fin variables → Int)
    (values : Fin ((variables + 1) + 1) → SignedRatio) :
    Satisfies (program rows denominator numerator) values ↔
      Satisfies (normalizedRows rows denominator) (fun i => values i.succ) ∧
        SignedRatio.Equiv (values 0) (dot (variables + 1) (objectiveCoefficients numerator) (fun i => values i.succ)) ∧
          SignedRatio.LE SignedRatio.zero (values 0) ∧ SignedRatio.LE (values 0) SignedRatio.one := by
  rw [program, satisfies_append_iff, satisfies_weaken_iff, satisfies_append_iff, objectiveRows_iff, unitRows_iff]

/-- The original fractional domain with its explicit probability-value
bounds. These bounds will be proved from actual events in the law adapter. -/
structure UnitValueAssignment (rows : List (Inequality variables)) (denominator numerator : Fin variables → Int) where
  source : SupportedAssignment rows denominator
  nonnegative : SignedRatio.LE SignedRatio.zero (source.conditionalValue numerator)
  bounded : SignedRatio.LE (source.conditionalValue numerator) SignedRatio.one

namespace UnitValueAssignment

variable {rows : List (Inequality variables)} {denominator numerator : Fin variables → Int}

def value (source : UnitValueAssignment rows denominator numerator) : SignedRatio := source.source.conditionalValue numerator

def encode (source : UnitValueAssignment rows denominator numerator) : Fin ((variables + 1) + 1) → SignedRatio :=
  prepend source.value source.source.normalize.values

theorem encode_valid (source : UnitValueAssignment rows denominator numerator) :
    Satisfies (program rows denominator numerator) source.encode := by
  apply (program_iff rows denominator numerator source.encode).mpr
  have response := SignedRatio.equiv_trans (objectiveCoefficients_dot source.source.normalize numerator)
    (source.source.normalize_response numerator)
  simpa only [encode, prepend_succ, prepend_zero] using
    (show Satisfies (normalizedRows rows denominator) source.source.normalize.values ∧
      SignedRatio.Equiv source.value (dot (variables + 1) (objectiveCoefficients numerator) source.source.normalize.values) ∧
        SignedRatio.LE SignedRatio.zero source.value ∧ SignedRatio.LE source.value SignedRatio.one from
      ⟨source.source.normalize.feasible, SignedRatio.equiv_symm response, source.nonnegative, source.bounded⟩)

end UnitValueAssignment

structure ProgramAssignment (rows : List (Inequality variables)) (denominator numerator : Fin variables → Int) where
  values : Fin ((variables + 1) + 1) → SignedRatio
  feasible : Satisfies (program rows denominator numerator) values

namespace ProgramAssignment

variable {rows : List (Inequality variables)} {denominator numerator : Fin variables → Int}

def normalized (point : ProgramAssignment rows denominator numerator) : NormalizedAssignment rows denominator :=
  ⟨fun i => point.values i.succ, ((program_iff rows denominator numerator point.values).mp point.feasible).1⟩

theorem response (point : ProgramAssignment rows denominator numerator) :
    SignedRatio.Equiv (point.normalized.toSupported.conditionalValue numerator) (point.values 0) :=
  SignedRatio.equiv_trans (point.normalized.toSupported_response numerator)
    (SignedRatio.equiv_trans (SignedRatio.equiv_symm (objectiveCoefficients_dot point.normalized numerator))
      (SignedRatio.equiv_symm ((program_iff rows denominator numerator point.values).mp point.feasible).2.1))

def decode (point : ProgramAssignment rows denominator numerator) : UnitValueAssignment rows denominator numerator where
  source := point.normalized.toSupported
  nonnegative := (SignedRatio.le_congr (SignedRatio.equiv_refl _) point.response).mpr
    ((program_iff rows denominator numerator point.values).mp point.feasible).2.2.1
  bounded := (SignedRatio.le_congr point.response (SignedRatio.equiv_refl _)).mpr
    ((program_iff rows denominator numerator point.values).mp point.feasible).2.2.2

end ProgramAssignment

/-- Both endpoints are actual original supported assignments; all values in
the original fractional domain lie between their actual conditional values. -/
structure FractionalRange (rows : List (Inequality variables)) (denominator numerator : Fin variables → Int) where
  lower : UnitValueAssignment rows denominator numerator
  upper : UnitValueAssignment rows denominator numerator
  bounds : ∀ original : UnitValueAssignment rows denominator numerator,
    SignedRatio.LE lower.value original.value ∧ SignedRatio.LE original.value upper.value
  pointBetween : ∀ value : SignedRatio, SignedRatio.LE lower.value value → SignedRatio.LE value upper.value →
    {original : UnitValueAssignment rows denominator numerator // SignedRatio.Equiv original.value value}

/-- Compute the exact attained range with the existing finite elimination
algorithm. A supplied supported reference only establishes nonemptiness; no
endpoints, fractional optimizer or complete family of models is assumed. -/
def fractionalRange {rows : List (Inequality variables)} {denominator numerator : Fin variables → Int}
    (reference : UnitValueAssignment rows denominator numerator) : FractionalRange rows denominator numerator := by
  let linear := sharpRange (variables + 1) (program rows denominator numerator) reference.encode reference.encode_valid
    SignedRatio.zero SignedRatio.one
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self ..)))
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  let lowPoint : ProgramAssignment rows denominator numerator := ⟨linear.lower, linear.lower_valid⟩
  let highPoint : ProgramAssignment rows denominator numerator := ⟨linear.upper, linear.upper_valid⟩
  refine ⟨lowPoint.decode, highPoint.decode, ?_, ?_⟩
  · intro original
    have bounded := linear.bounds original.encode original.encode_valid
    have actual : original.encode 0 = original.value := prepend_zero _ _
    rw [actual] at bounded
    exact ⟨(SignedRatio.le_congr lowPoint.response (SignedRatio.equiv_refl _)).mpr bounded.1,
      (SignedRatio.le_congr (SignedRatio.equiv_refl _) highPoint.response).mpr bounded.2⟩
  · intro value lower upper
    have between : SignedRatio.LE (linear.lower 0) value ∧ SignedRatio.LE value (linear.upper 0) :=
      ⟨(SignedRatio.le_congr lowPoint.response (SignedRatio.equiv_refl _)).mp lower,
        (SignedRatio.le_congr (SignedRatio.equiv_refl _) highPoint.response).mp upper⟩
    let lifted := linear.pointBetween value between
    let point : ProgramAssignment rows denominator numerator := ⟨lifted.val, lifted.property.1⟩
    exact ⟨point.decode, SignedRatio.equiv_trans point.response lifted.property.2⟩

end Thesis.Probability.Distros.RationalLinear.Conditional
