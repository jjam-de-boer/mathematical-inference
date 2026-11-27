import Thesis.Causality.QualitativeTieMasses
import Thesis.Probability.IntegerPolynomialSolvability
import Thesis.Probability.FourSquares

namespace Thesis.Causality.QualitativeTies
open Probability

/-!
# Compile literal ties into one integer polynomial

Each local recipe contributes a rational rate. Its lower and upper bounds
are equality constraints witnessed by two lists of four squares. Equality
constraints need only a single polynomial: summing their squared residuals
preserves exactly the rational zeros of the system. The variable allocation
retains each bound witness separately, including for legal endpoint rates.
-/

namespace TiesToPolynomial

variable {n : Nat}

/-- Eighteen slots per vertex, nine for each parent input. The first is the
rate itself and the other eight certify its bounds. Root rates use the
false-indexed row in the literal expressions. -/
def slot (node : Fin n) (input : Bool) (kind : Fin 9) : Fin (18 * n) :=
  ⟨18 * node.val + (if input then 9 else 0) + kind.val, by
    have vertexBound := node.isLt
    have slotBound := kind.isLt
    cases input <;> simp <;> omega⟩

theorem slot_injective : Function.Injective
    (fun row : Fin n × Bool × Fin 9 => slot row.1 row.2.1 row.2.2) := by
  rintro ⟨first, input, lower⟩ ⟨second, output, upper⟩ same
  have sameValue := congrArg Fin.val same
  have lowerBound := lower.isLt
  have upperBound := upper.isLt
  cases input <;> cases output <;> simp [slot] at sameValue
  · have nodes : first = second := Fin.ext (by omega)
    have kinds : lower = upper := Fin.ext (by omega)
    rw [nodes, kinds]
  · omega
  · omega
  · have nodes : first = second := Fin.ext (by omega)
    have kinds : lower = upper := Fin.ext (by omega)
    rw [nodes, kinds]

abbrev Polynomial (n : Nat) := IntegerPolynomial (Fin (18 * n))

def rate (node : Fin n) (input : Bool) : Polynomial n := .variable (slot node input 0)

private def row (node : Fin n) (input output : Bool) : Polynomial n :=
  if output then rate node input else IntegerPolynomial.sub (.constant 1) (rate node input)

private def indicator (actual wanted : Bool) : Polynomial n :=
  .constant (if actual = wanted then 1 else 0)

private def root (experiment : Experiment n) (node : Fin n) (bit : Bool) : Polynomial n :=
  match experiment.forced node with
  | some value => indicator value bit
  | none => row node false bit

/-- Translate exactly the formula proved from the urn game. Its products are
ordinary polynomial products; no joint event occurs in the input syntax. -/
def literal (graph : Matching n) (experiment : Experiment n) (event : Literal n) : Polynomial n :=
  match experiment.forced event.node with
  | some value => indicator value event.value
  | none => match graph.parent event.node with
    | none => row event.node false event.value
    | some source => .add
      (.mul (root experiment source false) (row event.node false event.value))
      (.mul (root experiment source true) (row event.node true event.value))

def tieEquation (graph : Matching n) (tie : Tie n) : Polynomial n :=
  (literal graph tie.experiment tie.left).sub (literal graph tie.experiment tie.right)

private def fourSquares (node : Fin n) (input : Bool) (upper : Bool) : Polynomial n :=
  IntegerPolynomial.sumSquares ((List.finRange 4).map fun index =>
    let kind : Fin 9 := ⟨index.val + (if upper then 5 else 1), by
      have bound := index.isLt
      cases upper <;> simp <;> omega⟩
    .variable (slot node input kind))

/-- Separate square witnesses for a rate and for its complement. -/
def rowEquations (node : Fin n) (input : Bool) : List (Polynomial n) :=
  [ (rate node input).sub (fourSquares node input false),
    (IntegerPolynomial.sub (.constant 1) (rate node input)).sub (fourSquares node input true) ]

/-- The computable translation to a single polynomial in finitely many
variables. It is defined even on empty graphs and empty comparison lists. -/
def compile (problem : Instance) : RationalZeroProblem where
  count := 18 * problem.count
  polynomial := IntegerPolynomial.sumSquares
    ((problem.ties.map (tieEquation problem.graph)) ++
      (List.finRange problem.count).flatMap fun node => rowEquations node false ++ rowEquations node true)

private theorem held_rate_toSignedRatio (rate : {value : QProb // QProb.LE value QProb.one}) :
    (opposite rate.val).toSignedRatio.Equiv (SignedRatio.one.sub rate.val.toSignedRatio) := by
  have bounded : rate.val.num ≤ rate.val.den := by
    simpa [QProb.LE, QProb.one] using rate.property
  simp only [opposite, QProb.toSignedRatio, SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add,
    SignedRatio.neg, SignedRatio.one, Nat.one_mul, Int.natCast_one, Int.one_mul, Int.mul_one]
  rw [Int.natCast_sub bounded]
  rfl

private theorem row_correct (valuation : Fin (18 * n) → SignedRatio) (rates : Rates n)
    (signedRates : ∀ node input, (valuation (slot node input 0)).Equiv (rates node input).val.toSignedRatio)
    (node : Fin n) (input output : Bool) :
    ((row node input output).evaluate valuation).Equiv (rates.rowMass node input output).toSignedRatio := by
  cases output with
  | true => exact signedRates node input
  | false =>
    exact SignedRatio.equiv_trans
      (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.neg_congr (signedRates node input)))
      (SignedRatio.equiv_symm (held_rate_toSignedRatio (rates node input)))

private theorem root_correct (valuation : Fin (18 * n) → SignedRatio) (rates : Rates n)
    (signedRates : ∀ node input, (valuation (slot node input 0)).Equiv (rates node input).val.toSignedRatio)
    (experiment : Experiment n) (node : Fin n) (bit : Bool) :
    ((root experiment node bit).evaluate valuation).Equiv (rootMass rates.rowMass experiment node bit).toSignedRatio := by
  cases forced : experiment.forced node with
  | none => simpa only [root, rootMass, forced] using row_correct valuation rates signedRates node false bit
  | some value => cases value <;> cases bit <;> simp only [root, rootMass, forced] <;> exact SignedRatio.equiv_refl _

/-- The formal polynomial and the operational mass formula evaluate to
exactly the same rational value when their recipe entries agree. -/
theorem literal_correct (valuation : Fin (18 * n) → SignedRatio) (rates : Rates n)
    (signedRates : ∀ node input, (valuation (slot node input 0)).Equiv (rates node input).val.toSignedRatio)
    (graph : Matching n) (experiment : Experiment n) (event : Literal n) :
    ((literal graph experiment event).evaluate valuation).Equiv
      (event.massFromRows graph rates.rowMass experiment).toSignedRatio := by
  cases forced : experiment.forced event.node with
  | some value =>
    obtain ⟨node, bit⟩ := event
    cases value <;> cases bit <;> simp only [literal, Literal.massFromRows, forced] <;> exact SignedRatio.equiv_refl _
  | none =>
    cases parent : graph.parent event.node with
    | none =>
      simpa only [literal, Literal.massFromRows, forced, parent] using
        row_correct valuation rates signedRates event.node false event.value
    | some source =>
      simp only [literal, Literal.massFromRows, forced, parent, IntegerPolynomial.evaluate]
      rw [QProb.toSignedRatio_add, QProb.toSignedRatio_mul, QProb.toSignedRatio_mul]
      exact SignedRatio.add_congr
        (SignedRatio.mul_congr (root_correct valuation rates signedRates _ _ _)
          (row_correct valuation rates signedRates _ _ _))
        (SignedRatio.mul_congr (root_correct valuation rates signedRates _ _ _)
          (row_correct valuation rates signedRates _ _ _))

theorem tieEquation_zero_iff (valuation : Fin (18 * n) → SignedRatio) (rates : Rates n)
    (signedRates : ∀ node input, (valuation (slot node input 0)).Equiv (rates node input).val.toSignedRatio)
    (graph : Matching n) (tie : Tie n) : ((tieEquation graph tie).evaluate valuation).Equiv .zero ↔
      QProb.Equiv (tie.left.massFromRows graph rates.rowMass tie.experiment)
        (tie.right.massFromRows graph rates.rowMass tie.experiment) := by
  unfold tieEquation IntegerPolynomial.sub
  simp only [IntegerPolynomial.evaluate]
  rw [← SignedRatio.sub, SignedRatio.sub_equiv_zero_iff, ← QProb.toSignedRatio_equiv_iff]
  have left := literal_correct valuation rates signedRates graph tie.experiment tie.left
  have right := literal_correct valuation rates signedRates graph tie.experiment tie.right
  exact ⟨fun same => SignedRatio.equiv_trans (SignedRatio.equiv_symm left) (SignedRatio.equiv_trans same right),
    fun same => SignedRatio.equiv_trans left (SignedRatio.equiv_trans same (SignedRatio.equiv_symm right))⟩

private theorem rows_bounded (node : Fin n) (input : Bool) (valuation : Fin (18 * n) → SignedRatio)
    (equations : ∀ expression ∈ rowEquations node input, (expression.evaluate valuation).Equiv .zero) :
    let value := valuation (slot node input 0)
    value.Nonnegative ∧ value.LE .one := by
  have lower := equations ((rate node input).sub (fourSquares node input false)) (by simp [rowEquations])
  have upper := equations ((IntegerPolynomial.sub (.constant 1) (rate node input)).sub
    (fourSquares node input true)) (by simp [rowEquations])
  change ((valuation (slot node input 0)).sub ((fourSquares node input false).evaluate valuation)).Equiv .zero at lower
  change ((SignedRatio.one.sub (valuation (slot node input 0))).sub
    ((fourSquares node input true).evaluate valuation)).Equiv .zero at upper
  exact ⟨(SignedRatio.nonnegative_congr ((SignedRatio.sub_equiv_zero_iff _ _).mp lower)).mpr
      (IntegerPolynomial.sumSquares_nonnegative _ _),
    (SignedRatio.nonnegative_congr ((SignedRatio.sub_equiv_zero_iff _ _).mp upper)).mpr
      (IntegerPolynomial.sumSquares_nonnegative _ _)⟩

private def boundedRate (value : SignedRatio) (sign : value.Nonnegative) (bound : value.LE .one) :
    {rate : QProb // QProb.LE rate QProb.one} :=
  let rate : QProb := ⟨value.num.toNat, value.den, value.den_pos⟩
  have same : rate.toSignedRatio.Equiv value := by
    change (value.num.toNat : Int) * (value.den : Int) = value.num * (value.den : Int)
    rw [Int.toNat_of_nonneg sign]
  ⟨rate, (SignedRatio.toSignedRatio_le_iff rate QProb.one).mp
    ((SignedRatio.le_congr same (SignedRatio.equiv_refl _)).mpr bound)⟩

private theorem boundedRate_correct (value : SignedRatio) (sign : value.Nonnegative) (bound : value.LE .one) :
    value.Equiv (boundedRate value sign bound).val.toSignedRatio := by
  change value.num * (value.den : Int) = (value.num.toNat : Int) * (value.den : Int)
  rw [Int.toNat_of_nonneg sign]

/-- A rational zero certifies an actual game, including when a recipe is
monochromatic. The square witnesses already give all bounds needed by the
Bernoulli-urn constructor. -/
theorem realizable_of_solvable (problem : Instance) (solved : (compile problem).Solvable) :
    problem.Realizable := by
  rcases solved with ⟨valuation, polynomialZero⟩
  have equations := (IntegerPolynomial.sumSquares_zero_iff _ valuation).mp polynomialZero
  have localBounds (node : Fin problem.count) (input : Bool) := rows_bounded node input valuation (by
    intro expression appears
    apply equations expression
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨node, List.mem_finRange node, ?_⟩
    cases input
    · exact List.mem_append_left _ appears
    · exact List.mem_append_right _ appears)
  let rates : Rates problem.count := fun node input =>
    boundedRate _ (localBounds node input).1 (localBounds node input).2
  apply problem.realizable_iff_rates.mpr
  refine ⟨rates, fun tie member => ?_⟩
  have compiledTie := equations (tieEquation problem.graph tie)
    (List.mem_append_left _ (List.mem_map.mpr ⟨tie, member, rfl⟩))
  exact (tieEquation_zero_iff valuation rates (fun node input => boundedRate_correct _ _ _)
    problem.graph tie).mp compiledTie

private def squareSum (values : Fin 4 → SignedRatio) : SignedRatio :=
  SignedRatio.listSum ((List.finRange 4).map fun i => (values i).mul (values i))

/-- A nonnegative rational n/d is a sum of four squares: represent the
natural product n·d and divide the four witnesses by d. -/
private theorem rational_squares (value : QProb) : ∃ roots : Fin 4 → SignedRatio,
    (squareSum roots).Equiv value.toSignedRatio := by
  obtain ⟨a, b, c, d, squares⟩ := FourSquareNorm.exists_natural_squares (value.num * value.den)
  let quotient (n : Nat) : SignedRatio := ⟨n, value.den, value.den_pos⟩
  let roots (i : Fin 4) : SignedRatio := [quotient a, quotient b, quotient c, quotient d][i.val]
  refine ⟨roots, ?_⟩
  let numerators : List Int := [((a*a : Nat) : Int), ((b*b : Nat) : Int), ((c*c : Nat) : Int), ((d*d : Nat) : Int)]
  have aligned : (List.finRange 4).map (fun i => (roots i).mul (roots i)) =
      numerators.map (fun num => ⟨num, value.den*value.den, Nat.mul_pos value.den_pos value.den_pos⟩) := by
    dsimp [numerators, roots, quotient, SignedRatio.mul]
    rfl
  unfold squareSum
  rw [aligned]
  apply SignedRatio.equiv_trans (SignedRatio.listSum_mk_same_den _ _ numerators)
  have total := congrArg (fun n : Nat => (n : Int)) squares
  change numerators.sum * (value.den : Int) = (value.num : Int) * (value.den * value.den : Nat)
  dsimp [numerators]
  simp only [Int.add_zero, Int.natCast_add, Int.natCast_mul] at total ⊢
  rw [← Int.add_assoc, ← Int.add_assoc, total, Int.mul_assoc]

private theorem finite_witnesses {W : Type} {n : Nat} {p : Fin n → W → Prop}
    (pointwise : ∀ i, ∃ witness, p i witness) : ∃ witnesses : Fin n → W, ∀ i, p i (witnesses i) := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨first, correctFirst⟩ := pointwise 0
    obtain ⟨rest, correctRest⟩ := ih (p := fun i => p i.succ) (fun i => pointwise i.succ)
    refine ⟨Fin.cases first rest, ?_⟩
    intro i
    refine Fin.cases correctFirst correctRest i

private theorem bool_witnesses {W : Type} {p : Bool → W → Prop}
    (pointwise : ∀ i, ∃ witness, p i witness) : ∃ witnesses : Bool → W, ∀ i, p i (witnesses i) := by
  obtain ⟨first, correctFirst⟩ := pointwise false
  obtain ⟨last, correctLast⟩ := pointwise true
  refine ⟨fun bit => if bit then last else first, ?_⟩
  intro bit
  cases bit
  · exact correctFirst
  · exact correctLast

/-- Recover the three indices packed in a polynomial coordinate. Every
actual slot decodes back to its original row and witness position. -/
private def slotData (index : Fin (18 * n)) : Fin n × Bool × Fin 9 :=
  (⟨index.val / 18, by have h := index.isLt; omega⟩,
    decide (9 ≤ index.val % 18), ⟨(index.val % 18) % 9, Nat.mod_lt _ (by decide)⟩)

private theorem slotData_slot (node : Fin n) (input : Bool) (kind : Fin 9) :
    slotData (slot node input kind) = (node, input, kind) := by
  have kindBound := kind.isLt
  have nodeEq : (slotData (slot node input kind)).1 = node := by
    apply Fin.ext
    cases input <;> dsimp [slotData, slot] <;> omega
  have inputEq : (slotData (slot node input kind)).2.1 = input := by
    cases input
    · change decide (9 ≤ (18 * node.val + 0 + kind.val) % 18) = false
      exact decide_eq_false (by omega)
    · change decide (9 ≤ (18 * node.val + 9 + kind.val) % 18) = true
      exact decide_eq_true (by omega)
  have kindEq : (slotData (slot node input kind)).2.2 = kind := by
    apply Fin.ext
    cases input <;> dsimp [slotData, slot] <;> omega
  exact Prod.ext nodeEq (Prod.ext inputEq kindEq)

private def valuationOf (rates : Rates n) (roots : Fin n → Bool → Bool → Fin 4 → SignedRatio)
    (index : Fin (18 * n)) : SignedRatio :=
  let (node, input, kind) := slotData index
  if kind.val = 0 then (rates node input).val.toSignedRatio
  else if lower : kind.val < 5 then roots node input false ⟨kind.val - 1, by omega⟩
  else roots node input true ⟨kind.val - 5, by have h := kind.isLt; omega⟩

private theorem valuationOf_rate (rates : Rates n) (roots : Fin n → Bool → Bool → Fin 4 → SignedRatio)
    (node : Fin n) (input : Bool) :
    valuationOf rates roots (slot node input 0) = (rates node input).val.toSignedRatio := by
  rw [valuationOf, slotData_slot]
  rfl

private theorem valuationOf_witness (rates : Rates n) (roots : Fin n → Bool → Bool → Fin 4 → SignedRatio)
    (node : Fin n) (input upper : Bool) (index : Fin 4) :
    valuationOf rates roots (slot node input ⟨index.val + (if upper then 5 else 1), by
        have h := index.isLt
        cases upper <;> dsimp <;> omega⟩) = roots node input upper index := by
  rw [valuationOf, slotData_slot]
  have indexBound := index.isLt
  cases upper <;> dsimp
  · rw [dif_pos (show index.val + 1 < 5 by omega)]
  · rw [dif_neg (show ¬index.val + 5 < 5 by omega)]
    exact congrArg (roots node input true) (Fin.ext (by dsimp; omega))

private theorem evaluate_fourSquares (rates : Rates n) (roots : Fin n → Bool → Bool → Fin 4 → SignedRatio)
    (node : Fin n) (input upper : Bool) :
    (fourSquares node input upper).evaluate (valuationOf rates roots) = squareSum (roots node input upper) := by
  unfold fourSquares IntegerPolynomial.sumSquares squareSum
  rw [IntegerPolynomial.evaluate_sum]
  simp only [List.map_map, Function.comp_def, IntegerPolynomial.square, IntegerPolynomial.evaluate, valuationOf_witness]

/-- The bounds for all the rows extend any realizing game to a zero of the
single compiled polynomial. Witnesses are assembled over explicit finite
index types, so no unrestricted choice is needed. -/
theorem solvable_of_realizable (problem : Instance) (realized : problem.Realizable) : (compile problem).Solvable := by
  obtain ⟨rates, holds⟩ := problem.realizable_iff_rates.mp realized
  have rootWitnesses (node : Fin problem.count) (input upper : Bool) :
      ∃ witnesses : Fin 4 → SignedRatio, (squareSum witnesses).Equiv
        ((if upper then opposite (rates node input).val else (rates node input).val).toSignedRatio) :=
    rational_squares _
  obtain ⟨roots, rootsCorrect⟩ := finite_witnesses (fun node =>
    bool_witnesses (fun input => bool_witnesses (rootWitnesses node input)))
  let valuation := valuationOf rates roots
  refine ⟨valuation, (IntegerPolynomial.sumSquares_zero_iff _ _).mpr ?_⟩
  intro expression appearing
  rcases List.mem_append.mp appearing with fromTie | fromBound
  · obtain ⟨tie, member, rfl⟩ := List.mem_map.mp fromTie
    exact (tieEquation_zero_iff valuation rates
      (fun node input => by unfold valuation; rw [valuationOf_rate]; exact SignedRatio.equiv_refl _)
      problem.graph tie).mpr (holds tie member)
  · obtain ⟨node, _, fromRow⟩ := List.mem_flatMap.mp fromBound
    have rowCorrect (input : Bool) (term : Polynomial problem.count) (member : term ∈ rowEquations node input) :
        (term.evaluate valuation).Equiv .zero := by
      rcases List.mem_cons.mp member with lower | rest
      · subst term
        change ((valuation (slot node input 0)).sub ((fourSquares node input false).evaluate valuation)).Equiv .zero
        unfold valuation
        rw [SignedRatio.sub_equiv_zero_iff, valuationOf_rate, evaluate_fourSquares]
        exact SignedRatio.equiv_symm (rootsCorrect node input false)
      · rcases List.mem_cons.mp rest with upper | impossible
        · subst term
          change ((SignedRatio.one.sub (valuation (slot node input 0))).sub
            ((fourSquares node input true).evaluate valuation)).Equiv .zero
          unfold valuation
          rw [SignedRatio.sub_equiv_zero_iff, valuationOf_rate, evaluate_fourSquares]
          exact SignedRatio.equiv_symm (SignedRatio.equiv_trans (rootsCorrect node input true)
            (held_rate_toSignedRatio (rates node input)))
        · cases impossible
    rcases List.mem_append.mp fromRow with falseRow | trueRow
    · exact rowCorrect false _ falseRow
    · exact rowCorrect true _ trueRow

/-- Exact rational realization is preserved and reflected by the
computable reduction from unary ties to one integer polynomial. -/
theorem compile_correct (problem : Instance) : (compile problem).Solvable ↔ problem.Realizable :=
  ⟨realizable_of_solvable problem, solvable_of_realizable problem⟩

end TiesToPolynomial
end Thesis.Causality.QualitativeTies
