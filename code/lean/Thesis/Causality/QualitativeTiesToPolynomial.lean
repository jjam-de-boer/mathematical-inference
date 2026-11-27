import Thesis.Causality.QualitativeTieMasses
import Thesis.Probability.IntegerPolynomialSolvability

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

end TiesToPolynomial
end Thesis.Causality.QualitativeTies
