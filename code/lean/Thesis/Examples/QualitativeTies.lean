import Thesis.Causality.QualitativeTieMasses
import Thesis.Probability.RationalSquareObstruction
import Thesis.Probability.SignedRatioOrder

namespace Thesis.Examples.QualitativeTies
open Probability Causality Causality.QualitativeTies

/-!
# Three bits, individually consistent experiments, and an irrational bias

The graph has the single edge X → Y. R is a reference bit whose rate is
unaffected by either setting of X. Tying X to R in observation gives a
common rate p. Setting X=false lets the impossible literal X=true pin
Y's first recipe row at zero. Setting X=true then pins the next row at p,
by the comparison with R. The shared observational recipe therefore has
success probability p². Tying its two outcomes makes it fair and forces
p² = 1/2. Every individual experiment can obey its judgments with rational
weights. The obstruction arises from sharing the same recipes.
-/

private abbrev x : Fin 3 := 0
private abbrev y : Fin 3 := 1
private abbrev reference : Fin 3 := 2

def graph : Matching 3 where
  parent node := if node = y then some x else none
  parentEarlier := by decide +kernel
  parentRoot := by decide +kernel
  uniqueChild := by decide +kernel

def rootsTie : Tie 3 := ⟨.observe, ⟨x, true⟩, ⟨reference, true⟩⟩
def fairTie : Tie 3 := ⟨.observe, ⟨y, true⟩, ⟨y, false⟩⟩
def zeroTie : Tie 3 := ⟨.set x false, ⟨y, true⟩, ⟨x, true⟩⟩
def copyTie : Tie 3 := ⟨.set x true, ⟨y, true⟩, ⟨reference, true⟩⟩

def problem : Instance := ⟨3, graph, [rootsTie, fairTie, zeroTie, copyTie]⟩

private theorem tie_cases (tie : Tie 3) (member : tie ∈ problem.ties) :
    tie = rootsTie ∨ tie = fairTie ∨ tie = zeroTie ∨ tie = copyTie := by
  change List.Mem tie [rootsTie, fairTie, zeroTie, copyTie] at member
  rcases List.mem_cons.mp member with first | rest
  · exact .inl first
  · rcases List.mem_cons.mp rest with second | rest
    · exact .inr (.inl second)
    · rcases List.mem_cons.mp rest with third | rest
      · exact .inr (.inr (.inl third))
      · rcases List.mem_cons.mp rest with fourth | impossible
        · exact .inr (.inr (.inr fourth))
        · cases impossible

private def half : QProb := ⟨1, 2, by decide⟩
private abbrev Game := CausalUrnGame graph.signature graph.projection

private def individualRates (experiment : Experiment 3) : Rates 3 := fun node _ =>
  if experiment = .set x false ∧ node = y then ⟨QProb.zero, QProb.zero_le _⟩
  else ⟨half, by change 1 ≤ 2; decide⟩

/-- Each regime on its own has a rational urn satisfying its comparisons.
These witnesses vary the recipes with the experiment. The laws themselves
come from finite draws with the declared setting performed literally. -/
theorem experiments_separately_realizable (experiment : Experiment 3) :
    ∃ urn : UrnProb graph.signature.Assignment,
      (∀ tie ∈ problem.ties, tie.experiment = experiment →
        QProb.Equiv (urn.probVal (tie.left.event graph)) (urn.probVal (tie.right.event graph))) ∧
      (∀ node bit, experiment.forced node = some bit →
        QProb.Equiv (urn.probVal ((Literal.mk node bit).event graph)) QProb.one) := by
  let game := graph.gameOfRates (individualRates experiment)
  refine ⟨game.recordUrn (experiment.intervention graph), ?_, ?_⟩
  · intro tie member regime
    rcases tie_cases tie member with rfl | rfl | rfl | rfl <;> subst experiment <;> decide +kernel
  · intro node bit forced
    have mass := (Literal.mk node bit).mass_gameOfRates graph (individualRates experiment) experiment
    rw [Literal.massFromRows, forced] at mass
    cases bit <;> exact mass

private theorem equality_with_complement_forces_half (p : QProb) (bounded : QProb.LE p QProb.one)
    (same : QProb.Equiv p (opposite p)) : QProb.Equiv p half := by
  have countBound : p.num ≤ p.den := by simpa [QProb.LE, QProb.one] using bounded
  have counts : p.num = p.den - p.num := Nat.eq_of_mul_eq_mul_right p.den_pos same
  change p.num * 2 = _
  simp only [half, Nat.one_mul]
  omega

private theorem selectFalse (q₀ q₁ : QProb) :
    QProb.Equiv (QProb.add (QProb.mul QProb.one q₀) (QProb.mul QProb.zero q₁)) q₀ := by
  simp only [QProb.Equiv, QProb.one, QProb.zero, QProb.mul, QProb.add,
    Nat.one_mul, Nat.zero_mul, Nat.add_zero]
  ac_rfl

private theorem selectTrue (q₀ q₁ : QProb) :
    QProb.Equiv (QProb.add (QProb.mul QProb.zero q₀) (QProb.mul QProb.one q₁)) q₁ := by
  simp only [QProb.Equiv, QProb.one, QProb.zero, QProb.mul, QProb.add,
    Nat.one_mul, Nat.zero_mul, Nat.zero_add]
  ac_rfl

private theorem mixtureZero (p q : QProb) :
    QProb.Equiv (QProb.add (QProb.mul (opposite p) QProb.zero) (QProb.mul p q)) (QProb.mul p q) := by
  simp only [QProb.Equiv, QProb.zero, QProb.mul, QProb.add,
    Nat.mul_one, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  ac_rfl

private theorem tie_rows (game : Game) (tie : Tie 3) (holds : tie.holds game) :
    QProb.Equiv (tie.left.massFromRows graph (ratesOfGame game).rowMass tie.experiment)
      (tie.right.massFromRows graph (ratesOfGame game).rowMass tie.experiment) :=
  QProb.equiv_trans (QProb.equiv_symm (tie.left.mass_ratesOfGame game tie.experiment))
    (QProb.equiv_trans holds (tie.right.mass_ratesOfGame game tie.experiment))

/-- Sharing the recipe between the two settings and observation forces the
squared bias. The observed fair literal still has its ordinary urn meaning. -/
theorem common_game_forces_square (game : Game) (obeys : ∀ tie ∈ problem.ties, tie.holds game) :
    QProb.Equiv (QProb.mul (recipeMass game x false true) (recipeMass game x false true)) half := by
  let rates := ratesOfGame game
  let p := (rates x false).val
  let r := (rates reference false).val
  let q₀ := (rates y false).val
  let q₁ := (rates y true).val
  have roots := tie_rows game rootsTie (obeys rootsTie (by decide +kernel))
  change QProb.Equiv p r at roots
  have zeroed := tie_rows game zeroTie (obeys zeroTie (by decide +kernel))
  change QProb.Equiv (QProb.add (QProb.mul QProb.one q₀) (QProb.mul QProb.zero q₁)) QProb.zero at zeroed
  have zeroRow := QProb.equiv_trans (QProb.equiv_symm (selectFalse q₀ q₁)) zeroed
  have copied := tie_rows game copyTie (obeys copyTie (by decide +kernel))
  change QProb.Equiv (QProb.add (QProb.mul QProb.zero q₀) (QProb.mul QProb.one q₁)) r at copied
  have copiedRow := QProb.equiv_trans (QProb.equiv_symm (selectTrue q₀ q₁))
    (QProb.equiv_trans copied (QProb.equiv_symm roots))
  let observed := game.recordUrn (Experiment.observe.intervention graph)
  let success := (Literal.mk y true).event graph
  have fair := obeys fairTie (by decide +kernel)
  have falseEvent : (Literal.mk y false).event graph = complement success := by
    funext assignment
    change decide (assignment y = false) = !(decide (assignment y = true))
    cases assignment y <;> rfl
  change QProb.Equiv (observed.probVal success) (observed.probVal ((Literal.mk y false).event graph)) at fair
  rw [falseEvent, probVal_complement_eq] at fair
  have observedHalf := equality_with_complement_forces_half _ (observed.probVal_le_one success) fair
  have mixture := (Literal.mk y true).mass_ratesOfGame game Experiment.observe
  change QProb.Equiv (observed.probVal success)
    (QProb.add (QProb.mul (opposite p) q₀) (QProb.mul p q₁)) at mixture
  have product := QProb.equiv_trans mixture (QProb.equiv_trans
    (QProb.add_congr (QProb.mul_congr (QProb.equiv_refl _) zeroRow)
      (QProb.mul_congr (QProb.equiv_refl _) copiedRow)) (mixtureZero p p))
  exact QProb.equiv_trans (QProb.equiv_symm product) observedHalf

/-- Four unary ties refute every finite rational game on the supplied graph. -/
theorem no_common_rational_game : ¬ problem.Realizable := by
  rintro ⟨game, obeys⟩
  exact QProb.square_ne_half _ (common_game_forces_square game obeys)

/-!
## Exact algebraic realization

For this example the quadratic extension suffices. Write a value as
`a + b√2` using two signed rational coefficients. Multiplication replaces
`(√2)²` by `2`, and testing the sign only requires squaring magnitudes
when the signs of the two terms disagree. Thus the witness verifies the
weights and all four comparisons by exact arithmetic.
-/

/-- A coefficient pair in the ordered quadratic extension Q(√2), using
its positive generator. Equality below compares the two coefficients. -/
structure Quadratic where
  rational : SignedRatio
  radical : SignedRatio

namespace Quadratic

def zero : Quadratic := ⟨.zero, .zero⟩
def one : Quadratic := ⟨.one, .zero⟩
private def two : SignedRatio := ⟨2, 1, by decide⟩

def add (a b : Quadratic) : Quadratic :=
  ⟨a.rational.add b.rational, a.radical.add b.radical⟩

def mul (a b : Quadratic) : Quadratic :=
  ⟨(a.rational.mul b.rational).add (two.mul (a.radical.mul b.radical)),
    (a.rational.mul b.radical).add (a.radical.mul b.rational)⟩

def complement (a : Quadratic) : Quadratic :=
  ⟨SignedRatio.one.sub a.rational, a.radical.neg⟩

def Equiv (a b : Quadratic) : Prop :=
  a.rational.Equiv b.rational ∧ a.radical.Equiv b.radical

instance (a b : Quadratic) : Decidable (a.Equiv b) := by
  unfold Equiv
  infer_instance

/-- Sign in the positive embedding of Q(√2). In the two mixed-sign cases
compare the squares of the opposing terms, which have equal sign after
moving one to the other side. -/
def Nonnegative (a : Quadratic) : Prop :=
  let rationalSquared := a.rational.mul a.rational
  let radicalSquared := two.mul (a.radical.mul a.radical)
  if a.rational.Nonnegative then
    if a.radical.Nonnegative then True else radicalSquared.LE rationalSquared
  else a.radical.Nonnegative ∧ rationalSquared.LE radicalSquared

instance (a : Quadratic) : Decidable a.Nonnegative := by
  unfold Nonnegative
  infer_instance

/-- A unit-interval rate checks the rate itself and its complement. -/
def IsRate (a : Quadratic) : Prop := a.Nonnegative ∧ a.complement.Nonnegative

instance (a : Quadratic) : Decidable a.IsRate := by
  unfold IsRate
  infer_instance

end Quadratic

/-- The algebraic local rates indexed by the same graph and parent bits. -/
abbrev AlgebraicRates := Fin 3 → Bool → Quadratic

private def algebraicBitMass (chosen wanted : Bool) : Quadratic :=
  if chosen = wanted then .one else .zero

private def algebraicRow (rates : AlgebraicRates) (node : Fin 3) (input output : Bool) : Quadratic :=
  if output then rates node input else (rates node input).complement

private def algebraicRoot (rates : AlgebraicRates) (experiment : Experiment 3)
    (node : Fin 3) (bit : Bool) : Quadratic :=
  match experiment.forced node with
  | some chosen => algebraicBitMass chosen bit
  | none => algebraicRow rates node false bit

/-- Evaluate the same literal-mass formula as the rational game proof,
using exact quadratic arithmetic. -/
def algebraicMass (rates : AlgebraicRates) (experiment : Experiment 3) (literal : Literal 3) : Quadratic :=
  match experiment.forced literal.node with
  | some chosen => algebraicBitMass chosen literal.value
  | none => match graph.parent literal.node with
    | none => algebraicRow rates literal.node false literal.value
    | some source =>
      ((algebraicRoot rates experiment source false).mul (algebraicRow rates literal.node false literal.value)).add
        ((algebraicRoot rates experiment source true).mul (algebraicRow rates literal.node true literal.value))

private def inverseSqrtTwo : Quadratic := ⟨.zero, ⟨1, 2, by decide⟩⟩

/-- X and R use the bias √2/2. Y has recipe rows zero and √2/2.
This supplies bounded local weights and verifies every one of the same
four input judgments by exact arithmetic in the quadratic extension. -/
theorem exact_algebraic_realization :
    ∃ rates : AlgebraicRates, (∀ node input, (rates node input).IsRate) ∧
      ∀ tie ∈ problem.ties,
        (algebraicMass rates tie.experiment tie.left).Equiv (algebraicMass rates tie.experiment tie.right) := by
  let rates : AlgebraicRates := fun node input =>
    if node = y ∧ input = false then .zero else inverseSqrtTwo
  refine ⟨rates, ?_, ?_⟩
  · decide +kernel
  · intro tie member
    rcases tie_cases tie member with rfl | rfl | rfl | rfl <;> decide +kernel

end Thesis.Examples.QualitativeTies
