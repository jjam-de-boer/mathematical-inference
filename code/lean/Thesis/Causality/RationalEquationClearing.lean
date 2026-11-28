import Thesis.Causality.BoundedMonomialEquations
import Thesis.Probability.ElementaryRationalEquations
import Thesis.Probability.PellHalfRates
import Thesis.Probability.RationalPolynomialExpression

namespace Thesis.Causality.QualitativeTies
open Probability

/-!
# Clear a common positive denominator using comparisons

Represent a rational variable x by (aₓ−bₓ)/d. Its two numerators are
nonnegative rates. Each elementary equation then equates sums of at most
three nonnegative products. For example x·y=z becomes

    aₓ·aᵧ + bₓ·bᵧ + d·b_z = aₓ·bᵧ + bₓ·aᵧ + d·a_z.

The denominator is a rate too. The constraint d² + 2s² = 1 excludes zero
with exact rational rates, and the explicit Pell family supplies rates
small enough for any particular finite collection of rational values.
-/

namespace RationalEquationClearing

/-- Program-wide positions for zero, one, the denominator and its Pell
companion, followed by two rates for each source variable. -/
private def width (n : Nat) : Nat := 4 + 2*n
private def zero (n : Nat) : Fin (width n) := ⟨0, by unfold width; omega⟩
private def one (n : Nat) : Fin (width n) := ⟨1, by unfold width; omega⟩
private def denominator (n : Nat) : Fin (width n) := ⟨2, by unfold width; omega⟩
private def companion (n : Nat) : Fin (width n) := ⟨3, by unfold width; omega⟩
private def numerator (i : Fin n) (minus : Bool) : Fin (width n) :=
  ⟨4 + 2*i.val + (if minus then 1 else 0), by have h := i.isLt; unfold width; cases minus <;> dsimp <;> omega⟩

private def side (first second third : Monomial n) : MonomialSide n :=
  fun i => if i.val = 0 then first else if i.val = 1 then second else third

private inductive Shape where
  | equal | zero | one | negative | add | multiply

/-- Local notation for the nine schematic weights. Positions 0,1 are the
fixed constants, position 2 is d, and positions 3–8 are the three signed
pairs. Unused pairs can be filled with zero. -/
private def template (shape : Shape) : MonomialEquation 9 :=
  let term (i : Fin 9) : Monomial 9 := (i,1)
  let z := term 0
  match shape with
  | .equal => ⟨side (term 3) (term 6) z, side (term 4) (term 5) z⟩
  | .zero => ⟨side (term 3) z z, side (term 4) z z⟩
  | .one => ⟨side (term 3) z z, side (term 4) (term 2) z⟩
  | .negative => ⟨side (term 3) (term 7) z, side (term 4) (term 8) z⟩
  | .add => ⟨side (term 3) (term 5) (term 8), side (term 4) (term 6) (term 7)⟩
  | .multiply => ⟨side (3,5) (4,6) (2,8), side (3,6) (4,5) (2,7)⟩

private def rename (map : Fin n → Fin m) (equation : MonomialEquation n) : MonomialEquation m :=
  let apply (s : MonomialSide n) : MonomialSide m := fun i => (map (s i).1, map (s i).2)
  ⟨apply equation.left, apply equation.right⟩

private def mapping (first middle last : Fin n) (index : Fin 9) : Fin (width n) :=
  match index.val with
  | 0 => zero n
  | 1 => one n
  | 2 => denominator n
  | 3 => numerator first false
  | 4 => numerator first true
  | 5 => numerator middle false
  | 6 => numerator middle true
  | 7 => numerator last false
  | _ => numerator last true

private def shapeOf : RationalEquation (Fin n) → Shape × (Fin n × Fin n × Fin n)
  | .equal a b => (.equal, a, b, a)
  | .zero a => (.zero, a, a, a)
  | .one a => (.one, a, a, a)
  | .negative a r => (.negative, a, a, r)
  | .add a b r => (.add, a, b, r)
  | .multiply a b r => (.multiply, a, b, r)

private def equationFor (equation : RationalEquation (Fin n)) : MonomialEquation (width n) :=
  let (shape,a,b,r) := shapeOf equation
  rename (mapping a b r) (template shape)

private def pellEquation (n : Nat) : MonomialEquation (width n) :=
  let d := denominator n
  let s := companion n
  let o := one n
  let z := zero n
  ⟨side (d,d) (s,s) (s,s), side (o,o) (z,z) (z,z)⟩

/-- Integer equations become a balanced monomial system plus the shared
rational denominator constraint. The compiled system uses only bounded
rate variables. -/
def compile (system : RationalEquationSystem) : MonomialSystem where
  count := width system.count
  requirements := [.zero (zero system.count), .one (one system.count)]
  equations := pellEquation system.count :: system.equations.map equationFor

private abbrev Expr := RationalPolynomial.Expression 9

private def coefficient (i : Fin 9) : Expr :=
  if i.val = 0 then .constant .zero else if i.val = 1 then .constant .one else .coordinate i

private def polynomialSide (terms : MonomialSide 9) : Expr :=
  let term := fun i => (coefficient (terms i).1).mul (coefficient (terms i).2)
  ((term 0).add (term 1)).add (term 2)

private def clearedResidual (shape : Shape) : Expr :=
  let x := (coefficient 3).sub (coefficient 4)
  let y := (coefficient 5).sub (coefficient 6)
  let r := (coefficient 7).sub (coefficient 8)
  let d := coefficient 2
  match shape with
  | .equal => x.sub y
  | .zero => x
  | .one => x.sub d
  | .negative => r.sub (.sub (.constant .zero) x)
  | .add => (x.add y).sub r
  | .multiply => (x.mul y).sub (d.mul r)

/-- The finite algebraic certificates are checked by the existing sparse
polynomial normalizer over explicit rational presentations. -/
private theorem template_identity (shape : Shape) (values : Fin 9 → SignedRatio) :
    (((polynomialSide (template shape).left).sub (polynomialSide (template shape).right)).evaluate values).Equiv
      ((clearedResidual shape).evaluate values) := by
  apply RationalPolynomial.Expression.equalityCheck_sound
  cases shape <;> decide +kernel

private theorem interpreted_coefficient (rates : Fin 9 → QProb)
    (fixedZero : (rates 0).Equiv .zero) (fixedOne : (rates 1).Equiv .one) (index : Fin 9) :
    ((coefficient index).evaluate (fun i => (rates i).toSignedRatio)).Equiv (rates index).toSignedRatio := by
  unfold coefficient
  by_cases atZero : index.val = 0
  · rw [if_pos atZero]
    have eqIndex : index = 0 := Fin.ext atZero
    subst index
    exact SignedRatio.equiv_symm (QProb.toSignedRatio_congr fixedZero)
  · by_cases atOne : index.val = 1
    · rw [if_neg atZero, if_pos atOne]
      have eqIndex : index = 1 := Fin.ext atOne
      subst index
      exact SignedRatio.equiv_symm (QProb.toSignedRatio_congr fixedOne)
    · rw [if_neg atZero, if_neg atOne]
      exact SignedRatio.equiv_refl _

private theorem interpreted_side (rates : Fin 9 → QProb)
    (fixedZero : (rates 0).Equiv .zero) (fixedOne : (rates 1).Equiv .one) (terms : MonomialSide 9) :
    ((polynomialSide terms).evaluate (fun i => (rates i).toSignedRatio)).Equiv (terms.evaluate rates).toSignedRatio := by
  simp only [polynomialSide, MonomialSide.evaluate, RationalPolynomial.Expression.evaluate,
    QProb.toSignedRatio_add, QProb.toSignedRatio_mul]
  have coefficientCorrect := interpreted_coefficient rates fixedZero fixedOne
  exact SignedRatio.add_congr (SignedRatio.add_congr (SignedRatio.mul_congr (coefficientCorrect _) (coefficientCorrect _))
    (SignedRatio.mul_congr (coefficientCorrect _) (coefficientCorrect _)))
    (SignedRatio.mul_congr (coefficientCorrect _) (coefficientCorrect _))

private theorem sub_congr {a a' b b' : SignedRatio} (first : a.Equiv a') (second : b.Equiv b') :
    (a.sub b).Equiv (a'.sub b') := SignedRatio.add_congr first (SignedRatio.neg_congr second)

private theorem template_residual (shape : Shape) (rates : Fin 9 → QProb)
    (fixedZero : (rates 0).Equiv .zero) (fixedOne : (rates 1).Equiv .one) :
    ((template shape).left.evaluate rates).Equiv ((template shape).right.evaluate rates) ↔
      ((clearedResidual shape).evaluate (fun i => (rates i).toSignedRatio)).Equiv .zero := by
  let lhs := (template shape).left.evaluate rates
  let rhs := (template shape).right.evaluate rates
  have interpreted := sub_congr (interpreted_side rates fixedZero fixedOne (template shape).left)
    (interpreted_side rates fixedZero fixedOne (template shape).right)
  have residual := SignedRatio.equiv_trans (SignedRatio.equiv_symm interpreted)
    (template_identity shape (fun i => (rates i).toSignedRatio))
  constructor
  · intro equality
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm residual)
      ((SignedRatio.sub_equiv_zero_iff lhs.toSignedRatio rhs.toSignedRatio).mpr (QProb.toSignedRatio_congr equality))
  · intro vanished
    exact (QProb.toSignedRatio_equiv_iff _ _).mp
      ((SignedRatio.sub_equiv_zero_iff lhs.toSignedRatio rhs.toSignedRatio).mp (SignedRatio.equiv_trans residual vanished))

/-- Decode a signed difference by using the positive natural numerator of
the denominator rate. Multiplication by the denominator recovers the
difference exactly. -/
private def divideDifference (difference : SignedRatio) (d : QProb) (positive : 0 < d.num) : SignedRatio :=
  ⟨difference.num * (d.den : Int), difference.den * d.num, Nat.mul_pos difference.den_pos positive⟩

private theorem divide_mul (difference : SignedRatio) (d : QProb) (positive : 0 < d.num) :
    ((divideDifference difference d positive).mul d.toSignedRatio).Equiv difference := by
  simp only [divideDifference, QProb.toSignedRatio, SignedRatio.mul, SignedRatio.Equiv, Int.natCast_mul]
  ac_rfl

private theorem mul_cancel_right {left right factor : SignedRatio} (nonzero : factor.num ≠ 0)
    (same : (left.mul factor).Equiv (right.mul factor)) : left.Equiv right := by
  have posDen := factor.den_pos
  have notZeroDen : (factor.den : Int) ≠ 0 := by omega
  apply Int.eq_of_mul_eq_mul_right (a := factor.num * (factor.den : Int))
    (fun vanished => (Int.mul_eq_zero.mp vanished).elim nonzero notZeroDen)
  simp only [SignedRatio.Equiv, SignedRatio.mul, Int.natCast_mul] at same ⊢
  calc
    _ = (left.num * factor.num) * ((right.den : Int) * (factor.den : Int)) := by ac_rfl
    _ = (right.num * factor.num) * ((left.den : Int) * (factor.den : Int)) := same
    _ = _ := by ac_rfl

private theorem scaled_iff {a b factor first second : SignedRatio} (nonzero : factor.num ≠ 0)
    (left : (a.mul factor).Equiv first) (right : (b.mul factor).Equiv second) :
    first.Equiv second ↔ a.Equiv b :=
  ⟨fun equality => mul_cancel_right nonzero (SignedRatio.equiv_trans left
      (SignedRatio.equiv_trans equality (SignedRatio.equiv_symm right))),
    fun equality => SignedRatio.equiv_trans (SignedRatio.equiv_symm left)
      (SignedRatio.equiv_trans (SignedRatio.mul_congr equality (SignedRatio.equiv_refl _)) right)⟩

private def difference (rates : Fin 9 → QProb) (i : Fin 3) : SignedRatio :=
  let first : Fin 9 := ⟨3 + 2*i.val, by have h := i.isLt; omega⟩
  let second : Fin 9 := ⟨4 + 2*i.val, by have h := i.isLt; omega⟩
  (rates first).toSignedRatio.sub (rates second).toSignedRatio

private def localEquation : Shape → RationalEquation (Fin 3)
  | .equal => .equal 0 1
  | .zero => .zero 0
  | .one => .one 0
  | .negative => .negative 0 2
  | .add => .add 0 1 2
  | .multiply => .multiply 0 1 2

private theorem residual_solution (shape : Shape) (rates : Fin 9 → QProb) (positive : 0 < (rates 2).num) :
    ((clearedResidual shape).evaluate (fun i => (rates i).toSignedRatio)).Equiv .zero ↔
      (localEquation shape).holds (fun i => divideDifference (difference rates i) (rates 2) positive) := by
  let d := (rates 2).toSignedRatio
  let x := fun i => divideDifference (difference rates i) (rates 2) positive
  have nonzero : d.num ≠ 0 := by change ((rates 2).num : Int) ≠ 0; omega
  have scaled (i : Fin 3) : ((x i).mul d).Equiv (difference rates i) := divide_mul _ _ positive
  cases shape with
  | equal =>
    change ((difference rates 0).sub (difference rates 1)).Equiv .zero ↔ (x 0).Equiv (x 1)
    exact (SignedRatio.sub_equiv_zero_iff _ _).trans (scaled_iff nonzero (scaled 0) (scaled 1))
  | zero =>
    change (difference rates 0).Equiv .zero ↔ (x 0).Equiv .zero
    exact scaled_iff nonzero (scaled 0) (SignedRatio.zero_mul _)
  | one =>
    change ((difference rates 0).sub d).Equiv .zero ↔ (x 0).Equiv .one
    exact (SignedRatio.sub_equiv_zero_iff _ _).trans (scaled_iff nonzero (scaled 0) (SignedRatio.one_mul _))
  | negative =>
    change ((difference rates 2).sub (SignedRatio.zero.sub (difference rates 0))).Equiv .zero ↔
      (x 2).Equiv (x 0).neg
    rw [SignedRatio.sub_equiv_zero_iff]
    apply scaled_iff nonzero (scaled 2)
    exact SignedRatio.equiv_trans (SignedRatio.neg_mul _ _) (SignedRatio.equiv_trans
      (SignedRatio.neg_congr (scaled 0)) (SignedRatio.equiv_symm (SignedRatio.zero_add _)))
  | add =>
    change (((difference rates 0).add (difference rates 1)).sub (difference rates 2)).Equiv .zero ↔
      (x 2).Equiv ((x 0).add (x 1))
    rw [SignedRatio.sub_equiv_zero_iff]
    have plus : (((x 0).add (x 1)).mul d).Equiv ((difference rates 0).add (difference rates 1)) :=
      SignedRatio.equiv_trans (SignedRatio.add_mul _ _ _) (SignedRatio.add_congr (scaled 0) (scaled 1))
    have exactOrder := scaled_iff nonzero plus (scaled 2)
    exact ⟨fun same => SignedRatio.equiv_symm (exactOrder.mp same),
      fun same => exactOrder.mpr (SignedRatio.equiv_symm same)⟩
  | multiply =>
    change (((difference rates 0).mul (difference rates 1)).sub (d.mul (difference rates 2))).Equiv .zero ↔
      (x 2).Equiv ((x 0).mul (x 1))
    rw [SignedRatio.sub_equiv_zero_iff]
    have squareNonzero : (d.mul d).num ≠ 0 := fun h => (Int.mul_eq_zero.mp h).elim nonzero nonzero
    have mulScaled : (((x 0).mul (x 1)).mul (d.mul d)).Equiv
        ((difference rates 0).mul (difference rates 1)) :=
      SignedRatio.equiv_trans (SignedRatio.mul_interchange _ _ _ _) (SignedRatio.mul_congr (scaled 0) (scaled 1))
    have resultScaled : ((x 2).mul (d.mul d)).Equiv (d.mul (difference rates 2)) := by
      refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (SignedRatio.mul_assoc _ _ _)) ?_
      exact SignedRatio.equiv_trans (SignedRatio.mul_comm _ _)
        (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (scaled 2))
    have exactOrder := scaled_iff squareNonzero mulScaled resultScaled
    exact ⟨fun same => SignedRatio.equiv_symm (exactOrder.mp same),
      fun same => exactOrder.mpr (SignedRatio.equiv_symm same)⟩

private def decoded (rates : Fin (width n) → QProb) (positive : 0 < (rates (denominator n)).num)
    (i : Fin n) : SignedRatio :=
  divideDifference ((rates (numerator i false)).toSignedRatio.sub (rates (numerator i true)).toSignedRatio)
    (rates (denominator n)) positive

private theorem equation_correct (equation : RationalEquation (Fin n)) (rates : Fin (width n) → QProb)
    (positive : 0 < (rates (denominator n)).num)
    (fixedZero : (rates (zero n)).Equiv .zero) (fixedOne : (rates (one n)).Equiv .one) :
    ((equationFor equation).left.evaluate rates).Equiv ((equationFor equation).right.evaluate rates) ↔
      equation.holds (decoded rates positive) := by
  cases equation with
  | equal a b => exact (template_residual .equal (rates ∘ mapping a b a) fixedZero fixedOne).trans (residual_solution _ _ positive)
  | zero a => exact (template_residual .zero (rates ∘ mapping a a a) fixedZero fixedOne).trans (residual_solution _ _ positive)
  | one a => exact (template_residual .one (rates ∘ mapping a a a) fixedZero fixedOne).trans (residual_solution _ _ positive)
  | negative a r => exact (template_residual .negative (rates ∘ mapping a a r) fixedZero fixedOne).trans (residual_solution _ _ positive)
  | add a b r => exact (template_residual .add (rates ∘ mapping a b r) fixedZero fixedOne).trans (residual_solution _ _ positive)
  | multiply a b r => exact (template_residual .multiply (rates ∘ mapping a b r) fixedZero fixedOne).trans (residual_solution _ _ positive)

private theorem pellEquation_correct (rates : Fin (width n) → QProb)
    (fixedZero : (rates (zero n)).Equiv .zero) (fixedOne : (rates (one n)).Equiv .one) :
    ((pellEquation n).left.evaluate rates).Equiv ((pellEquation n).right.evaluate rates) ↔
      (((rates (denominator n)).mul (rates (denominator n))).add
        (QProb.scale 2 ((rates (companion n)).mul (rates (companion n))))).Equiv .one := by
  let d := rates (denominator n)
  let s := rates (companion n)
  let z := rates (zero n)
  let o := rates (one n)
  have left : (((d.mul d).add (s.mul s)).add (s.mul s)).Equiv
      ((d.mul d).add (QProb.scale 2 (s.mul s))) := by
    refine QProb.equiv_trans (QProb.add_assoc _ _ _) (QProb.add_congr (QProb.equiv_refl _) ?_)
    simp only [QProb.add, QProb.scale, QProb.Equiv]
    rw [Nat.two_mul]
    simp only [Nat.add_mul, Nat.mul_assoc]
  have right : (((o.mul o).add (z.mul z)).add (z.mul z)).Equiv .one :=
    QProb.equiv_trans (QProb.add_congr
      (QProb.add_congr (QProb.mul_congr fixedOne fixedOne) (QProb.mul_congr fixedZero fixedZero))
      (QProb.mul_congr fixedZero fixedZero)) (by decide)
  exact ⟨fun same => QProb.equiv_trans (QProb.equiv_symm left) (QProb.equiv_trans same right),
    fun same => QProb.equiv_trans left (QProb.equiv_trans same (QProb.equiv_symm right))⟩

/-- The denominator is positive in every rational solution, so every
cleared comparison decodes to the required rational equation. -/
theorem solvable_of_compiled (system : RationalEquationSystem) (solved : (compile system).Solvable) : system.Solvable := by
  obtain ⟨values, constants, equations⟩ := solved
  let rates := fun i => (values i).val
  have fixedZero : (rates (zero system.count)).Equiv .zero := constants _ List.mem_cons_self
  have fixedOne : (rates (one system.count)).Equiv .one := constants _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have pell := (pellEquation_correct rates fixedZero fixedOne).mp (equations _ List.mem_cons_self)
  have positive := PellHalfRates.positive_of_equation _ _ pell
  refine ⟨decoded rates positive, ?_⟩
  intro equation covered
  have given := equations (equationFor equation) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨equation, covered, rfl⟩))
  exact (equation_correct equation rates positive fixedZero fixedOne).mp given

private def magnitude (values : Fin n → SignedRatio) (indices : List (Fin n)) : Nat :=
  indices.foldr (fun i rest => max (values i).num.natAbs rest) 0

private theorem magnitude_bound (values : Fin n → SignedRatio) (indices : List (Fin n)) (index : Fin n)
    (appears : index ∈ indices) : (values index).num.natAbs ≤ magnitude values indices := by
  induction indices with
  | nil => cases appears
  | cons first rest ih =>
    rcases List.mem_cons.mp appears with atHead | inRest
    · subst first
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih inRest) (Nat.le_max_right _ _)

private def step (values : Fin n → SignedRatio) : Nat := magnitude values (List.finRange n)

/-- The numerator bounds are chosen from the finite witness, not built into
its input. A small enough common d scales all its intermediate values. -/
private theorem enough (values : Fin n → SignedRatio) (index : Fin n) :
    (values index).num.natAbs ≤ (PellHalfRates.pair (step values)).1 := by
  have bound := magnitude_bound values (List.finRange n) index (List.mem_finRange _)
  exact Nat.le_trans bound (Nat.le_trans (Nat.le_succ _) (PellHalfRates.lower_bound (step values)))

private def signedPart (value : SignedRatio) (minus : Bool) : Nat :=
  if minus then (-value.num).toNat else value.num.toNat

private def partRate (value : SignedRatio) (den : Nat) (positive : 0 < den)
    (small : value.num.natAbs ≤ den) (minus : Bool) : BoundedRate :=
  have numeratorBound : signedPart value minus ≤ den := by
    rw [← Int.toNat_add_toNat_neg_eq_natAbs] at small
    cases minus <;> dsimp [signedPart] <;> omega
  have scaledBound : den ≤ value.den * den := by
    have denPos := value.den_pos
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right den (show 1 ≤ value.den by omega)
  ⟨⟨signedPart value minus, value.den * den, Nat.mul_pos value.den_pos positive⟩,
    by change signedPart value minus * 1 ≤ 1 * (value.den * den)
       simp only [Nat.mul_one, Nat.one_mul]
       exact Nat.le_trans numeratorBound scaledBound⟩

private theorem parts_scaled (value : SignedRatio) (den : Nat) (positive : 0 < den)
    (small : value.num.natAbs ≤ den) :
    (value.mul (⟨1, den, positive⟩ : QProb).toSignedRatio).Equiv
      ((partRate value den positive small false).val.toSignedRatio.sub
        (partRate value den positive small true).val.toSignedRatio) := by
  have split : (value.num.toNat : Int) - ((-value.num).toNat : Int) = value.num := by omega
  have sameBound := Nat.mul_pos value.den_pos positive
  have joined := SignedRatio.add_mk_same_den (value.den * den) sameBound
    (value.num.toNat : Int) (-((-value.num).toNat : Int))
  have before : (value.mul (⟨1, den, positive⟩ : QProb).toSignedRatio).Equiv
      ⟨(value.num.toNat : Int) + -((-value.num).toNat : Int), value.den * den, sameBound⟩ := by
    simp only [QProb.toSignedRatio, SignedRatio.mul, SignedRatio.Equiv, Int.natCast_one, Int.mul_one]
    rw [← Int.sub_eq_add_neg, split]
  exact SignedRatio.equiv_trans before (SignedRatio.equiv_symm joined)

private def chosenRates (values : Fin n → SignedRatio) (index : Fin (width n)) : BoundedRate :=
  let selected := step values
  if atZero : index.val = 0 then ⟨.zero, QProb.zero_le _⟩
  else if atOne : index.val = 1 then ⟨.one, QProb.le_refl _⟩
  else if atDen : index.val = 2 then ⟨PellHalfRates.denominatorRate selected, PellHalfRates.denominatorRate_le_one _⟩
  else if atCompanion : index.val = 3 then ⟨PellHalfRates.companionRate selected, PellHalfRates.companionRate_le_one _⟩
  else
    let i : Fin n := ⟨(index.val-4)/2, by have h := index.isLt; unfold width at h; omega⟩
    partRate (values i) (PellHalfRates.pair selected).1 (PellHalfRates.denominator_pos _) (enough values i)
      (decide ((index.val-4)%2 = 1))

private theorem chosenRates_numerator (values : Fin n → SignedRatio) (i : Fin n) (minus : Bool) :
    chosenRates values (numerator i minus) =
      partRate (values i) (PellHalfRates.pair (step values)).1 (PellHalfRates.denominator_pos _) (enough values i) minus := by
  unfold chosenRates
  have coordinate : (numerator i minus).val = 4 + 2*i.val + (if minus then 1 else 0) := rfl
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
  dsimp
  have decodedIndex : (⟨((numerator i minus).val - 4) / 2, by
      have bound := (numerator i minus).isLt
      unfold width at bound
      omega⟩ : Fin n) = i := by
    apply Fin.ext
    cases minus <;> simp only [Bool.false_eq_true, if_false, if_true] at coordinate <;> dsimp <;> omega
  have sign : decide (((numerator i minus).val - 4) % 2 = 1) = minus := by
    cases minus
    · apply decide_eq_false; simp only [Bool.false_eq_true, if_false] at coordinate; omega
    · apply decide_eq_true; simp only [if_true] at coordinate; omega
  rw [decodedIndex, sign]

private theorem chosenRates_correct (values : Fin n → SignedRatio) (i : Fin n)
    (positive : 0 < (chosenRates values (denominator n)).val.num) :
    (decoded (fun t => (chosenRates values t).val) positive i).Equiv (values i) := by
  let d := PellHalfRates.denominatorRate (step values)
  let dR := d.toSignedRatio
  have nonzero : dR.num ≠ 0 := by change (1 : Int) ≠ 0; decide
  apply mul_cancel_right (factor := dR) nonzero
  refine SignedRatio.equiv_trans (divide_mul _ d positive) ?_
  change (((chosenRates values (numerator i false)).val.toSignedRatio).sub
    ((chosenRates values (numerator i true)).val.toSignedRatio)).Equiv ((values i).mul dR)
  rw [chosenRates_numerator, chosenRates_numerator]
  exact SignedRatio.equiv_symm (parts_scaled (values i) _ _ (enough values i))

private theorem holds_congr (eq : RationalEquation (Fin n)) (a b : Fin n → SignedRatio)
    (same : ∀ index, (a index).Equiv (b index)) (valid : eq.holds b) : eq.holds a := by
  have replace {x y x' y' : SignedRatio} (first : x.Equiv x') (second : y.Equiv y') (tie : x'.Equiv y') :=
    SignedRatio.equiv_trans first (SignedRatio.equiv_trans tie (SignedRatio.equiv_symm second))
  cases eq with
  | equal x y => exact replace (same x) (same y) valid
  | zero x => exact SignedRatio.equiv_trans (same x) valid
  | one x => exact SignedRatio.equiv_trans (same x) valid
  | negative x y => exact replace (same y) (SignedRatio.neg_congr (same x)) valid
  | add x y r => exact replace (same r) (SignedRatio.add_congr (same x) (same y)) valid
  | multiply x y r => exact replace (same r) (SignedRatio.mul_congr (same x) (same y)) valid

/-- Any finite collection of unbounded rational witnesses embeds as
unit-interval numerator rates at one common Pell denominator. -/
theorem compiled_of_solvable (system : RationalEquationSystem) (solved : system.Solvable) : (compile system).Solvable := by
  obtain ⟨values, obeys⟩ := solved
  let rates := fun i => (chosenRates values i).val
  have fixedZero : (rates (zero system.count)).Equiv .zero := QProb.equiv_refl _
  have fixedOne : (rates (one system.count)).Equiv .one := QProb.equiv_refl _
  have positive : 0 < (rates (denominator system.count)).num := by change 0 < 1; decide
  refine ⟨chosenRates values, ?_, ?_⟩
  · intro req belongs
    rcases List.mem_cons.mp belongs with z | rest
    · subst req
      exact fixedZero
    · rcases List.mem_cons.mp rest with o | absent
      · subst req
        exact fixedOne
      · cases absent
  · intro equation belongs
    rcases List.mem_cons.mp belongs with pell | orig
    · subst equation
      exact (pellEquation_correct rates fixedZero fixedOne).mpr (PellHalfRates.equation (step values))
    · obtain ⟨source, member, rfl⟩ := List.mem_map.mp orig
      exact (equation_correct source rates positive fixedZero fixedOne).mpr
        (holds_congr source _ _ (chosenRates_correct values · positive) (obeys source member))

/-- The bounded monomial constraints characterize the rational solutions
of the elementary equations with no prior denominator bound. -/
theorem compile_correct (system : RationalEquationSystem) :
    (compile system).Solvable ↔ system.Solvable := ⟨solvable_of_compiled system, compiled_of_solvable system⟩

end RationalEquationClearing
end Thesis.Causality.QualitativeTies
