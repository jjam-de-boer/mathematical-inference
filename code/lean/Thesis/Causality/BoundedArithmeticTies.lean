import Thesis.Causality.QualitativeTieMasses

namespace Thesis.Causality.QualitativeTies
open Probability

/-!
# Bounded arithmetic using within-experiment ties

One reference bit stores each arithmetic value as a success probability.
The reference bits are isolated. Comparisons may relate different reference
or output bits, but the causal arrows do not carry these values between
constructions. Each selector and its output occupy a fresh component.
This separation is what keeps the resulting graph a directed matching.

A multiplication reads the two rows (0,q) at selector bias p. The same
mixture in observation has output pq. Addition compares a fair mixture of
p and q with a second mixture computing r/2. Every tie compares two
unconditional unary events in the stated experiment. Zero and one are
implemented as the impossible and certain literals of a forced anchor.
-/

/-- Integer arithmetic is reduced to these constraints on a list of rates
in the closed unit interval. For addition, the result is also a rate. -/
inductive BoundedConstraint (variables : Nat) where
  | equal (left right : Fin variables)
  | zero (value : Fin variables)
  | one (value : Fin variables)
  | half (value : Fin variables)
  | multiply (left right result : Fin variables)
  | add (left right result : Fin variables)

namespace BoundedConstraint

variable {variables : Nat}

/-- The values are taken in the unit interval by the caller. -/
def holds (values : Fin variables → QProb) : BoundedConstraint variables → Prop
  | .equal a b => (values a).Equiv (values b)
  | .zero a => (values a).Equiv .zero
  | .one a => (values a).Equiv .one
  | .half a => (values a).Equiv ⟨1, 2, by decide⟩
  | .multiply a b result => ((values a).mul (values b)).Equiv (values result)
  | .add a b result => ((values a).add (values b)).Equiv (values result)

end BoundedConstraint

namespace BoundedArithmeticTies

variable {variables : Nat}

/-- One anchor, then the variable references, then two pairs for each
constraint. Addition uses both pairs. Simpler constraints leave spare
components free, which avoids a variable-width allocation proof. -/
def vertexCount (variables constraints : Nat) : Nat := variables + 1 + 4 * constraints

private def matchingParent (variables constraints : Nat) (node : Fin (vertexCount variables constraints)) :
    Option (Fin (vertexCount variables constraints)) :=
  if variables + 1 ≤ node.val ∧ (node.val - (variables + 1)) % 2 = 1 then
    some ⟨node.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) node.isLt⟩
  else none

private theorem parent_index (node source : Fin (vertexCount variables constraints))
    (parent : matchingParent variables constraints node = some source) :
    variables + 1 ≤ node.val ∧ (node.val - (variables + 1)) % 2 = 1 ∧ source.val = node.val - 1 := by
  unfold matchingParent at parent
  split at parent
  · rename_i h
    exact ⟨h.1, h.2, (congrArg Fin.val (Option.some.inj parent)).symm⟩
  · cases parent

/-- Exactly the arrows from even to following odd positions in the
selector/output section. The first `variables + 1` vertices are isolated. -/
def matching (variables constraints : Nat) : Matching (vertexCount variables constraints) where
  parent := matchingParent variables constraints
  parentEarlier := by
    intro child source parent
    obtain ⟨above, _, sourceIndex⟩ := parent_index child source parent
    omega
  parentRoot := by
    intro child source parent
    obtain ⟨above, odd, sourceIndex⟩ := parent_index child source parent
    unfold matchingParent
    apply if_neg
    intro bad
    omega
  uniqueChild := by
    intro left right source parentLeft parentRight
    obtain ⟨aboveLeft, _, leftIndex⟩ := parent_index left source parentLeft
    obtain ⟨aboveRight, _, rightIndex⟩ := parent_index right source parentRight
    exact Fin.ext (by omega)

private def anchor (variables constraints : Nat) : Fin (vertexCount variables constraints) :=
  ⟨0, by unfold vertexCount; omega⟩

private def reference (constraints : Nat) (index : Fin variables) : Fin (vertexCount variables constraints) :=
  ⟨index.val + 1, by unfold vertexCount; have bound := index.isLt; omega⟩

private def selector (variables : Nat) (constraint : Fin constraints) (which : Fin 2) :
    Fin (vertexCount variables constraints) :=
  ⟨variables + 1 + 4 * constraint.val + 2 * which.val,
    by unfold vertexCount; have i := constraint.isLt; have j := which.isLt; omega⟩

private def outcome (variables : Nat) (constraint : Fin constraints) (which : Fin 2) :
    Fin (vertexCount variables constraints) :=
  ⟨variables + 1 + 4 * constraint.val + 2 * which.val + 1,
    by unfold vertexCount; have i := constraint.isLt; have j := which.isLt; omega⟩

private theorem reference_is_root (constraints : Nat) (index : Fin variables) :
    (matching variables constraints).parent (reference constraints index) = none := by
  unfold matching matchingParent
  apply if_neg
  have indexBound := index.isLt
  simp only [reference, not_and]
  omega

private theorem selector_is_root (variables : Nat) (constraint : Fin constraints) (which : Fin 2) :
    (matching variables constraints).parent (selector variables constraint which) = none := by
  unfold matching matchingParent
  apply if_neg
  simp only [selector, not_and]
  omega

private theorem outcome_has_selector (variables : Nat) (constraint : Fin constraints) (which : Fin 2) :
    (matching variables constraints).parent (outcome variables constraint which) =
      some (selector variables constraint which) := by
  change matchingParent variables constraints (outcome variables constraint which) = _
  unfold matchingParent
  rw [if_pos (by simp only [outcome]; omega)]
  apply congrArg some
  apply Fin.ext
  simp only [outcome, selector]
  omega

private def yes (node : Fin n) : Literal n := ⟨node, true⟩
private def no (node : Fin n) : Literal n := ⟨node, false⟩

private def constraintTies (constraint : Fin constraints) (relation : BoundedConstraint variables) :
    List (Tie (vertexCount variables constraints)) :=
  let ref := reference constraints (variables := variables)
  let anchor := anchor variables constraints
  let u₀ := selector variables constraint 0
  let v₀ := outcome variables constraint 0
  let u₁ := selector variables constraint 1
  let v₁ := outcome variables constraint 1
  match relation with
  | .equal a b => [⟨.observe, yes (ref a), yes (ref b)⟩]
  | .zero a => [⟨.set anchor false, yes (ref a), yes anchor⟩]
  | .one a => [⟨.set anchor true, yes (ref a), yes anchor⟩]
  | .half a => [⟨.observe, yes (ref a), no (ref a)⟩]
  | .multiply a b result =>
    [⟨.observe, yes u₀, yes (ref a)⟩,
      ⟨.set u₀ false, yes v₀, yes u₀⟩,
      ⟨.set u₀ true, yes v₀, yes (ref b)⟩,
      ⟨.observe, yes v₀, yes (ref result)⟩]
  | .add a b result =>
    [⟨.observe, yes u₀, no u₀⟩,
      ⟨.set u₀ false, yes v₀, yes (ref a)⟩,
      ⟨.set u₀ true, yes v₀, yes (ref b)⟩,
      ⟨.observe, yes u₁, yes (ref result)⟩,
      ⟨.set u₁ false, yes v₁, yes u₁⟩,
      ⟨.set u₁ true, yes v₁, no v₁⟩,
      ⟨.observe, yes v₀, yes v₁⟩]

/-- Compile a finite bounded constraint program. Its type ensures every
comparison is a unary tie within a single experiment. -/
def compile (program : List (BoundedConstraint variables)) : Instance where
  count := vertexCount variables program.length
  graph := matching variables program.length
  ties := (List.finRange program.length).flatMap fun i => constraintTies i program[i]

/-!
## Probability calculations for a selector component

These are equations for the rate presentation proved equivalent to the urn
interpreter. No numerical probabilities appear in `constraintTies` itself.
-/

private def half : QProb := ⟨1, 2, by decide⟩

private def mixture (selector first second : QProb) : QProb :=
  QProb.add (QProb.mul (opposite selector) first) (QProb.mul selector second)

private theorem opposite_eq {first second : QProb} (same : first.Equiv second) :
    (opposite first).Equiv (opposite second) := by
  change (first.den - first.num) * second.den = (second.den - second.num) * first.den
  rw [Nat.mul_sub_right_distrib, Nat.mul_sub_right_distrib, same, Nat.mul_comm first.den second.den]

private theorem mixture_congr {p p' a a' b b' : QProb}
    (selector : p.Equiv p') (first : a.Equiv a') (second : b.Equiv b') :
    (mixture p a b).Equiv (mixture p' a' b') :=
  QProb.add_congr (QProb.mul_congr (opposite_eq selector) first) (QProb.mul_congr selector second)

private theorem select_false (a b : QProb) :
    ((QProb.one.mul a).add (QProb.zero.mul b)).Equiv a := by
  simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.zero, QProb.one,
    Nat.one_mul, Nat.zero_mul, Nat.add_zero]
  ac_rfl

private theorem select_true (a b : QProb) :
    ((QProb.zero.mul a).add (QProb.one.mul b)).Equiv b := by
  simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.zero, QProb.one,
    Nat.one_mul, Nat.zero_mul, Nat.zero_add]
  ac_rfl

private theorem mixture_zero (p q : QProb) : (mixture p .zero q).Equiv (p.mul q) := by
  simp only [mixture, QProb.Equiv, QProb.zero, QProb.add, QProb.mul,
    Nat.mul_one, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  ac_rfl

private theorem mixture_half (p q : QProb) : (mixture half p q).Equiv (half.mul (p.add q)) := by
  change (QProb.add (QProb.mul half p) (QProb.mul half q)).Equiv (half.mul (p.add q))
  exact QProb.equiv_symm (QProb.mul_add_distrib _ _ _)

private theorem mul_half_cancel {p q : QProb} (same : (half.mul p).Equiv (half.mul q)) : p.Equiv q := by
  change (1 * p.num) * (2 * q.den) = (1 * q.num) * (2 * p.den) at same
  simp only [Nat.one_mul] at same
  apply Nat.eq_of_mul_eq_mul_right (m := 2) (by decide)
  calc
    _ = p.num * (2 * q.den) := by ac_rfl
    _ = q.num * (2 * p.den) := same
    _ = _ := by ac_rfl

private theorem half_iff_opposite (value : {rate : QProb // rate.LE .one}) :
    value.val.Equiv (opposite value.val) ↔ value.val.Equiv half := by
  constructor
  · intro ties
    have bound : value.val.num ≤ value.val.den := by
      simpa [QProb.LE, QProb.one] using value.property
    have equal : value.val.num = value.val.den - value.val.num :=
      Nat.eq_of_mul_eq_mul_right value.val.den_pos ties
    change value.val.num * 2 = 1 * value.val.den
    omega
  · intro fair
    exact QProb.equiv_trans fair (QProb.equiv_symm (opposite_eq fair))

/-- A row formula simplified for single-node settings. It agrees with the
ordinary mass formula: setting the root makes its child mixture select just
one row. Keeping this simplification explicit makes each checked gate a
short list of elementary equations. -/
private def simplifiedMass (graph : Matching n) (rates : Rates n) (experiment : Experiment n)
    (literal : Literal n) : QProb :=
  match experiment.forced literal.node with
  | some actual => if actual = literal.value then .one else .zero
  | none => match graph.parent literal.node with
    | none => rates.rowMass literal.node false literal.value
    | some source => match experiment.forced source with
      | some actual => rates.rowMass literal.node actual literal.value
      | none => mixture (rates source false).val (rates.rowMass literal.node false literal.value)
        (rates.rowMass literal.node true literal.value)

private theorem simplifiedMass_correct (graph : Matching n) (rates : Rates n)
    (experiment : Experiment n) (literal : Literal n) :
    (literal.massFromRows graph rates.rowMass experiment).Equiv (simplifiedMass graph rates experiment literal) := by
  unfold Literal.massFromRows simplifiedMass
  cases selected : experiment.forced literal.node with
  | some actual => exact QProb.equiv_refl _
  | none =>
    cases parent : graph.parent literal.node with
    | none => exact QProb.equiv_refl _
    | some source =>
      cases setting : experiment.forced source with
      | none => simp only [rootMass, setting, Rates.rowMass, mixture, if_true, Bool.false_eq_true, if_false]; exact QProb.equiv_refl _
      | some actual =>
        simp only [rootMass, setting]
        cases actual
        · exact select_false _ _
        · exact select_true _ _

private def respects (graph : Matching n) (rates : Rates n) (tie : Tie n) : Prop :=
  (simplifiedMass graph rates tie.experiment tie.left).Equiv (simplifiedMass graph rates tie.experiment tie.right)

private theorem equiv_replace {p q p' q' : QProb} (left : p.Equiv p') (right : q.Equiv q') :
    p.Equiv q ↔ p'.Equiv q' :=
  ⟨fun same => QProb.equiv_trans (QProb.equiv_symm left) (QProb.equiv_trans same right),
    fun same => QProb.equiv_trans left (QProb.equiv_trans same (QProb.equiv_symm right))⟩

private theorem respects_iff (graph : Matching n) (rates : Rates n) (tie : Tie n) :
    respects graph rates tie ↔ (tie.left.massFromRows graph rates.rowMass tie.experiment).Equiv
      (tie.right.massFromRows graph rates.rowMass tie.experiment) :=
  (equiv_replace (simplifiedMass_correct graph rates tie.experiment tie.left)
    (simplifiedMass_correct graph rates tie.experiment tie.right)).symm

private theorem reference_apart_anchor (constraints : Nat) (index : Fin variables) :
    reference constraints index ≠ anchor variables constraints := by
  intro same
  have contra := congrArg Fin.val same
  change index.val + 1 = 0 at contra
  omega

private theorem reference_apart_selector (index : Fin variables) (instruction : Fin constraints) (which : Fin 2) :
    reference constraints index ≠ selector variables instruction which := by
  intro same
  have contra := congrArg Fin.val same
  change index.val + 1 = variables + 1 + 4 * instruction.val + 2 * which.val at contra
  have bound := index.isLt
  omega

private theorem selector_apart_outcome (variables : Nat) (instruction : Fin constraints) (which : Fin 2) :
    outcome variables instruction which ≠ selector variables instruction which := by
  intro same
  have contra := congrArg Fin.val same
  change variables + 1 + 4 * instruction.val + 2 * which.val + 1 =
    variables + 1 + 4 * instruction.val + 2 * which.val at contra
  omega

private def refs (rates : Rates (vertexCount variables constraints)) (index : Fin variables) : QProb :=
  (rates (reference constraints index) false).val

private def selectedRate (rates : Rates (vertexCount variables constraints)) (instruction : Fin constraints)
    (which : Fin 2) : {rate : QProb // rate.LE .one} :=
  rates (selector variables instruction which) false

private def childRate (rates : Rates (vertexCount variables constraints)) (instruction : Fin constraints)
    (which : Fin 2) (setting : Bool) : {rate : QProb // rate.LE .one} :=
  rates (outcome variables instruction which) setting

/-- The exact equations imposed by a single finite construction. The hard
settings inspect specific child rows, while the observational ties compare
mixtures. The definition lists all its obligations, including unused rows
when they are actually compared. -/
private def rowEquations (rates : Rates (vertexCount variables constraints)) (instruction : Fin constraints)
    (relation : BoundedConstraint variables) : Prop :=
  let value := refs rates
  let p₀ := (selectedRate rates instruction 0).val
  let p₁ := (selectedRate rates instruction 1).val
  let a₀ := (childRate rates instruction 0 false).val
  let b₀ := (childRate rates instruction 0 true).val
  let a₁ := (childRate rates instruction 1 false).val
  let b₁ := (childRate rates instruction 1 true).val
  match relation with
  | .equal a b => (value a).Equiv (value b)
  | .zero a => (value a).Equiv .zero
  | .one a => (value a).Equiv .one
  | .half a => (value a).Equiv (opposite (value a))
  | .multiply a b result => p₀.Equiv (value a) ∧ a₀.Equiv .zero ∧ b₀.Equiv (value b) ∧
      (mixture p₀ a₀ b₀).Equiv (value result)
  | .add a b result => p₀.Equiv (opposite p₀) ∧ a₀.Equiv (value a) ∧ b₀.Equiv (value b) ∧
      p₁.Equiv (value result) ∧ a₁.Equiv .zero ∧ b₁.Equiv (opposite b₁) ∧
      (mixture p₀ a₀ b₀).Equiv (mixture p₁ a₁ b₁)

private theorem respects_constraint_iff (rates : Rates (vertexCount variables constraints))
    (instruction : Fin constraints) (relation : BoundedConstraint variables) :
    (∀ tie ∈ constraintTies instruction relation, respects (matching variables constraints) rates tie) ↔
      rowEquations rates instruction relation := by
  cases relation <;>
    simp only [constraintTies, rowEquations, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      respects, simplifiedMass, yes, no, Experiment.forced, refs, selectedRate, childRate, Rates.rowMass,
      reference_is_root, selector_is_root, outcome_has_selector, reference_apart_anchor,
      reference_apart_selector, selector_apart_outcome, if_false, if_pos, Bool.false_eq_true, and_true]

private theorem rowEquations_imply (rates : Rates (vertexCount variables constraints)) (instruction : Fin constraints)
    (relation : BoundedConstraint variables) (constraintsHold : rowEquations rates instruction relation) :
    relation.holds (refs rates) := by
  cases relation with
  | equal a b => exact constraintsHold
  | zero a => exact constraintsHold
  | one a => exact constraintsHold
  | half a => exact (half_iff_opposite (rates (reference constraints a) false)).mp constraintsHold
  | multiply a b result =>
    obtain ⟨selector, first, second, compares⟩ := constraintsHold
    exact QProb.equiv_trans (QProb.equiv_symm (mixture_zero _ _))
      (QProb.equiv_trans (QProb.equiv_symm (mixture_congr selector first second)) compares)
  | add a b result =>
    obtain ⟨firstHalf, firstRow, secondRow, secondSelector, zeroRow, halfRow, compares⟩ := constraintsHold
    have fairSelector := (half_iff_opposite (selectedRate rates instruction 0)).mp firstHalf
    have fairRow := (half_iff_opposite (childRate rates instruction 1 true)).mp halfRow
    apply mul_half_cancel
    refine QProb.equiv_trans (QProb.equiv_symm (mixture_half _ _)) ?_
    refine QProb.equiv_trans (QProb.equiv_symm (mixture_congr fairSelector firstRow secondRow)) ?_
    refine QProb.equiv_trans compares (QProb.equiv_trans (mixture_congr secondSelector zeroRow fairRow) ?_)
    exact QProb.equiv_trans (mixture_zero _ _) (QProb.mul_comm _ _)

private abbrev UnitRate := {rate : QProb // rate.LE .one}

private def zeroRate : UnitRate := ⟨.zero, QProb.zero_le _⟩
private def halfRate : UnitRate := ⟨half, by change 1 ≤ 2; decide⟩

/-- Actual recipe choices for the four reserved vertices. Both rows are
specified even when one cannot occur under observation. -/
private def localRecipes (values : Fin variables → UnitRate) (relation : BoundedConstraint variables)
    (position : Nat) (input : Bool) : UnitRate :=
  match relation with
  | .multiply a b _ =>
    match position with
    | 0 => values a
    | 1 => if input then values b else zeroRate
    | _ => zeroRate
  | .add a b result =>
    match position with
    | 0 => halfRate
    | 1 => if input then values b else values a
    | 2 => values result
    | _ => if input then halfRate else zeroRate
  | _ => zeroRate

private def solutionRates (program : List (BoundedConstraint variables)) (values : Fin variables → UnitRate)
    (node : Fin (vertexCount variables program.length)) (input : Bool) : UnitRate :=
  if first : node.val = 0 then zeroRate
  else if before : node.val ≤ variables then values ⟨node.val - 1, by omega⟩
  else
    let offset := node.val - (variables + 1)
    let instruction : Fin program.length := ⟨offset / 4, by
      have bound := node.isLt
      unfold vertexCount at bound
      dsimp [offset]
      omega⟩
    localRecipes values program[instruction] (offset % 4) input

private theorem solutionRates_ref (program : List (BoundedConstraint variables)) (values : Fin variables → UnitRate)
    (index : Fin variables) (input : Bool) : solutionRates program values (reference program.length index) input = values index := by
  have bound := index.isLt
  unfold solutionRates
  rw [dif_neg (by change index.val + 1 ≠ 0; omega), dif_pos (by change index.val + 1 ≤ variables; omega)]
  exact congrArg values (Fin.ext (by change index.val + 1 - 1 = index.val; omega))

private theorem solutionRates_slot (program : List (BoundedConstraint variables)) (values : Fin variables → UnitRate)
    (instruction : Fin program.length) (position : Fin 4) (input : Bool)
    (node : Fin (vertexCount variables program.length))
    (atPosition : node.val = variables + 1 + 4 * instruction.val + position.val) :
    solutionRates program values node input = localRecipes values program[instruction] position.val input := by
  have positionBound := position.isLt
  unfold solutionRates
  rw [dif_neg (by omega), dif_neg (by omega)]
  have slot : (node.val - (variables + 1)) / 4 = instruction.val := by omega
  have phase : (node.val - (variables + 1)) % 4 = position.val := by omega
  dsimp
  rw [phase]
  simp only [slot]

private theorem solutionRates_select (program : List (BoundedConstraint variables))
    (values : Fin variables → UnitRate) (instruction : Fin program.length) (which : Fin 2) :
    selectedRate (solutionRates program values) instruction which =
      localRecipes values program[instruction] (2 * which.val) false := by
  apply solutionRates_slot program values instruction ⟨2 * which.val, by have h := which.isLt; omega⟩
  rfl

private theorem solutionRates_child (program : List (BoundedConstraint variables))
    (values : Fin variables → UnitRate) (instruction : Fin program.length) (which : Fin 2) (input : Bool) :
    childRate (solutionRates program values) instruction which input =
      localRecipes values program[instruction] (2 * which.val + 1) input := by
  apply solutionRates_slot program values instruction ⟨2 * which.val + 1, by have h := which.isLt; omega⟩
  rfl

private theorem solutionRates_rows (program : List (BoundedConstraint variables)) (values : Fin variables → UnitRate)
    (instruction : Fin program.length) (holds : program[instruction].holds (fun index => (values index).val)) :
    rowEquations (solutionRates program values) instruction program[instruction] := by
  unfold rowEquations
  simp only [refs, solutionRates_ref, solutionRates_select, solutionRates_child]
  cases equation : program[instruction] <;> rw [equation] at holds
  case equal a b => exact holds
  case zero a => exact holds
  case one a => exact holds
  case half a => exact (half_iff_opposite (values a)).mpr holds
  case multiply a b result =>
    refine ⟨QProb.equiv_refl _, QProb.equiv_refl _, QProb.equiv_refl _, ?_⟩
    exact QProb.equiv_trans (mixture_zero _ _) holds
  case add a b result =>
    refine ⟨QProb.equiv_refl _, QProb.equiv_refl _, QProb.equiv_refl _, QProb.equiv_refl _,
      QProb.equiv_refl _, QProb.equiv_refl _, ?_⟩
    refine QProb.equiv_trans (mixture_half _ _) ?_
    refine QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) holds) ?_
    exact QProb.equiv_trans (QProb.mul_comm _ _) (QProb.equiv_symm (mixture_zero _ _))

/-- Bounded arithmetic and the compiled comparison instance have witnesses
in both directions. The realizing witness is one ordinary causal urn game
on the generated directed matching. -/
theorem compile_correct (program : List (BoundedConstraint variables)) :
    (compile program).Realizable ↔
      ∃ values : Fin variables → UnitRate, ∀ relation ∈ program, relation.holds (fun index => (values index).val) := by
  constructor
  · intro realized
    obtain ⟨rates, ties⟩ := (compile program).realizable_iff_rates.mp realized
    refine ⟨fun i => rates (reference program.length i) false, ?_⟩
    intro relation member
    obtain ⟨index, bound, indexEq⟩ := List.getElem_of_mem member
    let instruction : Fin program.length := ⟨index, bound⟩
    have declared : program[instruction] = relation := indexEq
    rw [← declared]
    apply rowEquations_imply rates instruction
    apply (respects_constraint_iff _ _ _).mp
    intro tie localTie
    apply (respects_iff _ _ _).mpr
    exact ties tie (List.mem_flatMap.mpr ⟨instruction, List.mem_finRange _, localTie⟩)
  · rintro ⟨values, valid⟩
    let rates := solutionRates program values
    apply (compile program).realizable_iff_rates.mpr
    refine ⟨rates, ?_⟩
    intro tie member
    obtain ⟨instruction, _, localTie⟩ := List.mem_flatMap.mp member
    have equations := solutionRates_rows program values instruction (valid _ (List.getElem_mem _))
    exact (respects_iff _ _ _).mp ((respects_constraint_iff _ _ _).mpr equations tie localTie)

end BoundedArithmeticTies
end Thesis.Causality.QualitativeTies
