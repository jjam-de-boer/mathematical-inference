import Thesis.Causality.ProbabilityResult

namespace Thesis
namespace Causality

open Probability

/-!
# Local support for zero-weighted finite probability expressions

The ordinary `ProbabilityResult.multiply` and `sum` remain strict: an
undefined conditional is not a rational zero.  This module supplies a separate
operation for a *weighted* expression.  A defined zero weight contributes zero
without consulting its factor; a positive weight still requires a defined
factor, and an undefined weight remains undefined.

This distinction is needed when marginalizing over supported events in a
distribution that has observational zeros.  It does not make an unsupported
intervention identifiable, assign a value to `0 / 0`, or yet extend the
published identification compiler.  Its later integration must supply the
appropriate weights and justify that each skipped branch really has zero
mass.  Local support below refers only to the listed positive-weight branches,
not strict positivity of every observational assignment.

All guards inspect a natural numerator.  Numerator-zero and numerator-positive
tests are invariant under `QProb.Equiv`, so representation choices cannot
change which branches are skipped.  Support values are retained as data and
finite sums are assembled by list recursion, without choice or propositional
excluded middle.
-/

namespace ProbabilityResult

/-! ## An explicit zero-weight guard -/

/-- Evaluate a weighted factor only on the support of its weight.  The left
operand is distinguished deliberately: this is not a commutative replacement
for ordinary partial multiplication. -/
def weightedMultiply (weight factor : Result) : Result :=
  match weight with
  | none => none
  | some weightValue =>
      if weightValue.num = 0 then some QProb.zero
      else multiply (some weightValue) factor

/-- An unknown weight cannot justify ignoring its factor. -/
theorem weightedMultiply_none (factor : Result) :
    weightedMultiply none factor = none := rfl

/-- A known zero weight contributes zero even if the factor is undefined.
This is a rule for the complete weighted expression, not for the factor. -/
theorem weightedMultiply_zero (factor : Result) :
    weightedMultiply (some QProb.zero) factor = some QProb.zero := rfl

/-- Every positive-weight branch retains ordinary strict multiplication. -/
theorem weightedMultiply_of_positive (weight : QProb) (factor : Result)
    (positive : 0 < weight.num) :
    weightedMultiply (some weight) factor = multiply (some weight) factor := by
  simp only [weightedMultiply, if_neg (Nat.ne_of_gt positive)]

/-- In particular, a missing factor under positive mass remains undefined. -/
theorem weightedMultiply_none_of_positive (weight : QProb)
    (positive : 0 < weight.num) :
    weightedMultiply (some weight) none = none := by
  rw [weightedMultiply_of_positive weight none positive]
  rfl

/-- Equivalent weights choose the same guard.  Their factors need agree only
on the positive branch: differing values or support domains at zero weight
are irrelevant to the complete weighted expression. -/
def weightedMultiply_congr_on_positive {weight weight' factor factor' : Result}
    (weightEquivalent : Equivalent weight weight')
    (factorsOnPositive : PositiveSupportedValue weight ->
      Equivalent factor factor') :
    Equivalent (weightedMultiply weight factor)
      (weightedMultiply weight' factor') := by
  cases weightEquivalent with
  | unsupported => exact .unsupported
  | @value left right equivalent =>
      if zero : left.num = 0 then
        have zero' : right.num = 0 := (QProb.equiv_num_zero_iff equivalent).mp zero
        simpa only [weightedMultiply, if_pos zero, if_pos zero'] using
          refl (some QProb.zero)
      else
        have nonzero' : right.num ≠ 0 := fun zero' =>
          zero ((QProb.equiv_num_zero_iff equivalent).mpr zero')
        simpa only [weightedMultiply, if_neg zero, if_neg nonzero'] using
          multiply_congr (.value equivalent)
            (factorsOnPositive ⟨left, refl _, Nat.pos_of_ne_zero zero⟩)

/-- The everywhere-equivalent case is a specialization of positive-branch
congruence.  It is useful when transporting an already supported expression
without separately inspecting its zero weights. -/
def weightedMultiply_congr {weight weight' factor factor' : Result}
    (weightEquivalent : Equivalent weight weight')
    (factorEquivalent : Equivalent factor factor') :
    Equivalent (weightedMultiply weight factor)
      (weightedMultiply weight' factor') :=
  weightedMultiply_congr_on_positive weightEquivalent (fun _ => factorEquivalent)

/-- When both operands are defined, the weighted operation agrees with the
existing multiplication up to rational equivalence.  Skipping a zero branch
therefore does not alter any previously supported computation. -/
noncomputable def weightedMultiply_agrees {weight factor : Result}
    (weightSupported : Supported weight) (factorSupported : Supported factor) :
    Equivalent (weightedMultiply weight factor) (multiply weight factor) := by
  cases weight with
  | none =>
      rcases weightSupported with ⟨_, impossible⟩
      cases impossible
  | some weightValue =>
      cases factor with
      | none =>
          rcases factorSupported with ⟨_, impossible⟩
          cases impossible
      | some factorValue =>
          if zero : weightValue.num = 0 then
            simp only [weightedMultiply, if_pos zero, multiply]
            exact .value (by
              simp only [QProb.Equiv, QProb.zero, QProb.mul, zero,
                Nat.zero_mul])
          else
            simpa only [weightedMultiply, if_neg zero] using
              refl (multiply (some weightValue) (some factorValue))

/-! ## Support is required only where the defined weight is positive -/

/-- Construct the weighted result from a defined weight and factor support
on its positive branch.  No factor value is requested at zero weight.
The concrete numerator test constructs the zero/positive alternatives;
it does not eliminate a propositional disjunction into support data. -/
noncomputable def weightedMultiply_supported {weight factor : Result}
    (weightSupported : Supported weight)
    (factorOnPositive : PositiveSupportedValue weight -> Supported factor) :
    Supported (weightedMultiply weight factor) := by
  cases weight with
  | none =>
      rcases weightSupported with ⟨_, impossible⟩
      cases impossible
  | some weightValue =>
      if zero : weightValue.num = 0 then
        refine ⟨QProb.zero, ?_⟩
        simpa only [weightedMultiply, if_pos zero] using refl (some QProb.zero)
      else
        have positive : 0 < weightValue.num := Nat.pos_of_ne_zero zero
        let factorSupported := factorOnPositive
          ⟨weightValue, refl _, positive⟩
        simpa only [weightedMultiply, if_neg zero] using
          multiply_supported ⟨weightValue, refl _⟩ factorSupported

/-- The local factor-support requirement is necessary at every positive
weight, not just an optional sufficient hypothesis.  In particular, the guard
cannot hide a genuinely unsupported positive-mass conditioning branch. -/
noncomputable def supported_factor_of_weightedMultiply
    {weight factor : Result} (positive : PositiveSupportedValue weight)
    (supported : Supported (weightedMultiply weight factor)) : Supported factor := by
  cases weight with
  | none => cases positive.equivalent
  | some weightValue =>
      have valuePositive : 0 < weightValue.num := by
        cases positive.equivalent with
        | value equivalent =>
            exact (QProb.equiv_num_pos_iff equivalent).mpr positive.positive
      rw [weightedMultiply_of_positive weightValue factor valuePositive] at supported
      exact supported_right_of_multiply supported

/-! ## Finite weighted marginalization -/

/-- Sum weighted factors over the supplied finite enumeration.  No filtering
of an arbitrary proposition is involved; the only branch guard is the
decidable zero test inside `weightedMultiply`. -/
def weightedSum (values : List X) (weight factor : X -> Result) : Result :=
  sum (values.map (fun value => weightedMultiply (weight value) (factor value)))

/-- Every listed weight must be defined, but its factor is needed only when
that weight is positive.  Values absent from the finite list impose no support
obligation.  This is the local-support boundary for future marginal compilers. -/
noncomputable def weightedSum_supported_of_mem (values : List X)
    (weight factor : X -> Result)
    (weightsSupported : forall value, value ∈ values -> Supported (weight value))
    (factorsOnPositive : forall value, value ∈ values ->
      PositiveSupportedValue (weight value) -> Supported (factor value)) :
    Supported (weightedSum values weight factor) :=
  sum_map_supported_of_mem values
    (fun value => weightedMultiply (weight value) (factor value))
    (fun value member => weightedMultiply_supported
      (weightsSupported value member) (factorsOnPositive value member))

/-- Weighted sums compare factors only on listed positive-weight branches.
This permits different or undefined conditional values outside those branches
without treating the conditional itself as a defined zero. -/
noncomputable def weightedSum_congr_on_positive_mem (values : List X)
    (weight weight' factor factor' : X -> Result)
    (weightsEquivalent : forall value, value ∈ values ->
      Equivalent (weight value) (weight' value))
    (factorsOnPositive : forall value, value ∈ values ->
      PositiveSupportedValue (weight value) ->
        Equivalent (factor value) (factor' value)) :
    Equivalent (weightedSum values weight factor)
      (weightedSum values weight' factor') :=
  sum_map_congr_mem values _ _ (fun value member =>
    weightedMultiply_congr_on_positive (weightsEquivalent value member)
      (factorsOnPositive value member))

/-- Pointwise equivalent weights and factors yield equivalent weighted sums.
Only listed branches are compared; the sharper positive-branch theorem above
is used when conditional values outside support must remain unconstrained. -/
noncomputable def weightedSum_congr_mem (values : List X)
    (weight weight' factor factor' : X -> Result)
    (weightsEquivalent : forall value, value ∈ values ->
      Equivalent (weight value) (weight' value))
    (factorsEquivalent : forall value, value ∈ values ->
      Equivalent (factor value) (factor' value)) :
    Equivalent (weightedSum values weight factor)
      (weightedSum values weight' factor') :=
  sum_map_congr_mem values _ _ (fun value member =>
    weightedMultiply_congr (weightsEquivalent value member)
      (factorsEquivalent value member))

/-- On the old everywhere-supported summands, weighted marginalization agrees
with the original strict finite sum of products.  Thus the new operation can
extend support without silently changing the established positive semantics. -/
noncomputable def weightedSum_agrees_of_mem (values : List X)
    (weight factor : X -> Result)
    (weightsSupported : forall value, value ∈ values -> Supported (weight value))
    (factorsSupported : forall value, value ∈ values -> Supported (factor value)) :
    Equivalent (weightedSum values weight factor)
      (sum (values.map (fun value => multiply (weight value) (factor value)))) :=
  sum_map_congr_mem values _ _ (fun value member => weightedMultiply_agrees
    (weightsSupported value member) (factorsSupported value member))

/-! ## Recovering a dominated joint mass across zero conditioning cells -/

/-- The conditional chain identity with an explicit base conditioner.
The weight is `middle/base`, not the rightmost factor of the old strict
product.  If the base has zero mass, both complete expressions remain
undefined; if the middle cell has zero mass under a positive base, domination
forces the joint numerator to zero and only that weighted contribution is
defined.  Neither case fills in the conditional `numerator/middle`.

This form is the algebraic boundary needed by conditional kernel chains.
Its sole zero-cell premise is later discharged by containment of actual
events, rather than by requiring a globally positive distribution. -/
def weightedDivide_chain (numerator middle base : QProb)
    (zeroDominated : middle.num = 0 -> numerator.num = 0) :
    Equivalent
      (weightedMultiply (divide (some middle) (some base))
        (divide (some numerator) (some middle)))
      (divide (some numerator) (some base)) := by
  if basePositive : 0 < base.num then
    if middleZero : middle.num = 0 then
      have numeratorZero : numerator.num = 0 := zeroDominated middleZero
      simp only [divide, dif_pos basePositive, weightedMultiply,
        QProb.div, middleZero, Nat.zero_mul]
      exact .value (by
        simp only [QProb.Equiv, QProb.zero, numeratorZero, Nat.zero_mul])
    else
      have middlePositive : 0 < middle.num := Nat.pos_of_ne_zero middleZero
      have weightNonzero : middle.num * base.den ≠ 0 :=
        Nat.ne_of_gt (Nat.mul_pos middlePositive base.den_pos)
      simp only [divide, dif_pos basePositive, dif_pos middlePositive,
        weightedMultiply, QProb.div, if_neg weightNonzero, multiply]
      exact .value (by
        simp only [QProb.Equiv, QProb.mul]
        ac_rfl)
  else
    simp only [divide, dif_neg basePositive, weightedMultiply]
    exact .unsupported

/-- Domination discharges the zero-middle premise of the guarded conditional
chain.  This compares natural cross-products, without choosing conditional
values on null events. -/
def weightedDivide_chain_of_le (numerator middle base : QProb)
    (dominated : QProb.LE numerator middle) :
    Equivalent
      (weightedMultiply (divide (some middle) (some base))
        (divide (some numerator) (some middle)))
      (divide (some numerator) (some base)) :=
  weightedDivide_chain numerator middle base (fun zero => by
    have bound : numerator.num * middle.den ≤ 0 := by
      simpa only [QProb.LE, zero, Nat.zero_mul] using dominated
    have productZero : numerator.num * middle.den = 0 :=
      Nat.eq_zero_of_le_zero bound
    exact (Nat.mul_eq_zero.mp productZero).resolve_right
      (Nat.ne_of_gt middle.den_pos))

/-- Multiplying a conditional ratio by its conditioning mass recovers the
joint numerator even at a zero cell, provided zero conditioning mass forces
zero joint mass.  The ratio itself remains undefined there; only its complete
weighted contribution has the value zero.

The premise is essential.  Without it, guarding an arbitrary nonzero
numerator over a zero denominator would falsely turn that numerator into zero.
For event probabilities the premise follows from event containment, not an
assumption that every observational cell is positive. -/
def weightedMultiply_divide_cancel (numerator denominator : QProb)
    (zeroDominated : denominator.num = 0 -> numerator.num = 0) :
    Equivalent
      (weightedMultiply (some denominator)
        (divide (some numerator) (some denominator)))
      (some numerator) := by
  if zero : denominator.num = 0 then
    have numeratorZero : numerator.num = 0 := zeroDominated zero
    simp only [weightedMultiply, if_pos zero]
    exact .value (by
      simp only [QProb.Equiv, QProb.zero, numeratorZero,
        Nat.zero_mul])
  else
    have positive : 0 < denominator.num := Nat.pos_of_ne_zero zero
    simp only [weightedMultiply, if_neg zero, divide, dif_pos positive, multiply]
    exact .value (by
      simp only [QProb.Equiv, QProb.mul, QProb.div]
      ac_rfl)

/-- Probability domination supplies precisely the zero-cell premise of the
weighted chain identity.  Natural cross-multiplication proves it directly;
no positive conditioning event or general real-order decision is required. -/
def weightedMultiply_divide_cancel_of_le (numerator denominator : QProb)
    (dominated : QProb.LE numerator denominator) :
    Equivalent
      (weightedMultiply (some denominator)
        (divide (some numerator) (some denominator)))
      (some numerator) :=
  weightedMultiply_divide_cancel numerator denominator (fun zero => by
    have bound : numerator.num * denominator.den ≤ 0 := by
      simpa only [QProb.LE, zero, Nat.zero_mul] using dominated
    have productZero : numerator.num * denominator.den = 0 :=
      Nat.eq_zero_of_le_zero bound
    exact (Nat.mul_eq_zero.mp productZero).resolve_right
      (Nat.ne_of_gt denominator.den_pos))

/-- Finite marginalization of dominated conditional contributions recovers
the sum of joint masses, including zero conditioning cells.  This is the
chain-algebra identity needed before support-aware marginal compilation;
it is not permission to identify an unsupported causal intervention. -/
noncomputable def weightedSum_divide_cancel_of_le (values : List X)
    (numerator denominator : X -> QProb)
    (dominated : forall value, value ∈ values ->
      QProb.LE (numerator value) (denominator value)) :
    Equivalent
      (weightedSum values (fun value => some (denominator value))
        (fun value => divide (some (numerator value)) (some (denominator value))))
      (sum (values.map (fun value => some (numerator value)))) :=
  sum_map_congr_mem values _ _ (fun value member =>
    weightedMultiply_divide_cancel_of_le (numerator value)
      (denominator value) (dominated value member))

end ProbabilityResult
end Causality
end Thesis
