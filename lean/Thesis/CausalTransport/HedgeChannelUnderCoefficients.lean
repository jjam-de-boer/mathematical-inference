import Thesis.CausalTransport.HedgeChannelInstallation

namespace Thesis
namespace Causality

open Probability

/-!
# Actual scalar coefficients after a hard intervention

The routed character sum is nonnegative, but its actual monomial also has
row coefficients.  Those coefficients cannot be dropped or declared constant
on samples conflicting with the intervention.  This module separates the two
cases exactly.

For a consistent sample, each forced row contributes its literal indicator
one at the sole permitted choice.  Free rows retain the table's capacity or
chosen channel amplitude.  Their product is an explicitly defined natural
scalar, independent of the consistent sample.  A conflict instead gives
coefficient zero, regardless of the other rows or their character signs.

The scalar is strictly positive when the support test permits the choice and
every actually selected free-channel amplitude is positive.  The installed
power tables discharge that amplitude obligation automatically.  All these
facts concern the existing complete coefficient, not a substitute likelihood
or an assumed positive projected gap.
-/

namespace HedgeChannelTable

variable {S : ObservedSignature.{0}} {channels : Nat}

/-- The literal natural scalar on a sample consistent with the target.
A forced row contributes one only at `none`; unsupported channels remain
zero.  No denominator or row capacity is cancelled by this definition. -/
def choiceScalarUnder (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (choice : Fin S.count -> Option (Fin channels)) : Nat :=
  FiniteProduct.natProduct S.count (fun child =>
    match target child with
    | none => match choice child with
      | none => (tables child).capacity
      | some channel => (tables child).amplitude channel
    | some _ => match choice child with | none => 1 | some _ => 0)

/-- Equality with the actual coefficient holds on every supplied consistent
sample.  Unsupported forced channels still contribute zero on
both sides; support membership is not assumed for this equality. -/
theorem choiceCoefficient_eq_scalar_of_consistent
    (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (consistent : forall child fixed, target child = some fixed -> sample child = fixed) :
    choiceCoefficient tables target sample choice = (choiceScalarUnder tables target choice : Int) := by
  unfold choiceCoefficient choiceScalarUnder
  refine (FiniteProduct.iProduct_congr S.count _ _ ?_).trans (FiniteProduct.iProduct_nat S.count _)
  intro child
  cases forced : target child with
  | none => cases choice child <;> rfl
  | some fixed =>
      have equal := (consistent child fixed forced).symm
      cases choice child <;>
        simp only [BooleanChannelTable.expansionCoefficientUnder, equal, if_true,
          Int.natCast_one, Int.natCast_zero]

/-- One conflicting forced value zeros the complete coefficient.  No
positivity, actual-choice membership or division by another row is needed. -/
theorem choiceCoefficient_zero_of_conflict
    (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels)) (child : Fin S.count) (fixed : Bool)
    (forced : target child = some fixed) (conflict : sample child ≠ fixed) :
    choiceCoefficient tables target sample choice = 0 := by
  apply FiniteProduct.iProduct_eq_zero S.count _ child
  have different : fixed ≠ sample child := fun equal => conflict equal.symm
  change (tables child).expansionCoefficientUnder (target child) (sample child) (choice child) = 0
  rw [forced]
  cases choice child with
  | none => exact if_neg different
      | some _channel => rfl

/-- Only forced observed coordinates can affect an interventional row
coefficient.  Agreement at those coordinates preserves the complete scalar,
including every zero consistency indicator and unsupported forced choice.
No assumption that either sample is intervention-consistent is required. -/
theorem choiceCoefficient_congr_on_forced
    (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (first second : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (agree : forall child fixed, target child = some fixed -> first child = second child) :
    choiceCoefficient tables target first choice = choiceCoefficient tables target second choice := by
  unfold choiceCoefficient
  apply FiniteProduct.iProduct_congr S.count
  intro child
  cases forced : target child with
  | none => cases choice child <;> rfl
  | some fixed =>
      cases choice child <;>
        simp only [BooleanChannelTable.expansionCoefficientUnder, agree child fixed forced]

/-- The actual support test forces the indicator choice at every forced
row.  This is a finite Boolean test, not a classical semantic decision. -/
theorem choiceAllowedUnder_forced_none (target : Fin S.count -> Option Bool)
    (choice : Fin S.count -> Option (Fin channels)) (allowed : choiceAllowedUnder target choice = true)
    (child : Fin S.count) (fixed : Bool) (forced : target child = some fixed) : choice child = none := by
  have tested := (List.all_eq_true.mp allowed) child (List.mem_finRange child)
  change (match target child with | none => true | some _ => decide (choice child = none)) = true at tested
  rw [forced] at tested
  exact of_decide_eq_true tested

/-- Actual permitted choices have a strictly positive consistent-sample
scalar when their selected amplitudes are positive.  Unselected channels
may have zero amplitude; they are not an unnecessary global hypothesis. -/
theorem choiceScalarUnder_positive_of_allowed
    (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (choice : Fin S.count -> Option (Fin channels))
    (allowed : choiceAllowedUnder target choice = true)
    (positive : forall child channel, choice child = some channel -> 0 < (tables child).amplitude channel) :
    0 < choiceScalarUnder tables target choice := by
  apply FiniteProduct.natProduct_positive
  intro child
  cases forced : target child with
  | none =>
      cases picked : choice child with
      | none => exact (tables child).capacity_positive
      | some channel => exact positive child channel picked
  | some fixed =>
      rw [choiceAllowedUnder_forced_none target choice allowed child fixed forced]
      exact Nat.zero_lt_one

end HedgeChannelTable

namespace HedgeChannelCoefficients

variable {S : ObservedSignature.{0}}

/-- Every amplitude in a power table is explicitly positive, including
inactive slots.  The actual channel list separately decides which slots may
be selected at a row; no source slot is deleted to prove positivity. -/
theorem tables_amplitude_positive (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (child : Fin S.count) (channel : Fin channels) :
    0 < (tables channels bound nodes anchors deficits child).amplitude channel :=
  Nat.pow_pos (scale_positive channels)

/-- The installed power construction supplies positive actual scalars
after arbitrary hard cuts, whenever the finite choice-support test passes. -/
theorem tables_choiceScalarUnder_positive (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (target : Fin S.count -> Option Bool) (choice : Fin S.count -> Option (Fin channels))
    (allowed : HedgeChannelTable.choiceAllowedUnder target choice = true) :
    0 < HedgeChannelTable.choiceScalarUnder (tables channels bound nodes anchors deficits) target choice :=
  HedgeChannelTable.choiceScalarUnder_positive_of_allowed _ target choice allowed
    (fun child channel _picked => tables_amplitude_positive channels bound nodes anchors deficits child channel)

end HedgeChannelCoefficients
end Causality
end Thesis
