import Thesis.CausalTransport.HedgeChannelFullCoefficients
import Thesis.Examples.HedgeChannelConstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelFullTerms

open Probability

/-!
# Actual full-term correspondence in the installed bow

The two left full terms use distinct outer-mask slots.  Their matching right
terms use one small slot with, respectively, the empty background mask and
the selected action background.  This checks the new symbolic correspondence
on the actual installer rather than assuming the bow's previously proved
observational equality.

The literal coefficients are 2401 and 343.  Multiplication by the entire
actual shared-prior mass gives 76832 and 10976.  Flipping only the factual
action value negates the latter term on both sides, so the test exercises
the selected background phase as well as the anchored coefficient.

Only this two-node fixture and its thirty-two shared root assignments are
evaluated.  The symbolic theorem below is uniform in its sample, outer slot,
and outside-large mask.  Neither this fixture nor term-by-term equality
replaces the remaining repetition-free reindexing of general survivor sums.
-/

private def signature := HedgeChannelConstruction.signature
private def graph := HedgeChannelConstruction.graph
private def witness := HedgeChannelConstruction.witness
private def rich := HedgeChannelConstruction.rich
private def zeroSignal (_child : Fin signature.count) (_parents : signature.binary.ParentValues _child) : Bool := false

private def emptySlot : Fin (Causality.HedgeChannelInstallation.masks
    (Causality.HedgeChannelInstallation.outer witness)).length := ⟨0, by decide +kernel⟩
private def selectedSlot : Fin (Causality.HedgeChannelInstallation.masks
    (Causality.HedgeChannelInstallation.outer witness)).length := ⟨1, by decide +kernel⟩
private def firstSample : signature.binary.Assignment := fun _ => false
private def secondSample : signature.binary.Assignment := fun child => decide (child.val = 0)

private def leftChoice (index : Fin (Causality.HedgeChannelInstallation.masks
    (Causality.HedgeChannelInstallation.outer witness)).length) :=
  Causality.HedgeChannelInstallation.fullChoice witness witness.large
    (Causality.HedgeChannelInstallation.largeChannel witness index) NodeSet.empty
private def rightChoice (index : Fin (Causality.HedgeChannelInstallation.masks
    (Causality.HedgeChannelInstallation.outer witness)).length) :=
  Causality.HedgeChannelInstallation.fullChoice witness witness.small
    (Causality.HedgeChannelInstallation.smallChannel witness)
    (Causality.HedgeChannelInstallation.combinedBackgroundMask witness index NodeSet.empty)

/-- The explicit combined masks select no small-forest coordinate and
introduce the action background exactly for the second outer-mask slot. -/
theorem combined_mask_bits :
    (forall child, Causality.HedgeChannelInstallation.combinedBackgroundMask witness emptySlot NodeSet.empty child = false) ∧
    (forall child, Causality.HedgeChannelInstallation.combinedBackgroundMask witness selectedSlot NodeSet.empty child =
      decide (child.val = 0)) := by decide +kernel

/-- Uniform use of the new actual integrated-term theorem, without taking
observational equivalence or equality of abstract coefficients as inputs. -/
theorem actual_term_correspondence (sample : signature.binary.Assignment)
    (index : Fin (Causality.HedgeChannelInstallation.masks (Causality.HedgeChannelInstallation.outer witness)).length)
    (mask : NodeSet signature) (subset : NodeSet.Subset mask (Causality.HedgeChannelInstallation.outside witness.large)) :
    Causality.HedgeChannelInstallation.leftTermIntegral witness rich zeroSignal zeroSignal sample
      (Causality.HedgeChannelInstallation.fullChoice witness witness.large
        (Causality.HedgeChannelInstallation.largeChannel witness index) mask) =
    Causality.HedgeChannelInstallation.rightTermIntegral witness zeroSignal zeroSignal sample
      (Causality.HedgeChannelInstallation.fullChoice witness witness.small
        (Causality.HedgeChannelInstallation.smallChannel witness)
        (Causality.HedgeChannelInstallation.combinedBackgroundMask witness index mask)) :=
  Causality.HedgeChannelInstallation.fullTermIntegrals_equal witness rich zeroSignal zeroSignal sample index mask subset

/-- The actual installed row products include the right term's unselected
capacity, not just its small anchored amplitude. -/
theorem actual_coefficient_values :
    HedgeChannelTable.choiceCoefficient (Causality.HedgeChannelInstallation.leftTables witness)
      (fun _ => none) firstSample (leftChoice emptySlot) = 2401 ∧
    HedgeChannelTable.choiceCoefficient (Causality.HedgeChannelInstallation.rightTables witness)
      (fun _ => none) firstSample (rightChoice emptySlot) = 2401 ∧
    HedgeChannelTable.choiceCoefficient (Causality.HedgeChannelInstallation.leftTables witness)
      (fun _ => none) firstSample (leftChoice selectedSlot) = 343 ∧
    HedgeChannelTable.choiceCoefficient (Causality.HedgeChannelInstallation.rightTables witness)
      (fun _ => none) firstSample (rightChoice selectedSlot) = 343 := by decide +kernel

/-- Individual signed integrals retain the whole literal prior.  The
selected outer background changes sign when the factual action bit flips. -/
theorem actual_integral_values :
    Causality.HedgeChannelInstallation.leftTermIntegral witness rich zeroSignal zeroSignal firstSample (leftChoice emptySlot) = 76832 ∧
    Causality.HedgeChannelInstallation.rightTermIntegral witness zeroSignal zeroSignal firstSample (rightChoice emptySlot) = 76832 ∧
    Causality.HedgeChannelInstallation.leftTermIntegral witness rich zeroSignal zeroSignal firstSample (leftChoice selectedSlot) = 10976 ∧
    Causality.HedgeChannelInstallation.rightTermIntegral witness zeroSignal zeroSignal firstSample (rightChoice selectedSlot) = 10976 ∧
    Causality.HedgeChannelInstallation.leftTermIntegral witness rich zeroSignal zeroSignal secondSample (leftChoice selectedSlot) = -10976 ∧
    Causality.HedgeChannelInstallation.rightTermIntegral witness zeroSignal zeroSignal secondSample (rightChoice selectedSlot) = -10976 := by decide +kernel

/-- The reusable anchored-product identity requires no division by an
ordinary amplitude: here that amplitude is zero, but the only selected row
is the supplied anchor and the literal product is still ten. -/
theorem zero_ordinary_anchor_boundary :
    FiniteProduct.natProduct 2 (fun index =>
      if index = (0 : Fin 2) then 2 else if decide (index.val = 0) then 0 else 5) = 10 := by
  have anchored := FiniteProduct.natProduct_binary_mask_anchor 2 0 5 2
    (fun index => decide (index.val = 0)) (0 : Fin 2) rfl
  exact anchored.trans (by decide +kernel)

end HedgeChannelFullTerms
end Examples
end Causality
end Thesis
