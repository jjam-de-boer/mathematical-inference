import Thesis.CausalTransport.HedgeNoise
import Thesis.Examples.KernelFailureExtraction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgePrivateNoise

open Probability

/-!
# Regression checks for finite biased hedge noise

The numerical checks distinguish support from injectivity.  Independent fair
noise gives both outputs support but destroys a deterministic signal gap;
biased noise retains that gap, even after several flips and with unequal input
denominators.  The third observed value in the carrier example also receives
positive mass: these support theorems do not merely embed a binary model and
leave the remaining alphabet impossible.

The final regression applies the generic noise theorem to the actual hedge
extracted from a corrected-engine failure.  It retains the original action
and accepts any finite flip count.  As in the implementation, this tests an
interventional root signal, not a completed original-outcome countermodel.
-/

/-! ## Deterministic signals retain a gap after arbitrarily many biased flips -/

def constantSignal (bit : Bool) : FiniteProbRecord Bool :=
  ⟨[(bit, 1)], 1, by decide, rfl⟩

def noise (count : Nat) : FiniteProbRecord Bool :=
  FiniteProbRecord.biasedFlipParity 1 1 (by decide) count

theorem constants_separated :
    Not (QProb.Equiv ((constantSignal false).probVal id) ((constantSignal true).probVal id)) := by decide +kernel

/-- The gap theorem is uniform in the route length; no bounded list of
length-specific separation proofs is supplied to the implementation. -/
theorem constants_noisy_separated (count : Nat) :
    Not (QProb.Equiv
      (((constantSignal false).xorChannel id (noise count)).probVal id)
      (((constantSignal true).xorChannel id (noise count)).probVal id)) :=
  FiniteProbRecord.xorChannel_biasedFlipParity_not_equiv _ _ _ _ 1 1 (by decide) count constants_separated

/-- Four independent one-third flips have odd mass forty and even mass
forty-one on denominator eighty-one.  The gap is small but exactly nonzero. -/
theorem four_flips_odd_mass : FiniteProbRecord.eventMass (noise 4).atoms id = 40 := by decide +kernel
theorem four_flips_even_mass : FiniteProbRecord.eventMass (noise 4).atoms (fun bit => !bit) = 41 := by decide +kernel
theorem four_flips_den : (noise 4).den = 81 := by decide +kernel

/-- A nonempty finite flip family gives both outputs positive support even
when the input signal is a point mass. -/
theorem deterministic_noisy_positive (count : Nat) (input output : Bool) :
    ((constantSignal input).xorChannel id (noise (count + 1))).EventPositive
      (FiniteProbRecord.singletonEvent output) :=
  FiniteProbRecord.xorChannel_biasedFlipParity_positive _ _ 1 1 (by decide) (by decide) count output

/-! ## Different input denominators and the zero-noise boundary -/

def oneThirdSignal : FiniteProbRecord Bool :=
  ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩

theorem unequal_denominators_separated (count : Nat) :
    Not (QProb.Equiv
      (((constantSignal false).xorChannel id (noise count)).probVal id)
      ((oneThirdSignal.xorChannel id (noise count)).probVal id)) :=
  FiniteProbRecord.xorChannel_biasedFlipParity_not_equiv _ _ _ _ 1 1 (by decide) count (by decide +kernel)

/-- Zero coins keep a one-sided input one-sided.  Positivity is intentionally
stated only for a nonempty flip family, while separation includes this case. -/
theorem zero_flips_no_odd_support :
    FiniteProbRecord.eventMass ((constantSignal false).xorChannel id (noise 0)).atoms id = 0 := by decide +kernel

/-! ## Fair private noise is an invalid separator despite its full support -/

def fairNoise : FiniteProbRecord Bool :=
  ⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩

theorem fair_noise_erases_gap : QProb.Equiv
    (((constantSignal false).xorChannel id fairNoise).probVal id)
    (((constantSignal true).xorChannel id fairNoise).probVal id) :=
  FiniteProbRecord.xorChannel_probVal_equiv_of_balanced _ _ _ _ fairNoise (by decide +kernel)

/-! ## Full support includes values beyond the two parity labels -/

def ternarySignature : ObservedSignature where
  count := 1
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def ternaryRich : ObservedSignature.ValueRich ternarySignature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

def child : Fin ternarySignature.count := ⟨0, by decide⟩

def background : FiniteProbRecord (ternarySignature.Value child) :=
  ⟨[(⟨0, by decide⟩, 1), (⟨1, by decide⟩, 1), (⟨2, by decide⟩, 1)], 3, by decide, rfl⟩

theorem background_positive : forall value,
    background.EventPositive (FiniteProbRecord.singletonEvent value) := by
  intro value
  refine Fin.cases (by decide) (fun remaining => ?_) value
  refine Fin.cases (by decide) (fun last => ?_) remaining
  exact Fin.cases (by decide) (fun empty => Fin.elim0 empty) last

/-- Every ternary value, including label two outside the Boolean encoding,
remains possible after any nonempty finite biased flip family. -/
theorem ternary_carrier_positive (count : Nat) (value : ternarySignature.Value child) :
    (hedgeNoisyCarrierDistribution ternaryRich child (constantSignal false) id
      (noise (count + 1)) background).EventPositive (FiniteProbRecord.singletonEvent value) :=
  hedgeNoisyCarrierDistribution_biasedFlipParity_positive ternaryRich child _ _
    1 1 (by decide) (by decide) count background background_positive value

/-! ## Noise transport of an actual corrected-engine hedge's root signal -/

open CurrentKernelFailureExtraction

def immediateRich : ObservedSignature.ValueRich immediateSignature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := fun _ => List.mem_cons_self
  second_enumerated := fun _ => List.mem_cons.mpr (Or.inr List.mem_cons_self)
  different := fun _ => Bool.false_ne_true

/-- The existing general positive countermodel supplies the signal gap; the
new noise theorem preserves it for any chosen finite noise count. -/
theorem extracted_hedge_noisy_separated (count : Nat) :
    Not (QProb.Equiv
      (((immediateExtraction.witness.largeCarrierDefectParityModel immediateRich).noisyInterventionalSignal
        (hedgeDoSecond immediateRich immediateQuery.action)
        (hedgeRootParityEvent immediateRich immediateExtraction.witness.roots) (noise count)).probVal id)
      (((immediateExtraction.witness.smallCarrierDefectParityModel immediateRich).noisyInterventionalSignal
        (hedgeDoSecond immediateRich immediateQuery.action)
        (hedgeRootParityEvent immediateRich immediateExtraction.witness.roots) (noise count)).probVal id)) :=
  immediateExtraction.witness.carrierDefectRootParity_noisy_not_equiv immediateRich 1 1 (by decide) count

end HedgePrivateNoise
end Examples
end Causality
end Thesis
