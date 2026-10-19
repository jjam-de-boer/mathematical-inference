import Thesis.Probability.FiniteRecordCatalogue
import Thesis.Probability.FiniteRecordSupport

namespace Thesis.Probability.FiniteSupportCatalogue

open FiniteProbRecord FiniteRecordCatalogue

/-!
# One actual rational record for every nonempty finite support mask

Enumerate Boolean masks on a declared `Fin card` alphabet. A nonempty mask
receives unit weight at each selected code and zero weight everywhere else.
Its denominator is its number of selected codes. The empty mask is rejected:
there is no invented normalized record on an empty support or alphabet.

Every original finite rational record has one of these representatives with
exactly the same whole-label support, even when it repeats labels, stores
zero weights or has an arbitrarily large unreduced denominator. Uniformizing
support does *not* preserve numerical probabilities. The catalogue is for
support reasoning, not exact observed-law fitting or value comparison.

The construction uses no denominator-bound input, representative choice, or
excluded middle for arbitrary propositions. All decisions inspect finite
Boolean masks and natural total masses.
-/

def unitWeights {card : Nat} (pattern : Fin card → Bool) : Fin card → Nat :=
  fun value => if pattern value then 1 else 0

def patterns (card : Nat) : List (Fin card → Bool) :=
  FiniteProduct.enumeration card (fun _ => Bool) (fun _ => [false, true])

theorem patterns_complete {card : Nat} (pattern : Fin card → Bool) : pattern ∈ patterns card :=
  FiniteProduct.enumeration_mem_of_coordinate_mem _ _ _ pattern
    (fun value => by
      cases pattern value with
      | false => exact List.mem_cons_self
      | true => exact List.mem_cons_of_mem false List.mem_cons_self)

def maskRecord {card : Nat} (pattern : Fin card → Bool) (positive : 0 < mass (unitWeights pattern)) :
    FiniteProbRecord (Fin card) := fromWeights (unitWeights pattern) positive

theorem maskRecord_support {card : Nat} (pattern : Fin card → Bool) (positive : 0 < mass (unitWeights pattern)) :
    (maskRecord pattern positive).support = pattern := by
  funext value
  have cell := eventMass_weightedAtoms_singleton (List.finRange card) (finRange_nodup card) (unitWeights pattern) value
  rw [if_pos (List.mem_finRange value)] at cell
  change decide (0 < eventMass (weightedAtoms (List.finRange card) (unitWeights pattern)) (singletonEvent value)) = pattern value
  rw [cell]
  cases selected : pattern value <;> simp only [unitWeights, selected] <;> decide

def admit {card : Nat} (pattern : Fin card → Bool) : List (FiniteProbRecord (Fin card)) :=
  if positive : 0 < mass (unitWeights pattern) then [maskRecord pattern positive] else []

def catalogue (card : Nat) : List (FiniteProbRecord (Fin card)) := (patterns card).flatMap admit

theorem maskRecord_mem {card : Nat} (pattern : Fin card → Bool) (positive : 0 < mass (unitWeights pattern)) :
    maskRecord pattern positive ∈ catalogue card := by
  apply List.mem_flatMap_of_mem (patterns_complete pattern)
  rw [admit, dif_pos positive]
  exact List.mem_cons_self

/-- Positivity is proved from an original positive atom, but that atom is
used only inside this proposition proof. The output record is determined by
the entire computed support mask, not by a selected atom. -/
theorem original_mask_positive {card : Nat} (original : FiniteProbRecord (Fin card)) :
    0 < mass (unitWeights original.support) := by
  have topPositive : original.EventPositive topEvent := by
    change 0 < eventMass original.atoms topEvent
    rw [eventMass_top, original.total_mass]
    exact original.den_pos
  rcases (eventMass_pos_iff_exists_atom original.atoms topEvent).mp topPositive with
    ⟨atom, listed, positive, _⟩
  have singletonPositive : original.EventPositive (singletonEvent atom.1) :=
    (eventMass_pos_iff_exists_atom original.atoms _).mpr
      ⟨atom, listed, positive, decide_eq_true rfl⟩
  have selected : original.support atom.1 = true := decide_eq_true singletonPositive
  have cell := eventMass_weightedAtoms_singleton (List.finRange card) (finRange_nodup card)
    (unitWeights original.support) atom.1
  rw [if_pos (List.mem_finRange atom.1)] at cell
  have below := eventMass_le_totalMass (weightedAtoms (List.finRange card) (unitWeights original.support))
    (singletonEvent atom.1)
  rw [cell] at below
  change (if original.support atom.1 then 1 else 0) ≤ mass (unitWeights original.support) at below
  rw [selected] at below
  exact below

def uniformSupport {card : Nat} (original : FiniteProbRecord (Fin card)) : FiniteProbRecord (Fin card) :=
  maskRecord original.support (original_mask_positive original)

theorem uniformSupport_support {card : Nat} (original : FiniteProbRecord (Fin card)) :
    (uniformSupport original).support = original.support := maskRecord_support _ _

theorem uniformSupport_mem {card : Nat} (original : FiniteProbRecord (Fin card)) :
    uniformSupport original ∈ catalogue card := maskRecord_mem _ _

def factorCatalogue (count : Nat) (cards : Fin count → Nat) :
    List ((source : Fin count) → FiniteProbRecord (Fin (cards source))) :=
  FiniteProduct.enumeration count (fun source => FiniteProbRecord (Fin (cards source)))
    (fun source => catalogue (cards source))

theorem uniformFactors_mem (count : Nat) (cards : Fin count → Nat)
    (factors : (source : Fin count) → FiniteProbRecord (Fin (cards source))) :
    (fun source => uniformSupport (factors source)) ∈ factorCatalogue count cards :=
  FiniteProduct.enumeration_mem_of_coordinate_mem _ _ _ _ (fun source => uniformSupport_mem (factors source))

theorem empty_alphabet : catalogue 0 = [] := rfl

end Thesis.Probability.FiniteSupportCatalogue
