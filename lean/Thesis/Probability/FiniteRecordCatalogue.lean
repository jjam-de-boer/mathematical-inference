import Thesis.Probability.FiniteRecordSlicing
import Thesis.Probability.FiniteProductSupport
import Thesis.Probability.FiniteProductExtensional

namespace Thesis.Probability.FiniteRecordCatalogue

/-!
# Exhaustive rational factor records below a declared denominator bound

On `Fin card`, list every natural weight vector with entries at most `bound`.
Keep exactly the vectors whose positive total is at most that same bound,
and construct their normalized finite probability records. Zero-weight cells
remain legal. An empty alphabet or a zero denominator bound has no normalized
record; no default law is invented to fill those cases.

The coverage theorem applies to arbitrary original weighted records, including
repeated labels and explicit zero occurrences. It first aggregates singleton
masses on the declared finite alphabet, without expanding weights into unit
cells. Finite normalization proves that aggregation preserves the original
denominator. Singleton extensionality then proves agreement on every event.
The resulting canonical record is an actual member of the finite catalogue.

This denominator restriction is part of the model class, not a consequence of
source compression. The list may be large and is not an efficient optimizer.
Increasing its bound does not give a stopping rule for unrestricted rational
compatibility or identification. No general excluded middle or choice is used.
-/

open FiniteProbRecord

variable {card : Nat}

def weightedAtoms (values : List X) (weights : X → Nat) : List (X × Nat) :=
  values.map (fun value => (value, weights value))

theorem totalMass_weightedAtoms (values : List X) (weights : X → Nat) :
    totalMass (weightedAtoms values weights) = (values.map weights).sum := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [weightedAtoms, List.map_cons, totalMass, List.sum_cons] at *
      rw [ih]

theorem eventMass_weightedAtoms_singleton [DecidableEq X] (values : List X) (nodup : values.Nodup)
    (weights : X → Nat) (value : X) :
    eventMass (weightedAtoms values weights) (singletonEvent value) =
      if value ∈ values then weights value else 0 := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have parts := List.nodup_cons.mp nodup
      simp only [weightedAtoms, List.map_cons, eventMass, singletonEvent, decide_eq_true_eq]
      change (if head = value then weights head + eventMass (weightedAtoms tail weights) (singletonEvent value)
          else eventMass (weightedAtoms tail weights) (singletonEvent value)) = _
      rw [ih parts.2]
      by_cases same : head = value
      · subst head
        rw [if_pos rfl, if_neg parts.1, if_pos List.mem_cons_self, Nat.add_zero]
      · rw [if_neg same]
        simp only [List.mem_cons, Ne.symm same, false_or]

def mass (weights : Fin card → Nat) : Nat := totalMass (weightedAtoms (List.finRange card) weights)

def fromWeights (weights : Fin card → Nat) (positive : 0 < mass weights) : FiniteProbRecord (Fin card) where
  atoms := weightedAtoms (List.finRange card) weights
  den := mass weights
  den_pos := positive
  total_mass := rfl

/-- Every local vector is explicitly bounded, before normalization is tested. -/
def weightVectors (card bound : Nat) : List (Fin card → Nat) :=
  FiniteProduct.enumeration card (fun _ => Nat) (fun _ => List.range (bound + 1))

theorem weightVectors_complete (weights : Fin card → Nat) (bound : Nat) (bounded : ∀ value, weights value ≤ bound) :
    weights ∈ weightVectors card bound :=
  FiniteProduct.enumeration_mem_of_coordinate_mem _ _ _ weights
    (fun value => List.mem_range.mpr (Nat.lt_succ_of_le (bounded value)))

def admitWeights (bound : Nat) (weights : Fin card → Nat) : List (FiniteProbRecord (Fin card)) :=
  if valid : 0 < mass weights ∧ mass weights ≤ bound then [fromWeights weights valid.1] else []

def catalogue (card bound : Nat) : List (FiniteProbRecord (Fin card)) :=
  (weightVectors card bound).flatMap (admitWeights bound)

theorem mem_catalogue_den_le (record : FiniteProbRecord (Fin card)) (bound : Nat)
    (listed : record ∈ catalogue card bound) : record.den ≤ bound := by
  rcases List.mem_flatMap.mp listed with ⟨weights, _, admitted⟩
  by_cases valid : 0 < mass weights ∧ mass weights ≤ bound
  · rw [admitWeights, dif_pos valid] at admitted
    rcases List.mem_cons.mp admitted with same | impossible
    · subst record
      exact valid.2
    · exact False.elim (List.not_mem_nil impossible)
  · rw [admitWeights, dif_neg valid] at admitted
    exact False.elim (List.not_mem_nil admitted)

def cellMasses (original : FiniteProbRecord (Fin card)) : Fin card → Nat :=
  fun value => eventMass original.atoms (singletonEvent value)

/-- Aggregation counts every old occurrence, but retains just one weighted
cell per declared code. In particular, it does not enlarge the denominator. -/
theorem mass_cellMasses (original : FiniteProbRecord (Fin card)) : mass (cellMasses original) = original.den := by
  rw [mass, totalMass_weightedAtoms]
  exact original.sum_singletonMass_eq_den (List.finRange card) (finRange_nodup card) List.mem_finRange

def canonical (original : FiniteProbRecord (Fin card)) : FiniteProbRecord (Fin card) :=
  fromWeights (cellMasses original) (by rw [mass_cellMasses]; exact original.den_pos)

theorem canonical_den (original : FiniteProbRecord (Fin card)) : (canonical original).den = original.den :=
  mass_cellMasses original

theorem canonical_probVal (original : FiniteProbRecord (Fin card)) (event : Event (Fin card)) :
    QProb.Equiv ((canonical original).probVal event) (original.probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _ (List.finRange card)
    (finRange_nodup card) List.mem_finRange (fun value => ?_) event
  change eventMass (weightedAtoms (List.finRange card) (cellMasses original)) (singletonEvent value) * original.den =
    eventMass original.atoms (singletonEvent value) * mass (cellMasses original)
  rw [eventMass_weightedAtoms_singleton _ (finRange_nodup card), if_pos (List.mem_finRange value), mass_cellMasses]
  rfl

theorem canonical_mem (original : FiniteProbRecord (Fin card)) (bound : Nat) (bounded : original.den ≤ bound) :
    canonical original ∈ catalogue card bound := by
  have weightsBounded (value : Fin card) : cellMasses original value ≤ bound := by
    have below := eventMass_le_totalMass original.atoms (singletonEvent value)
    rw [original.total_mass] at below
    exact Nat.le_trans below bounded
  have valid : 0 < mass (cellMasses original) ∧ mass (cellMasses original) ≤ bound := by
    rw [mass_cellMasses]
    exact ⟨original.den_pos, bounded⟩
  apply List.mem_flatMap_of_mem (weightVectors_complete (cellMasses original) bound weightsBounded)
  rw [admitWeights, dif_pos valid]
  exact List.mem_cons_self

/-- A literal dependent catalogue of independent factor choices. The empty
source family has its single empty choice even when the denominator bound is
zero; a nonempty family with an impossible local law has no choice. -/
def factorCatalogue (count : Nat) (cards : Fin count → Nat) (bound : Nat) :
    List ((source : Fin count) → FiniteProbRecord (Fin (cards source))) :=
  FiniteProduct.enumeration count (fun source => FiniteProbRecord (Fin (cards source)))
    (fun source => catalogue (cards source) bound)

theorem canonicalFactors_mem (count : Nat) (cards : Fin count → Nat)
    (factors : (source : Fin count) → FiniteProbRecord (Fin (cards source)))
    (bound : Nat) (bounded : ∀ source, (factors source).den ≤ bound) :
    (fun source => canonical (factors source)) ∈ factorCatalogue count cards bound :=
  FiniteProduct.enumeration_mem_of_coordinate_mem _ _ _ _
    (fun source => canonical_mem (factors source) bound (bounded source))

theorem factorCatalogue_den_le (count : Nat) (cards : Fin count → Nat)
    (factors : (source : Fin count) → FiniteProbRecord (Fin (cards source)))
    (bound : Nat) (listed : factors ∈ factorCatalogue count cards bound) (source : Fin count) :
    (factors source).den ≤ bound :=
  mem_catalogue_den_le (factors source) bound
    (FiniteProduct.enumeration_coordinate_mem _ _ _ _ listed source)

/-- Replacing every factor by its aggregated canonical record preserves the
whole independent product law, not just the individual source marginals. -/
theorem canonicalProduct_probVal (count : Nat) (cards : Fin count → Nat)
    (factors : (source : Fin count) → FiniteProbRecord (Fin (cards source)))
    (event : Event ((source : Fin count) → Fin (cards source))) :
    QProb.Equiv
      ((FiniteProduct.record count _ (fun source => canonical (factors source))).probVal event)
      ((FiniteProduct.record count _ factors).probVal event) := by
  apply FiniteProduct.probVal_extensional_of_rectangles _ _
    (fun source => List.finRange (cards source)) (fun _ value => List.mem_finRange value)
    (fun _ => inferInstance) (fun events => ?_) event
  exact QProb.equiv_trans (FiniteProduct.record_rectangular_probVal _ _ _ events)
    (QProb.equiv_trans (FiniteProduct.qProduct_congr count
      (fun source => canonical_probVal (factors source) (events source)))
      (QProb.equiv_symm (FiniteProduct.record_rectangular_probVal _ _ _ events)))

end Thesis.Probability.FiniteRecordCatalogue
