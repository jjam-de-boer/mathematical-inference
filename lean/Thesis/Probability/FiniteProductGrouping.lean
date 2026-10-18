import Thesis.Probability.FiniteFunctionTables
import Thesis.Probability.FiniteProductExtensional
import Thesis.Probability.FiniteProductResponse

namespace Thesis.Probability.FiniteProductGrouping

/-!
# Group independent finite sources by an explicit ownership map

Each old source belongs to exactly one supplied group. A group's value is
the dependent product of its owned coordinates. Unowned coordinates are
functions from an impossible equality proof, not extra copies of a random
source and not missing values filled by choice. Empty groups therefore have
their unique vacuous value. The displayed encoding and decoding are inverse
on every typed assignment, not just on positive-probability samples.

Construct each block's actual product factor and the outer independent
product of those factors. Its decoded rectangular probabilities follow by
exchanging the two finite products: every old factor occurs exactly once,
and every unowned slot contributes probability one. Finite extensionality
then preserves every old event against any prior satisfying the original
product law, including mixed events, zeros and repeated atom labels.

This probability-only construction does not infer a grouping map from a
causal graph. The later clique-root adapter must construct that map, justify
all root incidences and prove the corresponding structural evaluator law.
-/

universe u
variable {count groups : Nat} {Value : Fin count → Type u}

abbrev Block (Value : Fin count → Type u) (owner : Fin count → Fin groups) (group : Fin groups) :=
  (source : Fin count) → owner source = group → Value source

abbrev GroupedAssignment (Value : Fin count → Type u) (owner : Fin count → Fin groups) :=
  (group : Fin groups) → Block Value owner group

def encode (owner : Fin count → Fin groups) (sample : FiniteProduct.Assignment count Value) : GroupedAssignment Value owner :=
  fun _ source _ => sample source

def decode (owner : Fin count → Fin groups) (blocks : GroupedAssignment Value owner) : FiniteProduct.Assignment count Value :=
  fun source => blocks (owner source) source rfl

theorem decode_encode (owner : Fin count → Fin groups) (sample : FiniteProduct.Assignment count Value) :
    decode owner (encode owner sample) = sample := rfl

/-- Total typed block values already exclude spurious coordinates. The
inverse uses equality elimination and proof irrelevance, not noise defaults. -/
theorem encode_decode (owner : Fin count → Fin groups) (blocks : GroupedAssignment Value owner) :
    encode owner (decode owner blocks) = blocks := by
  funext group source owned
  cases owned
  rfl

def blockEnumeration (owner : Fin count → Fin groups) (values : (source : Fin count) → List (Value source))
    (group : Fin groups) : List (Block Value owner group) :=
  FiniteProduct.enumeration count (fun source => owner source = group → Value source)
    (fun source => ProofFunction.enumeration (owner source = group) (values source))

theorem blockEnumeration_complete (owner : Fin count → Fin groups) (values : (source : Fin count) → List (Value source))
    (complete : ∀ source value, value ∈ values source) (group : Fin groups) (block : Block Value owner group) :
    block ∈ blockEnumeration owner values group :=
  FiniteProduct.enumeration_complete _ _ _ (fun source => ProofFunction.enumeration_complete _ _ (complete source)) block

def blockDecidableEq (owner : Fin count → Fin groups) (decEq : (source : Fin count) → DecidableEq (Value source))
    (group : Fin groups) : DecidableEq (Block Value owner group) :=
  FiniteProduct.assignmentDecidableEq count (fun source => owner source = group → Value source)
    (fun source => by
      letI : DecidableEq (Value source) := decEq source
      exact ProofFunction.decidableEq (owner source = group))

private def vacantSlot (owner : Fin count → Fin groups) (source : Fin count) (group : Fin groups)
    (absent : owner source ≠ group) : FiniteProbRecord (owner source = group → Value source) where
  atoms := [(fun impossible => False.elim (absent impossible), 1)]
  den := 1
  den_pos := Nat.zero_lt_one
  total_mass := rfl

/-- One original factor is installed at its owner only. A nonowner slot
has a genuine normalized deterministic record on its vacuous function type. -/
def slotFactor (owner : Fin count → Fin groups) (factors : (source : Fin count) → FiniteProbRecord (Value source))
    (group : Fin groups) (source : Fin count) : FiniteProbRecord (owner source = group → Value source) :=
  if owned : owner source = group then
    (factors source).map (fun value _ => value)
  else vacantSlot owner source group owned

def factor (owner : Fin count → Fin groups) (factors : (source : Fin count) → FiniteProbRecord (Value source))
    (group : Fin groups) : FiniteProbRecord (Block Value owner group) :=
  FiniteProduct.record count (fun source => owner source = group → Value source) (slotFactor owner factors group)

def prior (owner : Fin count → Fin groups) (factors : (source : Fin count) → FiniteProbRecord (Value source)) :
    FiniteProbRecord (GroupedAssignment Value owner) :=
  FiniteProduct.record groups (Block Value owner) (factor owner factors)

theorem product_law (owner : Fin count → Fin groups) (factors : (source : Fin count) → FiniteProbRecord (Value source))
    (events : (group : Fin groups) → Event (Block Value owner group)) :
    QProb.Equiv ((prior owner factors).probVal (FiniteProduct.rectangularEvent groups (Block Value owner) events))
      (FiniteProduct.qProduct groups (fun group => (factor owner factors group).probVal (events group))) :=
  FiniteProduct.record_rectangular_probVal groups (Block Value owner) (factor owner factors) events

/-- A block tests only its owned events. Every other slot is unconstrained,
so its probability is one without a positive-cell or cancellation premise. -/
def slotEvent (owner : Fin count → Fin groups) (events : (source : Fin count) → Event (Value source))
    (group : Fin groups) (source : Fin count) : Event (owner source = group → Value source) :=
  if owned : owner source = group then fun input => events source (input owned) else fun _ => true

theorem slotFactor_event (owner : Fin count → Fin groups) (factors : (source : Fin count) → FiniteProbRecord (Value source))
    (events : (source : Fin count) → Event (Value source)) (group : Fin groups) (source : Fin count) :
    QProb.Equiv ((slotFactor owner factors group source).probVal (slotEvent owner events group source))
      (if owner source = group then (factors source).probVal (events source) else QProb.one) := by
  by_cases owned : owner source = group
  · rw [slotFactor, dif_pos owned, slotEvent, dif_pos owned, if_pos owned]
    exact (factors source).map_probVal (fun value _ => value) (fun input => events source (input owned))
  · rw [slotEvent, dif_neg owned, if_neg owned]
    exact (slotFactor owner factors group source).normalization

theorem factor_rectangular_probVal (owner : Fin count → Fin groups) (factors : (source : Fin count) → FiniteProbRecord (Value source))
    (events : (source : Fin count) → Event (Value source)) (group : Fin groups) :
    QProb.Equiv ((factor owner factors group).probVal
      (FiniteProduct.rectangularEvent count (fun source => owner source = group → Value source) (slotEvent owner events group)))
      (FiniteProduct.qProduct count (fun source => if owner source = group then (factors source).probVal (events source) else QProb.one)) :=
  QProb.equiv_trans (FiniteProduct.record_rectangular_probVal _ _ _ _)
    (FiniteProduct.qProduct_congr count (slotFactor_event owner factors events group))

theorem rectangular_decode (owner : Fin count → Fin groups) (events : (source : Fin count) → Event (Value source))
    (blocks : GroupedAssignment Value owner) :
    FiniteProduct.rectangularEvent groups (Block Value owner)
      (fun group => FiniteProduct.rectangularEvent count (fun source => owner source = group → Value source)
        (slotEvent owner events group)) blocks =
      FiniteProduct.rectangularEvent count Value events (decode owner blocks) := by
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro all source
    simpa only [slotEvent, dif_pos rfl, decode] using all (owner source) source
  · intro all group source
    by_cases owned : owner source = group
    · subst group
      simpa only [slotEvent, dif_pos rfl, decode] using all source
    · simp only [slotEvent, dif_neg owned]

private theorem qProduct_atOwner (total : Nat) (chosen : Fin total) (value : QProb) :
    QProb.Equiv (FiniteProduct.qProduct total (fun group => if chosen = group then value else QProb.one)) value := by
  have same : (fun group : Fin total => if chosen = group then value else QProb.one) =
      (fun group => if group = chosen then value else QProb.one) := by
    funext group
    by_cases owned : chosen = group
    · subst group
      rfl
    · rw [if_neg owned, if_neg (Ne.symm owned)]
  rw [same]
  exact FiniteProduct.qProduct_singleton total chosen value

/-- Full rectangular preservation follows by finite product exchange, not
by treating independence of individual coordinate marginals as sufficient. -/
theorem decoded_rectangular_probVal (owner : Fin count → Fin groups)
    (factors : (source : Fin count) → FiniteProbRecord (Value source))
    (events : (source : Fin count) → Event (Value source)) :
    QProb.Equiv ((prior owner factors).probVal
      (fun blocks => FiniteProduct.rectangularEvent count Value events (decode owner blocks)))
      (FiniteProduct.qProduct count (fun source => (factors source).probVal (events source))) := by
  let rows := fun group => FiniteProduct.rectangularEvent count
    (fun source => owner source = group → Value source) (slotEvent owner events group)
  have reindexed := (prior owner factors).probVal_congr _ _ (rectangular_decode owner events)
  have outer := product_law owner factors rows
  have inner := FiniteProduct.qProduct_congr groups (factor_rectangular_probVal owner factors events)
  have exchanged := FiniteProduct.qProduct_exchange groups count
    (fun group source => if owner source = group then (factors source).probVal (events source) else QProb.one)
  have columns := FiniteProduct.qProduct_congr count (fun source =>
    qProduct_atOwner groups (owner source) ((factors source).probVal (events source)))
  exact QProb.equiv_trans (QProb.equiv_symm reindexed)
    (QProb.equiv_trans outer (QProb.equiv_trans inner (QProb.equiv_trans exchanged columns)))

/-- Compare with any old independent prior, not only the canonical product.
Complete old-coordinate lists are used for finite extensionality; the record
need not be positive, duplicate-free, or literally equal to that product. -/
theorem decoded_probVal (owner : Fin count → Fin groups)
    (factors : (source : Fin count) → FiniteProbRecord (Value source))
    (original : FiniteProbRecord (FiniteProduct.Assignment count Value))
    (independent : ∀ events, QProb.Equiv (original.probVal (FiniteProduct.rectangularEvent count Value events))
      (FiniteProduct.qProduct count (fun source => (factors source).probVal (events source))))
    (values : (source : Fin count) → List (Value source)) (complete : ∀ source value, value ∈ values source)
    (decEq : (source : Fin count) → DecidableEq (Value source)) (event : Event (FiniteProduct.Assignment count Value)) :
    QProb.Equiv ((prior owner factors).probVal (fun blocks => event (decode owner blocks))) (original.probVal event) := by
  let decoded := (prior owner factors).map (decode owner)
  have rectangles events : QProb.Equiv (decoded.probVal (FiniteProduct.rectangularEvent count Value events))
      (original.probVal (FiniteProduct.rectangularEvent count Value events)) :=
    QProb.equiv_trans ((prior owner factors).map_probVal (decode owner) _)
      (QProb.equiv_trans (decoded_rectangular_probVal owner factors events) (QProb.equiv_symm (independent events)))
  exact QProb.equiv_trans (QProb.equiv_symm ((prior owner factors).map_probVal (decode owner) event))
    (FiniteProduct.probVal_extensional_of_rectangles decoded original values complete decEq rectangles event)

end Thesis.Probability.FiniteProductGrouping
