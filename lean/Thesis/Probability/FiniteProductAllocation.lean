import Thesis.Probability.FiniteProductResponse

namespace Thesis
namespace Probability

/-!
# Allocate one finite random channel to one optional coordinate

An allocated channel is sampled at its unique owner.  Every other coordinate
is deterministic absence, not an independent copy of that random value.
An unallocated channel is absent everywhere and its original law integrates
out by normalization.  The optional owner also handles an empty coordinate
family without choosing a default index.

The rectangular law below compares the actual independent coordinate factors
with the explicit encoding of one supplied original value.  It holds for
arbitrary Boolean coordinate events, finite records with repeated labels,
zero-weight atoms and zero event probabilities.  The proof isolates the one
nonconstant factor and treats the remaining absence checks as a Boolean gate;
it never divides by their probabilities.
-/

namespace FiniteProductAllocation

universe u

/-- Deterministic absence uses an actual singleton atom of unit weight.
No value of the original alphabet is required or selected. -/
def absentChannel (Value : Type u) : FiniteProbRecord (Option Value) where
  atoms := [(none, 1)]
  den := 1
  den_pos := Nat.zero_lt_one
  total_mass := rfl

/-- The original factor is installed once, at its optional owner. -/
def channelFactor {Value : Type u} {count : Nat} (record : FiniteProbRecord Value)
    (owner : Option (Fin count)) (index : Fin count) : FiniteProbRecord (Option Value) :=
  if owner = some index then record.map some else absentChannel Value

/-- Encode one original value as a present owner slot and absent other
slots.  An unused channel has no selected owner, including at count zero. -/
def encode {Value : Type u} {count : Nat} (owner : Option (Fin count))
    (value : Value) : Fin count → Option Value :=
  fun index => if owner = some index then some value else none

/-- A deterministic absence factor evaluates a Boolean event exactly as
the corresponding unit-or-zero indicator. -/
theorem absentChannel_probVal {Value : Type u} (event : Option Value → Bool) :
    QProb.Equiv ((absentChannel Value).probVal event)
      (if event none then QProb.one else QProb.zero) := by
  cases checked : event none <;>
    simp [absentChannel, FiniteProbRecord.probVal, FiniteProbRecord.eventMass,
      QProb.Equiv, QProb.one, QProb.zero, checked]

/-- A product of deterministic Boolean checks is the indicator of their
finite conjunction.  This includes the empty conjunction, whose mass is one. -/
theorem qProduct_indicator (count : Nat) (checks : Fin count → Bool) :
    QProb.Equiv
      (FiniteProduct.qProduct count (fun index => if checks index then QProb.one else QProb.zero))
      (if finAll count checks then QProb.one else QProb.zero) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      have prefixLaw := inductionHypothesis (fun index => checks index.castSucc)
      exact QProb.equiv_trans
        (QProb.mul_congr (QProb.equiv_refl _) prefixLaw)
        (by
          cases lastCheck : checks (Fin.last count) <;>
            cases prefixCheck : finAll count (fun index => checks index.castSucc) <;>
            simp [finAll, QProb.Equiv, QProb.mul, QProb.one, QProb.zero, lastCheck, prefixCheck])

/-- A constant Boolean event has unit or zero mass.  In particular, an
unused original factor disappears by its genuine normalization theorem. -/
private theorem probVal_constant {Value : Type u} (record : FiniteProbRecord Value)
    (check : Bool) : QProb.Equiv (record.probVal (fun _ => check))
      (if check then QProb.one else QProb.zero) := by
  cases check with
  | false => exact record.probVal_false
  | true => exact record.normalization

/-- Gate an arbitrary original event by a constant Boolean check.  The
gate may be false; no support premise is needed to factor it out. -/
private theorem probVal_and_constant {Value : Type u} (record : FiniteProbRecord Value)
    (event : Value → Bool) (check : Bool) :
    QProb.Equiv (record.probVal (fun value => event value && check))
      (QProb.mul (record.probVal event) (if check then QProb.one else QProb.zero)) := by
  cases check with
  | false =>
      exact QProb.equiv_trans
        (record.probVal_congr _ (fun _ => false) (fun _ => Bool.and_false _))
        (QProb.equiv_trans record.probVal_false
          (by simp [QProb.Equiv, QProb.mul, QProb.zero]))
  | true =>
      exact QProb.equiv_trans
        (record.probVal_congr _ event (fun _ => Bool.and_true _))
        (QProb.equiv_symm (QProb.mul_one _))

/-- At a selected owner, the encoded conjunction consists of its original
random event and the constant absence checks at every other coordinate.
Finite equality splits are constructive and do not decide arbitrary Props. -/
private theorem rectangularEvent_encode_some {Value : Type u} {count : Nat}
    (owner : Fin count) (events : Fin count → Option Value → Bool) (value : Value) :
    FiniteProduct.rectangularEvent count (fun _ => Option Value) events (encode (some owner) value) =
      (events owner (some value) &&
        finAll count (fun index => if index = owner then true else events index none)) := by
  apply Bool.eq_iff_iff.mpr
  rw [FiniteProduct.rectangularEvent_eq_true_iff, Bool.and_eq_true_iff, finAll_eq_true_iff]
  constructor
  · intro all
    constructor
    · simpa only [encode, if_pos rfl] using all owner
    · intro index
      by_cases same : index = owner
      · simp only [if_pos same]
      · have different : some owner ≠ some index := fun equal => same (Option.some.inj equal).symm
        simpa only [encode, if_neg different, if_neg same] using all index
  · rintro ⟨atOwner, away⟩ index
    by_cases same : index = owner
    · subst index
      simpa only [encode, if_pos rfl] using atOwner
    · have different : some owner ≠ some index := fun equal => same (Option.some.inj equal).symm
      simpa only [encode, if_neg different, if_neg same] using away index

/-- The complete rectangular law of one optionally allocated channel.
Several independent channels can later share the same owner without merging
their values: this theorem concerns one original root coordinate at a time. -/
theorem channel_rectangular_probVal {Value : Type u} (count : Nat)
    (record : FiniteProbRecord Value) (owner : Option (Fin count))
    (events : Fin count → Option Value → Bool) :
    QProb.Equiv
      (FiniteProduct.qProduct count (fun index => (channelFactor record owner index).probVal (events index)))
      (record.probVal (fun value =>
        FiniteProduct.rectangularEvent count (fun _ => Option Value) events (encode owner value))) := by
  cases owner with
  | none =>
      let checks := fun index => events index none
      have independent := FiniteProduct.qProduct_congr count (fun index =>
        absentChannel_probVal (events index))
      have encoded : forall value, FiniteProduct.rectangularEvent count (fun _ => Option Value)
          events (encode none value) = finAll count checks := by
        intro value
        apply Bool.eq_iff_iff.mpr
        rw [FiniteProduct.rectangularEvent_eq_true_iff, finAll_eq_true_iff]
        rfl
      exact QProb.equiv_trans independent
        (QProb.equiv_trans (qProduct_indicator count checks)
          (QProb.equiv_trans (QProb.equiv_symm (probVal_constant record (finAll count checks)))
            (QProb.equiv_symm (record.probVal_congr _ _ encoded))))
  | some chosen =>
      let checks := fun index => if index = chosen then true else events index none
      have remaining : QProb.Equiv
          (FiniteProduct.qProductWithout count chosen
            (fun index => (channelFactor record (some chosen) index).probVal (events index)))
          (if finAll count checks then QProb.one else QProb.zero) := by
        apply QProb.equiv_trans (FiniteProduct.qProduct_congr count ?_)
          (qProduct_indicator count checks)
        intro index
        by_cases same : index = chosen
        · simp only [checks, if_pos same]
          exact QProb.equiv_refl _
        · have different : some chosen ≠ some index := fun equal => same (Option.some.inj equal).symm
          simp only [checks, if_neg same, channelFactor, if_neg different]
          exact absentChannel_probVal (events index)
      have selected : QProb.Equiv ((channelFactor record (some chosen) chosen).probVal (events chosen))
          (record.probVal (fun value => events chosen (some value))) := by
        rw [channelFactor, if_pos rfl]
        exact record.map_probVal some (events chosen)
      exact QProb.equiv_trans
        (FiniteProduct.qProduct_coordinate count chosen
          (fun index => (channelFactor record (some chosen) index).probVal (events index)))
        (QProb.equiv_trans (QProb.mul_congr selected remaining)
          (QProb.equiv_trans (QProb.equiv_symm (probVal_and_constant record
            (fun value => events chosen (some value)) (finAll count checks)))
            (QProb.equiv_symm (record.probVal_congr _ _
              (rectangularEvent_encode_some chosen events)))))

end FiniteProductAllocation
end Probability
end Thesis
