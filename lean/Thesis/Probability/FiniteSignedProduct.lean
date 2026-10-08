import Thesis.Probability.FiniteSignedMass
import Thesis.Probability.Construction

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Finite integer product expansions and actual independent-record integration

The multi-channel table argument must expand the full product of row sums,
not add one-row responses at a fixed old environment.  The finite expansion
below includes every joint term, on the same dependent coordinate order as
the existing rational product and independent finite-record construction.

Integers are used only for intermediate integrands and exact polynomial
identities.  Their connection to the natural probability numerators is an
explicit theorem.  No signed probability object, rational quotient, chosen
representative, or infinite sum is introduced.

The rectangular integration theorem concerns the actual weighted atoms of
`FiniteProduct.record`.  In particular it does not infer independent channels
from separately proved marginal laws.  The finite expansion works with
empty or repeated local choice lists; a channel construction must supply its
own graph-compatible factors and normalized nonnegative local rows.
-/

/-- Integer-valued product in the existing terminal-coordinate order. -/
def iProduct : (n : Nat) -> (Fin n -> Int) -> Int
  | 0, _ => 1
  | n + 1, values => values (Fin.last n) * iProduct n (fun index => values index.castSucc)

theorem iProduct_congr (n : Nat) (left right : Fin n -> Int)
    (same : forall index, left index = right index) : iProduct n left = iProduct n right := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [iProduct, iProduct, same (Fin.last n),
        inductionHypothesis (fun index => left index.castSucc) (fun index => right index.castSucc)
          (fun index => same index.castSucc)]

/-- The integer product is exactly the embedding of the natural product
when the factors are nonnegative natural weights. -/
theorem iProduct_nat (n : Nat) (values : Fin n -> Nat) :
    iProduct n (fun index => (values index : Int)) = (natProduct n values : Int) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [iProduct, natProduct, Int.natCast_mul,
        inductionHypothesis (fun index => values index.castSucc)]

/-- Literal rational numerators retain the complete natural product. -/
theorem qProduct_num (n : Nat) (values : Fin n -> QProb) :
    (qProduct n values).num = natProduct n (fun index => (values index).num) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [qProduct, QProb.mul, natProduct,
        inductionHypothesis (fun index => values index.castSucc)]

/-- Denominators likewise retain every factor, including at zero cells. -/
theorem qProduct_den (n : Nat) (values : Fin n -> QProb) :
    (qProduct n values).den = natProduct n (fun index => (values index).den) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [qProduct, QProb.mul, natProduct,
        inductionHypothesis (fun index => values index.castSucc)]

/-- Signed expansion of actual probability-cell numerators is an exact
integer embedding, not a replacement probability semantics. -/
theorem iProduct_qProduct_num (n : Nat) (values : Fin n -> QProb) :
    iProduct n (fun index => ((values index).num : Int)) = ((qProduct n values).num : Int) := by
  rw [iProduct_nat, qProduct_num]

/-- A single zero integrated channel kills its whole independent product.
No other factor is cancelled or required to be nonzero. -/
theorem iProduct_eq_zero (n : Nat) (values : Fin n -> Int) (chosen : Fin n)
    (zero : values chosen = 0) : iProduct n values = 0 := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n inductionHypothesis =>
      exact Fin.lastCases
        (motive := fun index => values index = 0 -> iProduct (n + 1) values = 0)
        (fun empty => by simp only [iProduct, empty, Int.zero_mul])
        (fun index empty => by
          rw [iProduct, inductionHypothesis (fun index => values index.castSucc) index empty, Int.mul_zero])
        chosen zero

private def sumWith (values : List α) (term : α -> Int) : Int := (values.map term).sum

private theorem sumWith_congr (values : List α) (left right : α -> Int)
    (same : forall value, left value = right value) : sumWith values left = sumWith values right := by
  unfold sumWith
  apply congrArg List.sum
  apply List.map_congr_left
  intro value _member
  exact same value

private theorem sumWith_map (values : List α) (map : α -> β) (term : β -> Int) :
    sumWith (values.map map) term = sumWith values (fun value => term (map value)) := by
  simp only [sumWith, List.map_map, Function.comp_def]

private theorem sumWith_flatMap (values : List α) (choices : α -> List β) (term : β -> Int) :
    sumWith (values.flatMap choices) term = sumWith values (fun value => sumWith (choices value) term) := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.flatMap_cons, sumWith, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]

private theorem sumWith_mul_left (values : List α) (term : α -> Int) (factor : Int) :
    sumWith values (fun value => factor * term value) = factor * sumWith values term := by
  induction values with
  | nil => simp [sumWith]
  | cons value rest inductionHypothesis =>
      simp only [sumWith, List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis, Int.mul_add]

private theorem sumWith_mul_right (values : List α) (term : α -> Int) (factor : Int) :
    sumWith values (fun value => term value * factor) = sumWith values term * factor := by
  rw [sumWith_congr values _ _ (fun value => Int.mul_comm (term value) factor), sumWith_mul_left,
    Int.mul_comm factor (sumWith values term)]

/-- The exact finite expansion of a product of local sums.  Each complete
dependent choice contributes one whole product, retaining all interactions.
There is no positivity, normalization, or distinct-label premise. -/
theorem iProduct_finite_sum (n : Nat) (Value : Fin n -> Type u)
    (choices : (index : Fin n) -> List (Value index))
    (term : (index : Fin n) -> Value index -> Int) :
    iProduct n (fun index => ((choices index).map (term index)).sum) =
      ((enumeration n Value choices).map fun assignment =>
        iProduct n (fun index => term index (assignment index))).sum := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      let earlierChoices := enumeration n (fun index => Value index.castSucc) (fun index => choices index.castSucc)
      let prefixTerm := fun (assignment : Assignment n (fun index => Value index.castSucc)) =>
        iProduct n (fun index => term index.castSucc (assignment index))
      have expanded : sumWith (enumeration (n + 1) Value choices)
          (fun assignment => iProduct (n + 1) (fun index => term index (assignment index))) =
          sumWith (choices (Fin.last n)) (fun last => term (Fin.last n) last * sumWith earlierChoices prefixTerm) := by
        rw [enumeration, sumWith_flatMap]
        apply sumWith_congr
        intro last
        rw [sumWith_map]
        have localProduct := sumWith_congr earlierChoices
          (fun initial => iProduct (n + 1) (fun index => term index (extend last initial index)))
          (fun initial => term (Fin.last n) last * prefixTerm initial) (fun initial => by
          simp only [iProduct, extend_last, extend_castSucc]
          rfl)
        exact localProduct.trans (sumWith_mul_left earlierChoices prefixTerm (term (Fin.last n) last))
      change _ = sumWith (enumeration (n + 1) Value choices) _
      rw [expanded]
      change ((choices (Fin.last n)).map (term (Fin.last n))).sum *
        iProduct n (fun index => ((choices index.castSucc).map (term index.castSucc)).sum) = _
      rw [inductionHypothesis (fun index => Value index.castSucc) (fun index => choices index.castSucc)
        (fun index => term index.castSucc)]
      exact (sumWith_mul_right (choices (Fin.last n)) (term (Fin.last n)) (sumWith earlierChoices prefixTerm)).symm

/-- Rectangular signed integration against the actual independent product
record.  All coordinate alphabets, natural atom weights and duplicate labels
are preserved.  This supplies the independence step for channel characters. -/
theorem record_signedMass_rectangular (n : Nat) (Value : Fin n -> Type u)
    (factors : (index : Fin n) -> FiniteProbRecord (Value index))
    (integrand : (index : Fin n) -> Value index -> Int) :
    (record n Value factors).signedMass (fun assignment => iProduct n (fun index => integrand index (assignment index))) =
      iProduct n (fun index => (factors index).signedMass (integrand index)) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      let prefixAtoms := atoms n (fun index => Value index.castSucc) (fun index => factors index.castSucc)
      change FiniteProbRecord.signedAtomMass
        ((FiniteProbRecord.weightedCartesian (factors (Fin.last n)).atoms prefixAtoms).map
          (fun atom => (extend atom.1.1 atom.1.2, atom.2))) _ = _
      refine Eq.trans
        (FiniteProbRecord.signedAtomMass_map
          (FiniteProbRecord.weightedCartesian (factors (Fin.last n)).atoms prefixAtoms)
          (fun pair => extend pair.1 pair.2)
          (fun assignment => iProduct (n + 1) (fun index => integrand index (assignment index)))) ?_
      have compared := FiniteProbRecord.signedAtomMass_congr
        (FiniteProbRecord.weightedCartesian (factors (Fin.last n)).atoms prefixAtoms)
        (fun pair => iProduct (n + 1) (fun index => integrand index (extend pair.1 pair.2 index)))
        (fun pair => integrand (Fin.last n) pair.1 *
          iProduct n (fun index => integrand index.castSucc (pair.2 index))) (fun pair => by
          simp only [iProduct, extend_last, extend_castSucc])
      rw [compared]
      refine Eq.trans
        (FiniteProbRecord.signedAtomMass_weightedCartesian (factors (Fin.last n)).atoms prefixAtoms
          (integrand (Fin.last n)) (fun assignment => iProduct n (fun index => integrand index.castSucc (assignment index)))) ?_
      change (factors (Fin.last n)).signedMass (integrand (Fin.last n)) *
        (record n (fun index => Value index.castSucc) (fun index => factors index.castSucc)).signedMass
          (fun assignment => iProduct n (fun index => integrand index.castSucc (assignment index))) = _
      rw [inductionHypothesis (fun index => Value index.castSucc) (fun index => factors index.castSucc)
        (fun index => integrand index.castSucc)]
      rfl

end FiniteProduct
end Probability
end Thesis
