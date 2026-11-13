import Thesis.Probability.FiniteSignedProduct

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Literal products over a shared prefix and a private suffix

The rational CPT likelihood orders its actual source coordinates as a shared
prefix followed by one integrated private-row factor per observed node.  The
whole product must be separated in that same coordinate order, retaining its
literal numerator and denominator even at a zero cell.

These finite natural identities provide that separation.  The suffix is the
left multiplication factor because the existing product recurses from the
terminal coordinate.  Both embeddings into `Fin (left + right)` are displayed
explicitly.  No fraction is cancelled and no positivity of a cell is assumed.
-/

/-- Pointwise equal natural factors give equal literal finite products. -/
theorem natProduct_congr (n : Nat) (left right : Fin n -> Nat)
    (same : forall index, left index = right index) : natProduct n left = natProduct n right := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [natProduct, natProduct, same (Fin.last n),
        inductionHypothesis (fun index => left index.castSucc) (fun index => right index.castSucc)
          (fun index => same index.castSucc)]

/-- Empty and nonempty products of unit factors both have natural mass one. -/
theorem natProduct_one (n : Nat) : natProduct n (fun _ => 1) = 1 := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis => simpa only [natProduct, Nat.one_mul] using inductionHypothesis

/-- Positive factor denominators give a positive product denominator.
This does not impose a positive numerator at forced or conflicting cells. -/
theorem natProduct_positive (n : Nat) (values : Fin n -> Nat) (positive : forall index, 0 < values index) :
    0 < natProduct n values := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n inductionHypothesis =>
      exact Nat.mul_pos (positive (Fin.last n))
        (inductionHypothesis (fun index => values index.castSucc) (fun index => positive index.castSucc))

/-- Split the actual coordinate product into its private suffix and shared
prefix.  The two embeddings keep every original slot, including empty blocks. -/
theorem natProduct_append (left right : Nat) (values : Fin (left + right) -> Nat) :
    natProduct (left + right) values =
      natProduct right (fun index => values (Fin.natAdd left index)) *
        natProduct left (fun index => values (index.castAdd right)) := by
  induction right with
  | zero => simp only [natProduct, Nat.one_mul]; rfl
  | succ right inductionHypothesis =>
      change values (Fin.last (left + right)) *
        natProduct (left + right) (fun index => values index.castSucc) =
          (values (Fin.natAdd left (Fin.last right)) *
            natProduct right (fun index => values (Fin.natAdd left index.castSucc))) *
              natProduct left (fun index => values (index.castAdd (right + 1)))
      rw [inductionHypothesis (fun index => values index.castSucc)]
      simp only [Fin.natAdd_last, Fin.castSucc_natAdd]
      rw [Nat.mul_assoc]
      rfl

/-- The real product record's denominator is precisely the natural product
of its supplied factor denominators, with no alternative presentation. -/
theorem record_den_eq_natProduct (n : Nat) (Value : Fin n -> Type u)
    (factors : (index : Fin n) -> FiniteProbRecord (Value index)) :
    (record n Value factors).den = natProduct n (fun index => (factors index).den) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      change (factors (Fin.last n)).den * denominator n (fun index => Value index.castSucc)
        (fun index => factors index.castSucc) = _
      rw [show denominator n (fun index => Value index.castSucc) (fun index => factors index.castSucc) =
        natProduct n (fun index => (factors index.castSucc).den) from
          inductionHypothesis (fun index => Value index.castSucc) (fun index => factors index.castSucc)]
      rfl

end FiniteProduct
end Probability
end Thesis
