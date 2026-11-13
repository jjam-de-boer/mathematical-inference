import Thesis.Probability.SignedRatio

namespace Thesis
namespace Probability
namespace FiniteDenominatorClearing

/-!
# Construct an integer presentation of a finite signed rational family

Every supplied denominator is already a positive natural.  The construction
recursively multiplies these denominators and rescales the corresponding
numerators, so there is no gcd, integer division, selected representative or
choice of a common denominator.  The returned denominator need not be least.

The index family may be empty.  Signed numerators and unreduced input values
are permitted; only denominators must be positive.  In compression the index
type is the finite list of original atom positions, not an enumeration of an
arbitrary ambient sample type.  Repeated labels are therefore harmless.
-/

structure Cleared {size : Nat} (values : Fin size → SignedRatio) where
  denominator : Nat
  positive : 0 < denominator
  numerator : Fin size → Int
  represents : forall index,
    SignedRatio.Equiv ⟨numerator index, denominator, positive⟩ (values index)

/-- Append one last coefficient using an explicit finite-index test.  This
avoids relying on finite-eliminator computation lemmas whose transitive proof
dependencies may be stronger than the project's constructive axiom policy. -/
def extendNumerator {size : Nat} (initial : Fin size → Int) (last : Int) : Fin (size + 1) → Int :=
  fun index => if earlier : index.val < size then initial ⟨index.val, earlier⟩ else last

theorem extendNumerator_castSucc {size : Nat} (initial : Fin size → Int) (last : Int) (index : Fin size) :
    extendNumerator initial last index.castSucc = initial index := by
  simp only [extendNumerator, Fin.val_castSucc, dif_pos index.isLt]

theorem extendNumerator_last {size : Nat} (initial : Fin size → Int) (last : Int) :
    extendNumerator initial last (Fin.last size) = last := by
  simp only [extendNumerator, Fin.val_last, dif_neg (Nat.lt_irrefl size)]

def clear : {size : Nat} → (values : Fin size → SignedRatio) → Cleared values
  | 0, _ => ⟨1, by decide, fun index => Fin.elim0 index, fun index => Fin.elim0 index⟩
  | size + 1, values => by
      let initial := clear (fun index : Fin size => values index.castSucc)
      let last := values (Fin.last size)
      refine ⟨initial.denominator * last.den, Nat.mul_pos initial.positive last.den_pos,
        extendNumerator (fun index => initial.numerator index * (last.den : Int))
          (last.num * (initial.denominator : Int)), ?_⟩
      intro index
      refine Fin.lastCases ?_ (fun earlier => ?_) index
      · rw [extendNumerator_last]
        change last.num * (initial.denominator : Int) * (last.den : Int) =
          last.num * ((initial.denominator * last.den : Nat) : Int)
        rw [Int.natCast_mul]
        ac_rfl
      · rw [extendNumerator_castSucc]
        change initial.numerator earlier * (last.den : Int) * ((values earlier.castSucc).den : Int) =
          (values earlier.castSucc).num * ((initial.denominator * last.den : Nat) : Int)
        rw [Int.natCast_mul]
        calc
          _ = (initial.numerator earlier * ((values earlier.castSucc).den : Int)) * (last.den : Int) := by ac_rfl
          _ = ((values earlier.castSucc).num * (initial.denominator : Int)) * (last.den : Int) := by
            rw [initial.represents earlier]
          _ = _ := by ac_rfl

end FiniteDenominatorClearing
end Probability
end Thesis
