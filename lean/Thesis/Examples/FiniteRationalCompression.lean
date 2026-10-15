import Thesis.Probability.FiniteRationalCompression

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteRationalCompression

open Probability.FiniteRationalCompression

/-!
# Rational compression with unequal denominators and signed responses

The three positive atoms have responses one half, two thirds and five sixths,
whose mean is two thirds.  The two zero input occurrences must not prevent
compression, and the new denominator is allowed to differ from the original.

The tests exercise actual computation as well as universal result fields.
The negative-response regression concerns a signed expectation only; it
never creates a negative atom weight.  No-moment compression and an empty
denominator family cover the two distinct empty-index boundaries.
-/

def original : FiniteProbRecord Nat := ⟨[(0, 0), (0, 1), (1, 1), (2, 1), (9, 0)], 3, by decide, rfl⟩
def response (value : Nat) : SignedRatio :=
  if value = 0 then ⟨1, 2, by decide⟩ else if value = 1 then ⟨2, 3, by decide⟩ else ⟨5, 6, by decide⟩
def family : Fin 1 → Nat → SignedRatio := fun _ => response
def reduced := compress original family

theorem bound : reduced.record.atoms.length ≤ 2 := reduced.bound
theorem preserved : SignedRatio.Equiv (reduced.record.rationalMean response) (original.rationalMean response) :=
  reduced.preserved 0
theorem original_mean : SignedRatio.Equiv (original.rationalMean response) ⟨2, 3, by decide⟩ := by decide +kernel
theorem compressed_mean : SignedRatio.Equiv (reduced.record.rationalMean response) ⟨2, 3, by decide⟩ :=
  SignedRatio.equiv_trans preserved original_mean
theorem computed_support_reduced : reduced.record.atoms.length = 2 := by decide +kernel
theorem computed_mean : SignedRatio.Equiv (reduced.record.rationalMean response) ⟨2, 3, by decide⟩ := by decide +kernel
theorem normalization : QProb.Equiv (reduced.record.probVal topEvent) QProb.one := reduced.record.normalization

def negativeFamily : Fin 1 → Nat → SignedRatio := fun _ value => SignedRatio.neg (response value)
def negativeReduced := compress original negativeFamily
theorem negative_mean : SignedRatio.Equiv (negativeReduced.record.rationalMean (negativeFamily 0)) ⟨-2, 3, by decide⟩ :=
  SignedRatio.equiv_trans (negativeReduced.preserved 0) (by decide +kernel)

def noResponses : Fin 0 → Nat → SignedRatio := fun index => Fin.elim0 index
def normalizedOnly := compress original noResponses
theorem single_positive_atom : normalizedOnly.record.atoms.length = 1 := by decide +kernel

def emptyValues : Fin 0 → SignedRatio := fun index => Fin.elim0 index
theorem empty_denominator : (FiniteDenominatorClearing.clear emptyValues).denominator = 1 := rfl

def values : Fin 3 → SignedRatio := fun index => response index.val
def cleared := FiniteDenominatorClearing.clear values
theorem denominator_product : cleared.denominator = 36 := by decide +kernel
theorem cleared_numerators : (cleared.numerator 0, cleared.numerator 1, cleared.numerator 2) = (18, 24, 30) := by decide +kernel
theorem clearing_correct (index : Fin 3) :
    SignedRatio.Equiv ⟨cleared.numerator index, cleared.denominator, cleared.positive⟩ (values index) := cleared.represents index

end FiniteRationalCompression
end Examples
end Probability
end Thesis
