import Thesis.Probability.FiniteIntegerCompression

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteIntegerCompression

open Probability.FiniteIntegerCompression

/-!
# Complete record compression with zeros, signed moments and no moments

The input has three positive atoms and two zero occurrences.  Preserving its
mean compresses it to the two extreme labels with new natural denominator six.
An empty moment family compresses it to one atom, and a two-moment family
already meets the bound after zero removal.  A negative mean uses auxiliary
signed moment values, never negative probability weights.

Both the actual computed records and the universal preservation fields are
exercised.  No native causal-source replacement is assumed by these tests.
-/

def original : FiniteProbRecord Nat := ⟨[(0, 0), (0, 1), (1, 1), (2, 1), (9, 0)], 3, by decide, rfl⟩
def mean : Fin 1 → Nat → Int := fun _ value => (value : Int)
def reduced := compress original mean

theorem mean_bound : reduced.record.atoms.length ≤ 2 := reduced.bound
theorem mean_preserved : SignedRatio.Equiv (moment reduced.record (mean 0)) (moment original (mean 0)) := reduced.preserved 0
theorem actual_atoms : reduced.record.atoms = [(0, 3), (2, 3)] := by decide +kernel
theorem actual_denominator : reduced.record.den = 6 := by decide +kernel
theorem exact_mean_one : SignedRatio.Equiv (moment reduced.record (mean 0)) SignedRatio.one := by decide +kernel

def noMoments : Fin 0 → Nat → Int := fun index => Fin.elim0 index
def normalizedOnly := compress original noMoments
theorem single_atom : normalizedOnly.record.atoms.length = 1 := by decide +kernel
theorem normalization_preserved : QProb.Equiv (normalizedOnly.record.probVal topEvent) QProb.one := normalizedOnly.record.normalization

def negativeMean : Fin 1 → Nat → Int := fun _ value => -(value : Int)
def negativeReduced := compress original negativeMean
theorem negative_mean_preserved : SignedRatio.Equiv (moment negativeReduced.record (negativeMean 0))
    ⟨-1, 1, by decide⟩ :=
  SignedRatio.equiv_trans (negativeReduced.preserved 0) (by decide +kernel)

def twoMoments : Fin 2 → Nat → Int := fun index value =>
  if index.val = 0 then (value : Int) else ((value * value : Nat) : Int)
def alreadySmall := compress original twoMoments
theorem only_zero_atoms_removed : alreadySmall.record.atoms = original.trimZeros.atoms := by decide +kernel

end FiniteIntegerCompression
end Examples
end Probability
end Thesis
