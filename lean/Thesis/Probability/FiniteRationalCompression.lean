import Thesis.Probability.FiniteIntegerCompression
import Thesis.Probability.FiniteDenominatorClearing
import Thesis.Probability.FiniteRationalMoment

namespace Thesis
namespace Probability
namespace FiniteRationalCompression

open FiniteProbRecord

universe u
variable {Ω : Type u} {count : Nat}

/-!
# Constructive compression preserving arbitrary finite rational responses

For `count` supplied signed rational responses, construct a genuine finite
probability record with at most `count + 1` positive atom occurrences and
exactly the original normalized expectations.  The output uses only labels
already present in the input; neither the ambient sample type nor its
equality needs to be finite or decidable.

Denominators are cleared separately for each response on the finite list of
original atom positions.  Integer compression then acts on those positions,
and its final record is mapped back to their original labels.  Repeated
labels and zero input weights are allowed.  Importantly, the original
clearing data are retained throughout reduction: recomputing them on a new
support would change the integer moment being preserved.

This is probability-record compression, not yet a native causal-model source
replacement theorem.  A source replacement must additionally integrate the
other independent sources and prove preservation of the model's requested
observational/interventional responses.
-/

def originalLabel (record : FiniteProbRecord Ω) (index : Fin record.atoms.length) : Ω :=
  record.atoms[index.val].1

/-- Sampling original atom positions keeps multiplicities and zero atoms
explicitly.  Its total-mass proof uses the already checked integer identity,
and no supported representative of an ambient label is chosen. -/
def indexedRecord (original : FiniteProbRecord Ω) : FiniteProbRecord (Fin original.atoms.length) where
  atoms := FiniteIntegerCompression.indexed (fun index => index) (fun index => original.atoms[index.val].2)
  den := original.den
  den_pos := original.den_pos
  total_mass := Int.ofNat.inj
    ((FiniteIntegerCompression.indexed_totalMass (fun index : Fin original.atoms.length => index)
      (fun index => original.atoms[index.val].2)).trans (FiniteIntegerCompression.original_mass_dot original))

theorem rationalMean_indexed (original : FiniteProbRecord Ω) (response : Ω → SignedRatio) :
    (indexedRecord original).rationalMean (fun index => response (originalLabel original index)) =
      original.rationalMean response := by
  have sameAtoms := FiniteIntegerCompression.reconstruct_atoms original.atoms
  have integrated := congrArg
    (fun atoms => SignedRatio.divideNat (rationalAtomSum atoms response) original.den original.den_pos) sameAtoms
  simpa only [rationalMean, rationalAtomSum, indexedRecord, originalLabel,
    FiniteIntegerCompression.indexed, List.map_map, Function.comp_def] using integrated

structure Compressed (original : FiniteProbRecord Ω) (responses : Fin count → Ω → SignedRatio) where
  record : FiniteProbRecord Ω
  bound : record.atoms.length ≤ count + 1
  positive : forall atom, atom ∈ record.atoms → 0 < atom.2
  label_mem : forall atom, atom ∈ record.atoms → Exists fun weight => (atom.1, weight) ∈ original.atoms
  preserved : forall index, SignedRatio.Equiv (record.rationalMean (responses index)) (original.rationalMean (responses index))

/-- Complete rational-response compression of a supplied finite record.
Natural probability weights remain nonnegative and normalized; signed values
occur only in the auxiliary responses.  All preservation proofs concern the
constructed output record itself, not an externally supplied replacement. -/
def compress (original : FiniteProbRecord Ω) (responses : Fin count → Ω → SignedRatio) : Compressed original responses := by
  let responseAt := fun row index => responses row (originalLabel original index)
  let cleared := fun row => FiniteDenominatorClearing.clear (responseAt row)
  let coefficients := fun row => (cleared row).numerator
  let solved := FiniteIntegerCompression.compress (indexedRecord original) coefficients
  refine ⟨solved.record.map (originalLabel original), ?_, ?_, ?_, ?_⟩
  · change (solved.record.atoms.map _).length ≤ count + 1
    rw [List.length_map]
    exact solved.bound
  · intro atom listed
    rcases List.mem_map.mp listed with ⟨previous, previousMem, rfl⟩
    exact solved.positive previous previousMem
  · intro atom listed
    rcases List.mem_map.mp listed with ⟨previous, _previousMem, rfl⟩
    exact ⟨original.atoms[previous.1.val].2, List.getElem_mem previous.1.isLt⟩
  · intro row
    rw [rationalMean_map]
    have agrees := fun index => SignedRatio.equiv_symm ((cleared row).represents index)
    have after := rationalMean_cleared solved.record (responseAt row) (coefficients row)
      (cleared row).denominator (cleared row).positive agrees
    have before := rationalMean_cleared (indexedRecord original) (responseAt row) (coefficients row)
      (cleared row).denominator (cleared row).positive agrees
    rw [rationalMean_indexed] at before
    exact SignedRatio.equiv_trans after
      (SignedRatio.equiv_trans
        (SignedRatio.divideNat_congr (solved.preserved row) (cleared row).denominator (cleared row).positive)
        (SignedRatio.equiv_symm before))

end FiniteRationalCompression
end Probability
end Thesis
