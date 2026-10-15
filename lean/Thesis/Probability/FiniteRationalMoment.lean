import Thesis.Probability.SignedRatioFiniteSum
import Thesis.Probability.FiniteSignedMass

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Rational-valued responses integrated against genuine finite records

The responses are signed rational presentations, but all record weights
remain natural.  `rationalMean` is the ordinary weighted sum divided by the
record's positive total mass.  It uses every supplied atom occurrence, so it
does not require decidable equality or an enumeration of the ambient type.

The common-denominator theorem connects this direct semantics to an integer
moment.  This is the bridge that lets the verified support-reduction engine
preserve rational responses, rather than merely their unnormalized sums.
-/

def rationalAtomSum (atoms : List (Ω × Nat)) (response : Ω → SignedRatio) : SignedRatio :=
  SignedRatio.listSum (atoms.map fun atom => SignedRatio.scaleNat atom.2 (response atom.1))

def rationalMean (record : FiniteProbRecord Ω) (response : Ω → SignedRatio) : SignedRatio :=
  SignedRatio.divideNat (rationalAtomSum record.atoms response) record.den record.den_pos

theorem rationalMean_map (record : FiniteProbRecord Ω) (map : Ω → X) (response : X → SignedRatio) :
    (record.map map).rationalMean response = record.rationalMean (fun value => response (map value)) := by
  simp only [rationalMean, rationalAtomSum, FiniteProbRecord.map, List.map_map, Function.comp_def]

/-- Clear only response denominators.  Atom weights are multiplied into
their numerators without dividing by an atom's mass, even when it is zero. -/
theorem rationalAtomSum_cleared (atoms : List (Ω × Nat)) (response : Ω → SignedRatio)
    (coefficient : Ω → Int) (denominator : Nat) (positive : 0 < denominator)
    (same : forall value, SignedRatio.Equiv (response value) ⟨coefficient value, denominator, positive⟩) :
    SignedRatio.Equiv (rationalAtomSum atoms response)
      ⟨signedAtomMass atoms coefficient, denominator, positive⟩ := by
  have scaled := SignedRatio.listSum_map_congr atoms
    (fun atom => SignedRatio.scaleNat atom.2 (response atom.1))
    (fun atom => (⟨(atom.2 : Int) * coefficient atom.1, denominator, positive⟩ : SignedRatio))
    (fun atom => SignedRatio.scaleNat_congr atom.2 (same atom.1))
  refine SignedRatio.equiv_trans scaled ?_
  simpa only [List.map_map, Function.comp_def, signedAtomMass] using
    SignedRatio.listSum_mk_same_den denominator positive (atoms.map fun atom => (atom.2 : Int) * coefficient atom.1)

theorem rationalMean_cleared (record : FiniteProbRecord Ω) (response : Ω → SignedRatio)
    (coefficient : Ω → Int) (denominator : Nat) (positive : 0 < denominator)
    (same : forall value, SignedRatio.Equiv (response value) ⟨coefficient value, denominator, positive⟩) :
    SignedRatio.Equiv (record.rationalMean response)
      (SignedRatio.divideNat ⟨record.signedMass coefficient, record.den, record.den_pos⟩ denominator positive) := by
  refine SignedRatio.equiv_trans
    (SignedRatio.divideNat_congr (rationalAtomSum_cleared record.atoms response coefficient denominator positive same)
      record.den record.den_pos) ?_
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, signedMass, Int.natCast_mul]
  ac_rfl

end FiniteProbRecord
end Probability
end Thesis
