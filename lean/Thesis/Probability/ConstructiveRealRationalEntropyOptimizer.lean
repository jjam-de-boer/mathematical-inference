import Thesis.Probability.ConstructiveRealRationalEntropyLaw

/-!
Constructive maximum entropy for a finite simplex with arbitrary signed
rational inequality data. An equality is two closed rows. The encoding into
integer-response moment bands adds only a proved redundant lower endpoint.

A supplied feasible analytic law yields an attained ideal maximum, unique
coordinate probabilities, and exactly feasible rational `Distro` outputs
with an explicit convergence rate. The ideal law is auxiliary: rational
probability weights and the existing certificate interface are unchanged.
No full-support, row-independence or decidable-real-comparison assumption is
introduced. This is an exhaustive reference construction, with no numerical
efficiency claim and no multiplier-existence claim.
-/

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

/-- The encoded solver's retained state is exactly the original coordinate. -/
theorem encoded_mass (problem : RationalEntropyProblem variables) (law : problem.encoded.CompatibleLaw) (index : Fin variables) :
    (law.toReal.mass (problem.lawIndex index)).value = ofSignedRatio (law.distro.pmf index).toSignedRatio := by
  change ofSignedRatio (law.distro.pmf (problem.encoded.cells.getD (problem.lawIndex index).val problem.encoded.default)).toSignedRatio = _
  rw [problem.grid_cell, problem.gridIndex_lawIndex]

/-- Every actual encoded solution satisfies the original rational rows,
with their original denominators and inequality directions. -/
theorem encoded_original_constraints (problem : RationalEntropyProblem variables) (law : problem.encoded.CompatibleLaw) :
    ∀ row ∈ problem.rows, row.Holds (fun i => (law.distro.pmf i).toSignedRatio) := by
  intro row member
  have original := (RealLaw.ofEncoded law.toReal).valid row member
  have coordinates : (fun i => ((RealLaw.ofEncoded law.toReal).mass i).value) =
      (fun i => ofSignedRatio (law.distro.pmf i).toSignedRatio) := by
    funext i
    exact problem.encoded_mass law i
  change row.RealHolds (fun i => ((RealLaw.ofEncoded law.toReal).mass i).value) at original
  rw [coordinates] at original
  exact (row.real_ofSignedRatio_iff _).mp original

/-- Exactly feasible density returns an actual rational `Distro`, preserves
all original rational rows, and records every declared state, including zeros.
No independent coordinate rounding or denominator cap is used. -/
def RealLaw.approximate {problem : RationalEntropyProblem variables} (law : problem.RealLaw) (precision : PositiveRatio) :
    {rational : Distro (Fin variables) //
      (∀ row ∈ problem.rows, row.Holds (fun i => (rational.pmf i).toSignedRatio)) ∧
      (∀ i, ∃ weight, (i, weight) ∈ rational.record.atoms) ∧
      ∀ i, Within precision.toQProb (law.mass i).value (ofSignedRatio (rational.pmf i).toSignedRatio)} := by
  let approximation := law.toEncoded.approximate precision
  refine ⟨approximation.val.distro, problem.encoded_original_constraints approximation.val,
    (fun i => approximation.val.retains i (List.mem_finRange i)), ?_⟩
  intro i
  have close := approximation.property (problem.lawIndex i)
  change Within precision.toQProb (law.mass (problem.gridIndex (problem.lawIndex i))).value
    (ofSignedRatio (approximation.val.distro.pmf (problem.encoded.cells.getD (problem.lawIndex i).val problem.encoded.default)).toSignedRatio) at close
  simpa only [problem.gridIndex_lawIndex, problem.grid_cell] using close

/-- Existing universal rational certificates bound every ideal competitor
for the original rational data, not only solutions in the encoded notation. -/
theorem certificate_global_bound {problem : RationalEntropyProblem variables} {tolerance : QProb}
    (certificate : problem.encoded.EntropyCertificate tolerance) (law : problem.RealLaw) :
    LE law.entropy (ofSignedRatio certificate.upper.toSignedRatio) :=
  (le_congr law.toEncoded_entropy (equiv_refl _)).mp (certificate.real_global_bound law.toEncoded)

/-- Certified entropy inference for the general rational rows reuses the
existing complete rational solver. Its output law remains exactly feasible. -/
def RealLaw.certifyEntropy {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (tolerance : QProb) (positive : 0 < tolerance.num) : problem.encoded.EntropyCertificate tolerance :=
  problem.encoded.certifyEntropy (feasible.toEncoded.approximate PositiveRatio.one).val tolerance positive

theorem RealLaw.certifyEntropy_valid {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (tolerance : QProb) (positive : 0 < tolerance.num) :
    ∀ row ∈ problem.rows, row.Holds (fun i => ((feasible.certifyEntropy tolerance positive).law.distro.pmf i).toSignedRatio) :=
  problem.encoded_original_constraints _

/-- Symbolic near-maximizers use the same exactly feasible starting law as
the ideal construction. This reference algorithm is total; its exhaustive
fallback carries no claim of efficient large-scale numerical optimization. -/
def RealLaw.rationalApproximations {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (n : Nat) : problem.encoded.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb :=
  problem.encoded.entropyApproximations (feasible.toEncoded.approximate PositiveRatio.one).val n

def RealLaw.rationalLaw {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw) (n : Nat) : Distro (Fin variables) :=
  (feasible.rationalApproximations n).law.distro

theorem RealLaw.rationalLaw_valid {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw) (n : Nat) :
    ∀ row ∈ problem.rows, row.Holds (fun i => (feasible.rationalLaw n).pmf i |>.toSignedRatio) :=
  problem.encoded_original_constraints _

theorem RealLaw.rationalLaw_retains {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw) (n : Nat)
    (index : Fin variables) : ∃ weight, (index, weight) ∈ (feasible.rationalLaw n).record.atoms :=
  (feasible.rationalApproximations n).law.retains index (List.mem_finRange index)

/-- The symbolic gap ranges over every original feasible analytic law. -/
theorem RealLaw.rationalApproximations_upper {problem : RationalEntropyProblem variables} (feasible other : problem.RealLaw) (n : Nat) :
    LE other.entropy (add ((feasible.rationalLaw n).entropy problem.encoded.entropyGrid
      (feasible.rationalApproximations n).law.support).interpret (ofSignedRatio (PositiveRatio.unitPrecision n).toSignedRatio)) := by
  have upper := (feasible.rationalApproximations n).real_upper other.toEncoded
  exact (le_congr other.toEncoded_entropy
    (add_congr (feasible.rationalApproximations n).law.toReal_entropy (equiv_refl _))).mp upper

/-- Actual rational law probabilities converge effectively to the unique
ideal law on the original coordinate system. Equality/interval rows and
forced zeros remain exact at every finite stage. -/
theorem RealLaw.rationalLaw_converges {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (radius : PositiveRatio) (n : Nat) (later : radius.half.half.entropyGapPrecision.den ≤ n) (index : Fin variables) :
    Within radius.toQProb (ofSignedRatio ((feasible.rationalLaw n).pmf index).toSignedRatio)
      (feasible.maximize.mass index).value := by
  have close := problem.encoded.idealEntropyLaw_coordinate_converges
    (feasible.toEncoded.approximate PositiveRatio.one).val radius n later (problem.lawIndex index)
  change Within radius.toQProb ((feasible.rationalApproximations n).law.toReal.mass (problem.lawIndex index)).value
    (feasible.maximize.mass index).value at close
  rw [problem.encoded_mass] at close
  exact close

end Thesis.Probability.Distros.RationalEntropyProblem
