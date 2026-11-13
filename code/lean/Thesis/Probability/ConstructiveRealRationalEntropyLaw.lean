import Thesis.Probability.ConstructiveRealRationalEntropyEncoding

namespace Thesis.Probability.ConstructiveReal

/-- A finite entropy sum is unchanged by transport of its dimension. -/
theorem realEntropyFin_cast (first second : Nat) (same : first = second) (masses : Fin first → UnitIntervalValue) :
    Equiv (realEntropySum ((List.finRange second).map (fun i => masses (Fin.cast same.symm i))))
      (realEntropySum ((List.finRange first).map masses)) := by
  cases same
  exact equiv_refl _

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- Original rational row semantics agree with their analytic embedding. -/
theorem RationalConstraint.real_ofSignedRatio_iff (row : RationalConstraint variables)
    (values : Fin variables → SignedRatio) :
    row.RealHolds (fun i => ofSignedRatio (values i)) ↔ row.Holds values := by
  have integer : row.clear.RealHolds (fun i => ofSignedRatio (values i)) ↔ row.clear.Holds values :=
    (le_congr (realDot_ofSignedRatio variables row.clear.coefficients values) (equiv_refl _)).trans
      (ofSignedRatio_le_iff _ _)
  exact (row.clear_real_iff (fun i => ofSignedRatio (values i))).symm.trans
    (integer.trans (row.clear_iff values))

end Thesis.Probability.Distros.RationalLinear

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

/-- Every original real feasible vector is admitted; the coordinate domain
witnesses follow from the original simplex rows rather than extra hypotheses. -/
def RealLaw.ofVector (problem : RationalEntropyProblem variables) (values : Fin variables → ConstructiveReal)
    (simplex : RationalLinear.RealSatisfies (RationalLinear.simplexRows variables) values)
    (valid : ∀ row ∈ problem.rows, row.RealHolds values) : problem.RealLaw where
  mass i := ⟨values i, (RationalLinear.real_simplex_bounds values simplex i).1,
    (RationalLinear.real_simplex_bounds values simplex i).2⟩
  normalized := RationalLinear.real_simplex_normalized values simplex
  valid := valid

/-- Exact rational feasible vectors provide ordinary inputs to the ideal
problem without any decision about analytic feasibility. -/
def RealLaw.ofRationalVector (problem : RationalEntropyProblem variables) (values : Fin variables → SignedRatio)
    (simplex : RationalLinear.Simplex values) (valid : ∀ row ∈ problem.rows, row.Holds values) : problem.RealLaw :=
  .ofVector problem (fun i => ofSignedRatio (values i)) (by
    intro row member
    exact (le_congr (RationalLinear.realDot_ofSignedRatio variables row.coefficients values) (equiv_refl _)).mpr
      ((ofSignedRatio_le_iff _ _).mpr ((RationalLinear.satisfies_simplex_iff variables values).mpr simplex row member)))
    (fun row member => (row.real_ofSignedRatio_iff values).mpr (valid row member))

theorem dot_inverse (problem : RationalEntropyProblem variables) (coefficients : Fin variables → Int)
    (values : Fin problem.encoded.cells.length → ConstructiveReal) :
    Equiv (RationalLinear.realDot variables coefficients (fun i => values (problem.lawIndex i)))
      (RationalLinear.realDot problem.encoded.cells.length (fun i => coefficients (problem.gridIndex i)) values) := by
  have transported := RationalLinear.realDot_cast problem.encoded.cells.length variables List.length_finRange
    (fun i => coefficients (problem.gridIndex i)) values
  change Equiv _ (RationalLinear.realDot variables (fun i => coefficients (problem.gridIndex (problem.lawIndex i)))
    (fun i => values (problem.lawIndex i))) at transported
  simpa only [gridIndex_lawIndex] using equiv_symm transported

/-- Decoding preserves all original rational rows. Only the proved redundant
lower endpoints are discarded; the original inequalities are retained. -/
def RealLaw.ofEncoded {problem : RationalEntropyProblem variables} (law : problem.encoded.RealCompatibleLaw) : problem.RealLaw where
  mass i := law.mass (problem.lawIndex i)
  normalized := equiv_trans (problem.dot_inverse (fun _ => 1) (fun i => (law.mass i).value))
    (RationalLinear.real_simplex_normalized (fun i => (law.mass i).value)
      (fun row member => law.valid row (List.mem_append_left _ member)))
  valid := by
    intro row member
    have listed : rowMoment row.clear ∈ problem.encoded.intervals := List.mem_map.mpr ⟨row, member, rfl⟩
    have band := (MomentInterval.real_rows_iff (rowMoment row.clear) problem.encoded.cells problem.encoded.default
      (fun i => (law.mass i).value)).mp
      (fun actual inside => law.valid actual (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, listed, inside⟩)))
    have upper := band.2
    rw [problem.row_coefficients row.clear] at upper
    exact (row.clear_real_iff (fun i => (law.mass (problem.lawIndex i)).value)).mp
      ((le_congr (problem.dot_inverse row.clear.coefficients (fun i => (law.mass i).value)) (equiv_refl _)).mpr upper)

theorem RealLaw.toEncoded_entropy {problem : RationalEntropyProblem variables} (law : problem.RealLaw) :
    Equiv law.toEncoded.entropy law.entropy :=
  realEntropyFin_cast variables problem.encoded.cells.length List.length_finRange.symm law.mass

theorem RealLaw.ofEncoded_entropy {problem : RationalEntropyProblem variables} (law : problem.encoded.RealCompatibleLaw) :
    Equiv (RealLaw.ofEncoded law).entropy law.entropy :=
  realEntropyFin_cast problem.encoded.cells.length variables List.length_finRange law.mass

/-- The original rational feasible polytope, not the encoding, determines
which law has maximum entropy. -/
def RealLaw.Maximal {problem : RationalEntropyProblem variables} (law : problem.RealLaw) : Prop :=
  ∀ other : problem.RealLaw, LE other.entropy law.entropy

theorem RealLaw.maximal_encoded {problem : RationalEntropyProblem variables} (law : problem.RealLaw)
    (maximal : law.Maximal) : law.toEncoded.Maximal := by
  intro other
  exact (le_congr (RealLaw.ofEncoded_entropy other) (equiv_symm law.toEncoded_entropy)).mp
    (maximal (RealLaw.ofEncoded other))

/-- Constructive existence over arbitrary rational constraint data, through
the already proved effective rational optimizer. Actual atom weights remain
rational at every finite approximation; this limit is auxiliary. -/
def RealLaw.maximize {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw) : problem.RealLaw :=
  .ofEncoded feasible.toEncoded.maximize

theorem RealLaw.maximize_maximal {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw) :
    feasible.maximize.Maximal := by
  intro other
  exact (le_congr other.toEncoded_entropy (equiv_symm (RealLaw.ofEncoded_entropy feasible.toEncoded.maximize))).mp
    (feasible.toEncoded.maximize_maximal other.toEncoded)

/-- Uniqueness is equality of the probabilities on the original finite
coordinates, independently of redundant rows and rational presentations. -/
theorem RealLaw.maximal_unique {problem : RationalEntropyProblem variables} (first second : problem.RealLaw)
    (maxFirst : first.Maximal) (maxSecond : second.Maximal) (index : Fin variables) :
    Equiv (first.mass index).value (second.mass index).value := by
  have same := first.toEncoded.maximal_unique second.toEncoded (first.maximal_encoded maxFirst)
    (second.maximal_encoded maxSecond) (problem.lawIndex index)
  change Equiv (first.mass (problem.gridIndex (problem.lawIndex index))).value
    (second.mass (problem.gridIndex (problem.lawIndex index))).value at same
  simpa only [gridIndex_lawIndex] using same

end Thesis.Probability.Distros.RationalEntropyProblem
