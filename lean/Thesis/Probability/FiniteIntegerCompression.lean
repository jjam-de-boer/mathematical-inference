import Thesis.Probability.AffineSupportReduction
import Thesis.Probability.FiniteRecordPositiveAtoms

namespace Thesis
namespace Probability
namespace FiniteIntegerCompression

open IntegerLinearAlgebra FiniteProbRecord

universe u
variable {Ω : Type u} {count : Nat}

/-!
# Terminating compression preserving a finite family of integer moments

Given a genuine finite rational probability record and `count` supplied
integer-valued integrands, return an actual probability record with at most
`count + 1` positive atom occurrences and exactly the same normalized moments.
Weights and denominators remain natural.  Repeated labels, zero input atoms,
negative integrand values and a family of zero moments are all permitted.

Each recursive step uses the constructed affine null direction and maximal
feasible update.  Its zero atoms are removed, so the number of actual atoms
strictly decreases.  The recursion is not on total integer mass, which may
grow as denominators are rescaled.  The retained normalization equation
constructs a positive denominator for every intermediate probability record.

This is the integer-moment compression theorem.  Denominator clearing for
rational-valued responses and independent native-source replacement remain
separate bridges; no such model-level preservation is assumed here.
-/

def moment (record : FiniteProbRecord Ω) (integrand : Ω → Int) : SignedRatio :=
  ⟨record.signedMass integrand, record.den, record.den_pos⟩

theorem moment_trimZeros (record : FiniteProbRecord Ω) (integrand : Ω → Int) :
    moment record.trimZeros integrand = moment record integrand := by
  simp only [moment, trimZeros_signedMass, trimZeros]

def indexed {size : Nat} (labels : Fin size → Ω) (weights : Fin size → Nat) : List (Ω × Nat) :=
  (List.finRange size).map (fun index => (labels index, weights index))

theorem sum_eq_list_sum (values : List Int) : IntegerLinearAlgebra.sum values = values.sum := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change head + IntegerLinearAlgebra.sum tail = (head :: tail).sum
      rw [List.sum_cons, inductionHypothesis]

theorem indexed_signedMass {size : Nat} (labels : Fin size → Ω) (weights : Fin size → Nat) (integrand : Ω → Int) :
    signedAtomMass (indexed labels weights) integrand =
      dot (fun index => integrand (labels index)) (fun index => (weights index : Int)) := by
  simp only [indexed, signedAtomMass, List.map_map, Function.comp_def, dot, sum_eq_list_sum]
  congr 1
  apply List.map_congr_left
  intro index _
  exact Int.mul_comm _ _

theorem indexed_totalMass {size : Nat} (labels : Fin size → Ω) (weights : Fin size → Nat) :
    (totalMass (indexed labels weights) : Int) = dot (fun _ => 1) (fun index => (weights index : Int)) := by
  have same := indexed_signedMass labels weights (fun _ => 1)
  rw [signedAtomMass_const, Int.mul_one] at same
  exact same

theorem reconstruct_atoms (atoms : List (Ω × Nat)) :
    indexed (fun index : Fin atoms.length => atoms[index.val].1) (fun index => atoms[index.val].2) = atoms := by
  change (List.finRange atoms.length).map (fun index => atoms[index.val]) = atoms
  rw [List.finRange, List.map_ofFn]
  exact List.ofFn_getElem

theorem original_dot (record : FiniteProbRecord Ω) (integrand : Ω → Int) :
    dot (fun index : Fin record.atoms.length => integrand record.atoms[index.val].1)
      (fun index => (record.atoms[index.val].2 : Int)) = record.signedMass integrand := by
  rw [← indexed_signedMass, reconstruct_atoms]
  rfl

theorem original_mass_dot (record : FiniteProbRecord Ω) :
    dot (fun _ : Fin record.atoms.length => 1) (fun index => (record.atoms[index.val].2 : Int)) = (record.den : Int) := by
  have same := original_dot record (fun _ => 1)
  rw [signedMass_const, Int.mul_one] at same
  exact same

theorem positiveAtoms_indexed_length {size : Nat} (labels : Fin size → Ω) (weights : Fin size → Nat) :
    (positiveAtoms (indexed labels weights)).length = AffineSupportReduction.positiveCount weights := by
  simp only [positiveAtoms, indexed, List.filter_map, List.length_map, AffineSupportReduction.positiveCount]

structure RecordStep (record : FiniteProbRecord Ω) (integrands : Fin count → Ω → Int) where
  reduced : FiniteProbRecord Ω
  positive : forall atom, atom ∈ reduced.atoms → 0 < atom.2
  shorter : reduced.atoms.length < record.atoms.length
  preserved : forall index, SignedRatio.Equiv (moment reduced (integrands index)) (moment record (integrands index))

/-- Turn the natural-weight affine step into an actual normalized record,
then discard the newly zero atoms.  Both denominator positivity and all
moment equalities are proved for this very record, not supplied by callers. -/
def recordStep (record : FiniteProbRecord Ω) (integrands : Fin count → Ω → Int)
    (positive : forall atom, atom ∈ record.atoms → 0 < atom.2)
    (larger : count + 1 < record.atoms.length) : RecordStep record integrands := by
  let labels := fun index : Fin record.atoms.length => record.atoms[index.val].1
  let weights := fun index : Fin record.atoms.length => record.atoms[index.val].2
  let matrix : Matrix count record.atoms.length := fun row column => integrands row (labels column)
  have positiveWeights : forall index, 0 < weights index := by
    intro index
    exact positive _ (List.getElem_mem index.isLt)
  let made := AffineSupportReduction.step matrix weights positiveWeights larger
  let raw : FiniteProbRecord Ω :=
    { atoms := indexed labels made.newWeights
      den := made.factor * record.den
      den_pos := Nat.mul_pos made.factor_positive record.den_pos
      total_mass := by
        have scaled : (totalMass (indexed labels made.newWeights) : Int) = (made.factor : Int) * (record.den : Int) := by
          rw [indexed_totalMass, made.mass_scaled]
          change (made.factor : Int) * dot (fun _ => 1) (fun index => (record.atoms[index.val].2 : Int)) = _
          rw [original_mass_dot]
        exact Int.ofNat.inj (scaled.trans (Int.natCast_mul _ _).symm) }
  have rawPreserved (row : Fin count) : SignedRatio.Equiv (moment raw (integrands row)) (moment record (integrands row)) := by
    change signedAtomMass (indexed labels made.newWeights) (integrands row) * (record.den : Int) =
      signedAtomMass record.atoms (integrands row) * ((made.factor * record.den : Nat) : Int)
    rw [indexed_signedMass]
    change dot (matrix row) (fun index => (made.newWeights index : Int)) * (record.den : Int) = _
    rw [made.moments_scaled row]
    change (made.factor : Int) * dot (fun index : Fin record.atoms.length => integrands row record.atoms[index.val].1)
      (fun index => (record.atoms[index.val].2 : Int)) * (record.den : Int) = _
    rw [original_dot]
    simp only [signedMass, Int.natCast_mul]
    ac_rfl
  refine ⟨raw.trimZeros, trimZeros_positive raw, ?_, ?_⟩
  · change (positiveAtoms (indexed labels made.newWeights)).length < record.atoms.length
    rw [positiveAtoms_indexed_length]
    have progress := made.positive_count_decreases
    rw [AffineSupportReduction.positiveCount_eq_columns weights positiveWeights] at progress
    exact progress
  · intro row
    rw [moment_trimZeros]
    exact rawPreserved row

structure Compressed (original : FiniteProbRecord Ω) (integrands : Fin count → Ω → Int) where
  record : FiniteProbRecord Ω
  bound : record.atoms.length ≤ count + 1
  positive : forall atom, atom ∈ record.atoms → 0 < atom.2
  preserved : forall index, SignedRatio.Equiv (moment record (integrands index)) (moment original (integrands index))

/-- Recursion on actual positive-atom count.  Each newly zero atom is
removed before the recursive call, and the constructed step supplies the
strict decrease.  No bound on denominators or number of unit weights is used. -/
def compressPositive (original : FiniteProbRecord Ω) (integrands : Fin count → Ω → Int)
    (positive : forall atom, atom ∈ original.atoms → 0 < atom.2) : Compressed original integrands :=
  if small : original.atoms.length ≤ count + 1 then
    ⟨original, small, positive, fun _ => SignedRatio.equiv_refl _⟩
  else
    let madeStep := recordStep original integrands positive (by omega)
    let solved := compressPositive madeStep.reduced integrands madeStep.positive
    { record := solved.record
      bound := solved.bound
      positive := solved.positive
      preserved := fun index => SignedRatio.equiv_trans (solved.preserved index) (madeStep.preserved index) }
termination_by original.atoms.length
decreasing_by exact madeStep.shorter

/-- Complete integer-moment compression for every supplied finite rational
record, including zero atoms and repeated labels.  The record is constructed
and normalized internally; the caller supplies only the desired integrands. -/
def compress (original : FiniteProbRecord Ω) (integrands : Fin count → Ω → Int) : Compressed original integrands :=
  let solved := compressPositive original.trimZeros integrands (trimZeros_positive original)
  { record := solved.record
    bound := solved.bound
    positive := solved.positive
    preserved := fun index => by
      have preserved := solved.preserved index
      rw [moment_trimZeros] at preserved
      exact preserved }

end FiniteIntegerCompression
end Probability
end Thesis
