import Thesis.Probability.Distros.UncertaintyMeasure
import Thesis.Probability.Distros.RationalPolya

/-!
Common-count presentations of normalized rational probability vectors.

`ofCounts` interprets a natural count list summing to a positive denominator
as rational coordinates. `countPresentation` computes such a presentation
for any normalized rational vector by clearing its actual entry denominators;
there is no supplied denominator bound. The proof identifies corresponding
coordinates up to rational equivalence and retains zero coordinates.
These counts are an exact finite representation of masses, not observations
from an experiment or an additional assumption about empirical frequencies.
The SameMasses helpers bridge indexed and recursive coordinate comparisons.
-/

namespace Thesis.Probability.ProbabilityVector

theorem sameMasses_refl (values : List QProb) : SameMasses values values := by
  induction values with
  | nil => trivial
  | cons value rest ih => exact ⟨QProb.equiv_refl value, ih⟩

theorem sameMasses_map (values : List A) (first second : A → QProb)
    (same : ∀ value ∈ values, QProb.Equiv (first value) (second value)) :
    SameMasses (values.map first) (values.map second) := by
  induction values with
  | nil => trivial
  | cons value rest ih =>
      exact ⟨same value (List.mem_cons_self ..), ih (fun entry member => same entry (List.mem_cons_of_mem _ member))⟩

/-- Matching dimensions and equivalent in-range coordinates suffice for
the recursive SameMasses relation. No arbitrary choices of fraction normal forms
are needed to compare the two vector presentations. -/
theorem sameMasses_of_getD (first second : List QProb) (dimension : first.length = second.length)
    (same : ∀ index, index < first.length → QProb.Equiv (first.getD index QProb.zero) (second.getD index QProb.zero)) :
    SameMasses first second := by
  induction first generalizing second with
  | nil => cases second with
    | nil => trivial
    | cons _ _ => simp only [List.length_nil, List.length_cons] at dimension; omega
  | cons value rest ih => cases second with
    | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
    | cons other tail =>
        exact ⟨same 0 (by simp), ih tail (Nat.succ.inj dimension)
          (fun index within => same (index + 1) (Nat.succ_lt_succ within))⟩

theorem sameMasses_replicate (values : List QProb) (entry : QProb)
    (same : ∀ value ∈ values, QProb.Equiv value entry) : SameMasses values (List.replicate values.length entry) := by
  induction values with
  | nil => trivial
  | cons value rest ih =>
      exact ⟨same value (List.mem_cons_self ..), ih (fun other member => same other (List.mem_cons_of_mem _ member))⟩

/-- Counts are a finite presentation of probability coordinates, not an
assumption about sampling frequencies or about an uncertainty formula. -/
def ofCounts (counts : List Nat) (den : Nat) (positive : 0 < den) (mass : counts.sum = den) : ProbabilityVector where
  masses := counts.map (fun count => ⟨count, den, positive⟩)
  normalized := by
    have common := QProb.listSum_mk_same_den den positive counts
    rw [mass] at common
    exact QProb.equiv_trans common (by simp only [QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul])

/-- Read an in-range coordinate of the constructed vector as its original
count over the common denominator. The range condition excludes the default entry. -/
theorem ofCounts_getD (counts : List Nat) (den : Nat) (positive : 0 < den) (mass : counts.sum = den)
    (index : Nat) (within : index < counts.length) :
    (ofCounts counts den positive mass).masses.getD index QProb.zero = (⟨counts.getD index 0, den, positive⟩ : QProb) := by
  simp only [ofCounts]
  rw [← List.getElem_eq_getD (h := by simpa only [List.length_map] using within) QProb.zero,
    List.getElem_map, List.getElem_eq_getD (h := within) 0]

/-- A computed natural-count representation, with a positive denominator,
exact total balance and coordinatewise rational equivalence to the target vector. -/
structure CountPresentation (vector : ProbabilityVector) where
  counts : List Nat
  den : Nat
  den_pos : 0 < den
  mass : counts.sum = den
  represents : SameMasses (ofCounts counts den den_pos mass).masses vector.masses

/-- Construct a common-count presentation of every normalized rational
vector. Its denominator is computed from its actual entries, with no cap. -/
def countPresentation (vector : ProbabilityVector) : CountPresentation vector := by
  let counts := Distros.rationalUrnWeights vector.masses
  let den := (QProb.listSum vector.masses).den
  have positive : 0 < den := (QProb.listSum vector.masses).den_pos
  have mass : counts.sum = den := by
    rw [Distros.rationalUrnWeights_sum]
    simpa only [QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul] using vector.normalized
  refine ⟨counts, den, positive, mass, ?_⟩
  have dimension : counts.length = vector.masses.length := Distros.rationalUrnWeights_length vector.masses
  apply sameMasses_of_getD
  · simpa only [ofCounts, List.length_map] using dimension
  · intro index within
    have inside : index < counts.length := by simpa only [ofCounts, List.length_map] using within
    rw [ofCounts_getD counts den positive mass index inside]
    have represented := Distros.rationalUrnWeights_parameter vector.masses index
    exact represented

end Thesis.Probability.ProbabilityVector
