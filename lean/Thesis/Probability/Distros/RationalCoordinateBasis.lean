import Thesis.Probability.Distros.RationalVectorSpace

namespace Thesis.Probability.Distros.RationalVector

def positiveIndices (active : Fin n → Bool) : List (Fin n) := (List.finRange n).filter active
def contrastIndices (active : Fin n → Bool) (pivot : Fin n) : List (Fin n) :=
  (positiveIndices active).filter (fun i => decide (i ≠ pivot))
def nullIndices (active : Fin n → Bool) : List (Fin n) := (List.finRange n).filter (fun i => !active i)

def ConstantOn (active : Fin n → Bool) (value : Vector n) : Prop :=
  ∃ constant : SignedRatio, ∀ i, active i = true → SignedRatio.Equiv (value i) constant

theorem positiveIndices_mem (active : Fin n → Bool) (i : Fin n) : i ∈ positiveIndices active ↔ active i = true := by
  simp only [positiveIndices, List.mem_filter, List.mem_finRange, true_and]

theorem contrastIndices_mem (active : Fin n → Bool) (pivot i : Fin n) :
    i ∈ contrastIndices active pivot ↔ active i = true ∧ i ≠ pivot := by
  simp only [contrastIndices, List.mem_filter, positiveIndices_mem, decide_eq_true_eq]

theorem nullIndices_mem (active : Fin n → Bool) (i : Fin n) : i ∈ nullIndices active ↔ active i = false := by
  simp only [nullIndices, List.mem_filter, List.mem_finRange, true_and]
  cases active i <;> decide

theorem contrastIndices_distinct (active : Fin n → Bool) (pivot : Fin n) : (contrastIndices active pivot).Nodup :=
  List.Sublist.nodup List.filter_sublist (List.Sublist.nodup List.filter_sublist (finRange_nodup n))

theorem nullIndices_distinct (active : Fin n → Bool) : (nullIndices active).Nodup :=
  List.Sublist.nodup List.filter_sublist (finRange_nodup n)

private theorem filter_ne_length [DecidableEq I] (indices : List I) (pivot : I)
    (distinct : indices.Nodup) (member : pivot ∈ indices) :
    (indices.filter (fun i => decide (i ≠ pivot))).length + 1 = indices.length := by
  induction indices with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head indices ih =>
      by_cases same : head = pivot
      · subst head
        have unchanged : indices.filter (fun i => decide (i ≠ pivot)) = indices := by
          apply List.filter_eq_self.mpr
          intro i listed
          apply decide_eq_true
          intro equal
          subst i
          exact (List.nodup_cons.mp distinct).1 listed
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, unchanged, List.length_cons]
      · have later := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        have previous := ih (List.nodup_cons.mp distinct).2 later
        simp only [List.filter_cons, decide_eq_true same, if_true, List.length_cons]
        omega

theorem contrastIndices_length (active : Fin n → Bool) (pivot : Fin n) (positive : active pivot = true) :
    (contrastIndices active pivot).length = (positiveIndices active).length - 1 := by
  have count := filter_ne_length (positiveIndices active) pivot
    (List.Sublist.nodup List.filter_sublist (finRange_nodup n)) ((positiveIndices_mem active pivot).mpr positive)
  change (contrastIndices active pivot).length + 1 = (positiveIndices active).length at count
  omega

private theorem sub_sub_cancel (a b : SignedRatio) : SignedRatio.Equiv (SignedRatio.sub a (SignedRatio.sub a b)) b := by
  simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg, Int.natCast_mul,
    Int.mul_add, Int.mul_neg, Int.neg_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- Subtracting the pivot coefficient and discarding null coordinates
chooses a representative of every quotient class modulo constant directions. -/
def contrastRepresentative (active : Fin n → Bool) (pivot : Fin n) (value : Vector n) : Vector n :=
  combine (contrastIndices active pivot) unit (fun i => SignedRatio.sub (value i) (value pivot))

theorem contrastRepresentative_difference (active : Fin n → Bool) (pivot : Fin n) (value : Vector n) :
    ConstantOn active (sub value (contrastRepresentative active pivot value)) := by
  refine ⟨value pivot, ?_⟩
  intro i positive
  have selected := combine_units (contrastIndices active pivot) (contrastIndices_distinct active pivot)
    (fun j => SignedRatio.sub (value j) (value pivot)) i
  by_cases same : i = pivot
  · subst i
    have absent : pivot ∉ contrastIndices active pivot := fun listed => ((contrastIndices_mem active pivot pivot).mp listed).2 rfl
    rw [if_neg absent] at selected
    exact SignedRatio.equiv_trans (ratio_sub_congr (SignedRatio.equiv_refl _) selected) (SignedRatio.sub_zero _)
  · have listed := (contrastIndices_mem active pivot i).mpr ⟨positive, same⟩
    rw [if_pos listed] at selected
    exact SignedRatio.equiv_trans (ratio_sub_congr (SignedRatio.equiv_refl _) selected) (sub_sub_cancel _ _)

theorem Operator.equal_of_difference_kernel (operator : Operator n m) (first second : Vector n)
    (null : operator.Kernel (RationalVector.sub first second)) : Equiv (operator.apply first) (operator.apply second) := by
  intro i
  apply (SignedRatio.sub_equiv_zero_iff _ _).mp
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (operator.sub first second i)) (null i)

/-- An exact kernel characterization constructs the image basis explicitly:
the columns for positive coordinates other than one fixed positive pivot. -/
def imageContrastBasis (operator : Operator n m) (active : Fin n → Bool) (pivot : Fin n)
    (positive : active pivot = true) (criterion : ∀ value, operator.Kernel value ↔ ConstantOn active value) :
    Basis m operator.Image (Fin n) where
  indices := contrastIndices active pivot
  distinct := contrastIndices_distinct active pivot
  vectors := fun i => operator.apply (unit i)
  belongs := by intro i _; exact ⟨unit i, equiv_refl _⟩
  independent := by
    intro coefficients vanished i listed
    have null : operator.Kernel (combine (contrastIndices active pivot) unit coefficients) :=
      equiv_trans (operator.map_combine _ unit coefficients) vanished
    rcases (criterion _).mp null with ⟨constant, constantOn⟩
    have pivotSelected := combine_units _ (contrastIndices_distinct active pivot) coefficients pivot
    have absent : pivot ∉ contrastIndices active pivot := fun member => ((contrastIndices_mem active pivot pivot).mp member).2 rfl
    rw [if_neg absent] at pivotSelected
    have constantZero := SignedRatio.equiv_trans (SignedRatio.equiv_symm (constantOn pivot positive)) pivotSelected
    have selected := combine_units _ (contrastIndices_distinct active pivot) coefficients i
    rw [if_pos listed] at selected
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm selected)
      (SignedRatio.equiv_trans (constantOn i ((contrastIndices_mem active pivot i).mp listed).1) constantZero)
  spanning := by
    rintro value ⟨source, same⟩
    let coefficients := fun i => SignedRatio.sub (source i) (source pivot)
    have null := (criterion _).mpr (contrastRepresentative_difference active pivot source)
    have sameImage := operator.equal_of_difference_kernel source (contrastRepresentative active pivot source) null
    refine ⟨coefficients, ?_⟩
    exact equiv_trans (equiv_symm (operator.map_combine _ unit coefficients)) (equiv_trans (equiv_symm sameImage) same)

/-- The image basis has exactly r-1 members, where r counts positive
coordinates. This includes a single positive coordinate and hence rank zero. -/
def contrastRank (operator : Operator n m) (active : Fin n → Bool) (pivot : Fin n)
    (positive : active pivot = true) (criterion : ∀ value, operator.Kernel value ↔ ConstantOn active value) :
    RankCertificate operator ((positiveIndices active).length - 1) :=
  ⟨Fin n, imageContrastBasis operator active pivot positive criterion, contrastIndices_length active pivot positive⟩

end Thesis.Probability.Distros.RationalVector
