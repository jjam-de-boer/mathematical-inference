import Thesis.Probability.Distros.RationalCoordinateBasis

namespace Thesis.Probability.Distros.RationalVector

def kernelIndices (active : Fin n → Bool) : List (Option (Fin n)) := none :: (nullIndices active).map some

def kernelVector : Option (Fin n) → Vector n
  | none => fun _ => SignedRatio.one
  | some i => unit i

theorem kernelIndices_distinct (active : Fin n → Bool) : (kernelIndices active).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨i, _, same⟩
    cases same
  · apply List.pairwise_map.mpr
    apply (nullIndices_distinct active).imp
    intro first second different same
    exact different (Option.some.inj same)

theorem kernelIndices_some_mem (active : Fin n → Bool) (i : Fin n) :
    some i ∈ kernelIndices active ↔ i ∈ nullIndices active := by
  simp [kernelIndices]

theorem combine_kernel_coordinate (active : Fin n → Bool) (coefficients : Option (Fin n) → SignedRatio) (i : Fin n) :
    SignedRatio.Equiv (combine (kernelIndices active) kernelVector coefficients i)
      (SignedRatio.add (coefficients none) (if i ∈ nullIndices active then coefficients (some i) else SignedRatio.zero)) := by
  change SignedRatio.Equiv (SignedRatio.add (SignedRatio.mul (coefficients none) SignedRatio.one)
    (SignedRatio.listSum (((nullIndices active).map some).map (fun index => SignedRatio.mul (coefficients index) (kernelVector index i))))) _
  rw [List.map_map]
  exact SignedRatio.add_congr (SignedRatio.mul_one _)
    (combine_units (nullIndices active) (nullIndices_distinct active) (fun j => coefficients (some j)) i)

private theorem add_sub_cancel (a b : SignedRatio) : SignedRatio.Equiv (SignedRatio.add a (SignedRatio.sub b a)) b := by
  simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg, Int.natCast_mul,
    Int.mul_add, Int.mul_neg, Int.neg_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- The kernel basis consists of the all-ones vector and one coordinate
unit for each null category. Positive coefficients must agree; null ones
remain free. No zero-weight category is removed from the ambient space. -/
def constantKernelBasis (operator : Operator n m) (active : Fin n → Bool) (pivot : Fin n)
    (positive : active pivot = true) (criterion : ∀ value, operator.Kernel value ↔ ConstantOn active value) :
    Basis n operator.Kernel (Option (Fin n)) where
  indices := kernelIndices active
  distinct := kernelIndices_distinct active
  vectors := kernelVector
  belongs := by
    intro index member
    apply (criterion _).mpr
    cases index with
    | none => exact ⟨SignedRatio.one, fun _ _ => SignedRatio.equiv_refl _⟩
    | some j =>
        have null := (nullIndices_mem active j).mp ((kernelIndices_some_mem active j).mp member)
        refine ⟨SignedRatio.zero, ?_⟩
        intro i present
        have different : j ≠ i := by intro same; subst j; rw [present] at null; cases null
        change SignedRatio.Equiv (unit j i) SignedRatio.zero
        rw [unit, if_neg different]
        exact SignedRatio.equiv_refl _
  independent := by
    intro coefficients vanished index member
    have pivotAbsent : pivot ∉ nullIndices active := by
      intro listed
      have null := (nullIndices_mem active pivot).mp listed
      rw [positive] at null
      cases null
    have atPivot := combine_kernel_coordinate active coefficients pivot
    rw [if_neg pivotAbsent] at atPivot
    have noneZero := SignedRatio.equiv_trans (SignedRatio.equiv_symm
      (SignedRatio.equiv_trans atPivot (SignedRatio.add_zero _))) (vanished pivot)
    cases index with
    | none => exact noneZero
    | some j =>
        have listed := (kernelIndices_some_mem active j).mp member
        have selected := combine_kernel_coordinate active coefficients j
        rw [if_pos listed] at selected
        have reduced := SignedRatio.equiv_trans (SignedRatio.add_congr noneZero (SignedRatio.equiv_refl (coefficients (some j))))
          (SignedRatio.zero_add _)
        exact SignedRatio.equiv_trans (SignedRatio.equiv_symm reduced)
          (SignedRatio.equiv_trans (SignedRatio.equiv_symm selected) (vanished j))
  spanning := by
    intro value null
    rcases (criterion value).mp null with ⟨constant, constantOn⟩
    let coefficients : Option (Fin n) → SignedRatio := fun index => match index with
      | none => constant
      | some i => SignedRatio.sub (value i) constant
    refine ⟨coefficients, ?_⟩
    intro i
    have selected := combine_kernel_coordinate active coefficients i
    by_cases listed : i ∈ nullIndices active
    · rw [if_pos listed] at selected
      exact SignedRatio.equiv_trans selected (add_sub_cancel constant (value i))
    · have present : active i = true := by
        have notNull : active i ≠ false := fun null => listed ((nullIndices_mem active i).mpr null)
        cases same : active i
        · exact False.elim (notNull same)
        · rfl
      rw [if_neg listed] at selected
      exact SignedRatio.equiv_trans selected (SignedRatio.equiv_trans (SignedRatio.add_zero constant)
        (SignedRatio.equiv_symm (constantOn i present)))

theorem constantKernelBasis_cardinality (operator : Operator n m) (active : Fin n → Bool) (pivot : Fin n)
    (positive : active pivot = true) (criterion : ∀ value, operator.Kernel value ↔ ConstantOn active value) :
    (constantKernelBasis operator active pivot positive criterion).indices.length = (nullIndices active).length + 1 := by
  simp only [constantKernelBasis, kernelIndices, List.length_cons, List.length_map]

end Thesis.Probability.Distros.RationalVector
