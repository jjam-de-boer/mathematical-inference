import Thesis.Probability.Distros.EntropyMomentConvex
import Thesis.Probability.ConstructiveInteger

namespace Thesis.Probability.Distros

/-- A computed finite offset makes an integer response nonnegative on the
original declared grid, including its forced-zero coordinates. -/
def EntropyGrid.responseShift (grid : EntropyGrid A) (response : A → Int) : Nat :=
  grid.cells.foldr (fun value bound => max (-response value).toNat bound) 0

private theorem shift_bound (values : List A) (response : A → Int) (value : A) (member : value ∈ values) :
    (-response value).toNat ≤ values.foldr (fun cell bound => max (-response cell).toNat bound) 0 := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

def EntropyGrid.shiftedResponse (grid : EntropyGrid A) (response : A → Int) (value : A) : Nat :=
  (response value + (grid.responseShift response : Int)).toNat

/-- Only the declared cells are used to choose the offset. Unsupported null
atom labels need not satisfy this identity and impose no extra hypothesis. -/
theorem EntropyGrid.shiftedResponse_spec (grid : EntropyGrid A) (response : A → Int) (value : A)
    (member : value ∈ grid.cells) :
    (grid.shiftedResponse response value : Int) = response value + (grid.responseShift response : Int) := by
  have clipped : -response value ≤ ((-response value).toNat : Int) := by
    cases val : -response value with
    | ofNat n => exact Int.le_refl _
    | negSucc n => exact Int.le_of_lt (Int.negSucc_lt_zero n)
  have bounded := Int.le_trans clipped (Int.ofNat_le.mpr (shift_bound grid.cells response value member))
  have nonnegative : 0 ≤ response value + (grid.responseShift response : Int) := by
    have difference := Int.sub_nonneg.mpr bounded
    simpa only [Int.sub_neg, Int.add_comm] using difference
  exact ConstructiveInteger.toNat_cast _ nonnegative

theorem MomentInterval.shiftedMean [DecidableEq A] (constraint : MomentInterval A) (μ : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells)) :
    SignedRatio.Equiv (μ.expectNat (grid.shiftedResponse constraint.response)).toSignedRatio
      (SignedRatio.add (constraint.mean μ) ⟨(grid.responseShift constraint.response : Int), 1, Nat.zero_lt_one⟩) := by
  have terms := μ.rationalExpectation_congr_positive
    (fun value => (QProb.ofNat (grid.shiftedResponse constraint.response value)).toSignedRatio)
    (fun value => SignedRatio.add (⟨constraint.response value, 1, Nat.zero_lt_one⟩ : SignedRatio)
      ⟨(grid.responseShift constraint.response : Int), 1, Nat.zero_lt_one⟩) (by
        intro atom member weight
        have identity := grid.shiftedResponse_spec constraint.response atom.1 (support atom member weight)
        simpa only [QProb.ofNat, QProb.toSignedRatio, SignedRatio.Equiv, SignedRatio.add,
          Nat.one_mul, Int.natCast_one, Int.mul_one] using identity)
  have expanded := μ.rationalExpectation_add
    (fun value => (⟨constraint.response value, 1, Nat.zero_lt_one⟩ : SignedRatio))
    (fun _ => (⟨(grid.responseShift constraint.response : Int), 1, Nat.zero_lt_one⟩ : SignedRatio))
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.rationalExpectation_ofNat _))
    (SignedRatio.equiv_trans terms (SignedRatio.equiv_trans expanded
      (SignedRatio.add_congr (SignedRatio.equiv_refl _) (μ.rationalExpectation_constant _))))

theorem MomentInterval.shiftedMean_congr [DecidableEq A] (constraint : MomentInterval A) (μ ν : Distro A) (grid : EntropyGrid A)
    (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (same : SignedRatio.Equiv (constraint.mean μ) (constraint.mean ν)) :
    QProb.Equiv (μ.expectNat (grid.shiftedResponse constraint.response)) (ν.expectNat (grid.shiftedResponse constraint.response)) := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  exact SignedRatio.equiv_trans (constraint.shiftedMean μ grid first)
    (SignedRatio.equiv_trans (SignedRatio.add_congr same (SignedRatio.equiv_refl _))
      (SignedRatio.equiv_symm (constraint.shiftedMean ν grid second)))

/-- Equal interval endpoints force equal selected means in any two feasible
laws. This does not assume row independence or positive cell probabilities. -/
theorem MomentInterval.mean_eq_of_exact (constraint : MomentInterval A) (μ ν : Distro A)
    (endpoints : SignedRatio.Equiv constraint.lower constraint.upper)
    (first : constraint.LawHolds μ) (second : constraint.LawHolds ν) :
    SignedRatio.Equiv (constraint.mean μ) (constraint.mean ν) := by
  have reverse : SignedRatio.LE constraint.upper constraint.lower :=
    (SignedRatio.le_congr endpoints (SignedRatio.equiv_refl _)).mp (SignedRatio.le_refl _)
  exact SignedRatio.equiv_of_le_of_le
    (SignedRatio.le_trans first.2 (SignedRatio.le_trans reverse second.1))
    (SignedRatio.le_trans second.2 (SignedRatio.le_trans reverse first.1))

end Thesis.Probability.Distros
