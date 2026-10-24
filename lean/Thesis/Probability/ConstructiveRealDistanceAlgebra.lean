import Thesis.Probability.ConstructiveRealReciprocal

namespace Thesis.Probability.ConstructiveReal

/-- Translation preserves and reflects closed rational distance bounds. -/
theorem within_add_left_iff (error : QProb) (offset x y : ConstructiveReal) :
    Within error (add offset x) (add offset y) ↔ Within error x y := by
  have cancel (a b : ConstructiveReal) :
      LE (add offset a) (add (add offset b) (ofSignedRatio error.toSignedRatio)) ↔
        LE a (add b (ofSignedRatio error.toSignedRatio)) := by
    have rearranged : Equiv (add (add offset b) (ofSignedRatio error.toSignedRatio))
        (add (add b (ofSignedRatio error.toSignedRatio)) offset) :=
      equiv_trans (add_assoc _ _ _) (add_comm _ _)
    exact (le_congr (add_comm _ _) rearranged).trans (add_le_add_right_iff _ _ offset)
  exact and_congr (cancel x y) (cancel y x)

/-- Multiplication by an explicitly positive rational scales distances
exactly; reflection uses the already proved positive inverse law. -/
theorem within_mul_positive_iff (factor : PositiveRatio) (error : QProb) (x y : ConstructiveReal) :
    Within (QProb.mul factor.toQProb error)
      (mul (ofSignedRatio factor.toSignedRatio) x) (mul (ofSignedRatio factor.toSignedRatio) y) ↔ Within error x y := by
  let f := ofSignedRatio factor.toSignedRatio
  let e := ofSignedRatio error.toSignedRatio
  have errorProduct : Equiv (ofSignedRatio (QProb.mul factor.toQProb error).toSignedRatio) (mul f e) := by
    rw [QProb.toSignedRatio_mul]
    exact equiv_symm (ofSignedRatio_mul _ _)
  have collect (value : ConstructiveReal) :
      Equiv (add (mul f value) (ofSignedRatio (QProb.mul factor.toQProb error).toSignedRatio)) (mul f (add value e)) :=
    equiv_trans (add_congr (equiv_refl _) errorProduct) (equiv_symm (mul_add _ _ _))
  exact and_congr
    ((le_congr (equiv_refl _) (collect y)).trans (mul_le_mul_positive_iff f factor (le_refl _) _ _))
    ((le_congr (equiv_refl _) (collect x)).trans (mul_le_mul_positive_iff f factor (le_refl _) _ _))

/-- A positive rational step supplies a nearby real point without choosing a
representative or comparing arbitrary real values. -/
theorem within_positive_shift (point : ConstructiveReal) (radius : PositiveRatio) :
    Within radius.toQProb point (add point (ofSignedRatio radius.toSignedRatio)) := by
  let r := ofSignedRatio radius.toSignedRatio
  have positive : LE zero r := (ofSignedRatio_le_iff _ _).mpr
    ((SignedRatio.zero_le_iff_nonnegative _).mpr radius.signed_nonnegative)
  have increased : LE point (add point r) :=
    (le_congr (add_zero point) (equiv_refl _)).mp (add_le_add (le_refl _) positive)
  exact ⟨le_trans increased (add_le_add increased (le_refl r)), le_refl _⟩

theorem positive_shift_increment (point : ConstructiveReal) (radius : PositiveRatio) :
    Equiv (sub (add point (ofSignedRatio radius.toSignedRatio)) point) (ofSignedRatio radius.toSignedRatio) :=
  equiv_trans (add_congr (add_comm _ _) (equiv_refl _))
    (equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg point)) (add_zero _)))

end Thesis.Probability.ConstructiveReal
