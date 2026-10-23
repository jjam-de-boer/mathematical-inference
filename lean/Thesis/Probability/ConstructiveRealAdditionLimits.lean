import Thesis.Probability.ConstructiveRealDistance

namespace Thesis.Probability.PositiveRatio

theorem half_le (precision : PositiveRatio) : LE precision.half precision := divideNat_le precision 2 (by decide)

end Thesis.Probability.PositiveRatio

namespace Thesis.Probability.ConstructiveReal

theorem add_four (a b c d : ConstructiveReal) : Equiv (add (add a b) (add c d)) (add (add a c) (add b d)) := by
  constructor
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_interchange _ _ _ _)).mp
      (SignedRatio.add_le_add (SignedRatio.add_le_add (a.coherent _ _) (b.coherent _ _))
        (SignedRatio.add_le_add (c.coherent _ _) (d.coherent _ _)))
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_interchange _ _ _ _)).mp
      (SignedRatio.add_le_add (SignedRatio.add_le_add (a.coherent _ _) (c.coherent _ _))
        (SignedRatio.add_le_add (b.coherent _ _) (d.coherent _ _)))

/-- Adding two certified approximations adds their rational error bounds. -/
theorem within_add {first second : QProb} {a a' b b' : ConstructiveReal}
    (left : Within first a a') (right : Within second b b') : Within (QProb.add first second) (add a b) (add a' b') := by
  have collect (x y : ConstructiveReal) : Equiv
      (add (add x (ofSignedRatio first.toSignedRatio)) (add y (ofSignedRatio second.toSignedRatio)))
      (add (add x y) (ofSignedRatio (QProb.add first second).toSignedRatio)) := by
    rw [QProb.toSignedRatio_add]
    exact equiv_trans (add_four _ _ _ _) (add_congr (equiv_refl _) (ofSignedRatio_add _ _))
  exact ⟨(le_congr (equiv_refl _) (collect a' b')).mp (add_le_add left.1 right.1),
    (le_congr (equiv_refl _) (collect a b)).mp (add_le_add left.2 right.2)⟩

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RegularRationalApproximation

/-- A real value within each advertised approximation radius is the limit. -/
theorem limit_unique_within (approximation : RegularRationalApproximation) (x : ConstructiveReal)
    (bounded : ∀ precision, ConstructiveReal.Within precision.toQProb x (ConstructiveReal.ofSignedRatio (approximation.value precision))) :
    ConstructiveReal.Equiv approximation.limit x := by
  apply ConstructiveReal.equiv_of_within_all
  intro error
  have combined := ConstructiveReal.within_triangle (approximation.limit_within error.half)
    (ConstructiveReal.within_symm (bounded error.half))
  have same : QProb.Equiv (QProb.add error.half.toQProb error.half.toQProb) error.toQProb := by
    apply (QProb.toSignedRatio_equiv_iff _ _).mp
    rw [QProb.toSignedRatio_add]
    exact error.half_add_half
  exact ConstructiveReal.within_mono combined (QProb.le_congr (QProb.equiv_refl _) same (QProb.le_refl _))

/-- Pointwise rational addition with half-precision arguments is regular. -/
def add (first second : RegularRationalApproximation) : RegularRationalApproximation where
  value precision := SignedRatio.add (first.value precision.half) (second.value precision.half)
  regular left right := by
    have compared := SignedRatio.add_le_add (first.regular left.half right.half) (second.regular left.half right.half)
    have collected := SignedRatio.add_interchange (first.value right.half)
      (SignedRatio.add left.half.toSignedRatio right.half.toSignedRatio) (second.value right.half)
      (SignedRatio.add left.half.toSignedRatio right.half.toSignedRatio)
    have errors := SignedRatio.equiv_trans (SignedRatio.add_interchange left.half.toSignedRatio right.half.toSignedRatio
      left.half.toSignedRatio right.half.toSignedRatio)
      (SignedRatio.add_congr left.half_add_half right.half_add_half)
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _)
      (SignedRatio.equiv_trans collected (SignedRatio.add_congr (SignedRatio.equiv_refl _) errors))).mp compared

theorem add_limit (first second : RegularRationalApproximation) :
    ConstructiveReal.Equiv (first.add second).limit (ConstructiveReal.add first.limit second.limit) := by
  apply limit_unique_within
  intro precision
  have combined := ConstructiveReal.within_add (first.limit_within precision.half) (second.limit_within precision.half)
  have same : QProb.Equiv (QProb.add precision.half.toQProb precision.half.toQProb) precision.toQProb := by
    apply (QProb.toSignedRatio_equiv_iff _ _).mp
    rw [QProb.toSignedRatio_add]
    exact precision.half_add_half
  have widened := ConstructiveReal.within_mono combined (QProb.le_congr (QProb.equiv_refl _) same (QProb.le_refl _))
  exact (ConstructiveReal.within_congr (ConstructiveReal.equiv_refl _) (ConstructiveReal.ofSignedRatio_add _ _)).mp widened

end Thesis.Probability.RegularRationalApproximation
