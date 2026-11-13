import Thesis.Probability.ConstructiveRealEntropyFirstVariation
import Thesis.Probability.ConstructiveDerivativeLocalDomain
import Thesis.Probability.ConstructiveRealMomentRows
import Thesis.Probability.ConstructiveRealMomentConvexity

namespace Thesis.Probability.ConstructiveReal

/-- A finite intersection of computed positive radii. The empty family has
a harmless radius one; no minimum over analytic values is requested. -/
def finitePositiveRadius : List PositiveRatio → PositiveRatio
  | [] => PositiveRatio.one
  | first :: rest => if PositiveRatio.LE first (finitePositiveRadius rest) then first else finitePositiveRadius rest

theorem finitePositiveRadius_le (radii : List PositiveRatio) (radius : PositiveRatio) (member : radius ∈ radii) :
    PositiveRatio.LE (finitePositiveRadius radii) radius := by
  induction radii with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
      have both : PositiveRatio.LE (finitePositiveRadius (first :: rest)) first ∧
          PositiveRatio.LE (finitePositiveRadius (first :: rest)) (finitePositiveRadius rest) := by
        by_cases ordered : PositiveRatio.LE first (finitePositiveRadius rest)
        · simp only [finitePositiveRadius, if_pos ordered]; exact ⟨PositiveRatio.le_refl _, ordered⟩
        · simp only [finitePositiveRadius, if_neg ordered]
          exact ⟨(PositiveRatio.le_total first (finitePositiveRadius rest)).resolve_left ordered, PositiveRatio.le_refl _⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact both.1
      · exact PositiveRatio.le_trans both.2 (ih later)

/-- A computed two-sided neighborhood on which each affine coordinate keeps
half of its supplied positive lower bound. Direction coordinates may be
arbitrary constructive reals and may have either sign. -/
def affinePositiveRadius (masses directions : Fin variables → ConstructiveReal) (lower : Fin variables → PositiveRatio) : PositiveRatio :=
  finitePositiveRadius ((List.finRange variables).map (fun i =>
    (HasDerivativeAt.affine zero (directions i) (masses i)).positiveRadius (lower i)))

theorem affineCoordinate_positive_near (masses directions : Fin variables → ConstructiveReal)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (masses i))
    (parameter : ConstructiveReal) (close : Within (affinePositiveRadius masses directions lower).toQProb zero parameter)
    (index : Fin variables) :
    LE (ofSignedRatio (lower index).half.toSignedRatio) (affineCoordinate (masses index) (directions index) parameter) := by
  let derivative := HasDerivativeAt.affine zero (directions index) (masses index)
  have listed : derivative.positiveRadius (lower index) ∈
      ((List.finRange variables).map (fun i =>
        (HasDerivativeAt.affine zero (directions i) (masses i)).positiveRadius (lower i))) :=
    List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  have bound := finitePositiveRadius_le _ _ listed
  exact derivative.positive_near (lower index)
    ((le_congr (equiv_refl _) (affineCoordinate_zero _ _)).mpr (positive index)) parameter (within_mono close bound)

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

theorem realDot_congr_values (variables : Nat) (coefficients : Fin variables → Int)
    (first second : Fin variables → ConstructiveReal) (same : ∀ i, Equiv (first i) (second i)) :
    Equiv (realDot variables coefficients first) (realDot variables coefficients second) := by
  induction variables with
  | zero => exact equiv_refl _
  | succ variables ih =>
      exact add_congr (mul_congr (equiv_refl _) (same (Fin.last variables)))
        (ih (fun i => coefficients i.castSucc) (fun i => first i.castSucc) (fun i => second i.castSucc) (fun i => same i.castSucc))

/-- Exact affine evaluation for signed integer responses. This also covers
arbitrary rational rows after their already proved denominator clearing. -/
theorem realDot_affineCoordinate (variables : Nat) (coefficients : Fin variables → Int)
    (masses directions : Fin variables → ConstructiveReal) (parameter : ConstructiveReal) :
    Equiv (realDot variables coefficients (fun i => affineCoordinate (masses i) (directions i) parameter))
      (add (mul (realDot variables coefficients directions) parameter) (realDot variables coefficients masses)) :=
  equiv_trans (realDot_add_values variables coefficients _ masses)
    (add_congr (equiv_trans (realDot_congr_values variables coefficients _ _ (fun i => mul_comm parameter (directions i)))
      (realDot_mul_values variables coefficients directions parameter)) (equiv_refl _))

/-- A tangent that annihilates a row preserves that row at every parameter,
not merely to first order or up to a numerical tolerance. -/
theorem realDot_affineCoordinate_fixed (variables : Nat) (coefficients : Fin variables → Int)
    (masses directions : Fin variables → ConstructiveReal) (kernel : Equiv (realDot variables coefficients directions) zero)
    (parameter : ConstructiveReal) :
    Equiv (realDot variables coefficients (fun i => affineCoordinate (masses i) (directions i) parameter))
      (realDot variables coefficients masses) :=
  equiv_trans (realDot_affineCoordinate variables coefficients masses directions parameter)
    (equiv_trans (add_congr (equiv_trans (mul_congr kernel (equiv_refl _)) (zero_mul parameter)) (equiv_refl _)) (zero_add _))

/-- Normalization supplies the upper endpoint of the entropy domain, even
when a base coordinate is exactly one. Positive tangent coordinates are
controlled by the computed radius; no arbitrary real sign is decided. -/
theorem affine_simplex_positive_near (masses directions : Fin variables → ConstructiveReal)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (masses i))
    (normalized : Equiv (realDot variables (fun _ => 1) masses) one)
    (tangent : Equiv (realDot variables (fun _ => 1) directions) zero)
    (parameter : ConstructiveReal) (close : Within (affinePositiveRadius masses directions lower).toQProb zero parameter) :
    entropyLineDomain masses directions (fun i => (lower i).half) parameter := by
  have positiveNear := affineCoordinate_positive_near masses directions lower positive parameter close
  have nonnegative (i : Fin variables) : LE zero (affineCoordinate (masses i) (directions i) parameter) :=
    le_trans ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr (lower i).half.signed_nonnegative)) (positiveNear i)
  have normalizedNear := equiv_trans (realDot_affineCoordinate_fixed variables (fun _ => 1) masses directions tangent parameter) normalized
  have simplex := real_simplex_of_nonnegative _ nonnegative normalizedNear
  intro i
  exact ⟨positiveNear i, (real_simplex_bounds _ simplex i).2⟩

end Thesis.Probability.Distros.RationalLinear
