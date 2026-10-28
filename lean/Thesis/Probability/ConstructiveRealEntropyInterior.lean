import Thesis.Probability.ConstructiveRealEntropyPositivePath
import Thesis.Probability.ConstructiveRealEntropyGibbsForm

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

/-- An explicit optimizer floor determined by a positive feasible coordinate
floor and the finite state count. It is coarse and claims no numerical
conditioning or efficient parameter-fitting rate. -/
def interiorLower (variables : Nat) (lower : PositiveRatio) : PositiveRatio :=
  crossEntropyFloor (entropySizeBound variables) lower

/-- A positive feasible law forces every entropy maximum into the positive
simplex. The proof supplies an actual rational floor, rather than merely
negating equality to zero or deciding the sign of an analytic coordinate.
All original closed rational constraints remain in force along the path. -/
theorem RealLaw.maximum_positive {problem : RationalEntropyProblem variables} (reference target : problem.RealLaw)
    (maximal : reference.Maximal) (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (target.mass i).value) (index : Fin variables) :
    LE (ofSignedRatio (interiorLower variables (lower index)).toSignedRatio) (reference.mass index).value := by
  apply le_of_forall_rational_error
  intro precision
  let n := precision.den
  let sample := reference.towards target n
  let floors := fun i => (lower i).mul (dyadicPrecision n)
  have admitted (i : Fin variables) : LE (ofSignedRatio (floors i).toSignedRatio) (sample.mass i).value := by
    rw [reference.towards_mass target n i]
    exact (reference.mass i).towards_target_positive (target.mass i) (lower i) (positive i) n
  have crossBound : LE (realCrossEntropySum target.mass sample.mass floors admitted) (entropySizeBound variables) :=
    reference.maximum_towards_crossEntropy target maximal lower positive n
  have floorBound := crossEntropyFloor_le target.mass sample.mass floors admitted index (lower index) (positive index)
    (entropySizeBound variables) crossBound
  have sampleClose : Within (dyadicPrecision n).toQProb (reference.mass index).value (sample.mass index).value := by
    rw [reference.towards_mass target n index]
    exact (reference.mass index).towards_within (target.mass index) n
  have smaller : LE (ofSignedRatio (dyadicPrecision n).toSignedRatio) (ofSignedRatio precision.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (dyadicPrecision_small precision))
  exact le_trans floorBound (le_trans sampleClose.2 (add_le_add (le_refl _) smaller))

/-- The effective ideal optimizer therefore has computed positive floors as
soon as the input includes a positive feasible witness. No positivity of
the unknown optimum is an input to this theorem. -/
theorem RealLaw.maximize_positive {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (index : Fin variables) :
    LE (ofSignedRatio (interiorLower variables (lower index)).toSignedRatio) (feasible.maximize.mass index).value :=
  feasible.maximize.maximum_positive feasible feasible.maximize_maximal lower positive index

/-- Computed natural-unit coefficients of the actual ideal optimizer. Both
the ideal law and the finite elimination algorithm have certified rational
evaluations. Redundant rows may yield nonunique multipliers; this function
selects one constructive solution and makes no rank assumption. For closed
inequalities it is an all-row stationarity representation, not signed KKT. -/
def RealLaw.fittedNaturalMultipliers {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) :
    problem.LagrangeCoefficients (fun i => entropyNaturalGradient (feasible.maximize.mass i).value
      (interiorLower variables (lower i)) (feasible.maximize_positive lower positive i)) :=
  feasible.maximize.naturalLagrangeMultipliers feasible.maximize_maximal
    (fun i => interiorLower variables (lower i)) (feasible.maximize_positive lower positive)

/-- The fitted coefficients give a normalized Gibbs description of the
constructed maximum. This is existence from positive feasibility, not a
caller-supplied multiplier or caller-supplied optimum certificate. -/
theorem RealLaw.fitted_gibbsForm {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (index : Fin variables) :
    let coefficients := feasible.fittedNaturalMultipliers lower positive
    Equiv (feasible.maximize.mass index).value
      (mul (exp (neg (coefficients.score index))) coefficients.partitionInverse) :=
  gibbsForm_of_coefficients feasible.maximize (fun i => interiorLower variables (lower i))
    (feasible.maximize_positive lower positive) (feasible.fittedNaturalMultipliers lower positive) index

end Thesis.Probability.Distros.RationalEntropyProblem
