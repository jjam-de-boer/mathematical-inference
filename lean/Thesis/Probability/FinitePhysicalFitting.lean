import Thesis.Probability.FinitePhysicalEnsembles
import Thesis.Probability.ConstructiveRealEqualityConstraints
import Thesis.Probability.ConstructiveRealEntropyPartitionIdentity
import Thesis.Probability.ConstructiveRealGibbsTiltComparison

namespace Thesis.Probability.FinitePhysicalModel
open ConstructiveReal
open Distros Distros.RationalLinear Distros.RationalEntropyProblem

/-- Prescribed rational mean energy on the actual declared states. Exact
normalization is part of `RealLaw`; the two original rows fix the mean. -/
def canonicalProblem (model : FinitePhysicalModel states) (target : SignedRatio) : RationalEntropyProblem states :=
  equalities states model.nonempty [⟨model.energy, target⟩]

theorem canonicalProblem_mean (model : FinitePhysicalModel states) (target : SignedRatio)
    (law : (model.canonicalProblem target).RealLaw) :
    Equiv (FiniteLinear.pair states model.energyValue (fun i => (law.mass i).value)) (ofSignedRatio target) :=
  equiv_trans (equiv_symm (realRationalDot_pair states model.energy (fun i => (law.mass i).value)))
    (equalities_exact model.nonempty [⟨model.energy, target⟩] law _ (List.mem_cons_self ..))

/-- A fitted inverse-energy parameter from positive feasibility alone. The
optimizer, its quantitative positivity, and the original-row multipliers are
constructed by the general finite solver. The signed parameter is the
difference of the two row coefficients; no parameter solution is supplied.
Positive temperature calibration is a separate physical condition. -/
def fittedBeta (model : FinitePhysicalModel states) (target : SignedRatio)
    (feasible : (model.canonicalProblem target).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) : ConstructiveReal :=
  let certificate := feasible.fittedNaturalMultipliers lower positive
  sub (certificate.coefficient (0 : Fin 2)) (certificate.coefficient (1 : Fin 2))

private theorem canonical_score (model : FinitePhysicalModel states) (target : SignedRatio)
    (feasible : (model.canonicalProblem target).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (i : Fin states) :
    Equiv ((feasible.fittedNaturalMultipliers lower positive).score i)
      (mul (model.fittedBeta target feasible lower positive) (model.energyValue i)) := by
  let certificate := feasible.fittedNaturalMultipliers lower positive
  change Equiv (add (mul (ofSignedRatio (SignedRatio.neg (model.energy i))) (certificate.coefficient (1 : Fin 2)))
    (add (mul (model.energyValue i) (certificate.coefficient (0 : Fin 2))) zero)) _
  exact equiv_trans (add_congr (equiv_trans (mul_congr (ofSignedRatio_neg _) (equiv_refl _)) (neg_mul _ _)) (add_zero _))
    (equiv_trans (add_comm _ _) (equiv_trans (equiv_symm (mul_sub _ _ _)) (mul_comm _ _)))

private theorem canonical_logWeights (model : FinitePhysicalModel states) (target : SignedRatio)
    (feasible : (model.canonicalProblem target).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (i : Fin states) :
    Equiv (((model.canonicalProblem target).gibbsFamily.asTilt (feasible.fittedNaturalMultipliers lower positive).coefficient).logWeight one i)
      (model.canonical.logWeight (model.fittedBeta target feasible lower positive) i) :=
  equiv_trans (gibbsFamily_logWeight (feasible.fittedNaturalMultipliers lower positive) i)
    (equiv_trans (neg_congr (model.canonical_score target feasible lower positive i))
      (equiv_symm (equiv_trans (add_zero _) (mul_neg _ _))))

/-- The constructed ideal maximum is the named canonical law at the fitted
parameter. This connects prescribed mean constraints to the ensemble itself,
rather than merely proving maximality at a parameter's preexisting mean.
A physical closed system uses the fixed-particle admissible sector. -/
theorem fitted_canonical_mass (model : FinitePhysicalModel states) (target : SignedRatio)
    (feasible : (model.canonicalProblem target).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (i : Fin states) :
    Equiv (feasible.maximize.mass i).value (model.canonical.mass (model.fittedBeta target feasible lower positive) i) :=
  equiv_trans (feasible.maximize.gibbsFamily_mass (fun i => interiorLower states (lower i))
    (feasible.maximize_positive lower positive) (feasible.fittedNaturalMultipliers lower positive) i)
    (FiniteGibbsTilt.mass_congr (model.canonical_logWeights target feasible lower positive) i)

/-- The fitted named law has exactly the requested rational energy mean.
Its probabilities and parameter may be irrational; rational solver outputs
continue to satisfy the same original rational constraints exactly. -/
theorem fitted_canonical_mean (model : FinitePhysicalModel states) (target : SignedRatio)
    (feasible : (model.canonicalProblem target).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) :
    Equiv (model.canonical.expectation (model.fittedBeta target feasible lower positive) model.energyValue) (ofSignedRatio target) :=
  equiv_trans (FiniteLinear.pair_congr states model.energyValue model.energyValue _ _ (fun _ => equiv_refl _)
    (fun i => equiv_symm (model.fitted_canonical_mass target feasible lower positive i))) (model.canonicalProblem_mean target feasible.maximize)

/-- Every maximum under the original prescribed mean has the same canonical
probabilities. No row-rank or unique-parameter hypothesis is needed. -/
theorem canonical_maximum_unique (model : FinitePhysicalModel states) (target : SignedRatio)
    (feasible : (model.canonicalProblem target).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value)
    (law : (model.canonicalProblem target).RealLaw) (maximal : law.Maximal) (i : Fin states) :
    Equiv (law.mass i).value (model.canonical.mass (model.fittedBeta target feasible lower positive) i) :=
  equiv_trans (law.maximal_unique feasible.maximize maximal feasible.maximize_maximal i)
    (model.fitted_canonical_mass target feasible lower positive i)

end Thesis.Probability.FinitePhysicalModel
