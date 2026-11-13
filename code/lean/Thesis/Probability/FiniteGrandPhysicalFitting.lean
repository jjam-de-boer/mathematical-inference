import Thesis.Probability.FinitePhysicalFitting

namespace Thesis.Probability.FinitePhysicalModel
open ConstructiveReal
open Distros Distros.RationalLinear Distros.RationalEntropyProblem

/-- Prescribed rational energy and particle means. All four original closed
rows remain exact; proportional or constant observables require no rank test. -/
def grandCanonicalProblem (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio) : RationalEntropyProblem states :=
  equalities states model.nonempty [⟨model.energy, energyTarget⟩,
    ⟨(fun i => ⟨(model.particles i : Int), 1, by decide⟩), particleTarget⟩]

def fittedGrandBeta (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio)
    (feasible : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) : ConstructiveReal :=
  let certificate := feasible.fittedNaturalMultipliers lower positive
  sub (certificate.coefficient (0 : Fin 4)) (certificate.coefficient (1 : Fin 4))

def fittedGrandAlpha (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio)
    (feasible : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) : ConstructiveReal :=
  let certificate := feasible.fittedNaturalMultipliers lower positive
  sub (certificate.coefficient (2 : Fin 4)) (certificate.coefficient (3 : Fin 4))

private abbrev Expression := RationalPolynomial.Expression 6
private def e : Expression := .coordinate 0
private def n : Expression := .coordinate 1
private def a : Expression := .coordinate 2
private def b : Expression := .coordinate 3
private def c : Expression := .coordinate 4
private def d : Expression := .coordinate 5
private def z : Expression := .constant SignedRatio.zero
private def scoreExpr : Expression := .add (.mul (.sub z n) d)
  (.add (.mul n c) (.add (.mul (.sub z e) b) (.add (.mul e a) z)))
private def fittedExpr : Expression := .add (.mul (.sub a b) e) (.mul (.sub c d) n)

private theorem grandFitted_score (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio)
    (feasible : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (i : Fin states) :
    Equiv ((feasible.fittedNaturalMultipliers lower positive).score i)
      (add (mul (model.fittedGrandBeta energyTarget particleTarget feasible lower positive) (model.energyValue i))
        (mul (model.fittedGrandAlpha energyTarget particleTarget feasible lower positive) (model.particleValue i))) := by
  let certificate := feasible.fittedNaturalMultipliers lower positive
  let lambda := certificate.coefficient
  change Equiv (add (mul (ofSignedRatio (SignedRatio.neg ⟨(model.particles i : Int), 1, by decide⟩)) (lambda (3 : Fin 4)))
    (add (mul (model.particleValue i) (lambda (2 : Fin 4)))
      (add (mul (ofSignedRatio (SignedRatio.neg (model.energy i))) (lambda (1 : Fin 4)))
        (add (mul (model.energyValue i) (lambda (0 : Fin 4))) zero)))) _
  have polynomial := RationalPolynomial.Expression.equalityCheck_sound_real scoreExpr fittedExpr (by decide +kernel)
    (fun j => if j = 0 then model.energyValue i else if j = 1 then model.particleValue i
      else if j = 2 then lambda (0 : Fin 4) else if j = 3 then lambda (1 : Fin 4)
      else if j = 4 then lambda (2 : Fin 4) else lambda (3 : Fin 4))
  have negate (value : SignedRatio) : Equiv (ofSignedRatio (SignedRatio.neg value)) (sub zero (ofSignedRatio value)) :=
    equiv_trans (ofSignedRatio_neg value) (equiv_symm (zero_add _))
  exact equiv_trans (add_congr (mul_congr (negate _) (equiv_refl _))
    (add_congr (equiv_refl _) (add_congr (mul_congr (negate _) (equiv_refl _)) (equiv_refl _)))) polynomial

private theorem grandFitted_logWeights (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio)
    (feasible : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (i : Fin states) :
    Equiv (((model.grandCanonicalProblem energyTarget particleTarget).gibbsFamily.asTilt
      (feasible.fittedNaturalMultipliers lower positive).coefficient).logWeight one i)
      ((model.grandCanonical (model.fittedGrandBeta energyTarget particleTarget feasible lower positive)
        (model.fittedGrandAlpha energyTarget particleTarget feasible lower positive)).logWeight one i) := by
  let beta := model.fittedGrandBeta energyTarget particleTarget feasible lower positive
  let alpha := model.fittedGrandAlpha energyTarget particleTarget feasible lower positive
  have right : Equiv ((model.grandCanonical beta alpha).logWeight one i)
      (neg (add (mul beta (model.energyValue i)) (mul alpha (model.particleValue i)))) :=
    equiv_trans (add_congr (one_mul _) (positiveLn_one PositiveRatio.one (le_refl one)))
      (equiv_trans (add_zero _) (neg_congr (model.grand_score beta alpha i)))
  exact equiv_trans (gibbsFamily_logWeight (feasible.fittedNaturalMultipliers lower positive) i)
    (equiv_trans (neg_congr (model.grandFitted_score energyTarget particleTarget feasible lower positive i)) (equiv_symm right))

/-- Positive feasibility at the prescribed rational means constructs the
actual named grand-canonical ensemble. Beta and alpha may be signed and
nonunique; their computed values give the unique maximizing probabilities.
Temperature and chemical-potential interpretation remain separate inputs. -/
theorem fitted_grandCanonical_mass (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio)
    (feasible : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (i : Fin states) :
    Equiv (feasible.maximize.mass i).value
      ((model.grandCanonical (model.fittedGrandBeta energyTarget particleTarget feasible lower positive)
        (model.fittedGrandAlpha energyTarget particleTarget feasible lower positive)).mass one i) :=
  equiv_trans (feasible.maximize.gibbsFamily_mass (fun i => interiorLower states (lower i))
    (feasible.maximize_positive lower positive) (feasible.fittedNaturalMultipliers lower positive) i)
    (FiniteGibbsTilt.mass_congr (model.grandFitted_logWeights energyTarget particleTarget feasible lower positive) i)

/-- Both original target means are attained exactly by the fitted named
law. This does not claim exact rational representability of its probabilities. -/
theorem fitted_grandCanonical_means (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio)
    (feasible : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) :
    let family := model.grandCanonical (model.fittedGrandBeta energyTarget particleTarget feasible lower positive)
      (model.fittedGrandAlpha energyTarget particleTarget feasible lower positive)
    Equiv (family.expectation one model.energyValue) (ofSignedRatio energyTarget) ∧
      Equiv (family.expectation one model.particleValue) (ofSignedRatio particleTarget) := by
  let features : List (RationalConstraint states) := [⟨model.energy, energyTarget⟩,
    ⟨(fun i => ⟨(model.particles i : Int), 1, by decide⟩), particleTarget⟩]
  have transfer (observable : Fin states → ConstructiveReal) := FiniteLinear.pair_congr states observable observable _ _
    (fun _ => equiv_refl _) (fun i => equiv_symm (model.fitted_grandCanonical_mass energyTarget particleTarget feasible lower positive i))
  constructor
  · exact equiv_trans (transfer model.energyValue)
      (equiv_trans (equiv_symm (realRationalDot_pair states model.energy (fun i => (feasible.maximize.mass i).value)))
        (equalities_exact model.nonempty features feasible.maximize _ (List.mem_cons_self ..)))
  · exact equiv_trans (transfer model.particleValue)
      (equiv_trans (equiv_symm (realRationalDot_pair states (fun i => ⟨(model.particles i : Int), 1, by decide⟩)
        (fun i => (feasible.maximize.mass i).value)))
        (equalities_exact model.nonempty features feasible.maximize _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem grandCanonical_maximum_unique (model : FinitePhysicalModel states) (energyTarget particleTarget : SignedRatio)
    (feasible : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value)
    (law : (model.grandCanonicalProblem energyTarget particleTarget).RealLaw) (maximal : law.Maximal) (i : Fin states) :
    Equiv (law.mass i).value
      ((model.grandCanonical (model.fittedGrandBeta energyTarget particleTarget feasible lower positive)
        (model.fittedGrandAlpha energyTarget particleTarget feasible lower positive)).mass one i) :=
  equiv_trans (law.maximal_unique feasible.maximize maximal feasible.maximize_maximal i)
    (model.fitted_grandCanonical_mass energyTarget particleTarget feasible lower positive i)

end Thesis.Probability.FinitePhysicalModel
