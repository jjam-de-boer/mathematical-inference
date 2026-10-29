import Thesis.Probability.FiniteGrandPhysicalFitting

namespace Thesis.Examples.FiniteEnsembleFitting
open Probability Probability.Distros ConstructiveReal
open Probability.Distros.RationalEntropyProblem Probability.Distros.RationalLinear

/-- The excited state has energy one in an unreduced representation. -/
private def binary : FinitePhysicalModel 2 := {
  nonempty := by decide
  energy i := if i = 0 then SignedRatio.zero else ⟨2, 2, by decide⟩
  particles _ := 1 }
private def openBinary : FinitePhysicalModel 2 := {
  nonempty := by decide
  energy := binary.energy
  particles i := if i = 0 then 0 else 1 }
private def third : SignedRatio := ⟨1, 3, by decide⟩
private def unreducedThird : SignedRatio := ⟨2, 6, by decide⟩
private def vector (i : Fin 2) : SignedRatio := if i = 0 then ⟨2, 3, by decide⟩ else third
private def floor : PositiveRatio := ⟨1, 3, by decide, by decide⟩
private def canonicalSeed : (binary.canonicalProblem third).RealLaw :=
  .ofRationalVector _ vector ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
private def grandSeed : (openBinary.grandCanonicalProblem third unreducedThird).RealLaw :=
  .ofRationalVector _ vector ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
private theorem canonicalPositive (i : Fin 2) : LE (ofSignedRatio floor.toSignedRatio) (canonicalSeed.mass i).value := by
  apply (ofSignedRatio_le_iff _ _).mpr
  have cases := (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i
  rcases cases with rfl | rfl <;> decide +kernel
private theorem grandPositive (i : Fin 2) : LE (ofSignedRatio floor.toSignedRatio) (grandSeed.mass i).value := canonicalPositive i

/-- Closed-system particle count is part of the declared state model. -/
example (i : Fin 2) : binary.particles i = 1 := rfl

/-- No beta or optimum certificate is supplied: the actual parameter is
fitted from the exact rational energy target and positive feasible seed. -/
example : Equiv
    (binary.canonical.expectation (binary.fittedBeta third canonicalSeed (fun _ => floor) canonicalPositive) binary.energyValue)
    (ofSignedRatio third) := binary.fitted_canonical_mean third canonicalSeed (fun _ => floor) canonicalPositive

private theorem indicator (i : Fin 2) : Equiv (binary.energyValue i) (realInteger (if i = 1 then 1 else 0)) := by
  have cases := (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i
  rcases cases with rfl | rfl <;> exact (ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)

/-- Independently recovering the fitted excited-state probability as 1/3
checks the physical observable and target connection on an actual named law. -/
example : Equiv
    (binary.canonical.mass (binary.fittedBeta third canonicalSeed (fun _ => floor) canonicalPositive) (1 : Fin 2))
    (ofSignedRatio third) := by
  let beta := binary.fittedBeta third canonicalSeed (fun _ => floor) canonicalPositive
  have selected := equiv_trans (FiniteLinear.pair_congr 2 binary.energyValue _ (binary.canonical.mass beta)
    (binary.canonical.mass beta) indicator (fun _ => equiv_refl _)) (FiniteLinear.pair_unit 2 1 _)
  exact equiv_trans (equiv_symm selected) (binary.fitted_canonical_mean third canonicalSeed (fun _ => floor) canonicalPositive)

/-- E=N makes the two physical features linearly dependent. The constructor
still fits parameters and attains both targets, including the unreduced
particle target. No independent-row assumption is supplied. -/
example :
    let family := openBinary.grandCanonical
      (openBinary.fittedGrandBeta third unreducedThird grandSeed (fun _ => floor) grandPositive)
      (openBinary.fittedGrandAlpha third unreducedThird grandSeed (fun _ => floor) grandPositive)
    Equiv (family.expectation one openBinary.energyValue) (ofSignedRatio third) ∧
      Equiv (family.expectation one openBinary.particleValue) (ofSignedRatio unreducedThird) :=
  openBinary.fitted_grandCanonical_means third unreducedThird grandSeed (fun _ => floor) grandPositive

example (i : Fin 2) : Equiv (grandSeed.maximize.mass i).value
    ((openBinary.grandCanonical
      (openBinary.fittedGrandBeta third unreducedThird grandSeed (fun _ => floor) grandPositive)
      (openBinary.fittedGrandAlpha third unreducedThird grandSeed (fun _ => floor) grandPositive)).mass one i) :=
  openBinary.fitted_grandCanonical_mass third unreducedThird grandSeed (fun _ => floor) grandPositive i

/-- Fitted parameters remain constructive analytic values with certified
rational enclosures; this fixture does not posit exact rational parameters. -/
example (precision : PositiveRatio) :
    let beta := binary.fittedBeta third canonicalSeed (fun _ => floor) canonicalPositive
    LE (ofSignedRatio (beta.enclose precision).lower) beta ∧ LE beta (ofSignedRatio (beta.enclose precision).upper) :=
  (binary.fittedBeta third canonicalSeed (fun _ => floor) canonicalPositive).enclosure_bounds precision

end Thesis.Examples.FiniteEnsembleFitting
