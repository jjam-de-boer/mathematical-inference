import Thesis.Probability.FinitePhysicalModel
import Thesis.Probability.ConstructiveRealGibbsTiltOptimality

namespace Thesis.Probability.FinitePhysicalModel
open ConstructiveReal
open Distros.RationalLinear

/-- Analytic versions of the physical observables retain the original signed
rational energies and natural particle counts. -/
def energyValue (model : FinitePhysicalModel states) (i : Fin states) : ConstructiveReal := ofSignedRatio (model.energy i)
def particleValue (model : FinitePhysicalModel states) (i : Fin states) : ConstructiveReal := realInteger (model.particles i : Int)

/-- The energy-constrained finite Gibbs family on the declared states. For
a physical canonical ensemble use `Sector.canonicalModel`, whose computed
sector fixes the particle number. The inverse
energy multiplier is mathematically signed; positive-temperature calibration
is an additional physical condition, not a probability theorem. -/
def canonical (model : FinitePhysicalModel states) : FiniteGibbsTilt states :=
  ⟨model.nonempty, (fun _ => zero), model.energyValue⟩

/-- The canonical law is derived as a global entropy maximum under its
expected-energy constraint, against all normalized analytic competitors,
including zeros. No exact rational solver for this possibly irrational
energy mean is asserted. `Sector.canonicalModel` supplies the fixed-particle
admissible state space for the physical canonical interpretation. -/
theorem canonical_maximal (model : FinitePhysicalModel states) (beta : ConstructiveReal)
    (observed : Fin states → UnitIntervalValue)
    (normalized : Equiv (realDot states (fun _ => 1) (fun i => (observed i).value)) one)
    (fixedEnergy : Equiv (FiniteLinear.pair states model.energyValue (fun i => (observed i).value))
      (model.canonical.expectation beta model.energyValue)) :
    LE (realEntropySum ((List.finRange states).map observed)) (model.canonical.entropy beta) :=
  model.canonical.maximal_zero_offset beta (fun _ => equiv_refl zero) observed normalized fixedEnergy

/-- Energy and particle number are the two original rational features of the
finite grand-canonical family. Each physical microstate has unit reference
weight, including when two states have identical observable values. -/
def grandFamily (model : FinitePhysicalModel states) : FiniteGibbsFamily states 2 := {
  nonempty := model.nonempty
  reference _ := PositiveRatio.one
  response j i := if j = 0 then model.energy i else ⟨(model.particles i : Int), 1, by decide⟩ }

def grandParameters (beta alpha : ConstructiveReal) (j : Fin 2) : ConstructiveReal := if j = 0 then beta else alpha

def grandCanonical (model : FinitePhysicalModel states) (beta alpha : ConstructiveReal) : FiniteGibbsTilt states :=
  model.grandFamily.asTilt (grandParameters beta alpha)

/-- The two independent multiplier terms have their original physical units. -/
theorem grand_score (model : FinitePhysicalModel states) (beta alpha : ConstructiveReal) (i : Fin states) :
    Equiv (model.grandFamily.score (grandParameters beta alpha) i)
      (add (mul beta (model.energyValue i)) (mul alpha (model.particleValue i))) := by
  change Equiv (add (mul (model.particleValue i) alpha) (add (mul (model.energyValue i) beta) zero)) _
  exact equiv_trans (add_congr (mul_comm _ _) (equiv_trans (add_zero _) (mul_comm _ _))) (add_comm _ _)

/-- Chemical-potential convention: alpha = -beta*mu yields beta*(E-mu*N).
This calibration is explicit rather than hidden in the particle feature. -/
theorem grand_chemical_score (model : FinitePhysicalModel states) (beta mu : ConstructiveReal) (i : Fin states) :
    Equiv (model.grandFamily.score (grandParameters beta (neg (mul beta mu))) i)
      (mul beta (sub (model.energyValue i) (mul mu (model.particleValue i)))) :=
  equiv_trans (model.grand_score beta (neg (mul beta mu)) i)
    (equiv_trans (add_congr (equiv_refl _) (equiv_trans (neg_mul _ _) (neg_congr (mul_assoc _ _ _))))
      (equiv_symm (mul_sub _ _ _)))

theorem grand_score_pair (model : FinitePhysicalModel states) (beta alpha : ConstructiveReal)
    (masses : Fin states → ConstructiveReal) :
    Equiv (FiniteLinear.pair states (model.grandFamily.score (grandParameters beta alpha)) masses)
      (add (mul beta (FiniteLinear.pair states model.energyValue masses)) (mul alpha (FiniteLinear.pair states model.particleValue masses))) :=
  equiv_trans (FiniteLinear.pair_congr states _ _ masses masses (model.grand_score beta alpha) (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_add_first states _ _ masses)
      (add_congr (FiniteLinear.pair_scale_first states beta model.energyValue masses) (FiniteLinear.pair_scale_first states alpha model.particleValue masses)))

/-- The grand-canonical law is a global Shannon maximum when energy and
particle means are fixed. These two constraints imply the score constraint;
they are not replaced by a caller-supplied stationarity certificate. -/
theorem grandCanonical_maximal (model : FinitePhysicalModel states) (beta alpha : ConstructiveReal)
    (observed : Fin states → UnitIntervalValue)
    (normalized : Equiv (realDot states (fun _ => 1) (fun i => (observed i).value)) one)
    (fixedEnergy : Equiv (FiniteLinear.pair states model.energyValue (fun i => (observed i).value))
      ((model.grandCanonical beta alpha).expectation one model.energyValue))
    (fixedParticles : Equiv (FiniteLinear.pair states model.particleValue (fun i => (observed i).value))
      ((model.grandCanonical beta alpha).expectation one model.particleValue)) :
    LE (realEntropySum ((List.finRange states).map observed)) ((model.grandCanonical beta alpha).entropy one) := by
  apply (model.grandCanonical beta alpha).maximal_zero_offset one
    (fun i => positiveLn_one PositiveRatio.one (le_refl one)) observed normalized
  exact equiv_trans (model.grand_score_pair beta alpha (fun i => (observed i).value))
    (equiv_trans (add_congr (mul_congr (equiv_refl _) fixedEnergy) (mul_congr (equiv_refl _) fixedParticles))
      (equiv_symm (model.grand_score_pair beta alpha ((model.grandCanonical beta alpha).mass one))))

end Thesis.Probability.FinitePhysicalModel
