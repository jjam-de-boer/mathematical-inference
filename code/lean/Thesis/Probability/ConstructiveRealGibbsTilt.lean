import Thesis.Probability.ConstructiveRealBilinearFubini
import Thesis.Probability.ConstructiveRealAffineSimplex
import Thesis.Probability.ConstructiveRealEntropyVectorConcavity
import Thesis.Probability.ConstructiveRealNaturalLog

namespace Thesis.Probability
open ConstructiveReal
open Distros.RationalLinear

/-- A finite exponential tilt on distinct declared states. Analytic offsets
can include reference weights or other fixed parameter terms. Even equal
energies leave two indices as distinct states. These auxiliary analytic
probabilities do not change the rational atom weights of `Distro`. -/
structure FiniteGibbsTilt (states : Nat) where
  nonempty : 0 < states
  offset : Fin states → ConstructiveReal
  energy : Fin states → ConstructiveReal

namespace FiniteGibbsTilt

def logWeight (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) : ConstructiveReal :=
  add (mul parameter (neg (family.energy i))) (family.offset i)

def weight (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) : ConstructiveReal :=
  (family.logWeight parameter i).exp

def partition (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) : ConstructiveReal :=
  listSum ((List.finRange states).map (family.weight parameter))

def partitionLower (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) : PositiveRatio :=
  (family.logWeight parameter ⟨0, family.nonempty⟩).expLower

theorem partition_positive (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    LE (ofSignedRatio (family.partitionLower parameter).toSignedRatio) (family.partition parameter) := by
  apply le_trans (exp_lower (family.logWeight parameter ⟨0, family.nonempty⟩))
  exact le_listSum_of_mem _ (fun value member => by
    obtain ⟨i, _, same⟩ := List.mem_map.mp member
    cases same
    exact exp_nonnegative _) _ (List.mem_map.mpr ⟨⟨0, family.nonempty⟩, List.mem_finRange _, rfl⟩)

def partitionInverse (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) : ConstructiveReal :=
  (family.partition parameter).positiveInverse (family.partitionLower parameter) (family.partition_positive parameter)

def mass (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) : ConstructiveReal :=
  mul (family.weight parameter i) (family.partitionInverse parameter)

def massLower (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) : PositiveRatio :=
  (family.logWeight parameter i).expLower.mul (family.partition parameter).positiveInverseLower

theorem mass_positive (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) :
    LE (ofSignedRatio (family.massLower parameter i).toSignedRatio) (family.mass parameter i) :=
  mul_positive_lower _ _ _ _ (exp_lower _)
    ((family.partition parameter).positiveInverse_lower (family.partitionLower parameter) (family.partition_positive parameter))

theorem mass_nonnegative (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) :
    LE zero (family.mass parameter i) :=
  mul_nonnegative (exp_nonnegative _)
    ((family.partition parameter).positiveInverse_nonnegative (family.partitionLower parameter) (family.partition_positive parameter))

theorem weight_sum (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    Equiv (realDot states (fun _ => 1) (family.weight parameter)) (family.partition parameter) :=
  equiv_trans (FiniteLinear.realDot_pair states (fun _ => 1) (family.weight parameter))
    (listSum_map_congr (List.finRange states) _ _ (fun i _ => one_mul _))

/-- Normalization is proved from the constructed reciprocal of the actual
finite partition sum, with no rational representability assumption. -/
theorem normalized (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    Equiv (realDot states (fun _ => 1) (family.mass parameter)) one :=
  equiv_trans (realDot_mul_values states (fun _ => 1) (family.weight parameter) (family.partitionInverse parameter))
    (equiv_trans (mul_congr (family.weight_sum parameter) (equiv_refl _))
      ((family.partition parameter).mul_positiveInverse (family.partitionLower parameter) (family.partition_positive parameter)))

def probability (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) : UnitIntervalValue :=
  ⟨family.mass parameter i, family.mass_nonnegative parameter i,
    (real_simplex_bounds _ (real_simplex_of_nonnegative _ (family.mass_nonnegative parameter) (family.normalized parameter)) i).2⟩

/-- Observables may be signed auxiliary analytic coordinates. Rational
responses embed directly, including energy and particle counts. -/
def expectation (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (observable : Fin states → ConstructiveReal) : ConstructiveReal :=
  FiniteLinear.pair states observable (family.mass parameter)

def covariance (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (first second : Fin states → ConstructiveReal) : ConstructiveReal :=
  sub (family.expectation parameter (fun i => mul (first i) (second i)))
    (mul (family.expectation parameter first) (family.expectation parameter second))

def entropy (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) : ConstructiveReal :=
  realEntropySum ((List.finRange states).map (family.probability parameter))

def logPartition (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) : ConstructiveReal :=
  (family.partition parameter).positiveLn (family.partitionLower parameter) (family.partition_positive parameter)

def log2Partition (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) : ConstructiveReal :=
  (family.partition parameter).positiveLog2 (family.partitionLower parameter) (family.partition_positive parameter)

end FiniteGibbsTilt
end Thesis.Probability
