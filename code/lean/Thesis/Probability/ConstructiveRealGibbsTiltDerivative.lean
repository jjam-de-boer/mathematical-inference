import Thesis.Probability.ConstructiveRealGibbsTilt
import Thesis.Probability.ConstructiveDerivativePositiveComposition
import Thesis.Probability.ConstructiveRealExpDerivative
import Thesis.Probability.ConstructiveDerivativeProduct

namespace Thesis.Probability.FiniteGibbsTilt
open ConstructiveReal
open Distros.RationalLinear

/-- The unnormalized observable numerator, before division by `Z`. -/
def numerator (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) : ConstructiveReal :=
  FiniteLinear.pair states observable (family.weight parameter)

theorem expectation_numerator (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) :
    Equiv (family.expectation parameter observable) (mul (family.numerator parameter observable) (family.partitionInverse parameter)) :=
  equiv_trans (FiniteLinear.pair_congr states observable observable (family.mass parameter)
    (fun i => mul (family.partitionInverse parameter) (family.weight parameter i)) (fun _ => equiv_refl _) (fun i => mul_comm _ _))
    (equiv_trans (FiniteLinear.pair_scale_second states (family.partitionInverse parameter) observable (family.weight parameter)) (mul_comm _ _))

/-- Individual tilted weights have the derivative proved from Taylor
exponential differentiation, for arbitrary signed analytic energies. -/
def weight_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) :
    HasDerivativeAt (fun t => family.weight t i) parameter (mul (neg (family.energy i)) (family.weight parameter i)) :=
  exp_affine_hasDerivativeAt parameter (neg (family.energy i)) (family.offset i)

/-- Finite partition differentiation, with an effective remainder modulus
assembled from the actual finite list of weight derivatives. -/
def partition_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    HasDerivativeAt family.partition parameter (neg (family.numerator parameter family.energy)) :=
  (HasDerivativeAt.listSum (List.finRange states) (fun i t => family.weight t i)
    (fun i => mul (neg (family.energy i)) (family.weight parameter i)) parameter (family.weight_hasDerivativeAt parameter)).slope_congr
    (FiniteLinear.pair_neg_first states family.energy (family.weight parameter))

/-- Natural log partition gradient is minus expected energy. Point-dependent
positive bounds are handled by the proved local-domain chain rule. -/
def logPartition_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    HasDerivativeAt family.logPartition parameter (neg (family.expectation parameter family.energy)) :=
  ((family.partition_hasDerivativeAt parameter).positiveLn family.partitionLower family.partition_positive).slope_congr
    (equiv_trans (neg_mul _ _) (neg_congr (equiv_symm (family.expectation_numerator parameter family.energy))))

/-- The base-two log partition derivative includes the necessary `1/ln(2)`
coefficient. Natural and bit conventions are not silently identified. -/
def log2Partition_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    HasDerivativeAt family.log2Partition parameter
      (neg (mul (family.expectation parameter family.energy) RationalLogSecant.limit)) :=
  (((family.logPartition_hasDerivativeAt parameter).mul_constant RationalLogSecant.limit).function_congr
    (fun t => equiv_symm (positiveLog2_from_positiveLn _ _ _))).slope_congr (neg_mul _ _)

/-- The derivative of `1/Z` is `E[energy]/Z`; its sign is unrestricted when
energies may be signed. Only positivity of `Z` is used. -/
def partitionInverse_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    HasDerivativeAt family.partitionInverse parameter
      (mul (family.expectation parameter family.energy) (family.partitionInverse parameter)) := by
  let inverse := family.partitionInverse parameter
  let value := family.numerator parameter family.energy
  let derivative := (family.partition_hasDerivativeAt parameter).positiveInverse family.partitionLower family.partition_positive
  have algebra : Equiv (mul (neg value) (neg (mul inverse inverse))) (mul (mul value inverse) inverse) :=
    equiv_trans (neg_mul _ _) (equiv_trans (neg_congr (mul_neg _ _))
      (equiv_trans (neg_neg _) (equiv_symm (mul_assoc _ _ _))))
  exact derivative.slope_congr (equiv_trans algebra
    (mul_congr (equiv_symm (family.expectation_numerator parameter family.energy)) (equiv_refl _)))

/-- Normalized probability derivative. All probabilities are the constructed
analytic law, not newly asserted rational `Distro` weights. -/
def mass_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) :
    HasDerivativeAt (fun t => family.mass t i) parameter
      (mul (family.mass parameter i) (sub (family.expectation parameter family.energy) (family.energy i))) := by
  let mean := family.expectation parameter family.energy
  let mass := family.mass parameter i
  let derivative := (family.weight_hasDerivativeAt parameter i).mul (family.partitionInverse_hasDerivativeAt parameter)
  have first : Equiv (mul (mul (neg (family.energy i)) (family.weight parameter i)) (family.partitionInverse parameter))
      (neg (mul mass (family.energy i))) :=
    equiv_trans (mul_assoc _ _ _) (equiv_trans (neg_mul _ _) (neg_congr (mul_comm _ _)))
  have second : Equiv (mul (family.weight parameter i) (mul mean (family.partitionInverse parameter))) (mul mass mean) :=
    equiv_trans (mul_congr (equiv_refl _) (mul_comm _ _)) (equiv_symm (mul_assoc _ _ _))
  exact derivative.slope_congr (equiv_trans (add_congr first second)
    (equiv_trans (add_comm _ _) (equiv_symm (mul_sub _ _ _))))

private theorem sub_reversed (first second : ConstructiveReal) : Equiv (sub first second) (neg (sub second first)) :=
  equiv_symm (equiv_trans (neg_add _ _) (equiv_trans (add_congr (equiv_refl _) (neg_neg _)) (add_comm _ _)))

/-- Summing normalized weight variations yields minus covariance. This
applies to every signed fixed observable and to energy itself. -/
def expectation_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observable : Fin states → ConstructiveReal) :
    HasDerivativeAt (fun t => family.expectation t observable) parameter
      (neg (family.covariance parameter observable family.energy)) := by
  let mean := family.expectation parameter family.energy
  let slopes := fun i => mul (family.mass parameter i) (sub mean (family.energy i))
  have derivative (i : Fin states) : HasDerivativeAt (fun t => mul (observable i) (family.mass t i)) parameter
      (mul (observable i) (slopes i)) :=
    ((HasDerivativeAt.constant parameter (observable i)).mul (family.mass_hasDerivativeAt parameter i)).slope_congr
      (equiv_trans (add_congr (zero_mul _) (equiv_refl _)) (zero_add _))
  let summed := HasDerivativeAt.listSum (List.finRange states) (fun i t => mul (observable i) (family.mass t i))
    (fun i => mul (observable i) (slopes i)) parameter derivative
  have expanded (i : Fin states) : Equiv (slopes i)
      (sub (mul mean (family.mass parameter i)) (mul (family.energy i) (family.mass parameter i))) :=
    equiv_trans (mul_sub _ _ _) (add_congr (mul_comm _ _) (neg_congr (mul_comm _ _)))
  have cross : Equiv (FiniteLinear.pair states observable (fun i => mul (family.energy i) (family.mass parameter i)))
      (family.expectation parameter (fun i => mul (observable i) (family.energy i))) :=
    listSum_map_congr (List.finRange states) _ _ (fun i _ => equiv_symm (mul_assoc _ _ _))
  exact summed.slope_congr (equiv_trans (FiniteLinear.pair_congr states observable observable slopes _ (fun _ => equiv_refl _) expanded)
    (equiv_trans (FiniteLinear.pair_sub_second states observable _ _) (equiv_trans
      (add_congr (equiv_trans (FiniteLinear.pair_scale_second states mean observable (family.mass parameter)) (mul_comm _ _)) (neg_congr cross))
      (sub_reversed _ _))))

/-- The second natural-log partition derivative is the energy variance,
expressed as the actual derivative of its first-derivative function. -/
def logPartition_secondDerivative (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    HasDerivativeAt (fun t => neg (family.expectation t family.energy)) parameter
      (family.covariance parameter family.energy family.energy) :=
  ((family.expectation_hasDerivativeAt parameter family.energy).neg).slope_congr (neg_neg _)

end Thesis.Probability.FiniteGibbsTilt
