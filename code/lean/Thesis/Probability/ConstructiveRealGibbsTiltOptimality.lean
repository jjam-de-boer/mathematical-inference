import Thesis.Probability.ConstructiveRealGibbsTiltEntropy
import Thesis.Probability.ConstructiveRealGibbsInequality

namespace Thesis.Probability.FiniteGibbsTilt
open ConstructiveReal
open Distros.RationalLinear

private theorem constant_normalized (size : Nat) (value : ConstructiveReal) (masses : Fin size → ConstructiveReal)
    (normalized : Equiv (realDot size (fun _ => 1) masses) one) :
    Equiv (FiniteLinear.pair size (fun _ => value) masses) value :=
  equiv_trans (FiniteLinear.pair_congr size _ (fun _ => mul value one) masses masses
    (fun _ => equiv_symm (mul_one value)) (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_scale_first size value (fun _ => one) masses)
      (equiv_trans (mul_congr (equiv_refl _) (equiv_trans
        (equiv_symm (FiniteLinear.realDot_pair size (fun _ => 1) masses)) normalized)) (mul_one value)))

private theorem neg_sub_swapped (first second : ConstructiveReal) : Equiv (neg (sub first second)) (sub second first) :=
  equiv_trans (neg_add _ _) (equiv_trans (add_congr (equiv_refl _) (neg_neg _)) (add_comm _ _))

private theorem difference_cancel (first second : ConstructiveReal) : Equiv (add (sub first second) second) first :=
  equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _)
    (equiv_trans (add_comm _ _) (add_neg second))) (add_zero _))

private abbrev Expression := RationalPolynomial.Expression 3
private def partitionExpr : Expression := .coordinate 0
private def contributionExpr : Expression := .coordinate 1
private def offsetExpr : Expression := .coordinate 2

/-- Cross entropy against a finite Gibbs law depends only on the observed
energy and reference-offset means. Observed zero probabilities are admitted;
only the explicitly positive reference probabilities are logged. -/
theorem crossEntropy_natural (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observed : Fin states → UnitIntervalValue)
    (normalized : Equiv (realDot states (fun _ => 1) (fun i => (observed i).value)) one) :
    Equiv (mul (realCrossEntropySum observed (family.probability parameter)
      (family.massLower parameter) (family.mass_positive parameter)) lnTwo)
      (sub (add (family.logPartition parameter)
        (mul parameter (FiniteLinear.pair states family.energy (fun i => (observed i).value))))
        (FiniteLinear.pair states family.offset (fun i => (observed i).value))) := by
  let masses := fun i => (observed i).value
  let terms := fun i => neg (mul (masses i) ((family.mass parameter i).positiveLog2
    (family.massLower parameter i) (family.mass_positive parameter i)))
  have distribution : Equiv (mul (listSum ((List.finRange states).map terms)) lnTwo)
      (listSum ((List.finRange states).map (fun i => mul (terms i) lnTwo))) := by
    simpa only [List.map_map, Function.comp_def] using listSum_mul ((List.finRange states).map terms) lnTwo
  have scalar (i : Fin states) : Equiv (mul (terms i) lnTwo)
      (mul (neg ((family.mass parameter i).positiveLn (family.massLower parameter i) (family.mass_positive parameter i))) (masses i)) :=
    equiv_trans (neg_mul _ _) (equiv_trans (neg_congr (mul_assoc _ _ _))
      (equiv_trans (neg_congr (mul_comm _ _)) (equiv_symm (neg_mul _ _))))
  have converted : Equiv (mul (realCrossEntropySum observed (family.probability parameter)
      (family.massLower parameter) (family.mass_positive parameter)) lnTwo)
      (FiniteLinear.pair states (fun i => neg ((family.mass parameter i).positiveLn
        (family.massLower parameter i) (family.mass_positive parameter i))) masses) :=
    equiv_trans distribution (listSum_map_congr (List.finRange states) _ _ (fun i _ => scalar i))
  have observedLog : Equiv (FiniteLinear.pair states (family.logWeight parameter) masses)
      (sub (FiniteLinear.pair states family.offset masses) (mul parameter (FiniteLinear.pair states family.energy masses))) :=
    equiv_trans (FiniteLinear.pair_congr states _ _ masses masses (fun i =>
      equiv_trans (add_congr (mul_neg _ _) (equiv_refl _)) (add_comm _ _)) (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.pair_sub_first states family.offset _ masses)
        (add_congr (equiv_refl _) (neg_congr (FiniteLinear.pair_scale_first states parameter family.energy masses))))
  have logarithm := equiv_trans converted (equiv_trans
    (FiniteLinear.pair_congr states _ _ masses masses (fun i =>
      equiv_trans (neg_congr (family.mass_logarithm parameter i)) (neg_sub_swapped _ _)) (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_sub_first states _ _ masses)
      (add_congr (constant_normalized states (family.logPartition parameter) masses normalized) (neg_congr observedLog))))
  exact equiv_trans logarithm (RationalPolynomial.Expression.equalityCheck_sound_real
    (.sub partitionExpr (.sub offsetExpr contributionExpr)) (.sub (.add partitionExpr contributionExpr) offsetExpr)
    (by decide +kernel) (fun i => if i = 0 then family.logPartition parameter else if i = 1 then
      mul parameter (FiniteLinear.pair states family.energy masses) else FiniteLinear.pair states family.offset masses))

/-- Under a fixed energy mean, the Gibbs law maximizes Shannon natural
entropy plus the mean log reference weight. This gives the correct objective
for aggregated states with degeneracies. Unit reference weights reduce it
to ordinary Shannon entropy. No rationality of the fixed mean is assumed. -/
theorem weighted_maximal (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observed : Fin states → UnitIntervalValue)
    (normalized : Equiv (realDot states (fun _ => 1) (fun i => (observed i).value)) one)
    (fixed : Equiv (FiniteLinear.pair states family.energy (fun i => (observed i).value)) (family.expectation parameter family.energy)) :
    LE (add (mul (realEntropySum ((List.finRange states).map observed)) lnTwo)
      (FiniteLinear.pair states family.offset (fun i => (observed i).value)))
      (add (mul (family.entropy parameter) lnTwo) (family.expectation parameter family.offset)) := by
  let target := add (family.logPartition parameter) (mul parameter (family.expectation parameter family.energy))
  let offset := FiniteLinear.pair states family.offset (fun i => (observed i).value)
  have factor : LE zero lnTwo := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr RationalLogSecant.limit.positiveInverseLower.signed_nonnegative)) lnTwo_lower
  have gibbs := realEntropySum_le_crossEntropy observed (family.probability parameter) normalized (family.normalized parameter)
    (family.massLower parameter) (family.mass_positive parameter)
  have compared := (le_congr (equiv_refl _) (mul_comm _ _)).mp (mul_le_mul_nonnegative factor gibbs)
  have natural : LE (mul (realEntropySum ((List.finRange states).map observed)) lnTwo) (sub target offset) :=
    (le_congr (mul_comm _ _) (equiv_trans (family.crossEntropy_natural parameter observed normalized)
      (add_congr (add_congr (equiv_refl _) (mul_congr (equiv_refl _) fixed)) (equiv_refl _)))).mp compared
  have upper := (le_congr (equiv_refl _) (difference_cancel target offset)).mp (add_le_add natural (le_refl offset))
  have reference : Equiv (add (mul (family.entropy parameter) lnTwo) (family.expectation parameter family.offset)) target :=
    equiv_trans (add_congr (family.entropy_partition parameter) (equiv_refl _)) (difference_cancel _ _)
  exact (le_congr (equiv_refl _) (equiv_symm reference)).mp upper

/-- Ordinary Shannon maximality when energy and reference-offset means are
fixed. The theorem compares with every normalized analytic law, including
boundary competitors, and introduces no solver for arbitrary real means. -/
theorem maximal_fixed_means (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (observed : Fin states → UnitIntervalValue)
    (normalized : Equiv (realDot states (fun _ => 1) (fun i => (observed i).value)) one)
    (fixedEnergy : Equiv (FiniteLinear.pair states family.energy (fun i => (observed i).value)) (family.expectation parameter family.energy))
    (fixedOffset : Equiv (FiniteLinear.pair states family.offset (fun i => (observed i).value)) (family.expectation parameter family.offset)) :
    LE (realEntropySum ((List.finRange states).map observed)) (family.entropy parameter) := by
  have weighted := (le_congr (add_congr (equiv_refl _) fixedOffset) (equiv_refl _)).mp
    (family.weighted_maximal parameter observed normalized fixedEnergy)
  have natural := (add_le_add_right_iff _ _ (family.expectation parameter family.offset)).mp weighted
  exact (mul_le_mul_positive_iff lnTwo RationalLogSecant.limit.positiveInverseLower lnTwo_lower _ _).mp
    ((le_congr (mul_comm _ _) (mul_comm _ _)).mp natural)

/-- Zero reference offsets give the usual canonical maximum-entropy theorem
under only a fixed expected energy. -/
theorem maximal_zero_offset (family : FiniteGibbsTilt states) (parameter : ConstructiveReal)
    (zeroOffset : ∀ i, Equiv (family.offset i) zero)
    (observed : Fin states → UnitIntervalValue)
    (normalized : Equiv (realDot states (fun _ => 1) (fun i => (observed i).value)) one)
    (fixedEnergy : Equiv (FiniteLinear.pair states family.energy (fun i => (observed i).value)) (family.expectation parameter family.energy)) :
    LE (realEntropySum ((List.finRange states).map observed)) (family.entropy parameter) := by
  apply family.maximal_fixed_means parameter observed normalized fixedEnergy
  exact equiv_trans (FiniteLinear.pair_congr states family.offset (fun _ => zero) _ _ zeroOffset (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_zero_first states _) (equiv_symm (equiv_trans
      (family.expectation_congr parameter _ _ zeroOffset) (family.expectation_constant parameter zero))))

end Thesis.Probability.FiniteGibbsTilt
