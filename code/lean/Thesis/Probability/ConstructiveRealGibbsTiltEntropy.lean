import Thesis.Probability.ConstructiveRealGibbsTiltMoments

namespace Thesis.Probability.FiniteGibbsTilt
open ConstructiveReal

/-- The log of the actual normalized probability is log weight minus log
partition, using the computed positive floor of each factor. -/
theorem mass_logarithm (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) (i : Fin states) :
    Equiv ((family.mass parameter i).positiveLn (family.massLower parameter i) (family.mass_positive parameter i))
      (sub (family.logWeight parameter i) (family.logPartition parameter)) :=
  equiv_trans (positiveLn_quotient (family.weight parameter i) (family.partition parameter)
    (family.logWeight parameter i).expLower (family.partitionLower parameter)
    (exp_lower _) (family.partition_positive parameter))
    (add_congr (positiveLn_exp _) (equiv_refl _))

/-- Positive finite Shannon entropy in natural units is the expectation of
minus the probability log. This is derived from the continuous entropy
implementation, not used as a new definition of it. -/
theorem entropy_expectation_log (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    Equiv (mul (family.entropy parameter) lnTwo)
      (family.expectation parameter (fun i => neg ((family.mass parameter i).positiveLn
        (family.massLower parameter i) (family.mass_positive parameter i)))) := by
  have converted := realEntropySum_natural ((List.finRange states).map (family.probability parameter))
  simp only [List.map_map, Function.comp_def] at converted
  exact equiv_trans converted (listSum_map_congr (List.finRange states) _ _ (fun i _ =>
    equiv_trans (naturalEntropyTerm_formula (family.mass parameter i) (family.probability parameter i).nonnegative
      (family.probability parameter i).bounded (family.massLower parameter i) (family.mass_positive parameter i))
      (equiv_trans (neg_congr (mul_comm _ _)) (equiv_symm (neg_mul _ _)))))

private theorem neg_sub_swapped (first second : ConstructiveReal) : Equiv (neg (sub first second)) (sub second first) :=
  equiv_trans (neg_add _ _) (equiv_trans (add_congr (equiv_refl _) (neg_neg _)) (add_comm _ _))

theorem expectation_logWeight (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    Equiv (family.expectation parameter (family.logWeight parameter))
      (sub (family.expectation parameter family.offset) (mul parameter (family.expectation parameter family.energy))) :=
  equiv_trans (family.expectation_congr parameter _ _ (fun i =>
    equiv_trans (add_congr (mul_neg _ _) (equiv_refl _)) (add_comm _ _)))
    (equiv_trans (family.expectation_sub parameter family.offset _)
      (add_congr (equiv_refl _) (neg_congr (family.expectation_scale parameter parameter family.energy))))

private abbrev Expression := RationalPolynomial.Expression 3
private def partitionExpr : Expression := .coordinate 0
private def contributionExpr : Expression := .coordinate 1
private def offsetExpr : Expression := .coordinate 2

/-- Entropy-partition dual identity. Fixed log reference weights appear as
an explicit correction `-E[offset]`; with unit reference weights this is
`H_natural = ln Z + parameter * E[energy]`. Bits retain their `ln(2)` factor. -/
theorem entropy_partition (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    Equiv (mul (family.entropy parameter) lnTwo)
      (sub (add (family.logPartition parameter) (mul parameter (family.expectation parameter family.energy)))
        (family.expectation parameter family.offset)) := by
  have logarithm := equiv_trans (family.entropy_expectation_log parameter)
    (equiv_trans (family.expectation_congr parameter _ _ (fun i =>
      equiv_trans (neg_congr (family.mass_logarithm parameter i)) (neg_sub_swapped _ _)))
      (equiv_trans (family.expectation_sub parameter _ _)
        (add_congr (family.expectation_constant parameter (family.logPartition parameter))
          (neg_congr (family.expectation_logWeight parameter)))))
  exact equiv_trans logarithm (RationalPolynomial.Expression.equalityCheck_sound_real
    (.sub partitionExpr (.sub offsetExpr contributionExpr)) (.sub (.add partitionExpr contributionExpr) offsetExpr)
    (by decide +kernel) (fun i => if i = 0 then family.logPartition parameter
      else if i = 1 then mul parameter (family.expectation parameter family.energy) else family.expectation parameter family.offset))

/-- Entropy varies by the covariance of the fixed reference offset with
energy minus parameter times energy variance. This follows from the proved
partition identity and derivative rules, with no entropy smoothness premise. -/
def entropyNatural_hasDerivativeAt (family : FiniteGibbsTilt states) (parameter : ConstructiveReal) :
    HasDerivativeAt (fun t => mul (family.entropy t) lnTwo) parameter
      (sub (family.covariance parameter family.offset family.energy)
        (mul parameter (family.covariance parameter family.energy family.energy))) := by
  let mean := family.expectation parameter family.energy
  let variance := family.covariance parameter family.energy family.energy
  let cross := family.covariance parameter family.offset family.energy
  let product := ((HasDerivativeAt.identity parameter).mul (family.expectation_hasDerivativeAt parameter family.energy)).slope_congr
    (add_congr (one_mul mean) (equiv_refl _))
  let derivative := ((family.logPartition_hasDerivativeAt parameter).add product).add
    ((family.expectation_hasDerivativeAt parameter family.offset).neg)
  have canceled : Equiv (add (neg mean) (add mean (mul parameter (neg variance)))) (mul parameter (neg variance)) :=
    equiv_trans (equiv_symm (add_assoc _ _ _)) (equiv_trans
      (add_congr (equiv_trans (add_comm _ _) (add_neg mean)) (equiv_refl _)) (zero_add _))
  have slope : Equiv (add (add (neg mean) (add mean (mul parameter (neg variance)))) (neg (neg cross)))
      (sub cross (mul parameter variance)) :=
    equiv_trans (add_congr canceled (neg_neg cross))
      (equiv_trans (add_congr (mul_neg _ _) (equiv_refl _)) (add_comm _ _))
  exact (derivative.function_congr (fun t => equiv_symm (family.entropy_partition t))).slope_congr slope

end Thesis.Probability.FiniteGibbsTilt
