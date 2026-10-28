import Thesis.Probability.ConstructiveRealLagrangePairing

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal
open RationalLinear

/-- Slack in the original closed row `a · p ≤ b`, before denominator
clearing or any decision about whether the analytic slack is zero. -/
def RealLaw.rowSlack {problem : RationalEntropyProblem variables} (law : problem.RealLaw) (row : Fin problem.rows.length) : ConstructiveReal :=
  sub (ofSignedRatio (problem.rows[row.val]).bound)
    (realRationalDot variables (problem.rows[row.val]).coefficients (fun i => (law.mass i).value))

theorem RealLaw.rowSlack_nonnegative {problem : RationalEntropyProblem variables} (law : problem.RealLaw) (row : Fin problem.rows.length) :
    LE zero (law.rowSlack row) :=
  (zero_le_sub_iff _ _).mpr (law.valid _ (List.getElem_mem row.isLt))

/-- KKT signs for entropy maximization under original rows `a · p ≤ b`.
The affine stationarity equation is contained in `certificate`; these are
the additional nonnegative multipliers and complementary products. No
active-row equality test or row-independence assumption is introduced. -/
structure LagrangeCoefficients.KKTAt {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    (certificate : problem.LagrangeCoefficients gradient) (law : problem.RealLaw) : Prop where
  nonnegative : ∀ row, LE zero (certificate.coefficient row)
  complementary : ∀ row, Equiv (mul (certificate.coefficient row) (law.rowSlack row)) zero

/-- Nonnegative changes of entropy units preserve the actual multiplier
signs and complementary products. -/
theorem LagrangeCoefficients.KKTAt.scale {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    {certificate : problem.LagrangeCoefficients gradient} {law : problem.RealLaw} (kkt : certificate.KKTAt law)
    (factor : ConstructiveReal) (positive : LE zero factor) (converted : Fin variables → ConstructiveReal)
    (same : ∀ i, Equiv (mul (gradient i) factor) (converted i)) : (certificate.scale factor converted same).KKTAt law := by
  constructor
  · intro row
    exact mul_nonnegative (kkt.nonnegative row) positive
  · intro row
    exact equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _))
      (equiv_trans (mul_assoc _ _ _) (equiv_trans (mul_congr (equiv_refl _) (kkt.complementary row)) (mul_zero _)))

/-- A certified strict slack forces its multiplier to vanish. This does not
try to decide arbitrary analytic activity: the positive margin is supplied. -/
theorem LagrangeCoefficients.KKTAt.zero_of_positive_slack {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    {certificate : problem.LagrangeCoefficients gradient} {law : problem.RealLaw} (kkt : certificate.KKTAt law)
    (row : Fin problem.rows.length) (lower : PositiveRatio) (positive : LE (ofSignedRatio lower.toSignedRatio) (law.rowSlack row)) :
    Equiv (certificate.coefficient row) zero := by
  have product : Equiv (mul (law.rowSlack row) (certificate.coefficient row)) (mul (law.rowSlack row) zero) :=
    equiv_trans (mul_comm _ _) (equiv_trans (kkt.complementary row) (equiv_symm (mul_zero _)))
  exact ⟨(mul_le_mul_positive_iff (law.rowSlack row) lower positive _ _).mp product.1,
    (mul_le_mul_positive_iff (law.rowSlack row) lower positive _ _).mp product.2⟩

private theorem sum_nonpositive (indices : List A) (terms : A → ConstructiveReal)
    (bounded : ∀ i ∈ indices, LE (terms i) zero) : LE (listSum (indices.map terms)) zero := by
  induction indices with
  | nil => exact le_refl zero
  | cons first rest ih =>
      have compared := add_le_add (bounded first (List.mem_cons_self ..))
        (ih (fun i member => bounded i (List.mem_cons_of_mem _ member)))
      exact (le_congr (equiv_refl _) (zero_add zero)).mp compared

private theorem kkt_row_pair_nonpositive {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    {certificate : problem.LagrangeCoefficients gradient} {reference : problem.RealLaw} (kkt : certificate.KKTAt reference)
    (observed : problem.RealLaw) (row : Fin problem.rows.length) :
    LE (mul (certificate.coefficient row) (realRationalDot variables (problem.rows[row.val]).coefficients
      (fun i => sub (observed.mass i).value (reference.mass i).value))) zero := by
  let multiplier := certificate.coefficient row
  let prior := realRationalDot variables (problem.rows[row.val]).coefficients (fun i => (reference.mass i).value)
  let posterior := realRationalDot variables (problem.rows[row.val]).coefficients (fun i => (observed.mass i).value)
  let bound := ofSignedRatio (problem.rows[row.val]).bound
  have compared := add_le_add (mul_le_mul_nonnegative (kkt.nonnegative row) (observed.valid _ (List.getElem_mem row.isLt)))
    (le_refl (neg (mul multiplier prior)))
  have left : Equiv (mul multiplier (realRationalDot variables (problem.rows[row.val]).coefficients
      (fun i => sub (observed.mass i).value (reference.mass i).value))) (sub (mul multiplier posterior) (mul multiplier prior)) :=
    equiv_trans (mul_congr (equiv_refl multiplier) (realRationalDot_sub_values variables (problem.rows[row.val]).coefficients _ _)) (mul_sub _ _ _)
  have right : Equiv (sub (mul multiplier bound) (mul multiplier prior)) zero :=
    equiv_trans (equiv_symm (mul_sub _ _ _)) (kkt.complementary row)
  exact (le_congr (equiv_symm left) right).mp compared

/-- All feasible directions to competing laws have nonpositive pairing
with a KKT gradient. Boundary competitors are allowed. -/
theorem LagrangeCoefficients.KKTAt.direction_nonpositive {problem : RationalEntropyProblem variables} {gradient : Fin variables → ConstructiveReal}
    {certificate : problem.LagrangeCoefficients gradient} {reference : problem.RealLaw} (kkt : certificate.KKTAt reference)
    (observed : problem.RealLaw) :
    LE (FiniteLinear.pair variables (fun i => sub (observed.mass i).value (reference.mass i).value) gradient) zero := by
  let directions := fun i => sub (observed.mass i).value (reference.mass i).value
  have normalized : Equiv (realDot variables (fun _ => 1) directions) zero :=
    equiv_trans (realDot_sub_values variables (fun _ => 1) _ _)
      (equiv_trans (add_congr observed.normalized (neg_congr reference.normalized)) ((sub_equiv_zero_iff one one).mpr (equiv_refl one)))
  have rowBound : LE (FiniteLinear.pair problem.rows.length certificate.coefficient
      (fun row => realRationalDot variables (problem.rows[row.val]).coefficients directions)) zero :=
    sum_nonpositive (List.finRange problem.rows.length) _ (fun row _ => kkt_row_pair_nonpositive kkt observed row)
  exact (le_congr (equiv_trans (FiniteLinear.pair_comm variables _ gradient)
    (certificate.pairing_normalized directions normalized)) (equiv_refl _)).mpr rowBound

/-- Global sufficient KKT theorem for entropy and rational closed rows.
The proof combines actual nonnegative multipliers and complementary
products with the global Gibbs inequality, including zero
competitors. General constructive KKT necessity is a separate result. -/
theorem RealLaw.maximal_of_kkt {problem : RationalEntropyProblem variables} (reference : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyBitGradient (reference.mass i).value (lower i) (positive i)))
    (kkt : certificate.KKTAt reference) : reference.Maximal := by
  intro observed
  have tangent := realEntropy_tangent_eq_crossEntropy observed.mass reference.mass observed.normalized reference.normalized lower positive
  have crossBound : LE (realCrossEntropySum observed.mass reference.mass lower positive) reference.entropy :=
    (le_congr tangent (add_zero reference.entropy)).mp (add_le_add (le_refl reference.entropy) (kkt.direction_nonpositive observed))
  exact le_trans (realEntropySum_le_crossEntropy observed.mass reference.mass observed.normalized reference.normalized lower positive) crossBound

/-- Natural-to-bit calibration preserves signs and complementarity of
actual coefficient data, not just equivalence of the two gradient formulas. -/
theorem RealLaw.naturalKKT_to_bits {problem : RationalEntropyProblem variables} (reference : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (reference.mass i).value (lower i) (positive i)))
    (kkt : certificate.KKTAt reference) : (reference.coefficientsToBits lower positive certificate).KKTAt reference := by
  have factorPositive : LE zero RationalLogSecant.limit := le_trans
    ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel)) RationalLogSecant.one_le_limit
  constructor
  · intro row
    exact mul_nonnegative (kkt.nonnegative row) factorPositive
  · intro row
    exact equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _))
      (equiv_trans (mul_assoc _ _ _) (equiv_trans (mul_congr (equiv_refl _) (kkt.complementary row)) (mul_zero _)))

theorem RealLaw.maximal_of_natural_kkt {problem : RationalEntropyProblem variables} (reference : problem.RealLaw)
    (lower : Fin variables → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference.mass i).value)
    (certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (reference.mass i).value (lower i) (positive i)))
    (kkt : certificate.KKTAt reference) : reference.Maximal :=
  reference.maximal_of_kkt lower positive (reference.coefficientsToBits lower positive certificate)
    (reference.naturalKKT_to_bits lower positive certificate kkt)

end Thesis.Probability.Distros.RationalEntropyProblem
