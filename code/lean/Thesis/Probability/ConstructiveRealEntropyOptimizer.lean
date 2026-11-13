import Thesis.Probability.ConstructiveRealEntropyOptimizerSequence
import Thesis.Probability.ConstructiveRealLinearLimits

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- Effective limit of rational near-maximizers. Each original rational
constraint row holds at the limit, including normalization, equalities,
interval endpoints and forced zeros. No compactness or choice axiom is used. -/
def entropyLimitLaw [DecidableEq A] {problem : PartialMomentProblem A}
    (approximations : (n : Nat) → problem.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb) :
    problem.RealCompatibleLaw :=
  .ofVector problem (fun i => (entropyMaximizingCoordinate approximations i).limit)
    (RationalLinear.realSatisfies_limits problem.rows (entropyMaximizingCoordinate approximations)
      (fun n => (approximations n).law.toReal.valid))

/-- The finite entropy sum of the approximants has its own explicit Cauchy
modulus. Continuity is on the closed simplex, so vanishing coordinates are
included without assuming a uniform strictly positive lower bound. -/
def entropyMaximizingEntropy [DecidableEq A] {problem : PartialMomentProblem A}
    (approximations : (n : Nat) → problem.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb) :
    RealCauchySequence :=
  RealCauchySequence.listSum ((List.finRange problem.cells.length).map (fun i =>
    (entropyMaximizingCoordinate approximations i).mapEntropy
      (fun n => ((approximations n).law.toReal.mass i).nonnegative)
      (fun n => ((approximations n).law.toReal.mass i).bounded)))

theorem entropyMaximizingEntropy_value [DecidableEq A] {problem : PartialMomentProblem A}
    (approximations : (n : Nat) → problem.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb) (n : Nat) :
    Equiv ((entropyMaximizingEntropy approximations).value n) (approximations n).law.toReal.entropy := by
  unfold entropyMaximizingEntropy
  rw [RealCauchySequence.listSum_value]
  simp only [RealCompatibleLaw.entropy, realEntropySum, List.map_map]
  exact equiv_refl _

theorem entropyMaximizingEntropy_limit [DecidableEq A] {problem : PartialMomentProblem A}
    (approximations : (n : Nat) → problem.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb) :
    Equiv (entropyMaximizingEntropy approximations).limit (entropyLimitLaw approximations).entropy := by
  apply equiv_trans (RealCauchySequence.listSum_limit _)
  simp only [RealCompatibleLaw.entropy, realEntropySum, List.map_map]
  apply listSum_map_congr
  intro i _
  exact (entropyMaximizingCoordinate approximations i).mapEntropy_limit _ _

/-- Attained maximum over every feasible analytic law, expressed in closed
order. This is a property to prove, rather than an assumed maximizer input. -/
def RealCompatibleLaw.Maximal {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw) : Prop :=
  ∀ other : problem.RealCompatibleLaw, LE other.entropy law.entropy

/-- The constructed feasible limit attains the ideal maximum. Rational
certificates bound every real competitor, and their gaps and the entropy-tail
errors both tend effectively to zero. -/
theorem entropyLimitLaw_maximal [DecidableEq A] {problem : PartialMomentProblem A}
    (approximations : (n : Nat) → problem.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb) :
    (entropyLimitLaw approximations).Maximal := by
  intro other
  apply le_of_forall_rational_error
  intro precision
  let sequence := entropyMaximizingEntropy approximations
  let n := max (sequence.modulus precision.half.half.half) precision.half.den
  have tail := sequence.tail_within precision.half n (Nat.le_max_left _ _)
  have entropyUpper : LE (approximations n).law.toReal.entropy
      (add (entropyLimitLaw approximations).entropy (ofSignedRatio precision.half.toSignedRatio)) :=
    (le_congr (entropyMaximizingEntropy_value approximations n)
      (add_congr (entropyMaximizingEntropy_limit approximations) (equiv_refl _))).mp tail.1
  have errorUpper : LE (ofSignedRatio (PositiveRatio.unitPrecision n).toSignedRatio)
      (ofSignedRatio precision.half.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr
      (PositiveRatio.unitPrecision_le precision.half n (Nat.le_max_right _ _)))
  have compared := le_trans ((approximations n).nearOptimal other) (add_le_add entropyUpper errorUpper)
  have collect : Equiv
      (add (add (entropyLimitLaw approximations).entropy (ofSignedRatio precision.half.toSignedRatio))
        (ofSignedRatio precision.half.toSignedRatio))
      (add (entropyLimitLaw approximations).entropy (ofSignedRatio precision.toSignedRatio)) :=
    equiv_trans (add_assoc _ _ _) (add_congr (equiv_refl _)
      (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr precision.half_add_half)))
  exact (le_congr (equiv_refl _) collect).mp compared

/-- Maximal laws are unique up to equality of every declared probability
value. Distinct approximation presentations need not be equal Lean records. -/
theorem RealCompatibleLaw.maximal_unique {problem : PartialMomentProblem A}
    (first second : problem.RealCompatibleLaw) (optimalX : first.Maximal) (optimalY : second.Maximal)
    (index : Fin problem.cells.length) : Equiv (first.mass index).value (second.mass index).value := by
  have nearX : first.NearOptimal QProb.zero := fun other =>
    (le_congr (equiv_refl _) (add_zero first.entropy)).mpr (optimalX other)
  have nearY : second.NearOptimal QProb.zero := fun other =>
    (le_congr (equiv_refl _) (add_zero second.entropy)).mpr (optimalY other)
  have distance := first.squaredDistance_le_of_nearOptimal second QProb.zero QProb.zero nearX nearY
  have zeroBound : Equiv (ofSignedRatio (QProb.mul (QProb.ofNat 4) (QProb.add QProb.zero QProb.zero)).toSignedRatio) zero :=
    (ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)
  have vanished := le_trans (first.coordinate_square_le_distance second index)
    ((le_congr (equiv_refl _) zeroBound).mp distance)
  exact equiv_of_square_sub_zero _ _ vanished

/-- Ideal auxiliary maximum computed from the existing exactly feasible
rational solver. Its weights may be irrational; actual `Distro` outputs at
every finite precision remain rational and exactly feasible. -/
def idealEntropyLaw [DecidableEq A] (problem : PartialMomentProblem A) (initial : problem.CompatibleLaw) :
    problem.RealCompatibleLaw := entropyLimitLaw (problem.entropyApproximations initial)

theorem idealEntropyLaw_maximal [DecidableEq A] (problem : PartialMomentProblem A) (initial : problem.CompatibleLaw) :
    (problem.idealEntropyLaw initial).Maximal := entropyLimitLaw_maximal _

/-- A common explicit modulus controls every grid coordinate of the actual
rational solver outputs. This is a convergence certificate, not merely a
uniqueness argument for a hypothetically existing optimum. -/
theorem idealEntropyLaw_coordinate_converges [DecidableEq A] (problem : PartialMomentProblem A)
    (initial : problem.CompatibleLaw) (radius : PositiveRatio) (n : Nat)
    (later : radius.half.half.entropyGapPrecision.den ≤ n) (index : Fin problem.cells.length) :
    Within radius.toQProb ((problem.entropyApproximations initial n).law.toReal.mass index).value
      ((problem.idealEntropyLaw initial).mass index).value :=
  (entropyMaximizingCoordinate (problem.entropyApproximations initial) index).tail_within radius n later

/-- The initial feasible witness affects presentations and the reference
algorithm's path, but not the probability values of its ideal output. -/
theorem idealEntropyLaw_initial_independent [DecidableEq A] (problem : PartialMomentProblem A)
    (first second : problem.CompatibleLaw) (index : Fin problem.cells.length) :
    Equiv ((problem.idealEntropyLaw first).mass index).value ((problem.idealEntropyLaw second).mass index).value :=
  (problem.idealEntropyLaw first).maximal_unique (problem.idealEntropyLaw second)
    (problem.idealEntropyLaw_maximal first) (problem.idealEntropyLaw_maximal second) index

/-- A supplied feasible analytic law also suffices to compute a maximizer.
Exact-feasible rational density constructs the solver's initial rational
witness; the caller need not supply one separately. -/
def RealCompatibleLaw.maximize [DecidableEq A] {problem : PartialMomentProblem A}
    (feasible : problem.RealCompatibleLaw) : problem.RealCompatibleLaw :=
  problem.idealEntropyLaw (feasible.approximate PositiveRatio.one).val

theorem RealCompatibleLaw.maximize_maximal [DecidableEq A] {problem : PartialMomentProblem A}
    (feasible : problem.RealCompatibleLaw) : feasible.maximize.Maximal :=
  problem.idealEntropyLaw_maximal _

end Thesis.Probability.Distros.PartialMomentProblem
