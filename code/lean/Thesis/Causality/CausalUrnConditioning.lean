import Thesis.Causality.CausalUrnTickets
import Thesis.Probability.QualitativeUrn
import Thesis.Causality.ProbabilityResult

namespace Thesis.Causality.CausalUrnGame
open Probability Probability.ClaytonWaddington Probability.ClaytonWaddington.UrnRatio
universe u
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Clayton reconstruction on game records and honest conditioning

The ordinary probability of a record event is obtained by counting the
common superurn's tickets after executing the declared experiment. Arbitrary
Clayton scales recover precisely those comparisons. Evidence then filters
that experiment's tickets; it never changes a recipe or resets an urn.
In contrast a hard setting keeps all source tickets and reruns the altered
instructions. A null filter has no posterior urn and no conditional value.
-/

def eventPlaus (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    (setting : HardIntervention S) (event : Event S.Assignment) : scale.Plaus :=
  scale.ratioPlaus (ofUrnEvent (game.recordUrn setting) event)

/-- The comparison is valid across different experiments too: both are read
from the one common source construction, rather than from arbitrary unrelated
per-experiment plausibility assignments. -/
theorem eventPlaus_eqv_iff (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    (first second) (left right : Event S.Assignment) :
    scale.eqv (game.eventPlaus scale first left) (game.eventPlaus scale second right) ↔
      QProb.Equiv ((game.law first).probVal left) ((game.law second).probVal right) := by
  constructor
  · intro qualitative
    have numerical := (scale.eqv_iff_sameRatio _ _).mp qualitative
    change QProb.Equiv ((game.recordUrn first).probVal left) ((game.recordUrn second).probVal right) at numerical
    exact QProb.equiv_trans (game.recordUrn_agrees first left)
      (QProb.equiv_trans numerical (QProb.equiv_symm (game.recordUrn_agrees second right)))
  · intro numerical
    apply (scale.eqv_iff_sameRatio _ _).mpr
    exact QProb.equiv_trans (QProb.equiv_symm (game.recordUrn_agrees first left))
      (QProb.equiv_trans numerical (game.recordUrn_agrees second right))

/-- Strict qualitative comparison is likewise exactly cross-multiplication
of the observed event counts, without selecting a numerical scale as input. -/
theorem eventPlaus_lt_iff (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    (first second) (left right : Event S.Assignment) :
    scale.lt (game.eventPlaus scale first left) (game.eventPlaus scale second right) ↔
      (game.recordUrn first).probNum left * (game.recordUrn second).n <
        (game.recordUrn second).probNum right * (game.recordUrn first).n :=
  scale.lt_iff_ratio_lt _ _

/-- Ordinary conditioning inside the chosen experiment. The numerator is
the joint record event, not a rerun after forcing the evidence values. -/
def conditional (game : CausalUrnGame S P) (setting : HardIntervention S)
    (event evidence : Event S.Assignment) : ProbabilityResult.Result :=
  ProbabilityResult.divide (some ((game.law setting).probVal (inter event evidence)))
    (some ((game.law setting).probVal evidence))

theorem conditional_none_iff (game : CausalUrnGame S P) (setting) (event evidence : Event S.Assignment) :
    game.conditional setting event evidence = none ↔
      ¬ 0 < ((game.law setting).probVal evidence).num := by
  simp only [conditional, ProbabilityResult.divide]
  split <;> simp_all

/-- Retaining exactly the positive evidence cells computes the conditional.
The equality is extensional in rational presentations; repeated record labels
and unused random-table entries remain genuine distinct tickets. -/
def conditional_restriction (game : CausalUrnGame S P) (setting)
    (event evidence : Event S.Assignment)
    (positive : 0 < (game.recordUrn setting).probNum evidence) :
    ProbabilityResult.Equivalent (game.conditional setting event evidence)
      (some (((game.recordUrn setting).conditionOn evidence positive).probVal event)) := by
  have recordPositive : 0 < ((game.law setting).probVal evidence).num :=
    (QProb.equiv_num_pos_iff (game.recordUrn_agrees setting evidence)).mpr positive
  unfold conditional
  simp only [ProbabilityResult.divide, dif_pos recordPositive]
  apply ProbabilityResult.Equivalent.value
  refine QProb.equiv_trans (QProb.div_congr
    (game.recordUrn_agrees setting (inter event evidence))
    (game.recordUrn_agrees setting evidence) recordPositive positive) ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm ((game.recordUrn setting).conditionOn_probVal evidence event positive))
  simp only [QProb.Equiv, QProb.div, UrnProb.probVal, UrnProb.condVal]
  ac_rfl

/-- A supported zero conditional stays a supported value. Its denominator
is checked independently of its numerator; no zero-result shortcut turns an
undefined conditional into a value. -/
def conditional_zero (game : CausalUrnGame S P) (setting) (event evidence : Event S.Assignment)
    (positive : 0 < ((game.law setting).probVal evidence).num)
    (zero : ((game.law setting).probVal (inter event evidence)).num = 0) :
    ProbabilityResult.Equivalent (game.conditional setting event evidence) (some QProb.zero) := by
  unfold conditional
  simp only [ProbabilityResult.divide, dif_pos positive]
  apply ProbabilityResult.Equivalent.value
  simp only [QProb.Equiv, QProb.div, QProb.zero, zero, Nat.zero_mul]

end Thesis.Causality.CausalUrnGame
