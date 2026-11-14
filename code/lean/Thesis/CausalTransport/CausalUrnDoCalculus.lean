import Thesis.Causality.CausalUrnTickets
import Thesis.Causality.QualitativeDoCalculus
import Thesis.CausalTransport.HiddenDAGSoundness

namespace Thesis.Causality.CausalUrnGame
open Probability Probability.ClaytonWaddington Probability.ClaytonWaddington.UrnRatio
open QualitativeDoCalculus
universe u
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Pearl's rules for arbitrary recorded/unrecorded urn games

The public semantics below is defined from the game interpreter and its
constructed ticket law. The representation lemmas then connect that semantics
to the existing, proved hidden-DAG soundness theorem. Thus the caller supplies
a game, graphical side conditions and actual local support, never an SCM,
Markov assumption, causal soundness certificate or Pearl rule as a game field.

Hiding nodes uses the checked latent projection in `P`. A hidden common cause
is not dropped and the observed graph is generally mixed, not a DAG with
independent observed noises. All three rules retain their original graphical
conditions. Zeros are allowed; only the displayed conditional denominators
must be supported. The ordinal conclusion uses Clayton's arbitrary qualitative
scale, not a numerically chosen plausibility scale.
-/

/-- Select an experiment directly in operational game semantics. Empty action
really means the original game. It does not condition on a setting's values. -/
def kernelLaw (game : CausalUrnGame S P) (kernel : Kernel S) (reference : S.Assignment) :
    FiniteProbRecord S.Assignment :=
  if kernel.hasAction then game.law { value := kernel.intervention reference }
  else game.law (HardIntervention.empty S)

def kernelResult (game : CausalUrnGame S P) (kernel : Kernel S) (reference : S.Assignment) :
    ProbabilityResult.Result :=
  let distribution := game.kernelLaw kernel reference
  ProbabilityResult.divide (some (distribution.probVal (kernel.numeratorEvent reference)))
    (some (distribution.probVal (kernel.conditionEvent reference)))

/-- Support is a property of the game's own conditional, not a globally
positive model-class hypothesis or a promise about observational actions. -/
def KernelSupported (game : CausalUrnGame S P) (kernel : Kernel S) (reference : S.Assignment) : Type :=
  ProbabilityResult.Supported (game.kernelResult kernel reference)

/-- This unit-cell presentation comes from the operational law, which was
constructed from one common superurn. It is not an independently supplied
urn for each experiment; `recordUrn_agrees` relates it to the shared tickets. -/
def kernelUrn (game : CausalUrnGame S P) (kernel : Kernel S) (reference : S.Assignment) :
    UrnProb S.Assignment := (game.kernelLaw kernel reference).toUrn

def kernelRatio (game : CausalUrnGame S P) (kernel : Kernel S) (reference : S.Assignment)
    (positive : 0 < (game.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)) : UrnRatio where
  N := (game.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)
  k := (game.kernelUrn kernel reference).probNum (kernel.numeratorEvent reference)
  pos := positive
  le := count_mono (Kernel.numeratorEvent_implies_conditionEvent kernel reference)

/-- A qualitative conditional is a count-ratio plausibility when supported.
Undefined is represented by `none`, never by the zero plausibility. -/
def kernelPlaus (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    (kernel : Kernel S) (reference : S.Assignment) : Option scale.Plaus :=
  if positive : 0 < (game.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)
  then some (scale.ratioPlaus (game.kernelRatio kernel reference positive)) else none

theorem kernelLaw_toSCM (game : CausalUrnGame S P) (kernel) (reference) :
    game.kernelLaw kernel reference = game.toSCM.kernelDistribution kernel reference := by
  unfold kernelLaw FiniteHiddenDAGSCM.kernelDistribution
  split
  · exact (game.toSCM_law _).symm
  · exact (game.toSCM_law _).symm

theorem kernelLaw_collapsed (game : CausalUrnGame S P) (kernel) (reference) :
    game.kernelLaw kernel reference = kernel.distribution game.toSCM.toLatentRootSCM reference :=
  (game.kernelLaw_toSCM kernel reference).trans (game.toSCM.kernelDistribution_preserved kernel reference)

/-- Literal equality of partial results preserves unsupported as well as
zero values. This bridge has no support or positivity assumption. -/
theorem kernelResult_toSCM (game : CausalUrnGame S P) (kernel) (reference) :
    game.kernelResult kernel reference = game.toSCM.kernelDenote kernel reference := by
  unfold kernelResult FiniteHiddenDAGSCM.kernelDenote
  rw [game.kernelLaw_toSCM]

theorem kernelResult_collapsed (game : CausalUrnGame S P) (kernel) (reference) :
    game.kernelResult kernel reference = kernel.denote game.toSCM.toLatentRootSCM reference :=
  (game.kernelResult_toSCM kernel reference).trans (game.toSCM.kernelDenote_preserved kernel reference)

theorem kernelPlaus_collapsed (game : CausalUrnGame S P) (scale : QualitativeUrnScale) (kernel) (reference) :
    game.kernelPlaus scale kernel reference =
      QualitativeDoCalculus.kernelPlaus scale game.toSCM.toLatentRootSCM kernel reference := by
  unfold kernelPlaus kernelRatio kernelUrn QualitativeDoCalculus.kernelPlaus
    QualitativeDoCalculus.kernelRatio QualitativeDoCalculus.kernelUrn
  simp only [game.kernelLaw_collapsed]

/-- The familiar conditional-support criterion is proved for the actual game.
No event of zero mass acquires an invented conditional distribution. -/
theorem kernelResult_none_iff (game : CausalUrnGame S P) (kernel) (reference) :
    game.kernelResult kernel reference = none ↔
      ¬ 0 < ((game.kernelLaw kernel reference).probVal (kernel.conditionEvent reference)).num := by
  simp only [kernelResult, ProbabilityResult.divide]
  split <;> simp_all

theorem kernelPlaus_none_iff (game : CausalUrnGame S P) (scale : QualitativeUrnScale) (kernel) (reference) :
    game.kernelPlaus scale kernel reference = none ↔ game.kernelResult kernel reference = none := by
  rw [game.kernelPlaus_collapsed, game.kernelResult_collapsed]
  exact kernelPlaus_eq_none_iff_denote_eq_none scale _ _ _

/-- Every supported game conditional has the qualitative cell-count ratio
predicted by the existing Clayton reconstruction. -/
def kernelResult_ratio (game : CausalUrnGame S P) (kernel) (reference)
    (positive : 0 < (game.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)) :
    ProbabilityResult.Equivalent (game.kernelResult kernel reference)
      (some (game.kernelRatio kernel reference positive).toQProb) := by
  rw [game.kernelResult_collapsed]
  unfold kernelRatio kernelUrn at *
  simp only [game.kernelLaw_collapsed] at positive ⊢
  exact kernelDenote_equiv_ratio _ _ _ positive

/-- Numerical do-rule soundness now has a game as its only generating input.
The hidden-DAG theorem proves graph soundness; representation supplies its
actual model and transports both local support witnesses and the conclusion. -/
noncomputable def doRule_sound (game : CausalUrnGame S P) {left right : Kernel S}
    (reference : S.Assignment) (application : DoRuleApplication P.observedGraph left right)
    (leftSupported : game.KernelSupported left reference)
    (rightSupported : game.KernelSupported right reference) :
    ProbabilityResult.Equivalent (game.kernelResult left reference) (game.kernelResult right reference) := by
  have supportedLeft : game.toSCM.TermSupportedAt (.kernel left) reference := by
    change ProbabilityResult.Supported (game.toSCM.kernelDenote left reference)
    rw [← game.kernelResult_toSCM]
    exact leftSupported
  have supportedRight : game.toSCM.TermSupportedAt (.kernel right) reference := by
    change ProbabilityResult.Supported (game.toSCM.kernelDenote right reference)
    rw [← game.kernelResult_toSCM]
    exact rightSupported
  rw [game.kernelResult_toSCM, game.kernelResult_toSCM]
  exact game.toSCM.doRule_soundAt reference application supportedLeft supportedRight

/-- Qualitative soundness follows for ANY Clayton scale. Numerical equality
is a proved intermediate representation, never a game axiom. -/
theorem doRule_qualitative (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    {left right : Kernel S} (reference : S.Assignment)
    (application : DoRuleApplication P.observedGraph left right)
    (leftSupported : game.KernelSupported left reference)
    (rightSupported : game.KernelSupported right reference) :
    KernelPlausEqv scale (game.kernelPlaus scale left reference) (game.kernelPlaus scale right reference) := by
  rw [game.kernelPlaus_collapsed, game.kernelPlaus_collapsed]
  apply kernelPlausEqv_of_numerical scale game.toSCM.toLatentRootSCM left right reference
  · change ProbabilityResult.Supported (left.denote game.toSCM.toLatentRootSCM reference)
    rw [← game.kernelResult_collapsed]
    exact leftSupported
  · change ProbabilityResult.Supported (right.denote game.toSCM.toLatentRootSCM reference)
    rw [← game.kernelResult_collapsed]
    exact rightSupported
  · change ProbabilityResult.Equivalent (left.denote game.toSCM.toLatentRootSCM reference)
      (right.denote game.toSCM.toLatentRootSCM reference)
    rw [← game.kernelResult_collapsed, ← game.kernelResult_collapsed]
    exact game.doRule_sound reference application leftSupported rightSupported

/-- Rule 1: insertion/deletion of observations. Its graphical separation is
checked in the graph with incoming arrows to the fixed settings removed. -/
theorem qualitative_rule1 (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    (x y z w : NodeSet S) (reference : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (separated : P.observedGraph.dSeparated (.bar x) y z (NodeSet.union x w) = true)
    (leftSupported : game.KernelSupported (rule1Left x y z w) reference)
    (rightSupported : game.KernelSupported (rule1Right x y z w) reference) :
    KernelPlausEqv scale (game.kernelPlaus scale (rule1Left x y z w) reference)
      (game.kernelPlaus scale (rule1Right x y z w) reference) :=
  game.doRule_qualitative scale reference (.rule1 x y z w disjoint separated) leftSupported rightSupported

/-- Rule 2: exchange an observation for a setting under its distinct
incoming/outgoing-arrow separation test. Observing never means resetting. -/
theorem qualitative_rule2 (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    (x y z w : NodeSet S) (reference : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (separated : P.observedGraph.dSeparated (.barUnderline x z) y z (NodeSet.union x w) = true)
    (leftSupported : game.KernelSupported (rule2Left x y z w) reference)
    (rightSupported : game.KernelSupported (rule2Right x y z w) reference) :
    KernelPlausEqv scale (game.kernelPlaus scale (rule2Left x y z w) reference)
      (game.kernelPlaus scale (rule2Right x y z w) reference) :=
  game.doRule_qualitative scale reference (.rule2 x y z w disjoint separated) leftSupported rightSupported

/-- Rule 3: insertion/deletion of settings. Only the actions selected by
the original non-ancestor condition are removed from the graph. -/
theorem qualitative_rule3 (game : CausalUrnGame S P) (scale : QualitativeUrnScale)
    (x y z w : NodeSet S) (reference : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (separated : P.observedGraph.dSeparated
      { removeIncoming := NodeSet.union x (P.observedGraph.nonAncestorsOf (.bar x) z w),
        removeOutgoing := NodeSet.empty } y z (NodeSet.union x w) = true)
    (leftSupported : game.KernelSupported (rule3Left x y z w) reference)
    (rightSupported : game.KernelSupported (rule3Right x y z w) reference) :
    KernelPlausEqv scale (game.kernelPlaus scale (rule3Left x y z w) reference)
      (game.kernelPlaus scale (rule3Right x y z w) reference) :=
  game.doRule_qualitative scale reference (.rule3 x y z w disjoint separated) leftSupported rightSupported

end Thesis.Causality.CausalUrnGame
