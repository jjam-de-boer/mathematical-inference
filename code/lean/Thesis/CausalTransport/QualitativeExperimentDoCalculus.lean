import Thesis.Causality.QualitativeExperimentRoundTrip
import Thesis.CausalTransport.CausalUrnDoCalculus

namespace Thesis.Causality.QualitativeDoCalculus

private theorem partial_none_iff {left right : ProbabilityResult.Result}
    (same : ProbabilityResult.Equivalent left right) : left = none ↔ right = none := by
  cases same <;> simp only [Option.some_ne_none, iff_self]

theorem KernelPlausEqv.symm {scale : Probability.ClaytonWaddington.QualitativeUrnScale}
    {left right : Option scale.Plaus} (same : KernelPlausEqv scale left right) :
    KernelPlausEqv scale right left := by
  cases same with
  | unsupported => exact .unsupported
  | defined equal => exact .defined (scale.eqv_symm equal)

theorem KernelPlausEqv.trans {scale : Probability.ClaytonWaddington.QualitativeUrnScale}
    {left middle right : Option scale.Plaus}
    (first : KernelPlausEqv scale left middle) (second : KernelPlausEqv scale middle right) :
    KernelPlausEqv scale left right := by
  cases first with
  | unsupported => cases second; exact .unsupported
  | defined firstEqual =>
      cases second with
      | defined secondEqual => exact .defined (scale.eqv_trans firstEqual secondEqual)

end Thesis.Causality.QualitativeDoCalculus

namespace Thesis.Causality.CausalExperimentData
open Probability Probability.ClaytonWaddington Probability.ClaytonWaddington.UrnRatio QualitativeDoCalculus
universe u v
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Pearl's three rules from the approved qualitative requirements

The public kernels below use the supplied experimental urns. The proof
constructs a game from Effectiveness, Parent sufficiency and Experimental
stability. Full-law preservation transports the actual partial conditionals,
including failed support and defined zeros, to that game. Existing game
soundness proves the three rules and transports their conclusions back.

The caller supplies graphical tests and local support witnesses, but no
game, recipes, factorization, SCM or soundness certificate. The observed
projection is the supplied checked projection: unrecorded common causes
are retained internally throughout reconstruction.
-/

/-- Select the declared hard experiment and then project to recorded
outcomes. An empty action selects observation. Hidden values remain present
in the supplied full slice before this projection. -/
def kernelLaw (data : CausalExperimentData S P) (kernel : Kernel S) (reference : S.Assignment) :
    FiniteProbRecord S.Assignment :=
  if kernel.hasAction then data.recordedLaw { value := kernel.intervention reference }
  else data.recordedLaw (HardIntervention.empty S)

def kernelResult (data : CausalExperimentData S P) (kernel : Kernel S) (reference : S.Assignment) :
    ProbabilityResult.Result :=
  let distribution := data.kernelLaw kernel reference
  ProbabilityResult.divide (some (distribution.probVal (kernel.numeratorEvent reference)))
    (some (distribution.probVal (kernel.conditionEvent reference)))

/-- Local support of this actual conditional, retaining its rational value
as constructive data. Neither a positive outcome nor positivity of every
cell or every model compatible with the graph is required. -/
def KernelSupported (data : CausalExperimentData S P) (kernel : Kernel S) (reference : S.Assignment) : Type :=
  ProbabilityResult.Supported (data.kernelResult kernel reference)

def kernelUrn (data : CausalExperimentData S P) (kernel : Kernel S) (reference : S.Assignment) :
    UrnProb S.Assignment := (data.kernelLaw kernel reference).toUrn

/-- The ordinary finite conditional count ratio. Its positive denominator
is explicit, while its numerator may be zero. -/
def kernelRatio (data : CausalExperimentData S P) (kernel : Kernel S) (reference : S.Assignment)
    (positive : 0 < (data.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)) : UrnRatio where
  N := (data.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)
  k := (data.kernelUrn kernel reference).probNum (kernel.numeratorEvent reference)
  pos := positive
  le := count_mono (Kernel.numeratorEvent_implies_conditionEvent kernel reference)

/-- A null conditioner gives `none`; a zero outcome with positive evidence
has a defined zero plausibility. A setting selects an experimental law and
does not condition the observational law on the action's values. -/
def kernelPlaus (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (kernel : Kernel S) (reference : S.Assignment) : Option scale.Plaus :=
  if positive : 0 < (data.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)
  then some (scale.ratioPlaus (data.kernelRatio kernel reference positive)) else none

theorem kernelLaw_realize (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (kernel) (reference) (event : Event S.Assignment) :
    QProb.Equiv ((data.kernelLaw kernel reference).probVal event)
      ((data.realize.kernelLaw kernel reference).probVal event) := by
  unfold kernelLaw CausalUrnGame.kernelLaw
  split <;> exact data.realize_recorded_law scale rules data.defaultCompletion _ event

/-- No support premise: undefined and supported-zero results both transfer. -/
def kernelResult_realize (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (kernel) (reference) :
    ProbabilityResult.Equivalent (data.kernelResult kernel reference) (data.realize.kernelResult kernel reference) :=
  ProbabilityResult.divide_congr
    (.value (data.kernelLaw_realize scale rules kernel reference (kernel.numeratorEvent reference)))
    (.value (data.kernelLaw_realize scale rules kernel reference (kernel.conditionEvent reference)))

theorem kernelResult_realize_none_iff (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale) (kernel) (reference) :
    data.kernelResult kernel reference = none ↔ data.realize.kernelResult kernel reference = none := by
  exact partial_none_iff (data.kernelResult_realize scale rules kernel reference)

/-- Defined zero transports as defined zero. The hypothesis itself carries
support; it is not an assertion about an undefined numerator/denominator. -/
def kernelResult_realize_zero (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale) (kernel) (reference)
    (zero : ProbabilityResult.Equivalent (data.kernelResult kernel reference) (some QProb.zero)) :
    ProbabilityResult.Equivalent (data.realize.kernelResult kernel reference) (some QProb.zero) :=
  ProbabilityResult.trans (ProbabilityResult.symm (data.kernelResult_realize scale rules kernel reference)) zero

theorem kernelUrn_realize (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (kernel) (reference) (event : Event S.Assignment) :
    QProb.Equiv ((data.kernelUrn kernel reference).probVal event)
      ((data.realize.kernelUrn kernel reference).probVal event) :=
  QProb.equiv_trans (QProb.equiv_symm ((data.kernelLaw kernel reference).toUrn_agrees event))
    (QProb.equiv_trans (data.kernelLaw_realize scale rules kernel reference event)
      ((data.realize.kernelLaw kernel reference).toUrn_agrees event))

theorem kernelResult_none_iff (data : CausalExperimentData S P) (kernel) (reference) :
    data.kernelResult kernel reference = none ↔
      ¬ 0 < ((data.kernelLaw kernel reference).probVal (kernel.conditionEvent reference)).num := by
  simp only [kernelResult, ProbabilityResult.divide]
  split <;> simp_all

theorem kernelUrn_support_iff (data : CausalExperimentData S P) (kernel) (reference) :
    0 < (data.kernelUrn kernel reference).probNum (kernel.conditionEvent reference) ↔
      0 < ((data.kernelLaw kernel reference).probVal (kernel.conditionEvent reference)).num :=
  (QProb.equiv_num_pos_iff ((data.kernelLaw kernel reference).toUrn_agrees (kernel.conditionEvent reference))).symm

theorem kernelPlaus_none_iff (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v}) (kernel) (reference) :
    data.kernelPlaus scale kernel reference = none ↔ data.kernelResult kernel reference = none := by
  rw [data.kernelResult_none_iff]
  by_cases positive : 0 < (data.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)
  · rw [kernelPlaus, dif_pos positive]
    constructor
    · intro impossible; cases impossible
    · intro notSupported
      exact (notSupported ((data.kernelUrn_support_iff kernel reference).mp positive)).elim
  · rw [kernelPlaus, dif_neg positive]
    constructor
    · intro _ recordPositive
      exact positive ((data.kernelUrn_support_iff kernel reference).mpr recordPositive)
    · intro _; rfl

def kernelResult_ratio (data : CausalExperimentData S P) (kernel) (reference)
    (positive : 0 < (data.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)) :
    ProbabilityResult.Equivalent (data.kernelResult kernel reference)
      (some (data.kernelRatio kernel reference positive).toQProb) := by
  have recordPositive := (data.kernelUrn_support_iff kernel reference).mp positive
  simp only [kernelResult, ProbabilityResult.divide, dif_pos recordPositive]
  refine .value (QProb.equiv_trans
    (QProb.div_congr ((data.kernelLaw kernel reference).toUrn_agrees (kernel.numeratorEvent reference))
      ((data.kernelLaw kernel reference).toUrn_agrees (kernel.conditionEvent reference)) recordPositive positive) ?_)
  simp only [QProb.Equiv, QProb.div, UrnProb.probVal, kernelRatio, kernelUrn, UrnRatio.toQProb]
  ac_rfl

/-- Partial qualitative conditionals agree with those of the constructed
game. The unsupported branch never evaluates a null-evidence conditional. -/
theorem kernelPlaus_realize (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale) (kernel) (reference) :
    KernelPlausEqv scale (data.kernelPlaus scale kernel reference)
      (data.realize.kernelPlaus scale kernel reference) := by
  have support := QProb.equiv_num_pos_iff
    (data.kernelUrn_realize scale rules kernel reference (kernel.conditionEvent reference))
  by_cases positive : 0 < (data.kernelUrn kernel reference).probNum (kernel.conditionEvent reference)
  · have otherPositive : 0 < (data.realize.kernelUrn kernel reference).probNum
        (kernel.conditionEvent reference) := support.mp positive
    have ratios := ProbabilityResult.trans (ProbabilityResult.symm (data.kernelResult_ratio kernel reference positive))
      (ProbabilityResult.trans (data.kernelResult_realize scale rules kernel reference)
        (data.realize.kernelResult_ratio kernel reference otherPositive))
    have equal : QProb.Equiv (data.kernelRatio kernel reference positive).toQProb
        (data.realize.kernelRatio kernel reference otherPositive).toQProb := by
      cases ratios with
      | value equal => exact equal
    simp only [kernelPlaus, CausalUrnGame.kernelPlaus, dif_pos positive, dif_pos otherPositive]
    exact .defined ((scale.eqv_iff_sameRatio _ _).mpr equal)
  · have otherNotPositive : ¬ 0 < (data.realize.kernelUrn kernel reference).probNum
        (kernel.conditionEvent reference) := fun otherPositive => positive (support.mpr otherPositive)
    simp only [kernelPlaus, CausalUrnGame.kernelPlaus, dif_neg positive, dif_neg otherNotPositive]
    exact .unsupported

/-- Numerical soundness is a derived consequence of the qualitative rules.
Both support witnesses concern the supplied abstract experiments. -/
noncomputable def doRule_sound (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    {left right : Kernel S} (reference : S.Assignment)
    (application : DoRuleApplication P.observedGraph left right)
    (leftSupported : data.KernelSupported left reference)
    (rightSupported : data.KernelSupported right reference) :
    ProbabilityResult.Equivalent (data.kernelResult left reference) (data.kernelResult right reference) := by
  have leftAgreement := data.kernelResult_realize scale rules left reference
  have rightAgreement := data.kernelResult_realize scale rules right reference
  exact ProbabilityResult.trans leftAgreement
    (ProbabilityResult.trans
      (data.realize.doRule_sound reference application
        (ProbabilityResult.Supported.transport leftAgreement leftSupported)
        (ProbabilityResult.Supported.transport rightAgreement rightSupported))
      (ProbabilityResult.symm rightAgreement))

/-- The conclusion refers to original abstract experiments. The game and
its constructed SCM are internal proof steps, not caller-supplied evidence. -/
theorem doRule_qualitative (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    {left right : Kernel S} (reference : S.Assignment)
    (application : DoRuleApplication P.observedGraph left right)
    (leftSupported : data.KernelSupported left reference)
    (rightSupported : data.KernelSupported right reference) :
    KernelPlausEqv scale (data.kernelPlaus scale left reference) (data.kernelPlaus scale right reference) := by
  have leftAgreement := data.kernelResult_realize scale rules left reference
  have rightAgreement := data.kernelResult_realize scale rules right reference
  exact (data.kernelPlaus_realize scale rules left reference).trans
    ((data.realize.doRule_qualitative scale reference application
      (ProbabilityResult.Supported.transport leftAgreement leftSupported)
      (ProbabilityResult.Supported.transport rightAgreement rightSupported)).trans
        (data.kernelPlaus_realize scale rules right reference).symm)

/-- **Rule 1: observations.** Insert/delete an observation under separation
after cutting incoming arrows to the existing settings. -/
theorem qualitative_rule1 (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (x y z w : NodeSet S) (reference : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (separated : P.observedGraph.dSeparated (.bar x) y z (NodeSet.union x w) = true)
    (leftSupported : data.KernelSupported (rule1Left x y z w) reference)
    (rightSupported : data.KernelSupported (rule1Right x y z w) reference) :
    KernelPlausEqv scale (data.kernelPlaus scale (rule1Left x y z w) reference)
      (data.kernelPlaus scale (rule1Right x y z w) reference) :=
  data.doRule_qualitative scale rules reference (.rule1 x y z w disjoint separated) leftSupported rightSupported

/-- **Rule 2: observation/action exchange.** The usual incoming/outgoing
arrow test justifies the exchange. Observation is not defined as setting. -/
theorem qualitative_rule2 (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (x y z w : NodeSet S) (reference : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (separated : P.observedGraph.dSeparated (.barUnderline x z) y z (NodeSet.union x w) = true)
    (leftSupported : data.KernelSupported (rule2Left x y z w) reference)
    (rightSupported : data.KernelSupported (rule2Right x y z w) reference) :
    KernelPlausEqv scale (data.kernelPlaus scale (rule2Left x y z w) reference)
      (data.kernelPlaus scale (rule2Right x y z w) reference) :=
  data.doRule_qualitative scale rules reference (.rule2 x y z w disjoint separated) leftSupported rightSupported

/-- **Rule 3: actions.** Insert/delete settings with Pearl's non-ancestor
qualification. Only local conditional support is required. -/
theorem qualitative_rule3 (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (x y z w : NodeSet S) (reference : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (separated : P.observedGraph.dSeparated
      { removeIncoming := NodeSet.union x (P.observedGraph.nonAncestorsOf (.bar x) z w),
        removeOutgoing := NodeSet.empty } y z (NodeSet.union x w) = true)
    (leftSupported : data.KernelSupported (rule3Left x y z w) reference)
    (rightSupported : data.KernelSupported (rule3Right x y z w) reference) :
    KernelPlausEqv scale (data.kernelPlaus scale (rule3Left x y z w) reference)
      (data.kernelPlaus scale (rule3Right x y z w) reference) :=
  data.doRule_qualitative scale rules reference (.rule3 x y z w disjoint separated) leftSupported rightSupported

end Thesis.Causality.CausalExperimentData
