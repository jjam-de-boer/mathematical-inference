import Thesis.CausalTransport.QualitativeDoCalculus

namespace Thesis
namespace Causality
namespace Examples
namespace QualitativeDoCalculus

open Probability
open Probability.ClaytonWaddington
open Causality.QualitativeDoCalculus

/-!
Finite checks of qualitative do-calculus transport and the induced
intervention scale.  These fixtures are not foundations: the theorems live
in `Thesis.Causality.QualitativeDoCalculus` and
`Thesis.CausalTransport.QualitativeDoCalculus`.
-/

def G : ObservedGraph twoBoolSignature :=
  twoBoolIndependentModel.observedGraph

def y : NodeSet twoBoolSignature := NodeSet.singleton twoBoolSecond
def z : NodeSet twoBoolSignature := NodeSet.singleton twoBoolFirst
def idle : NodeSet twoBoolSignature := NodeSet.empty

def reference : twoBoolSignature.Assignment := fun _ => false

def independentDisjoint : FourWayDisjoint idle y z idle :=
  FourWayDisjoint.emptyAction y z idle
    (NodeSet.disjoint_singletons_of_ne (by decide))
    (NodeSet.disjoint_empty_right _)
    (NodeSet.disjoint_empty_right _)

theorem rule1_separated :
    PathSpecification.PathDSeparated G (.bar idle) y z idle := by
  have h : G.dSeparated (.bar idle) y z idle = true := by decide +kernel
  exact G.dSeparationCorrectness.pathDSeparated_of_dSeparated h

theorem rule2_separated :
    PathSpecification.PathDSeparated G (.barUnderline idle z) y z idle := by
  have h : G.dSeparated (.barUnderline idle z) y z idle = true := by
    decide +kernel
  exact G.dSeparationCorrectness.pathDSeparated_of_dSeparated h

theorem rule3_separated :
    PathSpecification.PathDSeparated G
      { removeIncoming := NodeSet.union idle (G.nonAncestorsOf (.bar idle) z idle)
        removeOutgoing := NodeSet.empty } y z idle := by
  have h : G.dSeparated
      { removeIncoming := NodeSet.union idle (G.nonAncestorsOf (.bar idle) z idle)
        removeOutgoing := NodeSet.empty } y z idle = true := by
    decide +kernel
  exact G.dSeparationCorrectness.pathDSeparated_of_dSeparated h

def rightUnconditionalSupported :
    ProbabilityTerm.SupportedAt twoBoolIndependentModel
      (.kernel (rule1Right idle y z idle)) reference :=
  let kernel := rule1Right idle y z idle
  have hpos : 0 < (kernelUrn twoBoolIndependentModel kernel reference).probNum
      (kernel.conditionEvent reference) := by decide +kernel
  ⟨(kernelRatio twoBoolIndependentModel kernel reference hpos).toQProb,
    kernelDenote_equiv_ratio twoBoolIndependentModel kernel reference hpos⟩

def leftConditionalSupported :
    ProbabilityTerm.SupportedAt twoBoolIndependentModel
      (.kernel (rule1Left idle y z idle)) reference :=
  let kernel := rule1Left idle y z idle
  have hpos : 0 < (kernelUrn twoBoolIndependentModel kernel reference).probNum
      (kernel.conditionEvent reference) := by decide +kernel
  ⟨(kernelRatio twoBoolIndependentModel kernel reference hpos).toQProb,
    kernelDenote_equiv_ratio twoBoolIndependentModel kernel reference hpos⟩

def rule2LeftSupported :
    ProbabilityTerm.SupportedAt twoBoolIndependentModel
      (.kernel (rule2Left idle y z idle)) reference :=
  let kernel := rule2Left idle y z idle
  have hpos : 0 < (kernelUrn twoBoolIndependentModel kernel reference).probNum
      (kernel.conditionEvent reference) := by decide +kernel
  ⟨(kernelRatio twoBoolIndependentModel kernel reference hpos).toQProb,
    kernelDenote_equiv_ratio twoBoolIndependentModel kernel reference hpos⟩

def rule2RightSupported :
    ProbabilityTerm.SupportedAt twoBoolIndependentModel
      (.kernel (rule2Right idle y z idle)) reference :=
  let kernel := rule2Right idle y z idle
  have hpos : 0 < (kernelUrn twoBoolIndependentModel kernel reference).probNum
      (kernel.conditionEvent reference) := by decide +kernel
  ⟨(kernelRatio twoBoolIndependentModel kernel reference hpos).toQProb,
    kernelDenote_equiv_ratio twoBoolIndependentModel kernel reference hpos⟩

/-- Rule 1 as an identity of the qualitative urn scale, not of a rational
display. -/
theorem rule1_qualitative :
    KernelPlausEqv rationalScale
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule1Left idle y z idle) reference)
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule1Right idle y z idle) reference) :=
  qualitative_rule1 rationalScale G twoBoolIndependentModel
    twoBoolIndependentModel_compatible idle y z idle reference
    independentDisjoint rule1_separated
    leftConditionalSupported rightUnconditionalSupported

/-- Rule 2: observation versus action of `Z` on independent nodes. -/
theorem rule2_qualitative :
    KernelPlausEqv rationalScale
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule2Left idle y z idle) reference)
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule2Right idle y z idle) reference) :=
  qualitative_rule2 rationalScale G twoBoolIndependentModel
    twoBoolIndependentModel_compatible idle y z idle reference
    independentDisjoint rule2_separated
    rule2LeftSupported rule2RightSupported

/-- Rule 3: inserting a non-ancestor intervention. -/
theorem rule3_qualitative :
    KernelPlausEqv rationalScale
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule3Left idle y z idle) reference)
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule3Right idle y z idle) reference) :=
  qualitative_rule3 rationalScale G twoBoolIndependentModel
    twoBoolIndependentModel_compatible idle y z idle reference
    independentDisjoint rule3_separated
    rule2LeftSupported rightUnconditionalSupported

/-- The same identities are theorems of the induced intervention scale. -/
theorem induced_rule1_example :
    KernelPlausEqv rationalScale
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule1Left idle y z idle) reference)
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule1Right idle y z idle) reference) :=
  induced_rule1 rationalScale G twoBoolIndependentModel
    twoBoolIndependentModel_compatible idle y z idle reference
    independentDisjoint rule1_separated
    leftConditionalSupported rightUnconditionalSupported

def pointFalse : FiniteProbRecord Bool where
  atoms := [(false, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

def constantSecondFactor (i : Fin 2) : FiniteProbRecord Bool :=
  if i.val = 0 then twoBoolFairBit else pointFalse

/-- Second coordinate constantly false: conditioning on `Y = true` has no
support. -/
def constantSecondModel : ExactModel twoBoolSignature where
  latent := twoBoolLatent
  factor := constantSecondFactor
  prior := FiniteProduct.record 2 (fun _ => Bool) constantSecondFactor
  product_law :=
    FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool)
      constantSecondFactor
  mechanism := fun child _ latents =>
    if child.val = 1 then false
    else latents ⟨child.val, child.isLt⟩ (by simp [twoBoolLatent])

def unsupportedKernel : Kernel twoBoolSignature :=
  ⟨z, idle, y⟩

def trueSecond : twoBoolSignature.Assignment := fun i => decide (i.val = 1)

/-- The numerical conditional `P(X | Y = true)` is undefined, not zero. -/
theorem unsupported_denote_none :
    unsupportedKernel.denote constantSecondModel trueSecond = none := by
  decide +kernel

/-- Qualitative comparison refuses to complete that undefined conditional
to the zero ratio. -/
theorem unsupported_kernelPlaus_none :
    kernelPlaus rationalScale constantSecondModel unsupportedKernel
      trueSecond = none :=
  (kernelPlaus_eq_none_iff_denote_eq_none rationalScale constantSecondModel
    unsupportedKernel trueSecond).mpr unsupported_denote_none

theorem unsupported_not_zero_ratio :
    ¬ KernelPlausEqv rationalScale
        (kernelPlaus rationalScale constantSecondModel unsupportedKernel
          trueSecond)
        (some (rationalScale.ratioPlaus ⟨1, 0, Nat.succ_pos 0, Nat.zero_le 1⟩)) :=
  kernelPlaus_undefined_not_zero_ratio rationalScale constantSecondModel
    unsupportedKernel trueSecond unsupported_kernelPlaus_none

theorem induced_scale_inhabited :
    Nonempty (QualitativeInterventionScale.{0} twoBoolSignature) :=
  qualitativeInterventionScale_nonempty

theorem induced_effectiveness_first_false :
    (induced twoBoolIndependentModel rationalScale).eqv
      ((induced twoBoolIndependentModel rationalScale).plaus
        ((HardIntervention.empty twoBoolSignature).set twoBoolFirst false)
        (fun a => decide (a twoBoolFirst = false)))
      ((induced twoBoolIndependentModel rationalScale).plaus
        ((HardIntervention.empty twoBoolSignature).set twoBoolFirst false)
        topEvent) :=
  (induced twoBoolIndependentModel rationalScale).effectiveness
    ((HardIntervention.empty twoBoolSignature).set twoBoolFirst false)
    twoBoolFirst false
    (HardIntervention.set_at_target _ _ _)

/-- Soundness of representation on the listed two-node experiments. -/
theorem listed_realization :
    Realizes (induced twoBoolIndependentModel rationalScale)
      twoBoolIndependentModel rationalScale :=
  induced_realizes_listed twoBoolIndependentModel rationalScale

/-- Empty versus sure is not an induced equivalence: cell counts `0` and
`n` are different ratios. -/
theorem induced_empty_not_sure :
    ¬ rationalScale.eqv
        (eventPlaus rationalScale twoBoolIndependentModel
          (HardIntervention.empty twoBoolSignature) bottomEvent)
        (eventPlaus rationalScale twoBoolIndependentModel
          (HardIntervention.empty twoBoolSignature) topEvent) :=
  induced_not_eqv_bottom_top twoBoolIndependentModel rationalScale
    (HardIntervention.empty twoBoolSignature)

/-- The indiscrete comparison equates every pair, including empty versus
sure, so it is not realized by any finite SCM. -/
theorem indiscrete_not_realized :
    ¬ Realizes indiscreteScale twoBoolIndependentModel rationalScale :=
  indiscrete_not_realizes twoBoolIndependentModel rationalScale

/-- Unrestricted thin-scale representation is false. -/
theorem converse_refuted : ¬ TwoNodeBooleanRepresentation :=
  not_twoNodeBooleanRepresentation

end QualitativeDoCalculus
end Examples
end Causality
end Thesis
