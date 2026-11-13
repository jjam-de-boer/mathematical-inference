import Thesis.CausalTransport.Soundness
import Thesis.Causality.QualitativeDoCalculus

namespace Thesis
namespace Causality

open Probability
open Probability.ClaytonWaddington
open QualitativeDoCalculus

/-!
Pearl's three rules as qualitative identities of an induced interventional
scale.

The numerical soundness package already supplies `QProb.Equiv` of supported
kernel denotations from path d-separation in the mutilated graph.  Transport
along the finite urn representation rewrites those identities as
`QualitativeUrnScale.eqv`.  Graph side conditions appear in the proofs, not
as axiom fields of `QualitativeInterventionScale`.

This does not derive `do` from Clayton–Waddington urn axioms, and it is not
a second identification engine.
-/

namespace QualitativeDoCalculus

theorem twoBoolIndependentModel_compatible :
    Compatible twoBoolIndependentModel
      twoBoolIndependentModel.observedGraph :=
  ⟨twoBoolIndependentModel.markovian_isCanonicalSemiMarkovian
    twoBoolIndependentModel_markovian,
    fun _ _ => rfl⟩

/-- Rule 1 as qualitative kernel-plausibility equality, from published
numerical soundness. -/
theorem qualitative_rule1 (Q : QualitativeUrnScale)
    (G : ObservedGraph S) (model : ExactModel S)
    (compatible : Compatible model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w))
    (leftSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule1Left x y z w)) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule1Right x y z w)) assignment) :
    KernelPlausEqv Q
      (kernelPlaus Q model (rule1Left x y z w) assignment)
      (kernelPlaus Q model (rule1Right x y z w) assignment) :=
  kernelPlausEqv_of_numerical Q model _ _ assignment
    leftSupported rightSupported
    ((G.publishedSoundness.pathPrimitive model compatible).doRule
      assignment
      (.rule1 (separation := pathRuleSeparation G) x y z w disjoint
        separated)
      leftSupported rightSupported)

/-- Rule 2 as qualitative kernel-plausibility equality. -/
theorem qualitative_rule2 (Q : QualitativeUrnScale)
    (G : ObservedGraph S) (model : ExactModel S)
    (compatible : Compatible model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w))
    (leftSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule2Left x y z w)) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule2Right x y z w)) assignment) :
    KernelPlausEqv Q
      (kernelPlaus Q model (rule2Left x y z w) assignment)
      (kernelPlaus Q model (rule2Right x y z w) assignment) :=
  kernelPlausEqv_of_numerical Q model _ _ assignment
    leftSupported rightSupported
    ((G.publishedSoundness.pathPrimitive model compatible).doRule
      assignment
      (.rule2 (separation := pathRuleSeparation G) x y z w disjoint
        separated)
      leftSupported rightSupported)

/-- Rule 3 as qualitative kernel-plausibility equality. -/
theorem qualitative_rule3 (Q : QualitativeUrnScale)
    (G : ObservedGraph S) (model : ExactModel S)
    (compatible : Compatible model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated :
      let base := GraphMutilation.bar x
      let removable := G.nonAncestorsOf base z w
      PathSpecification.PathDSeparated G
        { removeIncoming := NodeSet.union x removable,
          removeOutgoing := NodeSet.empty }
        y z (NodeSet.union x w))
    (leftSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule3Left x y z w)) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule3Right x y z w)) assignment) :
    KernelPlausEqv Q
      (kernelPlaus Q model (rule3Left x y z w) assignment)
      (kernelPlaus Q model (rule3Right x y z w) assignment) :=
  kernelPlausEqv_of_numerical Q model _ _ assignment
    leftSupported rightSupported
    ((G.publishedSoundness.pathPrimitive model compatible).doRule
      assignment
      (.rule3 (separation := pathRuleSeparation G) x y z w disjoint
        separated)
      leftSupported rightSupported)

/-- The three do-rules as theorems of the induced interventional scale.
d-separation is used in the proof; it is not an axiom field of the scale. -/
theorem induced_rule1 (Q : QualitativeUrnScale)
    (G : ObservedGraph S) (model : ExactModel S)
    (compatible : Compatible model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w))
    (leftSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule1Left x y z w)) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule1Right x y z w)) assignment) :
    KernelPlausEqv Q
      (kernelPlaus Q model (rule1Left x y z w) assignment)
      (kernelPlaus Q model (rule1Right x y z w) assignment) :=
  qualitative_rule1 Q G model compatible x y z w assignment disjoint
    separated leftSupported rightSupported

theorem induced_rule2 (Q : QualitativeUrnScale)
    (G : ObservedGraph S) (model : ExactModel S)
    (compatible : Compatible model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w))
    (leftSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule2Left x y z w)) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule2Right x y z w)) assignment) :
    KernelPlausEqv Q
      (kernelPlaus Q model (rule2Left x y z w) assignment)
      (kernelPlaus Q model (rule2Right x y z w) assignment) :=
  qualitative_rule2 Q G model compatible x y z w assignment disjoint
    separated leftSupported rightSupported

theorem induced_rule3 (Q : QualitativeUrnScale)
    (G : ObservedGraph S) (model : ExactModel S)
    (compatible : Compatible model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated :
      let base := GraphMutilation.bar x
      let removable := G.nonAncestorsOf base z w
      PathSpecification.PathDSeparated G
        { removeIncoming := NodeSet.union x removable,
          removeOutgoing := NodeSet.empty }
        y z (NodeSet.union x w))
    (leftSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule3Left x y z w)) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model
      (.kernel (rule3Right x y z w)) assignment) :
    KernelPlausEqv Q
      (kernelPlaus Q model (rule3Left x y z w) assignment)
      (kernelPlaus Q model (rule3Right x y z w) assignment) :=
  qualitative_rule3 Q G model compatible x y z w assignment disjoint
    separated leftSupported rightSupported

/-- Rule 1 for the induced scale, restated as qualitative independence of
node families (no mutilated-graph field). -/
theorem induced_rule1_independent (Q : QualitativeUrnScale)
    (G : ObservedGraph S) (model : ExactModel S)
    (compatible : Compatible model G)
    (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w)) :
    qualitativelyIndependent Q model x y z w := by
  intro assignment a b ha hb
  have hposL : 0 < (kernelUrn model (rule1Left x y z w) assignment).probNum
      ((rule1Left x y z w).conditionEvent assignment) := by
    by_cases hpos : 0 < (kernelUrn model (rule1Left x y z w) assignment).probNum
        ((rule1Left x y z w).conditionEvent assignment)
    · exact hpos
    · have hnone :
          kernelPlaus Q model (rule1Left x y z w) assignment = none := by
        simp [kernelPlaus, hpos]
      cases hnone.symm.trans ha
  have hposR : 0 < (kernelUrn model (rule1Right x y z w) assignment).probNum
      ((rule1Right x y z w).conditionEvent assignment) := by
    by_cases hpos : 0 < (kernelUrn model (rule1Right x y z w) assignment).probNum
        ((rule1Right x y z w).conditionEvent assignment)
    · exact hpos
    · have hnone :
          kernelPlaus Q model (rule1Right x y z w) assignment = none := by
        simp [kernelPlaus, hpos]
      cases hnone.symm.trans hb
  have hl :
      kernelPlaus Q model (rule1Left x y z w) assignment =
        some (Q.ratioPlaus (kernelRatio model (rule1Left x y z w) assignment
          hposL)) := by
    simp [kernelPlaus, hposL]
  have hr :
      kernelPlaus Q model (rule1Right x y z w) assignment =
        some (Q.ratioPlaus (kernelRatio model (rule1Right x y z w) assignment
          hposR)) := by
    simp [kernelPlaus, hposR]
  have ha' : a = Q.ratioPlaus
      (kernelRatio model (rule1Left x y z w) assignment hposL) :=
    Option.some.inj (ha.symm.trans hl)
  have hb' : b = Q.ratioPlaus
      (kernelRatio model (rule1Right x y z w) assignment hposR) :=
    Option.some.inj (hb.symm.trans hr)
  have leftSupported :
      ProbabilityTerm.SupportedAt model (.kernel (rule1Left x y z w))
        assignment :=
    ⟨(kernelRatio model (rule1Left x y z w) assignment hposL).toQProb,
      kernelDenote_equiv_ratio model (rule1Left x y z w) assignment hposL⟩
  have rightSupported :
      ProbabilityTerm.SupportedAt model (.kernel (rule1Right x y z w))
        assignment :=
    ⟨(kernelRatio model (rule1Right x y z w) assignment hposR).toQProb,
      kernelDenote_equiv_ratio model (rule1Right x y z w) assignment hposR⟩
  have heqv :=
    qualitative_rule1 Q G model compatible x y z w assignment disjoint
      separated leftSupported rightSupported
  have heqv' : KernelPlausEqv Q
      (some (Q.ratioPlaus (kernelRatio model (rule1Left x y z w) assignment
        hposL)))
      (some (Q.ratioPlaus (kernelRatio model (rule1Right x y z w) assignment
        hposR))) := by
    simpa [hl, hr] using heqv
  have hQ : Q.eqv
      (Q.ratioPlaus (kernelRatio model (rule1Left x y z w) assignment hposL))
      (Q.ratioPlaus (kernelRatio model (rule1Right x y z w) assignment
        hposR)) := by
    cases heqv' with
    | defined h => exact h
  rw [ha', hb']
  exact hQ

end QualitativeDoCalculus

end Causality
end Thesis
