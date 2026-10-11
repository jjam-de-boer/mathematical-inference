import Thesis.CausalTransport.HiddenDAGSoundness
import Thesis.Examples.HiddenDAGCollapse

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGSoundness

open Probability HiddenDAGCollapse

/-!
# Native soundness with three-child roots and observational zeros

Reuse the full hidden model from `HiddenDAGCollapse`: a common cause feeds
`X,Y,Z`, while `X -> V -> Y` passes through a hidden relay.  Its collapsed root
model is proved noncanonical, and the observational event `Y = true` is null.

Rule 3 nevertheless identifies `P(X | do(Y))` as `P(X)`, including the null
observational action value `Y = true`: intervening on a descendant cannot
change `X`.  The native full-DAG support tree and the general derivation theorem
prove this without a canonical compatibility proof or an external interface.

A second test uses a zero prefix `P(Y = true)` and the genuinely undefined
conditional `P(X | Y = true)`.  Both a guarded chain leaf and a guarded
congruence support tree remain valid.  The factor's hypothetical positive
branch is discharged from the checked zero weight, not given an arbitrary
conditional value.  A third test checks observable overlap for a supported
causal kernel with a zero outcome.
-/

def reference : signature.Assignment := fun _ => true

/-! ## A causal do-rule at a null observational action -/

def rule3Application : DoRuleApplication projection.observedGraph
    (rule3Left NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty)
    (rule3Right NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty) :=
  .rule3 NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty
    (FourWayDisjoint.emptyAction _ _ NodeSet.empty
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _))
    (by
      change projection.observedGraph.dSeparated
        { removeIncoming := NodeSet.union NodeSet.empty
            (projection.observedGraph.nonAncestorsOf (.bar NodeSet.empty)
              (NodeSet.singleton y) NodeSet.empty),
          removeOutgoing := NodeSet.empty }
        (NodeSet.singleton x) (NodeSet.singleton y)
        (NodeSet.union NodeSet.empty NodeSet.empty) = true
      decide +kernel)

def source : ProbabilityTerm signature :=
  .kernel (rule3Left NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty)

def observationalFormula : ProbabilityTerm signature :=
  .kernel (rule3Right NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty)

/-- Keep the unsimplified rule endpoints so the recursive support tree sees
an actual `doRule` constructor, not a stuck dependent equality transport. -/
def rule3Derivation : DoCalculusDerivation projection.observedGraph source observationalFormula :=
  .doRule rule3Application

/-- Both rule endpoints are unconditional causal kernels.  Their support is
available in every full model over this graph, with no positivity assumption. -/
noncomputable def rule3_supported (other : FiniteHiddenDAGSCM signature projection)
    (assignment : signature.Assignment) :
    HiddenDAGLocalDerivationSupport other assignment rule3Derivation :=
  ⟨other.kernelSupportedAt_unconditional (NodeSet.singleton x)
      (NodeSet.union NodeSet.empty (NodeSet.singleton y)) assignment,
    other.kernelSupportedAt_unconditional (NodeSet.singleton x) NodeSet.empty assignment, ()⟩

/-- The action value used in the regression has no observational mass.  This
does not stop the graph-derived rule-3 reduction, whose kernels are supported. -/
theorem observational_action_is_null :
    (model.observationalDist.probVal (Kernel.agreesOn (NodeSet.singleton y) reference)).num = 0 := by
  decide +kernel

/-- Instantiate the entire native derivation-soundness theorem on the actual
noncanonical collapse, rather than assuming a do-rule identity for the fixture. -/
noncomputable def effect_at_null_observational_action :
    model.TermEquivalentAt source observationalFormula reference :=
  rule3Derivation.hiddenDAG_denotational_soundAt (rule3_supported model reference)

/-- Any observationally equal full hidden-DAG model has the same effect.
The other model's hidden and private-noise finite sizes remain arbitrary. -/
noncomputable def effect_in_any_observationally_equal_full_model
    (other : FiniteHiddenDAGSCM signature projection)
    (observational : model.ObservationalAgreement other)
    (assignment : signature.Assignment) :
    ProbabilityResult.Equivalent (model.termDenote source assignment)
      (other.termDenote source assignment) :=
  rule3Derivation.hiddenDAG_identifiableAt model other observational
    (fun _ => rfl) assignment
    (rule3_supported model assignment) (rule3_supported other assignment)

/-- The original full-family query API reads the same native rule-3 result.
No `PublishedLatentProjection` value is passed to this adapter. -/
noncomputable def full_family_rule3_sound :
    ProbabilityResult.Equivalent
      ((HiddenDAGModelFamily.all projection).kernelResult model
        (rule3Left NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty) reference)
      ((HiddenDAGModelFamily.all projection).kernelResult model
        (rule3Right NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty) reference) :=
  effect_at_null_observational_action

/-! ## Native zero-prefix support, including guarded congruence -/

def weight : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.empty⟩

def conditional : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.singleton x, NodeSet.empty,
    NodeSet.union (NodeSet.singleton y) NodeSet.empty⟩

def guardedFormula : ProbabilityTerm signature := .weightedMultiply weight conditional

def jointSource : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.union (NodeSet.singleton x) (NodeSet.singleton y), NodeSet.empty, NodeSet.empty⟩

/-- Scan the actual computed option, not a truncated existential support
statement.  A successful support tag retains the option's own rational value. -/
private def support_of_isSome (result : ProbabilityResult.Result)
    (found : result.isSome = true) : ProbabilityResult.Supported result := by
  cases result with
  | none => cases found
  | some value => exact ⟨value, ProbabilityResult.refl _⟩

/-- The native factor is actually undefined; it is not redefined as zero. -/
theorem native_conditional_is_undefined : (model.termDenote conditional reference).isNone = true := by
  decide +kernel

/-- Only the complete guarded contribution has a supported result. -/
noncomputable def guarded_supported : model.TermSupportedAt guardedFormula reference :=
  support_of_isSome _ (by decide +kernel)

noncomputable def weight_supported : model.TermSupportedAt weight reference :=
  model.kernelSupportedAt_unconditional (NodeSet.singleton y) NodeSet.empty reference

/-- A positive support witness for the checked zero weight would contradict
rational numerator-zero invariance.  This proof uses explicit value data and
does not decide an arbitrary support proposition. -/
private theorem weight_cannot_be_positive
    (positive : ProbabilityResult.PositiveSupportedValue (model.termDenote weight reference)) : False := by
  have weightZero : ProbabilityResult.Equivalent (model.termDenote weight reference) (some QProb.zero) :=
    ProbabilityResult.trans weight_supported.2
      (.value (by decide +kernel : QProb.Equiv weight_supported.1 QProb.zero))
  have compared := ProbabilityResult.trans (ProbabilityResult.symm positive.equivalent) weightZero
  cases compared with
  | value equivalent =>
      have zero : positive.value.num = 0 := (QProb.equiv_num_zero_iff equivalent).mpr rfl
      exact (Nat.ne_of_gt positive.positive) zero

def guardedCongruence : DoCalculusDerivation projection.observedGraph guardedFormula guardedFormula :=
  .weightedMultiplyCongr (.refl weight) (.refl conditional)

/-- The weight subtree is present.  The factor subtree is requested only
under positive native weight, which is impossible at this null prefix cell. -/
noncomputable def guarded_congruence_supported :
    HiddenDAGLocalDerivationSupport model reference guardedCongruence :=
  ⟨guarded_supported, guarded_supported,
    ⟨weight_supported, weight_supported, ()⟩,
    fun positive => False.elim (weight_cannot_be_positive positive)⟩

noncomputable def guarded_congruence_sound :
    model.TermEquivalentAt guardedFormula guardedFormula reference :=
  guardedCongruence.hiddenDAG_denotational_soundAt guarded_congruence_supported

def guardedChainDerivation : DoCalculusDerivation projection.observedGraph jointSource guardedFormula :=
  .weightedChain NodeSet.empty (NodeSet.singleton x) (NodeSet.singleton y) NodeSet.empty
    (FourWayDisjoint.emptyAction _ _ NodeSet.empty
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _))

/-- The guarded chain derives the actual native joint probability despite
the undefined conditional.  No full-distribution positivity is requested. -/
noncomputable def guarded_chain_sound : model.TermEquivalentAt jointSource guardedFormula reference :=
  guardedChainDerivation.hiddenDAG_denotational_soundAt
    ⟨model.kernelSupportedAt_unconditional
        (NodeSet.union (NodeSet.singleton x) (NodeSet.singleton y)) NodeSet.empty reference,
      guarded_supported, ()⟩

/-! ## Observable overlap permits zero causal outcomes -/

theorem action_overlap : model.ObservationalCylinderPositiveAt (NodeSet.singleton x) reference := by
  unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
  decide +kernel

/-- At `do(X = true)`, the simultaneous outcome `Y = true, Z = true` is
impossible, but the kernel remains supported from observable action overlap. -/
noncomputable def locally_supported_zero_outcome :
    model.TermSupportedAt
      (.kernel ⟨NodeSet.union (NodeSet.singleton y) (NodeSet.singleton z),
        NodeSet.singleton x, NodeSet.empty⟩) reference :=
  model.kernelSupportedAt_of_observational_overlap _ reference
    (by simpa only [NodeSet.union_empty_right] using action_overlap)

theorem zero_causal_outcome :
    ((model.interventionalDist ((HardIntervention.empty signature).set x true)).probVal
      (Kernel.agreesOn (NodeSet.union (NodeSet.singleton y) (NodeSet.singleton z)) reference)).num = 0 := by
  decide +kernel

end HiddenDAGSoundness
end Examples
end Causality
end Thesis
