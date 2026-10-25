import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.ActionDeletion
import Thesis.Causality.TermSupport
import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

open Probability

/-!
# Supported observational marginals after action deletion

Rule 3 deletes a separated action, and finite marginalization then prints the
query as a marginal of the complete observational record. The support proof
keeps both operations explicit, including all marginal assignments. It uses
unconditional-kernel normalization, not a positivity assumption on observed
cells or a causal soundness theorem to manufacture support.

These general certificate constructors remain useful to modern current-input
compilation examples. They therefore live in the current implementation,
independently of the removed legacy engine and fixed-depth failure proofs.
The retained names and theorem statements still cover arbitrary graph model
classes; observational zeros are not excluded by this promotion.
-/

/-- Marginalization writes the observational joint as
`P(Y ∪ (V \ Y))`; ID writes it as `P(V)`.  The covering
`NodeSet.union_diff_full` identifies the two kernels. -/
theorem emptyActionMarginalizationTerm_eq_of (outcome : NodeSet S) :
    ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full outcome)
      (.kernel ⟨NodeSet.union outcome
        (NodeSet.diff NodeSet.full outcome),
        NodeSet.empty, NodeSet.empty⟩) =
      ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full outcome)
        (observationalJointTerm S) := by
  simp [observationalJointTerm, NodeSet.union_diff_full]

/-- The empty-condition observational joint is always defined: its
denominator is the sure event, whose mass is one. -/
noncomputable def observationalJointTerm_supportedAt
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    (observationalJointTerm S).SupportedAt model assignment :=
  ⟨((Kernel.mk NodeSet.full NodeSet.empty NodeSet.empty).distribution
      model assignment).probVal (Kernel.agreesOn NodeSet.full assignment),
    by
      simpa [observationalJointTerm, ProbabilityTerm.denote] using
        Kernel.unconditionalDenote model NodeSet.full NodeSet.empty
          assignment⟩

/-- A finite sum of defined observational joints is defined.  This is
the right endpoint of empty-action ID: `∑_{V \ Y} P(V)`. -/
noncomputable def emptyActionMarginal_supportedAt
    (model : FiniteLatentSCM S) (outcome : NodeSet S)
    (assignment : S.Assignment) :
    (ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full outcome)
      (observationalJointTerm S)).SupportedAt model assignment := by
  simpa [ProbabilityTerm.denote] using
    ProbabilityResult.sum_map_supported
      (ProbabilityTerm.marginalAssignments S
        (NodeSet.diff NodeSet.full outcome) assignment)
      (fun variant => (observationalJointTerm S).denote model variant)
      (fun variant => observationalJointTerm_supportedAt model variant)

/-- Empty-action marginalization of an unconditional kernel `P(Y)` onto
the ID formula `∑_{V \ Y} P(V)`. -/
def unconditionalEmptyActionIdDerivation {G : ObservedGraph S}
    (outcome : NodeSet S) :
    PathDoCalculusDerivation G
      (.kernel ⟨outcome, NodeSet.empty, NodeSet.empty⟩)
      (.marginalize (NodeSet.diff NodeSet.full outcome)
        (observationalJointTerm S)) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    rfl
    (emptyActionMarginalizationTerm_eq_of outcome).symm
    (DoCalculusDerivation.marginalization
      (G := G) (separation := pathRuleSeparation G)
      NodeSet.empty outcome (NodeSet.diff NodeSet.full outcome)
      NodeSet.empty (FourWayDisjoint.emptyActionMarginal outcome))

/-- Support tree of empty-action ID on an unconditional kernel. -/
noncomputable def unconditionalEmptyActionIdDerivation_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (outcome : NodeSet S)
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((unconditionalEmptyActionIdDerivation (G := G) outcome).compile
        correct) :=
  let kernelSupported :=
    emptyActionKernel_supportedAt model outcome assignment
  let identified :=
    emptyActionMarginal_supportedAt model outcome assignment
  let innerRight :=
    ProbabilityTerm.SupportedAt.congr
      (emptyActionMarginalizationTerm_eq_of outcome).symm identified
  ⟨kernelSupported, ⟨identified, ⟨kernelSupported, ⟨innerRight, ()⟩⟩⟩⟩

/--
Rule 3 followed by empty-action ID: `P(Y | do(X)) = P(Y) = ∑_{V \ Y} P(V)`
whenever `Y ⊥ X` in `G_{\overline{X}}`.
-/
def deleteActionIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.action NodeSet.empty) :
    PathDoCalculusDerivation G q.sourceTerm
      (.marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S)) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (deleteActionRule3Derivation q separated)
    (unconditionalEmptyActionIdDerivation q.outcome)

/--
Nonempty-action identification when the query outcome is d-separated from
the action in `G_{\overline{X}}`.  The formula is the same observational
marginal as empty-action ID.
-/
noncomputable def deleteActionIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.action NodeSet.empty) :
    PublishedJointCertificate C correct q where
  formula :=
    .marginalize (NodeSet.diff NodeSet.full q.outcome)
      (observationalJointTerm S)
  actionFree := observationalJointTerm_actionFree S
  derivation := deleteActionIdentifiedIdDerivation q separated
  supported := fun model _member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      deleteActionIdentifiedIdDerivation, deleteActionRule3Derivation]
    let pY :=
      emptyActionKernel_supportedAt model q.outcome assignment
    let formulaSupported :=
      emptyActionMarginal_supportedAt model q.outcome assignment
    let hleft := JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw q
    let rule3LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨⟨sourceSupported,
              ⟨pY, ⟨rule3LeftSupported, ⟨pY, ()⟩⟩⟩⟩,
            unconditionalEmptyActionIdDerivation_supported correct
              q.outcome model assignment⟩⟩⟩

end Causality
end Thesis
