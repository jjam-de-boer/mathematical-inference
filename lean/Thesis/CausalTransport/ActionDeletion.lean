import Thesis.CausalTransport.DSeparation
import Thesis.Causality.Identification

namespace Thesis
namespace Causality

/-!
# Inspectable action deletion and restriction by the third do rule

These constructors express the original query as rule 3's typed kernels.
They retain the original incoming-cut convention, explicit four-way
disjointness and the supplied path-separation proof. No syntactic rewrite is
silently promoted to a semantic equality or a support theorem.

Deleting the whole action leaves an observational kernel. Restricting it to
a host deletes only the action outside that host; the nested derivation still
has to be supplied. Interpretation belongs to published soundness, and support
of endpoints remains an independent obligation of certificate construction.

The statements and proof bodies are unchanged from
`CompletenessCertificates`. Both historical ready-case certificates and the
current recursive compiler now use this common derivation layer.
-/

/-- Outcome and action of a joint query are disjoint in either order. -/
theorem JointKernelQuery.outcome_action_disjoint
    (q : JointKernelQuery S) : NodeSet.Disjoint q.outcome q.action :=
  fun i hi =>
    match hact : q.action i with
    | false => rfl
    | true =>
        False.elim
          (Bool.false_ne_true
            ((q.action_outcome_disjoint i hact).symm.trans hi))

/-- Restrict the action to a host `H`.  Rule 3 deletes `X \ H` once
`Y ⊥ X \ H | X ∩ H` in `G_{\overline{X}}`, leaving the nested query
`P(Y | do(X ∩ H))`. -/
def JointKernelQuery.shrinkAction (q : JointKernelQuery S)
    (host : NodeSet S) : JointKernelQuery S where
  outcome := q.outcome
  action := NodeSet.inter q.action host
  action_outcome_disjoint :=
    NodeSet.Disjoint.of_subset_left q.action_outcome_disjoint
      (NodeSet.inter_subset_left q.action host)

/--
Rule 3 with empty original action and empty given-set: the incoming cut
is exactly `G_{\overline{Z}}`.  Deleting `Z` from `P(Y | do(Z))` is
therefore the ordinary bar-graph d-separation of `Y` from `Z`.
-/
theorem rule3_empty_xw_mutilation (G : ObservedGraph S) (z : NodeSet S) :
    { removeIncoming :=
        NodeSet.union NodeSet.empty
          (G.nonAncestorsOf (GraphMutilation.bar NodeSet.empty) z
            NodeSet.empty),
      removeOutgoing := NodeSet.empty } =
      GraphMutilation.bar z := by
  rw [ObservedGraph.nonAncestorsOf_empty_targets, NodeSet.union_empty_left]
  rfl

/--
Rule 3's empty-`X`, empty-`W` side graph is `G_{\overline{Z}}` with empty
conditioner.  The `let`-binders of `DoRuleApplication.rule3` are this
equality.
-/
theorem pathDSeparated_rule3_empty_xw
    (G : ObservedGraph S) (y z : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar z) y z
        NodeSet.empty) :
    let base := GraphMutilation.bar NodeSet.empty
    let removable := G.nonAncestorsOf base z NodeSet.empty
    PathSpecification.PathDSeparated G
      { removeIncoming := NodeSet.union NodeSet.empty removable,
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union NodeSet.empty NodeSet.empty) := by
  dsimp
  have hm := (rule3_empty_xw_mutilation G z).symm
  have hw :
      (NodeSet.empty : NodeSet S) =
        NodeSet.union (NodeSet.empty : NodeSet S)
          (NodeSet.empty : NodeSet S) :=
    (NodeSet.union_empty_left (NodeSet.empty : NodeSet S)).symm
  exact hm ▸ hw ▸ separated

/-- The query kernel is rule 3's left kernel at empty original action. -/
theorem JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw
    (q : JointKernelQuery S) :
    q.sourceTerm =
      .kernel
        (rule3Left NodeSet.empty q.outcome q.action NodeSet.empty) := by
  simp [JointKernelQuery.sourceTerm, rule3Left, NodeSet.union_empty_left]

/-- The query kernel is rule 3's left kernel after cutting the action
along a host: `do((X ∩ H) ∪ (X \ H))` is `do(X)`. -/
theorem JointKernelQuery.sourceTerm_eq_rule3Left_shrink
    (q : JointKernelQuery S) (host : NodeSet S) :
    q.sourceTerm =
      .kernel
        (rule3Left (NodeSet.inter q.action host) q.outcome
          (NodeSet.diff q.action host) NodeSet.empty) := by
  simp [JointKernelQuery.sourceTerm, rule3Left, NodeSet.union_inter_diff]

/-- The nested query is rule 3's right kernel: `P(Y | do(X ∩ H))`. -/
theorem JointKernelQuery.shrinkAction_sourceTerm_eq_rule3Right
    (q : JointKernelQuery S) (host : NodeSet S) :
    (q.shrinkAction host).sourceTerm =
      .kernel
        (rule3Right (NodeSet.inter q.action host) q.outcome
          (NodeSet.diff q.action host) NodeSet.empty) := by
  simp [JointKernelQuery.shrinkAction, JointKernelQuery.sourceTerm,
    rule3Right]

/-- Bar-graph d-separation of `Y` from `X \ H` given `X ∩ H` is the
rule-3 side condition on `G_{\overline{X}}`. -/
theorem pathDSeparated_rule3_shrink_of_action
    (G : ObservedGraph S) (q : JointKernelQuery S) (host : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome (NodeSet.diff q.action host)
        (NodeSet.inter q.action host)) :
    PathSpecification.PathDSeparated G
      (GraphMutilation.bar
        (NodeSet.union (NodeSet.inter q.action host)
          (NodeSet.diff q.action host)))
      q.outcome (NodeSet.diff q.action host)
      (NodeSet.inter q.action host) :=
  (congrArg GraphMutilation.bar
      (NodeSet.union_inter_diff q.action host).symm) ▸ separated

/--
Rule 3 shrinks `do(X)` to `do(X ∩ H)` once `Y ⊥ X \ H | X ∩ H` in
`G_{\overline{X}}`.  Deleting the whole action is the special case
`H = ∅`.
-/
def shrinkActionRule3Derivation {G : ObservedGraph S}
    (q : JointKernelQuery S) (host : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome (NodeSet.diff q.action host)
        (NodeSet.inter q.action host)) :
    PathDoCalculusDerivation G q.sourceTerm
      (q.shrinkAction host).sourceTerm :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (JointKernelQuery.sourceTerm_eq_rule3Left_shrink q host)
    (JointKernelQuery.shrinkAction_sourceTerm_eq_rule3Right q host)
    (DoCalculusDerivation.doRule
      (G := G) (separation := pathRuleSeparation G)
      (DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
        (NodeSet.inter q.action host) q.outcome
        (NodeSet.diff q.action host) NodeSet.empty
        (FourWayDisjoint.shrinkAction q.action q.outcome host
          q.action_outcome_disjoint q.outcome_action_disjoint)
        (pathDSeparated_rule3_empty_w G (NodeSet.inter q.action host)
          q.outcome (NodeSet.diff q.action host)
          (pathDSeparated_rule3_shrink_of_action G q host separated))))

/-- Rule 3 followed by a nested derivation of the shrunken query. -/
def shrinkActionIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) (host : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome (NodeSet.diff q.action host)
        (NodeSet.inter q.action host))
    {formula : ProbabilityTerm S}
    (nested :
      PathDoCalculusDerivation G (q.shrinkAction host).sourceTerm formula) :
    PathDoCalculusDerivation G q.sourceTerm formula :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (shrinkActionRule3Derivation q host separated)
    nested

/--
Rule 3 deletes a nonempty action once `Y` is path-d-separated from `X`
in `G_{\overline{X}}` with empty conditioner.  The right kernel is the
empty-action observational `P(Y)`.
-/
def deleteActionRule3Derivation {G : ObservedGraph S}
    (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.action NodeSet.empty) :
    PathDoCalculusDerivation G q.sourceTerm
      (.kernel ⟨q.outcome, NodeSet.empty, NodeSet.empty⟩) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw q)
    (by simp [rule3Right])
    (DoCalculusDerivation.doRule
      (G := G) (separation := pathRuleSeparation G)
      (DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty q.outcome q.action NodeSet.empty
        (FourWayDisjoint.emptyActionConditioning q.outcome q.action
          q.outcome_action_disjoint)
        (pathDSeparated_rule3_empty_xw G q.outcome q.action separated)))

end Causality
end Thesis
