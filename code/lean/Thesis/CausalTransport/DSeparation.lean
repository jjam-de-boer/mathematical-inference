import Thesis.Causality.Derivation
import Thesis.Causality.ReachabilityCorrectness

namespace Thesis
namespace Causality

/-!
Path-blocking specification for the executable d-separation test.

`ObservedGraph.dSeparated` computes through explicit-latent expansion,
ancestral moralisation and finite reachability.  The definitions below state
the usual active-path criterion independently.  Their equivalence is exposed
as a precise theorem interface instead of being folded silently into the
published completeness assumption.
-/

namespace PathSpecification

def Adjacent (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right : SeparationNode S) : Prop :=
  G.expandedMutilatedEdge mutilation left right = true \/
    G.expandedMutilatedEdge mutilation right left = true

def IsCollider (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (previous middle next : SeparationNode S) : Prop :=
  G.expandedMutilatedEdge mutilation previous middle = true /\
    G.expandedMutilatedEdge mutilation next middle = true

def ColliderActivated (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (node : SeparationNode S) : Prop :=
  G.ancestorOf mutilation conditioned node = true

def NonColliderOpen (conditioned : NodeSet S)
    (node : SeparationNode S) : Prop :=
  ObservedGraph.blockedBy conditioned node = false

def TripleActive (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (previous middle next : SeparationNode S) : Prop :=
  (IsCollider G mutilation previous middle next /\
      ColliderActivated G mutilation conditioned middle) \/
    (Not (IsCollider G mutilation previous middle next) /\
      NonColliderOpen conditioned middle)

inductive InternalTriplesActive (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S) :
    List (SeparationNode S) -> Prop
  | nil : InternalTriplesActive G mutilation conditioned []
  | singleton (node) :
      InternalTriplesActive G mutilation conditioned [node]
  | pair (left right) :
      InternalTriplesActive G mutilation conditioned [left, right]
  | step {previous middle next rest} :
      TripleActive G mutilation conditioned previous middle next ->
      InternalTriplesActive G mutilation conditioned (middle :: next :: rest) ->
      InternalTriplesActive G mutilation conditioned
        (previous :: middle :: next :: rest)

structure ActivePath (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (source target : SeparationNode S) : Type where
  nodes : List (SeparationNode S)
  starts : nodes.head? = some source
  finishes : nodes.getLast? = some target
  simple : nodes.Nodup
  adjacent : Consecutive (Adjacent G mutilation) nodes
  source_open : ObservedGraph.blockedBy conditioned source = false
  target_open : ObservedGraph.blockedBy conditioned target = false
  internal_active : InternalTriplesActive G mutilation conditioned nodes

def PathDSeparated (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S) : Prop :=
  Not (Exists fun source : Fin S.count =>
    Exists fun target : Fin S.count =>
      left source = true /\ right target = true /\
        Nonempty
          (ActivePath G mutilation conditioned
            (.observed source) (.observed target)))

/-- An empty left endpoint set admits no active path, so it is
d-separated from every right set. -/
theorem PathDSeparated.of_isEmpty_left
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (hleft : NodeSet.isEmpty left = true) :
    PathDSeparated G mutilation left right conditioned := by
  intro h
  rcases h with ⟨source, _target, hs, _ht, _path⟩
  have hfalse : left source = false :=
    (NodeSet.isEmpty_eq_true_iff left).mp hleft source
  exact Bool.false_ne_true (hfalse.symm.trans hs)

/-- An empty right endpoint set admits no active path. -/
theorem PathDSeparated.of_isEmpty_right
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (hright : NodeSet.isEmpty right = true) :
    PathDSeparated G mutilation left right conditioned := by
  intro h
  rcases h with ⟨_source, target, _hs, ht, _path⟩
  have hfalse : right target = false :=
    (NodeSet.isEmpty_eq_true_iff right).mp hright target
  exact Bool.false_ne_true (hfalse.symm.trans ht)

end PathSpecification

/--
Correctness interface for the finite Boolean d-separation implementation.

`ObservedGraph.dSeparationCorrectness` inhabits this with the ancestral-moral
search coinciding with the active-path specification. The named structure
keeps that correspondence explicit at certificate-transport boundaries.
-/
structure DSeparationCorrectness (G : ObservedGraph S) : Prop where
  algorithm_iff_active_path : forall mutilation left right conditioned,
    G.dSeparated mutilation left right conditioned = true <->
      PathSpecification.PathDSeparated
        G mutilation left right conditioned

/-- The executable test is a decision procedure for the active-path
specification. -/
theorem DSeparationCorrectness.pathDSeparated_of_dSeparated
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    {mutilation : GraphMutilation S}
    {left right conditioned : NodeSet S}
    (h : G.dSeparated mutilation left right conditioned = true) :
    PathSpecification.PathDSeparated G mutilation left right
      conditioned :=
  (correct.algorithm_iff_active_path mutilation left right
    conditioned).mp h

/-- The active-path specialization of the common rule-side-condition interface. -/
@[reducible] def pathRuleSeparation (G : ObservedGraph S) : RuleSeparation G where
  holds := PathSpecification.PathDSeparated G

/-- A published do-rule step stated with the standard active-path criterion. -/
abbrev PathDoRuleApplication (G : ObservedGraph S) :=
  DoRuleApplication G (separation := pathRuleSeparation G)

def PathDoRuleApplication.compile (correct : DSeparationCorrectness G)
    (application : PathDoRuleApplication G left right) :
    DoRuleApplication G left right :=
  DoRuleApplication.mapSeparation
    (source := pathRuleSeparation G)
    (target := executableRuleSeparation G)
    (fun mutilation first second conditioned separated =>
      (correct.algorithm_iff_active_path mutilation first second conditioned).mpr
        separated)
    application

def DoRuleApplication.toPath (correct : DSeparationCorrectness G)
    (application : DoRuleApplication G left right) :
    PathDoRuleApplication G left right :=
  DoRuleApplication.mapSeparation
    (source := executableRuleSeparation G)
    (target := pathRuleSeparation G)
    (fun mutilation first second conditioned separated =>
      (correct.algorithm_iff_active_path mutilation first second conditioned).mp
        separated)
    application

/-- Published derivation syntax whose causal side conditions use active paths. -/
abbrev PathDoCalculusDerivation (G : ObservedGraph S) :=
  DoCalculusDerivation G (separation := pathRuleSeparation G)

def PathDoCalculusDerivation.compile (correct : DSeparationCorrectness G) :
    PathDoCalculusDerivation G left right -> DoCalculusDerivation G left right :=
  DoCalculusDerivation.mapRules
    (source := pathRuleSeparation G)
    (target := executableRuleSeparation G)
    (PathDoRuleApplication.compile correct)

/-! ## Empty-conditioner rule-3 side graphs

These graph identities are shared by historical and current compilers.
They need neither a completeness theorem nor a soundness assumption. -/

/--
Rule 3 with empty given-set: the incoming cut is `G_{\overline{X ∪ Z}}`
because `Z(∅) = Z`.  Deleting `Z` from `P(Y | do(X ∪ Z))` is therefore
ordinary bar-graph d-separation of `Y` from `Z` given `X`.
-/
theorem rule3_empty_w_mutilation (G : ObservedGraph S)
    (kept removed : NodeSet S) :
    { removeIncoming :=
        NodeSet.union kept
          (G.nonAncestorsOf (GraphMutilation.bar kept) removed
            NodeSet.empty),
      removeOutgoing := NodeSet.empty } =
      GraphMutilation.bar (NodeSet.union kept removed) := by
  rw [ObservedGraph.nonAncestorsOf_empty_targets]
  rfl

/--
Rule 3's empty-`W` side graph is `G_{\overline{X ∪ Z}}` with conditioner
`X`.  The `let`-binders of `DoRuleApplication.rule3` are this equality.
-/
theorem pathDSeparated_rule3_empty_w
    (G : ObservedGraph S) (kept y removed : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar (NodeSet.union kept removed)) y removed kept) :
    let base := GraphMutilation.bar kept
    let removable := G.nonAncestorsOf base removed NodeSet.empty
    PathSpecification.PathDSeparated G
      { removeIncoming := NodeSet.union kept removable,
        removeOutgoing := NodeSet.empty }
      y removed (NodeSet.union kept NodeSet.empty) := by
  dsimp
  have hm := (rule3_empty_w_mutilation G kept removed).symm
  have hw := (NodeSet.union_empty_right kept).symm
  exact hm ▸ hw ▸ separated

end Causality
end Thesis
