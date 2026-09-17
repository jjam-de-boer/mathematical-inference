import Thesis.Causality.Derivation

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

def Consecutive {X : Type u} (relation : X -> X -> Prop) : List X -> Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      relation left right /\ Consecutive relation (right :: rest)

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

end Causality
end Thesis
