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
External correctness boundary for the finite Boolean implementation.

An inhabitant is the standard ancestral-moralisation theorem specialized to
the explicit-latent expansion used here.  It can later be replaced by an
internal proof without changing the transport interface.
-/
structure DSeparationCorrectness (G : ObservedGraph S) : Prop where
  algorithm_iff_active_path : forall mutilation left right conditioned,
    G.dSeparated mutilation left right conditioned = true <->
      PathSpecification.PathDSeparated
        G mutilation left right conditioned

/-- A published do-rule step stated with the standard active-path criterion. -/
inductive PathDoRuleApplication (G : ObservedGraph S) :
    Kernel S -> Kernel S -> Type
  | rule1 (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (separated :
        PathSpecification.PathDSeparated G (.bar x)
          y z (NodeSet.union x w)) :
      PathDoRuleApplication G (rule1Left x y z w) (rule1Right x y z w)
  | rule2 (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (separated :
        PathSpecification.PathDSeparated G (.barUnderline x z)
          y z (NodeSet.union x w)) :
      PathDoRuleApplication G (rule2Left x y z w) (rule2Right x y z w)
  | rule3 (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (separated :
        let base := GraphMutilation.bar x
        let removable := G.nonAncestorsOf base z w
        PathSpecification.PathDSeparated G
          { removeIncoming := NodeSet.union x removable
            removeOutgoing := NodeSet.empty }
          y z (NodeSet.union x w)) :
      PathDoRuleApplication G (rule3Left x y z w) (rule3Right x y z w)

def PathDoRuleApplication.compile (correct : DSeparationCorrectness G)
    (application : PathDoRuleApplication G left right) :
    DoRuleApplication G left right := by
  cases application with
  | rule1 x y z w disjoint separated =>
      exact .rule1 x y z w disjoint
        ((correct.algorithm_iff_active_path (.bar x) y z
          (NodeSet.union x w)).mpr separated)
  | rule2 x y z w disjoint separated =>
      exact .rule2 x y z w disjoint
        ((correct.algorithm_iff_active_path (.barUnderline x z) y z
          (NodeSet.union x w)).mpr separated)
  | rule3 x y z w disjoint separated =>
      exact .rule3 x y z w disjoint
        ((correct.algorithm_iff_active_path
          { removeIncoming := NodeSet.union x
              (G.nonAncestorsOf (.bar x) z w)
            removeOutgoing := NodeSet.empty }
          y z (NodeSet.union x w)).mpr separated)

def DoRuleApplication.toPath (correct : DSeparationCorrectness G)
    (application : DoRuleApplication G left right) :
    PathDoRuleApplication G left right := by
  cases application with
  | rule1 x y z w disjoint separated =>
      exact .rule1 x y z w disjoint
        ((correct.algorithm_iff_active_path (.bar x) y z
          (NodeSet.union x w)).mp separated)
  | rule2 x y z w disjoint separated =>
      exact .rule2 x y z w disjoint
        ((correct.algorithm_iff_active_path (.barUnderline x z) y z
          (NodeSet.union x w)).mp separated)
  | rule3 x y z w disjoint separated =>
      exact .rule3 x y z w disjoint
        ((correct.algorithm_iff_active_path
          { removeIncoming := NodeSet.union x
              (G.nonAncestorsOf (.bar x) z w)
            removeOutgoing := NodeSet.empty }
          y z (NodeSet.union x w)).mp separated)

/-- Published derivation syntax whose causal side conditions use active paths. -/
inductive PathDoCalculusDerivation (G : ObservedGraph S) :
    ProbabilityTerm S -> ProbabilityTerm S -> Type
  | refl (term) : PathDoCalculusDerivation G term term
  | symm {left right} :
      PathDoCalculusDerivation G left right ->
        PathDoCalculusDerivation G right left
  | trans {left middle right} :
      PathDoCalculusDerivation G left middle ->
      PathDoCalculusDerivation G middle right ->
      PathDoCalculusDerivation G left right
  | doRule {left right} :
      PathDoRuleApplication G left right ->
      PathDoCalculusDerivation G (.kernel left) (.kernel right)
  | marginalization (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      PathDoCalculusDerivation G
        (.kernel ⟨y, x, w⟩)
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩))
  | conditioning (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      PathDoCalculusDerivation G
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩))
  | chain (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      PathDoCalculusDerivation G
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩))
  | marginalizeCongr (nodes : NodeSet S) {left right} :
      PathDoCalculusDerivation G left right ->
      PathDoCalculusDerivation G (.marginalize nodes left) (.marginalize nodes right)
  | evaluateAtCongr (assignment : S.Assignment) {left right} :
      PathDoCalculusDerivation G left right ->
      PathDoCalculusDerivation G
        (.evaluateAt assignment left) (.evaluateAt assignment right)
  | addCongr {left left' right right'} :
      PathDoCalculusDerivation G left left' ->
      PathDoCalculusDerivation G right right' ->
      PathDoCalculusDerivation G (.add left right) (.add left' right')
  | multiplyCongr {left left' right right'} :
      PathDoCalculusDerivation G left left' ->
      PathDoCalculusDerivation G right right' ->
      PathDoCalculusDerivation G (.multiply left right) (.multiply left' right')
  | divideCongr {left left' right right'} :
      PathDoCalculusDerivation G left left' ->
      PathDoCalculusDerivation G right right' ->
      PathDoCalculusDerivation G (.divide left right) (.divide left' right')

def PathDoCalculusDerivation.compile (correct : DSeparationCorrectness G) :
    PathDoCalculusDerivation G left right -> DoCalculusDerivation G left right
  | .refl term => .refl term
  | .symm derivation => .symm (derivation.compile correct)
  | .trans first second =>
      .trans (first.compile correct) (second.compile correct)
  | .doRule application => .doRule (application.compile correct)
  | .marginalization x y z w disjoint =>
      .marginalization x y z w disjoint
  | .conditioning x y z w disjoint =>
      .conditioning x y z w disjoint
  | .chain x y z w disjoint => .chain x y z w disjoint
  | .marginalizeCongr nodes derivation =>
      .marginalizeCongr nodes (derivation.compile correct)
  | .evaluateAtCongr assignment derivation =>
      .evaluateAtCongr assignment (derivation.compile correct)
  | .addCongr first second =>
      .addCongr (first.compile correct) (second.compile correct)
  | .multiplyCongr first second =>
      .multiplyCongr (first.compile correct) (second.compile correct)
  | .divideCongr first second =>
      .divideCongr (first.compile correct) (second.compile correct)

end Causality
end Thesis
