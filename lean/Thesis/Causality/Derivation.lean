import Thesis.Causality.Graph

namespace Thesis
namespace Causality

/-!
Finite d-separation and a concrete symbolic derivation language for
do-calculus.  Bidirected edges are interpreted through explicit latent roots;
the separation test then uses ancestral moralization of that all-directed DAG.
-/

namespace FiniteReachability

def contains (same : α -> α -> Bool) (nodes : List α) (target : α) : Bool :=
  nodes.any (fun node => same node target)

def step (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (reached : List α) : List α :=
  nodes.filter (fun target =>
    reached.any (fun source =>
      same source target || edge source target))

def closure (same : α -> α -> Bool) (nodes : List α)
    (edge : α -> α -> Bool) :
    Nat -> List α -> List α
  | 0, reached => reached
  | fuel + 1, reached =>
      closure same nodes edge fuel (step same nodes edge reached)

def within (same : α -> α -> Bool) (nodes : List α)
    (edge : α -> α -> Bool)
    (fuel : Nat) (source target : α) : Bool :=
  contains same (closure same nodes edge fuel [source]) target

end FiniteReachability

/--
Nodes in the explicit-latent DAG used to decide separation.  A latent-pair
node is active only when the corresponding bidirected edge exists.
-/
inductive SeparationNode (S : ObservedSignature) where
  | observed : Fin S.count -> SeparationNode S
  | latentPair : Fin S.count -> Fin S.count -> SeparationNode S

namespace SeparationNode

/-- Injective finite code with disjoint observed and latent-pair ranges. -/
def code : SeparationNode S -> Nat
  | .observed node => node.val
  | .latentPair left right =>
      S.count + left.val * S.count + right.val

def beq (left right : SeparationNode S) : Bool :=
  Nat.beq left.code right.code

def allObserved (S : ObservedSignature) : List (SeparationNode S) :=
  List.ofFn (fun i : Fin S.count => observed i)

def allLatentPairs (S : ObservedSignature) : List (SeparationNode S) :=
  (List.ofFn (fun i : Fin S.count => i)).flatMap (fun i =>
    (List.ofFn (fun j : Fin S.count => j)).map (fun j => latentPair i j))

def all (S : ObservedSignature) : List (SeparationNode S) :=
  allObserved S ++ allLatentPairs S

def inObservedSet (nodes : NodeSet S) : SeparationNode S -> Bool
  | observed i => nodes i
  | latentPair _ _ => false

end SeparationNode

/-- Incoming and outgoing arrows removed for a do-calculus side graph. -/
structure GraphMutilation (S : ObservedSignature) where
  removeIncoming : NodeSet S
  removeOutgoing : NodeSet S

namespace GraphMutilation

def none (S : ObservedSignature) : GraphMutilation S where
  removeIncoming := NodeSet.empty
  removeOutgoing := NodeSet.empty

def bar (nodes : NodeSet S) : GraphMutilation S where
  removeIncoming := nodes
  removeOutgoing := NodeSet.empty

def barUnderline (incoming outgoing : NodeSet S) : GraphMutilation S where
  removeIncoming := incoming
  removeOutgoing := outgoing

end GraphMutilation

namespace ObservedGraph

def expandedMutilatedEdge (G : ObservedGraph S) (m : GraphMutilation S)
    (source target : SeparationNode S) : Bool :=
  match source with
  | .observed parent =>
      match target with
      | .observed child =>
          S.directed parent child &&
            !(m.removeOutgoing parent) && !(m.removeIncoming child)
      | .latentPair _ _ => false
  | .latentPair left right =>
      match target with
      | .observed child =>
          G.bidirected left right &&
            (finBeq child left || finBeq child right) &&
            !(m.removeIncoming child)
      | .latentPair _ _ => false

def separationNodes (_G : ObservedGraph S) : List (SeparationNode S) :=
  SeparationNode.all S

def expandedReachable (G : ObservedGraph S) (m : GraphMutilation S)
    (source target : SeparationNode S) : Bool :=
  FiniteReachability.within SeparationNode.beq
    G.separationNodes (G.expandedMutilatedEdge m)
    G.separationNodes.length source target

def ancestorOf (G : ObservedGraph S) (m : GraphMutilation S)
    (targets : NodeSet S) (node : SeparationNode S) : Bool :=
  (List.ofFn (fun i : Fin S.count => i)).any (fun target =>
    targets target && G.expandedReachable m node (.observed target))

def ancestralMoralEdge (G : ObservedGraph S) (m : GraphMutilation S)
    (targets : NodeSet S) (left right : SeparationNode S) : Bool :=
  G.ancestorOf m targets left && G.ancestorOf m targets right &&
    !(SeparationNode.beq left right) &&
    (G.expandedMutilatedEdge m left right ||
      G.expandedMutilatedEdge m right left ||
      G.separationNodes.any (fun child =>
        G.ancestorOf m targets child &&
          G.expandedMutilatedEdge m left child &&
          G.expandedMutilatedEdge m right child))

def blockedBy (conditioned : NodeSet S) : SeparationNode S -> Bool
  | .observed i => conditioned i
  | .latentPair _ _ => false

def moralReachable (G : ObservedGraph S) (m : GraphMutilation S)
    (targets conditioned : NodeSet S)
    (source target : SeparationNode S) : Bool :=
  let openEdge := fun left right =>
    !(blockedBy conditioned left) && !(blockedBy conditioned right) &&
      G.ancestralMoralEdge m targets left right
  FiniteReachability.within SeparationNode.beq G.separationNodes openEdge
    G.separationNodes.length source target

/--
Decidable d-separation in an ADMG, computed in its explicit-latent expansion.
The ancestral set is formed from `left ∪ right ∪ conditioned`, the ancestral
graph is moralized, conditioned observed nodes are deleted, and finite
reachability is tested in the resulting undirected graph.
-/
def dSeparated (G : ObservedGraph S) (m : GraphMutilation S)
    (left right conditioned : NodeSet S) : Bool :=
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  !((List.ofFn (fun i : Fin S.count => i)).any (fun x =>
    left x && !(conditioned x) &&
      (List.ofFn (fun i : Fin S.count => i)).any (fun y =>
        right y && !(conditioned y) &&
          G.moralReachable m targets conditioned
            (.observed x) (.observed y))))

def observedDirectedEdge (_G : ObservedGraph S) (m : GraphMutilation S)
    (parent child : Fin S.count) : Bool :=
  S.directed parent child &&
    !(m.removeOutgoing parent) && !(m.removeIncoming child)

def observedAncestorOf (G : ObservedGraph S) (m : GraphMutilation S)
    (targets : NodeSet S) (source : Fin S.count) : Bool :=
  let nodes := List.ofFn (fun i : Fin S.count => i)
  nodes.any (fun target =>
    targets target &&
      FiniteReachability.within finBeq nodes (G.observedDirectedEdge m)
        nodes.length source target)

/-- `Z(W)` from rule 3: action nodes that are not ancestors of `W`. -/
def nonAncestorsOf (G : ObservedGraph S) (m : GraphMutilation S)
    (actions targets : NodeSet S) : NodeSet S :=
  fun i => actions i && !(G.observedAncestorOf m targets i)

end ObservedGraph

/-! ## Symbolic probability expressions and do-calculus certificates -/

/-- A symbolic interventional kernel `P(outcome | do(action), condition)`. -/
structure Kernel (S : ObservedSignature) where
  outcome : NodeSet S
  action : NodeSet S
  condition : NodeSet S

def rule1Left (x y z w : NodeSet S) : Kernel S :=
  ⟨y, x, NodeSet.union z w⟩

def rule1Right (x y _z w : NodeSet S) : Kernel S :=
  ⟨y, x, w⟩

def rule2Left (x y z w : NodeSet S) : Kernel S :=
  ⟨y, NodeSet.union x z, w⟩

def rule2Right (x y z w : NodeSet S) : Kernel S :=
  ⟨y, x, NodeSet.union z w⟩

def rule3Left (x y z w : NodeSet S) : Kernel S :=
  ⟨y, NodeSet.union x z, w⟩

def rule3Right (x y _z w : NodeSet S) : Kernel S :=
  ⟨y, x, w⟩

/-- The four node families in a do-calculus rule are pairwise disjoint. -/
structure FourWayDisjoint (x y z w : NodeSet S) : Prop where
  xy : NodeSet.Disjoint x y
  xz : NodeSet.Disjoint x z
  xw : NodeSet.Disjoint x w
  yz : NodeSet.Disjoint y z
  yw : NodeSet.Disjoint y w
  zw : NodeSet.Disjoint z w

/-- The graph-separation judgement carried by a family of do-rule steps. -/
abbrev SeparationCondition (S : ObservedSignature) :=
  GraphMutilation S -> NodeSet S -> NodeSet S -> NodeSet S -> Prop

/-- The separation condition computed by the finite Boolean implementation. -/
abbrev ExecutableSeparation (G : ObservedGraph S) : SeparationCondition S :=
  fun mutilation left right conditioned =>
    G.dSeparated mutilation left right conditioned = true

/-- A selectable separation judgement for the shared do-calculus syntax. -/
class RuleSeparation (G : ObservedGraph S) where
  holds : SeparationCondition S

/-- The default rule syntax uses the executable Boolean separation check. -/
instance executableRuleSeparation (G : ObservedGraph S) : RuleSeparation G where
  holds := ExecutableSeparation G

/--
One application of one of Pearl's three rules, parameterized by the separation
judgement used in its side condition.  Omitting the final parameter selects the
executable Boolean judgement; active-path syntax supplies another specialization.
-/
inductive DoRuleApplication (G : ObservedGraph S)
    [separation : RuleSeparation G] :
    Kernel S -> Kernel S -> Type
  | rule1 (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (sideCondition : separation.holds (.bar x) y z (NodeSet.union x w)) :
      DoRuleApplication G (separation := separation)
        (rule1Left x y z w) (rule1Right x y z w)
  | rule2 (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (sideCondition : separation.holds (.barUnderline x z) y z (NodeSet.union x w)) :
      DoRuleApplication G (separation := separation)
        (rule2Left x y z w) (rule2Right x y z w)
  | rule3 (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (sideCondition :
        let base := GraphMutilation.bar x
        let removable := G.nonAncestorsOf base z w
        separation.holds
          { removeIncoming := NodeSet.union x removable,
            removeOutgoing := NodeSet.empty }
          y z (NodeSet.union x w)) :
      DoRuleApplication G (separation := separation)
        (rule3Left x y z w) (rule3Right x y z w)

/-- Transport all three do-rule constructors along a separation implication. -/
def DoRuleApplication.mapSeparation
    {S : ObservedSignature} {G : ObservedGraph S}
    {source target : RuleSeparation G} {left right : Kernel S}
    (translate : forall (mutilation : GraphMutilation S)
      (left right conditioned : NodeSet S),
      source.holds mutilation left right conditioned ->
        target.holds mutilation left right conditioned)
    (application : DoRuleApplication G (separation := source) left right) :
    DoRuleApplication G (separation := target) left right := by
  cases application with
  | rule1 x y z w disjoint sideCondition =>
      exact .rule1 (separation := target) x y z w disjoint
        (translate (.bar x) y z (NodeSet.union x w) sideCondition)
  | rule2 x y z w disjoint sideCondition =>
      exact .rule2 (separation := target) x y z w disjoint
        (translate (.barUnderline x z) y z (NodeSet.union x w) sideCondition)
  | rule3 x y z w disjoint sideCondition =>
      exact .rule3 (separation := target) x y z w disjoint
        (translate
          { removeIncoming := NodeSet.union x
              (G.nonAncestorsOf (.bar x) z w)
            removeOutgoing := NodeSet.empty }
          y z (NodeSet.union x w) sideCondition)

/-- Expressions generated from kernels by finite probability algebra. -/
inductive ProbabilityTerm (S : ObservedSignature) where
  | zero : ProbabilityTerm S
  | kernel : Kernel S -> ProbabilityTerm S
  | marginalize : NodeSet S -> ProbabilityTerm S -> ProbabilityTerm S
  | evaluateAt : S.Assignment -> ProbabilityTerm S -> ProbabilityTerm S
  | add : ProbabilityTerm S -> ProbabilityTerm S -> ProbabilityTerm S
  | multiply : ProbabilityTerm S -> ProbabilityTerm S -> ProbabilityTerm S
  | divide : ProbabilityTerm S -> ProbabilityTerm S -> ProbabilityTerm S

namespace ProbabilityTerm

def ActionFree : ProbabilityTerm S -> Prop
  | zero => True
  | kernel K => forall i, K.action i = false
  | marginalize _ term => term.ActionFree
  | evaluateAt _ term => term.ActionFree
  | add left right => left.ActionFree /\ right.ActionFree
  | multiply left right => left.ActionFree /\ right.ActionFree
  | divide numerator denominator => numerator.ActionFree /\ denominator.ActionFree

end ProbabilityTerm

/--
The common derivation skeleton for a chosen do-rule relation.  Probability
algebra is independent of whether rule leaves use executable or active-path
separation evidence.
-/
inductive DoCalculusDerivation (G : ObservedGraph S)
    [separation : RuleSeparation G] :
    ProbabilityTerm S -> ProbabilityTerm S -> Type
  | refl (term) : DoCalculusDerivation G (separation := separation) term term
  | symm {left right} :
      DoCalculusDerivation G (separation := separation) left right ->
        DoCalculusDerivation G (separation := separation) right left
  | trans {left middle right} :
      DoCalculusDerivation G (separation := separation) left middle ->
      DoCalculusDerivation G (separation := separation) middle right ->
      DoCalculusDerivation G (separation := separation) left right
  | doRule {left right} :
      DoRuleApplication G (separation := separation) left right ->
      DoCalculusDerivation G (separation := separation)
        (.kernel left) (.kernel right)
  | marginalization (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      DoCalculusDerivation G (separation := separation)
        (.kernel ⟨y, x, w⟩)
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩))
  | conditioning (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      DoCalculusDerivation G (separation := separation)
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩))
  | chain (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      DoCalculusDerivation G (separation := separation)
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩))
  | marginalizeCongr (nodes : NodeSet S) {left right} :
      DoCalculusDerivation G (separation := separation) left right ->
      DoCalculusDerivation G (separation := separation)
        (.marginalize nodes left) (.marginalize nodes right)
  | evaluateAtCongr (assignment : S.Assignment) {left right} :
      DoCalculusDerivation G (separation := separation) left right ->
      DoCalculusDerivation G (separation := separation)
        (.evaluateAt assignment left) (.evaluateAt assignment right)
  | addCongr {left left' right right'} :
      DoCalculusDerivation G (separation := separation) left left' ->
      DoCalculusDerivation G (separation := separation) right right' ->
      DoCalculusDerivation G (separation := separation)
        (.add left right) (.add left' right')
  | multiplyCongr {left left' right right'} :
      DoCalculusDerivation G (separation := separation) left left' ->
      DoCalculusDerivation G (separation := separation) right right' ->
      DoCalculusDerivation G (separation := separation)
        (.multiply left right) (.multiply left' right')
  | divideCongr {left left' right right'} :
      DoCalculusDerivation G (separation := separation) left left' ->
      DoCalculusDerivation G (separation := separation) right right' ->
      DoCalculusDerivation G (separation := separation)
        (.divide left right) (.divide left' right')

/-- Map only the do-rule leaves of a derivation. -/
def DoCalculusDerivation.mapRules
    {S : ObservedSignature} {G : ObservedGraph S}
    {source target : RuleSeparation G}
    {left right : ProbabilityTerm S}
    (translate : forall {left right : Kernel S},
      DoRuleApplication G (separation := source) left right ->
        DoRuleApplication G (separation := target) left right)
    : DoCalculusDerivation G (separation := source) left right ->
      DoCalculusDerivation G (separation := target) left right
  | @DoCalculusDerivation.refl _ _ source term =>
      @DoCalculusDerivation.refl S G target term
  | @DoCalculusDerivation.symm _ _ source first second derivation =>
      @DoCalculusDerivation.symm S G target first second
        (derivation.mapRules (source := source) (target := target) translate)
  | @DoCalculusDerivation.trans _ _ source first middle last
      firstDerivation secondDerivation =>
      @DoCalculusDerivation.trans S G target first middle last
        (firstDerivation.mapRules (source := source) (target := target) translate)
        (secondDerivation.mapRules (source := source) (target := target) translate)
  | @DoCalculusDerivation.doRule _ _ source first second application =>
      @DoCalculusDerivation.doRule S G target first second
        (translate application)
  | @DoCalculusDerivation.marginalization _ _ source x y z w disjoint =>
      @DoCalculusDerivation.marginalization S G target x y z w disjoint
  | @DoCalculusDerivation.conditioning _ _ source x y z w disjoint =>
      @DoCalculusDerivation.conditioning S G target x y z w disjoint
  | @DoCalculusDerivation.chain _ _ source x y z w disjoint =>
      @DoCalculusDerivation.chain S G target x y z w disjoint
  | @DoCalculusDerivation.marginalizeCongr _ _ source nodes first second
      derivation =>
      @DoCalculusDerivation.marginalizeCongr S G target nodes first second
        (derivation.mapRules (source := source) (target := target) translate)
  | @DoCalculusDerivation.evaluateAtCongr _ _ source assignment first second
      derivation =>
      @DoCalculusDerivation.evaluateAtCongr S G target assignment first second
        (derivation.mapRules (source := source) (target := target) translate)
  | @DoCalculusDerivation.addCongr _ _ source first first' second second'
      firstDerivation secondDerivation =>
      @DoCalculusDerivation.addCongr S G target first first' second second'
        (firstDerivation.mapRules (source := source) (target := target) translate)
        (secondDerivation.mapRules (source := source) (target := target) translate)
  | @DoCalculusDerivation.multiplyCongr _ _ source first first' second second'
      firstDerivation secondDerivation =>
      @DoCalculusDerivation.multiplyCongr S G target first first' second second'
        (firstDerivation.mapRules (source := source) (target := target) translate)
        (secondDerivation.mapRules (source := source) (target := target) translate)
  | @DoCalculusDerivation.divideCongr _ _ source first first' second second'
      firstDerivation secondDerivation =>
      @DoCalculusDerivation.divideCongr S G target first first' second second'
        (firstDerivation.mapRules (source := source) (target := target) translate)
        (secondDerivation.mapRules (source := source) (target := target) translate)

end Causality
end Thesis
