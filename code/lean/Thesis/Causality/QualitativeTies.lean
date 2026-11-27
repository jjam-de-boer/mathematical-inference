import Thesis.Causality.CausalUrnFreshness

namespace Thesis.Causality.QualitativeTies
open Probability

/-!
# Partial qualitative judgments on directed matchings

The supplied graph is a disjoint union of directed edges and isolated
vertices, with its vertices numbered in topological order. Every vertex is
recorded and has two values. An instance lists only ties between literal
masses within a single experiment. In particular it does not supply a joint
law, a recipe, or a comparison between different experiments. One common
operational urn game must realize all the judgments, including those that
refer to impossible or certain literals after a setting.
-/

/-- A directed matching in topological numbering. A child has at most one
parent by the type of `parent`. Requiring that parent to be a root and to
have at most one child gives exactly disjoint arrows and isolated bits. -/
structure Matching (n : Nat) where
  parent : Fin n → Option (Fin n)
  parentEarlier : ∀ {child source}, parent child = some source → source.val < child.val
  parentRoot : ∀ {child source}, parent child = some source → parent source = none
  uniqueChild : ∀ {left right source},
    parent left = some source → parent right = some source → left = right

namespace Matching

variable {n : Nat}

/-- The ordinary signature of the supplied matching, with no added causes. -/
def signature (graph : Matching n) : ObservedSignature where
  count := n
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed source child := decide (graph.parent child = some source)
  directed_earlier := by
    intro source child edge
    exact graph.parentEarlier (of_decide_eq_true edge)

/-- Every vertex of the full graph is an observed vertex with the same index.
The ordinary hidden-DAG game interface therefore requires no hidden urns. -/
def fullGraph (graph : Matching n) : FiniteHiddenDAG graph.signature where
  count := n
  observedNode := id
  observedNode_injective := fun _ _ h => h
  hidden _ := false
  observed_not_hidden _ := rfl
  node_classified node := Or.inr ⟨node, rfl⟩
  edge := graph.signature.directed
  rank := Fin.val
  edge_rank_lt := fun edge => graph.parentEarlier (of_decide_eq_true edge)

private theorem onlyDirect {S : ObservedSignature} (full : FiniteHiddenDAG S)
    (noHidden : ∀ node, full.hidden node ≠ true) {source target : Fin full.count}
    (path : full.HiddenInternalPath source target) : full.edge source target = true := by
  cases path with
  | direct edge => exact edge
  | tail _ hidden _ => exact False.elim (noHidden _ hidden)

/-- A hidden-internal path in this full graph must be a single edge, since
it has no hidden vertices. There are likewise no hidden common causes. -/
def projection (graph : Matching n) : FiniteLatentProjection graph.signature where
  hiddenDAG := graph.fullGraph
  directed_matches := by
    intro source child
    change graph.fullGraph.edge source child = true ↔ graph.fullGraph.HiddenInternalPath source child
    constructor
    · intro edge
      exact .direct edge
    · exact onlyDirect graph.fullGraph (fun _ impossible => Bool.noConfusion impossible)
  bidirected _ _ := false
  bidirected_matches := by
    intro source child
    constructor
    · intro h; cases h
    · intro h
      obtain ⟨_, hidden, impossible, _⟩ := h
      cases impossible

end Matching

/-- The regime is explicit data shared by both literals of a judgment. -/
inductive Experiment (n : Nat) where
  | observe
  | set (node : Fin n) (value : Bool)
  deriving DecidableEq

/-- The event that one specified bit has one specified value. -/
structure Literal (n : Nat) where
  node : Fin n
  value : Bool
  deriving DecidableEq

/-- A tie is equality of plausibilities within the indicated experiment. The
input contains neither numeric probabilities nor a list of complete laws. -/
structure Tie (n : Nat) where
  experiment : Experiment n
  left : Literal n
  right : Literal n
  deriving DecidableEq

/-- A finite comparison problem on a supplied, fully recorded graph. -/
structure Instance where
  count : Nat
  graph : Matching count
  ties : List (Tie count)

variable {n : Nat} {graph : Matching n}

/-- Translate a single-bit setting into the library's ordinary intervention. -/
def Experiment.intervention (experiment : Experiment n) (graph : Matching n) :
    HardIntervention graph.signature :=
  match experiment with
  | .observe => HardIntervention.empty graph.signature
  | .set node value => (HardIntervention.empty graph.signature).set node value

/-- A literal is read from the actual recorded assignment. -/
def Literal.event (literal : Literal n) (graph : Matching n) :
    Event graph.signature.Assignment :=
  fun record => decide (record literal.node = literal.value)

/-- Two events are tied exactly when their finite urn masses agree as
fractions. A tie to a zero-mass event is meaningful. -/
def Tie.holds (tie : Tie n) (game : CausalUrnGame graph.signature graph.projection) : Prop :=
  let urn := game.recordUrn (tie.experiment.intervention graph)
  QProb.Equiv (urn.probVal (tie.left.event graph)) (urn.probVal (tie.right.event graph))

/-- A single set of recipes must realize the whole list of ties using the
library's operational game and its usual hard settings. -/
def Instance.Realizable (problem : Instance) : Prop :=
  ∃ game : CausalUrnGame problem.graph.signature problem.graph.projection,
    ∀ tie ∈ problem.ties, tie.holds game

end Thesis.Causality.QualitativeTies
