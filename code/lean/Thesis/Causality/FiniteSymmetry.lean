import Thesis.Causality.Graph

namespace Thesis.Causality.FiniteSymmetry

/-!
# Finite groups, genuinely invertible actions, and graph relabellings

There are three different statements one might call a symmetry: equal prior
mass for renamed hypotheses, a symmetry of one particular model, and a
symmetry which fixes an entire experiment. This file only supplies the common
algebraic data. The probabilistic and causal consequences are proved in the
downstream symmetry modules, with the relevant extra hypotheses visible.

An action is not an arbitrary endomap. Its group laws construct an explicit
inverse, so a constant map on a nontrivial carrier cannot enter through this
interface. Finiteness concerns the supplied group, not an assertion that an
automorphism group has been discovered from data.
-/

/-- A finite group presented by actual elements and a complete enumeration.
The enumeration may contain repeated names: actions and laws depend on group
elements, never on the number of times an element is listed. -/
structure Group where
  Carrier : Type
  elements : List Carrier
  complete : ∀ g, g ∈ elements
  decidableEq : DecidableEq Carrier
  one : Carrier
  mul : Carrier → Carrier → Carrier
  inv : Carrier → Carrier
  one_mul : ∀ g, mul one g = g
  mul_one : ∀ g, mul g one = g
  mul_assoc : ∀ g h k, mul (mul g h) k = mul g (mul h k)
  inv_mul : ∀ g, mul (inv g) g = one
  mul_inv : ∀ g, mul g (inv g) = one

instance (G : Group) : DecidableEq G.Carrier := G.decidableEq

/-- A left action. The multiplication convention is explicit: `g*h` acts
by first applying `h`, then applying `g`. It applies equally to hypotheses,
node names, value labels, complete assignments, and interventions. -/
structure Action (G : Group) (α : Type u) where
  act : G.Carrier → α → α
  one_act : ∀ x, act G.one x = x
  mul_act : ∀ g h x, act (G.mul g h) x = act g (act h x)

namespace Action
variable {G : Group} {α : Type u}

/-- The identity action is useful when a symmetry changes value labels but
leaves node names or the model hypothesis fixed. It does not assert that
the associated probability distribution is invariant. -/
def trivial (G : Group) (α : Type u) : Action G α where
  act _ x := x
  one_act _ := rfl
  mul_act _ _ _ := rfl

/-- The inverse group element undoes the action, including on null outcomes
or hypotheses with zero prior mass. This is an identity of the carrier, not
merely an almost-sure identity under one chosen distribution. -/
theorem inv_act (A : Action G α) (g : G.Carrier) (x : α) :
    A.act (G.inv g) (A.act g x) = x := by
  rw [← A.mul_act, G.inv_mul, A.one_act]

/-- The inverse also works in the other order; no finite-choice principle
is needed to obtain either inverse law. -/
theorem act_inv (A : Action G α) (g : G.Carrier) (x : α) :
    A.act g (A.act (G.inv g) x) = x := by
  rw [← A.mul_act, G.mul_inv, A.one_act]

theorem injective (A : Action G α) (g : G.Carrier) {x y : α}
    (same : A.act g x = A.act g y) : x = y := by
  have back := congrArg (A.act (G.inv g)) same
  simpa only [A.inv_act] using back

/-- A putative constant action on two distinct points contradicts the
derived inverse law. Clients can use this theorem to reject invalid
"permutation" candidates before constructing causal symmetry data. -/
theorem not_constant (A : Action G α) (g : G.Carrier) (x y : α)
    (different : x ≠ y) : A.act g x ≠ A.act g y :=
  fun same => different (A.injective g same)

/-- Transport a Boolean adjacency table by the inverse node action. This
changes graph labels, rather than requiring every individual graph to be
fixed by every symmetry of the prior. -/
def transportEdge (A : Action G (Fin n)) (g : G.Carrier)
    (edge : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i j => edge (A.act (G.inv g) i) (A.act (G.inv g) j)

/-- The old edge is present between the corresponding renamed nodes.
Both directed and bidirected tables can use this identity. Acyclicity of a
renumbered directed graph still requires a compatible topological indexing;
we do not silently reuse the old numerical order. -/
theorem transportEdge_at (A : Action G (Fin n)) (g : G.Carrier)
    (edge : Fin n → Fin n → Bool) (i j : Fin n) :
    A.transportEdge g edge (A.act g i) (A.act g j) = edge i j := by
  simp only [transportEdge, A.inv_act]

/-- A complexity description is symmetric only when the score is constant
along the declared hypothesis action. The action does not itself choose
which description language or complexity score should be used. -/
def ScoreInvariant (A : Action G α) (score : α → Nat) : Prop :=
  ∀ g x, score (A.act g x) = score x

end Action

/-- A signature action keeps node names and dependent value labels coherent.
The value action is on labelled values `(node, value)`: its ordinary group
laws therefore express composition even when different nodes have different
value types. The coordinate equation prevents a value renaming from silently
moving a value to a node other than the one named by the node action. -/
structure SignatureAction (G : Group) (S : ObservedSignature.{0}) where
  nodes : Action G (Fin S.count)
  values : Action G (Sigma fun node : Fin S.count => S.Value node)
  coordinate : ∀ g node value,
    (values.act g ⟨node, value⟩).1 = nodes.act g node

/-- Compatibility with a complete-assignment action is checked at every
coordinate, including values that have probability zero under a particular
law. This is a relation between primitive labels, not an assumed equality
of observed distributions. -/
def SignatureAction.AssignmentCompatible (signature : SignatureAction G S)
    (outcomes : Action G S.Assignment) : Prop :=
  ∀ g state node,
    signature.values.act g ⟨node, state node⟩ =
      ⟨signature.nodes.act g node, outcomes.act g state (signature.nodes.act g node)⟩

/-- The two-element group is the smallest useful value symmetry: composition
is XOR, identity is `false`, and each element is its own inverse. -/
def bitGroup : Group where
  Carrier := Bool
  elements := [false, true]
  complete := by intro g; cases g <;> simp
  decidableEq := inferInstance
  one := false
  mul := Bool.xor
  inv := id
  one_mul := by intro g; cases g <;> rfl
  mul_one := by intro g; cases g <;> rfl
  mul_assoc := by intro g h k; cases g <;> cases h <;> cases k <;> rfl
  inv_mul := by intro g; cases g <;> rfl
  mul_inv := by intro g; cases g <;> rfl

/-- Acting on one bit by simultaneous complementation when the group
element is `true`. Larger coordinate actions can reuse the same group. -/
def bitAction : Action bitGroup Bool where
  act := Bool.xor
  one_act := by intro x; cases x <;> rfl
  mul_act := by intro g h x; cases g <;> cases h <;> cases x <;> rfl

/-- Any explicitly proved involution gives an action of the two-element
group. This constructor is useful for coordinate swaps as well as value
complementation; it requires the inverse law rather than guessing it. -/
def involutionAction (swap : α → α) (involutive : ∀ x, swap (swap x) = x) :
    Action bitGroup α where
  act g x := if g = true then swap x else x
  one_act := by intro x; rfl
  mul_act := by
    intro g h x
    cases g <;> cases h <;> simp [bitGroup, involutive]

end Thesis.Causality.FiniteSymmetry
