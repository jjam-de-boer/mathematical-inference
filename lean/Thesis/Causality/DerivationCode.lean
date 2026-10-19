import Thesis.Causality.ProbabilityTermCode

namespace Thesis.Causality

/-!
# Checked, serialized do-calculus proof trees

Only the code is untrusted input. Checking constructs an actual existing
`DoCalculusDerivation`; no soundness law or arbitrary proof field is supplied
by the input. All three graphical leaves use the existing executable
separation test, with its established path-correctness theorem. Rule 3 keeps
the incoming cut at `X ∪ Z(W)`, not an outgoing cut.

Syntactic equality uses the constructive finite-function equality checker.
Consequently a transitivity join or `eqCongr` cannot smuggle in a numerical
identity. Unsupported derivations can still pass this *syntax/graph* check:
the native recursive support checker is a separate, mandatory semantic gate.
There is no proof enumeration, formula selection or universal completeness
claim in this module.
-/

namespace ProbabilityCode

structure QuadCode where
  x : Nat
  y : Nat
  z : Nat
  w : Nat
  deriving Repr, DecidableEq

structure Quad (S : ObservedSignature) where
  x : NodeSet S
  y : NodeSet S
  z : NodeSet S
  w : NodeSet S

def QuadCode.decode (signature : ObservedSignature) (code : QuadCode) : Option (Quad signature) := do
  pure ⟨← mask signature code.x, ← mask signature code.y,
    ← mask signature code.z, ← mask signature code.w⟩

def Quad.disjoint (quad : Quad S) : Bool :=
  NodeSet.disjointBool quad.x quad.y && NodeSet.disjointBool quad.x quad.z &&
    NodeSet.disjointBool quad.x quad.w && NodeSet.disjointBool quad.y quad.z &&
    NodeSet.disjointBool quad.y quad.w && NodeSet.disjointBool quad.z quad.w

theorem Quad.disjointOfCheck (quad : Quad S) (accepted : quad.disjoint = true) :
    FourWayDisjoint quad.x quad.y quad.z quad.w := by
  simp only [disjoint, Bool.and_eq_true_iff, NodeSet.disjointBool_eq_true_iff] at accepted
  exact ⟨accepted.1.1.1.1.1, accepted.1.1.1.1.2, accepted.1.1.1.2,
    accepted.1.1.2, accepted.1.2, accepted.2⟩

inductive PrimitiveCode where
  | rule1 | rule2 | rule3 | marginalization | conditioning | chain | weightedChain
  deriving Repr, DecidableEq

inductive CongruenceCode where
  | add | multiply | weightedMultiply | divide
  deriving Repr, DecidableEq

inductive DerivationCode where
  | refl (term : TermCode)
  | symm (inner : DerivationCode)
  | trans (first second : DerivationCode)
  | primitive (kind : PrimitiveCode) (quad : QuadCode)
  | multiplyComm (left right : TermCode)
  | multiplyAssoc (first second third : TermCode)
  | marginalizeCongr (nodes : Nat) (inner : DerivationCode)
  | evaluateAtCongr (reference : Nat) (inner : DerivationCode)
  | congr (kind : CongruenceCode) (first second : DerivationCode)
  | eqCongr (left right : TermCode) (inner : DerivationCode)
  deriving Repr, DecidableEq

/-- An accepted tree contains the actual public proof, not just a claim that
some suitable semantic proof exists. Endpoint terms are retained explicitly. -/
structure CheckedDerivation (graph : ObservedGraph S) where
  left : ProbabilityTerm S
  right : ProbabilityTerm S
  derivation : DoCalculusDerivation graph left right

def checkPrimitive (graph : ObservedGraph S) (kind : PrimitiveCode) (code : QuadCode) :
    Option (CheckedDerivation graph) := do
  let quad ← code.decode S
  if accepted : quad.disjoint = true then
    let disjoint := quad.disjointOfCheck accepted
    match kind with
    | .rule1 =>
        if separated : graph.dSeparated (.bar quad.x) quad.y quad.z (NodeSet.union quad.x quad.w) = true then
          pure ⟨_, _, .doRule (.rule1 quad.x quad.y quad.z quad.w disjoint separated)⟩
        else none
    | .rule2 =>
        if separated : graph.dSeparated (.barUnderline quad.x quad.z) quad.y quad.z (NodeSet.union quad.x quad.w) = true then
          pure ⟨_, _, .doRule (.rule2 quad.x quad.y quad.z quad.w disjoint separated)⟩
        else none
    | .rule3 =>
        if separated : graph.dSeparated
            { removeIncoming := NodeSet.union quad.x (graph.nonAncestorsOf (.bar quad.x) quad.z quad.w),
              removeOutgoing := NodeSet.empty }
            quad.y quad.z (NodeSet.union quad.x quad.w) = true then
          pure ⟨_, _, .doRule (.rule3 quad.x quad.y quad.z quad.w disjoint separated)⟩
        else none
    | .marginalization => pure ⟨_, _, .marginalization quad.x quad.y quad.z quad.w disjoint⟩
    | .conditioning => pure ⟨_, _, .conditioning quad.x quad.y quad.z quad.w disjoint⟩
    | .chain => pure ⟨_, _, .chain quad.x quad.y quad.z quad.w disjoint⟩
    | .weightedChain => pure ⟨_, _, .weightedChain quad.x quad.y quad.z quad.w disjoint⟩
  else none

def DerivationCode.check (graph : ObservedGraph S) : DerivationCode → Option (CheckedDerivation graph)
  | .refl term => do
      let term ← term.decode S
      pure ⟨term, term, .refl term⟩
  | .symm inner => do
      let inner ← inner.check graph
      pure ⟨inner.right, inner.left, .symm inner.derivation⟩
  | .trans first second => do
      let first ← first.check graph
      let second ← second.check graph
      if same : first.right = second.left then
        pure ⟨first.left, second.right, .trans first.derivation (.eqCongr same rfl second.derivation)⟩
      else none
  | .primitive kind quad => checkPrimitive graph kind quad
  | .multiplyComm left right => do
      let left ← left.decode S
      let right ← right.decode S
      pure ⟨_, _, .multiplyComm left right⟩
  | .multiplyAssoc first second third => do
      let first ← first.decode S
      let second ← second.decode S
      let third ← third.decode S
      pure ⟨_, _, .multiplyAssoc first second third⟩
  | .marginalizeCongr nodes inner => do
      let nodes ← mask S nodes
      let inner ← inner.check graph
      pure ⟨_, _, .marginalizeCongr nodes inner.derivation⟩
  | .evaluateAtCongr reference inner => do
      let reference ← assignment S reference
      let inner ← inner.check graph
      pure ⟨_, _, .evaluateAtCongr reference inner.derivation⟩
  | .congr kind first second => do
      let first ← first.check graph
      let second ← second.check graph
      match kind with
      | .add => pure ⟨_, _, .addCongr first.derivation second.derivation⟩
      | .multiply => pure ⟨_, _, .multiplyCongr first.derivation second.derivation⟩
      | .weightedMultiply => pure ⟨_, _, .weightedMultiplyCongr first.derivation second.derivation⟩
      | .divide => pure ⟨_, _, .divideCongr first.derivation second.derivation⟩
  | .eqCongr left right inner => do
      let left ← left.decode S
      let right ← right.decode S
      let inner ← inner.check graph
      if sameLeft : left = inner.left then
        if sameRight : right = inner.right then
          pure ⟨left, right, .eqCongr sameLeft sameRight inner.derivation⟩
        else none
      else none

end ProbabilityCode
end Thesis.Causality
