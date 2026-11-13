import Thesis.CausalTransport.CatalogueInference
import Thesis.Probability.Distros.ObservationChains
import Thesis.Probability.RationalValues

namespace Thesis
namespace Causality
namespace CataloguePartition

open Probability Probability.Distros Probability.Combinatorics CatalogueInference

/-!
# Depth-capped partition trees on a Boolean modifier alphabet

Layer 3 runs only after Layer 2. It shares strength across `W`-cells; it does
not search graphs and does not identify a query that Layer 2 left
unidentified. The v1 alphabet is two Boolean coordinates (`Fin 4` cells).
A tree is a nested split of that alphabet, with an explicit depth cap.

Each leaf pools the remaining `(T, Y)` table of its cells and evaluates the
**already certified** Layer 2 formula, or carries bounds. Posterior mixing
over trees uses the same `reweightNat` update as Layer 1. Nested refinement
is an `ObservationChain` on the four cells.

Regime B in a leaf is Dirichlet–multinomial on the pooled table. The default
prior prefers shallower trees by weight `cap + 1 - depth`.
-/

/-- Two Boolean modifier coordinates, packed as `bit0 + 2 * bit1`. -/
abbrev Cell := Fin 4

def bit (coord : Fin 2) (cell : Cell) : Bool :=
  if coord.val = 0 then decide (cell.val % 2 = 1)
  else decide (cell.val / 2 = 1)

inductive SplitTree where
  | leaf
  | node (coord : Fin 2) (child0 child1 : SplitTree)
  deriving DecidableEq, Repr

def SplitTree.depth : SplitTree → Nat
  | .leaf => 0
  | .node _ left right => 1 + Nat.max left.depth right.depth

def SplitTree.leaves : SplitTree → Nat
  | .leaf => 1
  | .node _ left right => left.leaves + right.leaves

/-- Depth-capped enumeration. The cap is an input, not an inferred bound. -/
def treesUpTo : Nat → List SplitTree
  | 0 => [.leaf]
  | n + 1 =>
      .leaf ::
        (treesUpTo n).flatMap fun left =>
          (treesUpTo n).flatMap fun right =>
            [.node ⟨0, by decide⟩ left right,
              .node ⟨1, by decide⟩ left right]

def SplitTree.leafIndex : SplitTree → Cell → Nat
  | .leaf, _ => 0
  | .node coord left right, cell =>
      if bit coord cell then left.leaves + right.leafIndex cell
      else left.leafIndex cell

/-- Shallower trees receive larger prior weight. -/
def treeWeight (cap : Nat) (tree : SplitTree) : Nat :=
  if tree.depth ≤ cap then cap + 1 - tree.depth else 0

theorem treesUpTo_length_pos (n : Nat) : 0 < (treesUpTo n).length := by
  cases n with
  | zero => decide
  | succ _ => simp [treesUpTo]

theorem treesUpTo_get_zero (n : Nat) :
    (treesUpTo n).get ⟨0, treesUpTo_length_pos n⟩ = .leaf := by
  cases n <;> rfl

theorem treeWeight_leaf (cap : Nat) : 0 < treeWeight cap .leaf := by
  simp [treeWeight, SplitTree.depth]

theorem treePrior_positive (cap : Nat) :
    0 < natSum (treesUpTo cap).length
      (finWeight (fun i => treeWeight cap ((treesUpTo cap).get i))) := by
  have hlen := treesUpTo_length_pos cap
  have hleaf := treesUpTo_get_zero cap
  have wpos : 0 < treeWeight cap ((treesUpTo cap).get ⟨0, hlen⟩) := by
    rw [hleaf]
    exact treeWeight_leaf cap
  exact natSum_pos_of_term (i := 0) hlen (by
    simp only [finWeight]
    rw [dif_pos hlen]
    exact wpos)

def treePrior (cap : Nat) : Distro (Fin (treesUpTo cap).length) :=
  categoricalDistro _ (fun i => treeWeight cap ((treesUpTo cap).get i))
    (treePrior_positive cap)

/-- Pooled binary treatment/outcome counts in one leaf.
Index `0` is `(T=false, Y=false)`, then `(T=false, Y=true)`,
`(T=true, Y=false)`, `(T=true, Y=true)`. -/
abbrev TyTable := Fin 4 → Nat

def emptyTable : TyTable := fun _ => 0

def addCount (table : TyTable) (t y : Bool) (n : Nat) : TyTable :=
  let idx : Fin 4 :=
    ⟨(if t then 2 else 0) + (if y then 1 else 0), by
      cases t <;> cases y <;> decide⟩
  fun i => table i + if i = idx then n else 0

/-- Certified leaf answer. Unidentified Layer 2 queries stay bounded or
unsupported; this module never invents a point. -/
inductive LeafAnswer where
  | identified (tau : SignedRatio)
  | bounded (lower upper : QProb)
  | unsupported

/-- `P(Y=1 | T=t)` from a pooled table, undefined at a zero treatment cell. -/
def conditionalY (table : TyTable) (t : Bool) : Option QProb :=
  let n0 := table ⟨(if t then 2 else 0), by cases t <;> decide⟩
  let n1 := table ⟨(if t then 2 else 0) + 1, by cases t <;> decide⟩
  if h : 0 < n0 + n1 then
    some ⟨n1, n0 + n1, h⟩
  else
    none

/-- Identified `τ = P(Y=1 | do(T=1)) - P(Y=1 | do(T=0))` when Layer 2 gave
an action-free conditional that reduces to these two fibres in the leaf. -/
def tauOfTable (table : TyTable) : Option SignedRatio :=
  match conditionalY table true, conditionalY table false with
  | some one, some zero => some (SignedRatio.sub one.toSignedRatio zero.toSignedRatio)
  | _, _ => none

def leafAnswer (identified : Bool) (table : TyTable)
    (bounds : Option (QProb × QProb)) : LeafAnswer :=
  if identified then
    match tauOfTable table with
    | some tau => .identified tau
    | none => .unsupported
  else
    match bounds with
    | some ⟨lo, hi⟩ => .bounded lo hi
    | none => .unsupported

/-- Dirichlet–multinomial likelihood of a pooled four-cell `(T,Y)` table. -/
def tableLikelihood (table : TyTable) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num) : QProb :=
  let counts := [table ⟨0, by decide⟩, table ⟨1, by decide⟩,
    table ⟨2, by decide⟩, table ⟨3, by decide⟩]
  dirichletMultinomialMass counts.sum alphas positive counts

def treeLikelihood (tree : SplitTree) (tables : Nat → TyTable)
    (alphas : List QProb) (positive : 0 < (QProb.listSum alphas).num) : QProb :=
  let rec go : SplitTree → Nat → QProb
    | .leaf, idx => tableLikelihood (tables idx) alphas positive
    | .node _ left right, idx =>
        QProb.mul (go left idx) (go right (idx + left.leaves))
  go tree 0

def treePosterior? (cap : Nat)
    (tables : SplitTree → Nat → TyTable)
    (alphas : List QProb) (alphaPos : 0 < (QProb.listSum alphas).num) :
    Option (Distro (Fin (treesUpTo cap).length)) :=
  let items := treesUpTo cap
  let like : Fin items.length → QProb := fun i =>
    treeLikelihood (items.get i) (tables (items.get i)) alphas alphaPos
  posterior? (treePrior cap) (qprobWeights items.length like)

/-- Mix identified leaf `τ` values at a cell with the tree posterior.
Trees that do not identify contribute nothing to a point mixture. -/
def mixTau (cap : Nat) (posterior : Distro (Fin (treesUpTo cap).length))
    (answer : SplitTree → Cell → LeafAnswer) (cell : Cell) : Option SignedRatio :=
  let items := treesUpTo cap
  let rec acc : List (Fin items.length) → SignedRatio → Bool → Option SignedRatio
    | [], sum, true => some sum
    | [], _, false => none
    | i :: rest, sum, seen =>
        match answer (items.get i) cell with
        | .identified tau =>
            let weight := posterior.pmf i
            acc rest (SignedRatio.add sum (SignedRatio.mul weight.toSignedRatio tau)) true
        | _ =>
            if 0 < (posterior.pmf i).num then none
            else acc rest sum seen
  acc (List.finRange items.length) SignedRatio.zero false

/-- One-step `ObservationChain` on four modifier cells: stage 0 is the
undivided alphabet, stage 1 is the first Boolean coordinate. -/
def firstBitChain (μ : Distro Cell) : ObservationChain μ 1 where
  labels := fun stage => if stage = 0 then 1 else 2
  observe := fun stage cell =>
    if h : stage = 0 then
      ⟨0, by simp [h]⟩
    else
      if bit ⟨0, by decide⟩ cell then ⟨1, by simp [h]⟩
      else ⟨0, by simp [h]⟩
  merge := fun stage _ =>
    if h : stage = 0 then ⟨0, by simp [h]⟩
    else ⟨0, by simp [h]⟩
  agrees := fun stage hlt atom _ _ => by
    have : stage = 0 := Nat.lt_one_iff.mp hlt
    subst this
    rfl

end CataloguePartition
end Causality
end Thesis
