import Thesis.Causality.Graph
import Thesis.Probability.FiniteProductSupport
import Thesis.Probability.FiniteUniformProduct

namespace Thesis
namespace Causality
namespace NodeSet

open Probability

/-!
# Complete, repetition-free enumeration of permitted node subsets

An observed node set is an explicitly indexed Boolean assignment.  To list
its subsets, allow both Boolean values at permitted coordinates and only
`false` everywhere else.  This is a restricted Cartesian product, not a
complete Boolean cube subsequently masked down to the permitted nodes.
Masking would repeat each subset and needlessly enlarge adjustment searches.

The membership and uniqueness proofs reuse the symbolic finite-product
theorems.  They do not reduce an exponential concrete enumeration, choose a
set from an existential proposition, or import the hedge constructions that
also happen to enumerate masks.  Graph clients can therefore use this small
module independently of the completeness countermodel machinery.
-/

variable {S : ObservedSignature}

/-- Each permitted coordinate has two choices; every other coordinate has
one.  The order puts the empty subset first and is deterministic. -/
def subsetChoices (allowed : NodeSet S) (node : Fin S.count) : List Bool :=
  if allowed node then [false, true] else [false]

/-- List exactly the subsets of `allowed`, without repeating fixed bits. -/
def subsets (allowed : NodeSet S) : List (NodeSet S) :=
  FiniteProduct.enumeration S.count (fun _ => Bool) (subsetChoices allowed)

/-- Enumeration is exhaustive precisely on the supplied allowed region.
The reverse direction takes the proposed subset as data; it does not obtain
a Boolean function by eliminating a propositional existence proof. -/
theorem subsets_member_iff (allowed selected : NodeSet S) :
    selected ∈ subsets allowed ↔ Subset selected allowed := by
  constructor
  · intro member node atNode
    have localMember := FiniteProduct.enumeration_coordinate_mem S.count
      (fun _ => Bool) (subsetChoices allowed) selected member node
    cases permitted : allowed node with
    | true => rfl
    | false =>
        simp only [subsetChoices, permitted, Bool.false_eq_true, if_false,
          List.mem_singleton] at localMember
        exact False.elim (Bool.false_ne_true (localMember.symm.trans atNode))
  · intro contained
    apply FiniteProduct.enumeration_mem_of_coordinate_mem
    intro node
    cases permitted : allowed node with
    | true =>
        cases selected node <;>
          simp only [subsetChoices, permitted, if_true, List.mem_cons,
            List.not_mem_nil] <;> simp
    | false =>
        have absent : selected node = false := by
          cases atNode : selected node with
          | false => rfl
          | true =>
              exact False.elim
                (Bool.false_ne_true (permitted.symm.trans (contained node atNode)))
        simp only [subsetChoices, permitted, Bool.false_eq_true, if_false,
          List.mem_singleton, absent]

/-- Every permitted subset appears once.  Equality decisions are only the
explicit finite Boolean coordinate decisions used by the product theorem. -/
theorem subsets_nodup (allowed : NodeSet S) : (subsets allowed).Nodup := by
  apply FiniteProduct.enumeration_nodup S.count (fun _ => Bool)
    (subsetChoices allowed) (fun _ => inferInstance)
  intro node
  cases permitted : allowed node <;> simp only [subsetChoices, permitted] <;> decide

/-- Even an empty permitted region contains its explicitly empty subset. -/
theorem empty_mem_subsets (allowed : NodeSet S) : empty ∈ subsets allowed :=
  (subsets_member_iff allowed empty).mpr
    (fun _ selected => False.elim (Bool.false_ne_true selected))

end NodeSet
end Causality
end Thesis
