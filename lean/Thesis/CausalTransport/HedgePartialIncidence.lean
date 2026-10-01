import Thesis.CausalTransport.HedgePositive

namespace Thesis
namespace Causality

open Probability

/-!
# Partial incidence equations and their exact finite fibres

Pair-root incidence on a complete bidirected component has even parity.
That constraint does not remain a constraint on a proper subset of its
coordinates: an untested component vertex can absorb the missing parity.
Intervened vertices do not impose structural equations, and marginal events
likewise omit equations at coordinates they do not inspect.  The complete
incidence solver must therefore not be applied to such events as if their
targets still had to be even.

This module supplies explicit sections and equally sized fibres for those
partial equations.  The balancing vertex is supplied as finite data and
proved to lie outside the tested set.  Its correction uses the existing
Boolean parity calculation; exhaustive pair-bit search then produces an
actual vector without extracting data from a propositional existence proof.
XOR translation between the computed representatives is an involution on
the whole enumeration and an exact bijection between its filtered fibres.

The nested incidence map has the corresponding statement when a vertex of
the inner component is untested.  Outer equations remain unrestricted.
These are incidence and counting theorems, not countermodels by themselves:
SCM evaluation, weighted private backgrounds, and query-local events must
still be connected to the appropriate partial equations.  In particular,
equal fibres of each map do not by themselves assert equality between two
different maps' probabilities.
-/

/-! ## Ordinary component incidence on a tested subset -/

/-- Test only the indicated incidence equations.  `nodes` determines which
pair roots contribute; `tested` determines which output rows are compared.
They are deliberately different arguments. -/
def hedgePartialPairBitsRealizes (G : ObservedGraph S)
    (nodes tested : NodeSet S) (target : Fin S.count -> Bool)
    (pairBits : Fin (pairRootCount G) -> Bool) : Bool :=
  (NodeSet.members tested).all fun node =>
    hedgeXorPairBitsWithinFrom G nodes node pairBits == target node

theorem hedgePartialPairBitsRealizes_of (G : ObservedGraph S)
    (nodes tested : NodeSet S) (target : Fin S.count -> Bool)
    (pairBits : Fin (pairRootCount G) -> Bool)
    (agrees : forall node, tested node = true ->
      hedgeXorPairBitsWithinFrom G nodes node pairBits = target node) :
    hedgePartialPairBitsRealizes G nodes tested target pairBits = true := by
  apply List.all_eq_true.mpr
  intro node listed
  exact beq_iff_eq.mpr (agrees node ((NodeSet.mem_members_iff tested node).mp listed))

theorem hedgePartialPairBitsRealizes_spec (G : ObservedGraph S)
    (nodes tested : NodeSet S) (target : Fin S.count -> Bool)
    (pairBits : Fin (pairRootCount G) -> Bool)
    (realizes : hedgePartialPairBitsRealizes G nodes tested target pairBits = true) :
    forall node, tested node = true ->
      hedgeXorPairBitsWithinFrom G nodes node pairBits = target node := by
  intro node selected
  exact beq_iff_eq.mp ((List.all_eq_true.mp realizes) node
    ((NodeSet.mem_members_iff tested node).mpr selected))

/-- Correct an arbitrary target at an untested component vertex and run
the existing constructive complete solver.  No parity hypothesis on the
tested pattern is needed. -/
def BidirectedComponent.partialTargetPairBits
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (balance : Fin S.count) (inside : nodes balance = true)
    (target : Fin S.count -> Bool) : Fin (pairRootCount G) -> Bool :=
  component.evenTargetPairBits G nodes (hedgeDefectAdjustedTarget nodes balance target)
    (hedgeDefectAdjustedTarget_even nodes balance inside target)

/-- The parity correction changes only `balance`.  Every tested equation
is therefore realized literally, not merely up to an unspecified parity. -/
theorem BidirectedComponent.partialTargetPairBits_spec
    (G : ObservedGraph S) (nodes tested : NodeSet S)
    (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes)
    (balance : Fin S.count) (inside : nodes balance = true) (untested : tested balance = false)
    (target : Fin S.count -> Bool) :
    forall node, tested node = true ->
      hedgeXorPairBitsWithinFrom G nodes node
        (component.partialTargetPairBits G nodes balance inside target) = target node := by
  intro node selected
  have different : node ≠ balance := by
    intro equal
    subst node
    rw [untested] at selected
    cases selected
  have realizes := component.evenTargetPairBits_spec G nodes
    (hedgeDefectAdjustedTarget nodes balance target)
    (hedgeDefectAdjustedTarget_even nodes balance inside target) node (subset node selected)
  simpa only [BidirectedComponent.partialTargetPairBits, hedgeDefectAdjustedTarget,
    if_neg different, Bool.xor_false] using realizes

/-- Translation of two arbitrary partial patterns, with no evenness
premise.  The same explicit vector will be used in both directions. -/
def BidirectedComponent.partialTargetTranslation
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (balance : Fin S.count) (inside : nodes balance = true)
    (left right : Fin S.count -> Bool) : Fin (pairRootCount G) -> Bool :=
  hedgePairBitsXor G
    (component.partialTargetPairBits G nodes balance inside left)
    (component.partialTargetPairBits G nodes balance inside right)

theorem BidirectedComponent.partialTargetTranslation_spec
    (G : ObservedGraph S) (nodes tested : NodeSet S)
    (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes)
    (balance : Fin S.count) (inside : nodes balance = true) (untested : tested balance = false)
    (left right : Fin S.count -> Bool) :
    forall node, tested node = true ->
      hedgeXorPairBitsWithinFrom G nodes node
        (component.partialTargetTranslation G nodes balance inside left right) =
      Bool.xor (left node) (right node) := by
  intro node selected
  rw [BidirectedComponent.partialTargetTranslation, hedgeXorPairBitsWithinFrom_xor,
    component.partialTargetPairBits_spec G nodes tested subset balance inside untested left node selected,
    component.partialTargetPairBits_spec G nodes tested subset balance inside untested right node selected]

/-- Exact equality of executable fibre tests under the XOR translation.
Boolean elimination proves both implications, including the empty tested
set and every repeated zero contribution of a disabled pair root. -/
theorem BidirectedComponent.partialTargetTranslation_realizes_eq
    (G : ObservedGraph S) (nodes tested : NodeSet S)
    (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes)
    (balance : Fin S.count) (inside : nodes balance = true) (untested : tested balance = false)
    (left right : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool) :
    hedgePartialPairBitsRealizes G nodes tested right
        (hedgePairBitsXor G pairBits
          (component.partialTargetTranslation G nodes balance inside left right)) =
      hedgePartialPairBitsRealizes G nodes tested left pairBits := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro translated
    apply hedgePartialPairBitsRealizes_of
    intro node selected
    have equation := hedgePartialPairBitsRealizes_spec G nodes tested right _ translated node selected
    rw [hedgeXorPairBitsWithinFrom_xor,
      component.partialTargetTranslation_spec G nodes tested subset balance inside untested
        left right node selected] at equation
    cases pair : hedgeXorPairBitsWithinFrom G nodes node pairBits <;>
      cases first : left node <;> cases second : right node <;> simp_all
  · intro original
    apply hedgePartialPairBitsRealizes_of
    intro node selected
    rw [hedgeXorPairBitsWithinFrom_xor,
      component.partialTargetTranslation_spec G nodes tested subset balance inside untested
        left right node selected,
      hedgePartialPairBitsRealizes_spec G nodes tested left pairBits original node selected]
    cases left node <;> cases right node <;> rfl

/-- Every partial pattern has the same number of pair-root realizations.
The statement is uniform in the component and tested-set sizes; it neither
assumes nor computes a particular kernel dimension. -/
theorem BidirectedComponent.partialPairBitRealizers_length_eq
    (G : ObservedGraph S) (nodes tested : NodeSet S)
    (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes)
    (balance : Fin S.count) (inside : nodes balance = true) (untested : tested balance = false)
    (left right : Fin S.count -> Bool) :
    ((hedgePairBitEnum G).filter (hedgePartialPairBitsRealizes G nodes tested left)).length =
      ((hedgePairBitEnum G).filter (hedgePartialPairBitsRealizes G nodes tested right)).length := by
  let delta := component.partialTargetTranslation G nodes balance inside left right
  have permutation := (hedgePairBitEnum_map_xor_perm G delta).filter
    (hedgePartialPairBitsRealizes G nodes tested right)
  have predicateEq : hedgePartialPairBitsRealizes G nodes tested right ∘
      (fun pairBits => hedgePairBitsXor G pairBits delta) =
      hedgePartialPairBitsRealizes G nodes tested left := by
    funext pairBits
    exact component.partialTargetTranslation_realizes_eq G nodes tested subset balance inside
      untested left right pairBits
  rw [List.filter_map, predicateEq] at permutation
  simpa using permutation.length_eq

/-! ## Nested incidence when an inner coordinate is untested -/

/-- The partial test for the piecewise outer/inner incidence map. -/
def hedgePartialNestedPairBitsRealizes (G : ObservedGraph S)
    (outer inner tested : NodeSet S) (target : Fin S.count -> Bool)
    (pairBits : Fin (pairRootCount G) -> Bool) : Bool :=
  (NodeSet.members tested).all fun node =>
    hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits == target node

theorem hedgePartialNestedPairBitsRealizes_of (G : ObservedGraph S)
    (outer inner tested : NodeSet S) (target : Fin S.count -> Bool)
    (pairBits : Fin (pairRootCount G) -> Bool)
    (agrees : forall node, tested node = true ->
      hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits = target node) :
    hedgePartialNestedPairBitsRealizes G outer inner tested target pairBits = true := by
  apply List.all_eq_true.mpr
  intro node listed
  exact beq_iff_eq.mpr (agrees node ((NodeSet.mem_members_iff tested node).mp listed))

theorem hedgePartialNestedPairBitsRealizes_spec (G : ObservedGraph S)
    (outer inner tested : NodeSet S) (target : Fin S.count -> Bool)
    (pairBits : Fin (pairRootCount G) -> Bool)
    (realizes : hedgePartialNestedPairBitsRealizes G outer inner tested target pairBits = true) :
    forall node, tested node = true ->
      hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits = target node := by
  intro node selected
  exact beq_iff_eq.mp ((List.all_eq_true.mp realizes) node
    ((NodeSet.mem_members_iff tested node).mpr selected))

/-- An omitted inner row absorbs the inner parity constraint.  The same
normalization leaves all outer rows untouched, so every partial target is
realized even when the tested set contains vertices in `outer \ inner`. -/
def BidirectedComponent.partialNestedTargetPairBits
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (balance : Fin S.count) (inside : inner balance = true)
    (target : Fin S.count -> Bool) : Fin (pairRootCount G) -> Bool :=
  outerComponent.nestedEvenTargetPairBits G outer inner innerComponent subset
    (hedgeDefectAdjustedTarget inner balance target)
    (hedgeDefectAdjustedTarget_even inner balance inside target)

theorem BidirectedComponent.partialNestedTargetPairBits_spec
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer) (testedSubset : NodeSet.Subset tested outer)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (target : Fin S.count -> Bool) :
    forall node, tested node = true ->
      hedgeNestedXorPairBitsWithinFrom G outer inner node
        (outerComponent.partialNestedTargetPairBits G outer inner innerComponent subset
          balance inside target) = target node := by
  intro node selected
  have different : node ≠ balance := by
    intro equal
    subst node
    rw [untested] at selected
    cases selected
  have realizes := outerComponent.nestedEvenTargetPairBits_spec G outer inner innerComponent subset
    (hedgeDefectAdjustedTarget inner balance target)
    (hedgeDefectAdjustedTarget_even inner balance inside target) node (testedSubset node selected)
  simpa only [BidirectedComponent.partialNestedTargetPairBits, hedgeDefectAdjustedTarget,
    if_neg different, Bool.xor_false] using realizes

/-- The nested counterpart of the ordinary partial-target translation. -/
def BidirectedComponent.partialNestedTargetTranslation
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (balance : Fin S.count) (inside : inner balance = true)
    (left right : Fin S.count -> Bool) : Fin (pairRootCount G) -> Bool :=
  hedgePairBitsXor G
    (outerComponent.partialNestedTargetPairBits G outer inner innerComponent subset balance inside left)
    (outerComponent.partialNestedTargetPairBits G outer inner innerComponent subset balance inside right)

theorem BidirectedComponent.partialNestedTargetTranslation_spec
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer) (testedSubset : NodeSet.Subset tested outer)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (left right : Fin S.count -> Bool) :
    forall node, tested node = true ->
      hedgeNestedXorPairBitsWithinFrom G outer inner node
        (outerComponent.partialNestedTargetTranslation G outer inner innerComponent subset
          balance inside left right) = Bool.xor (left node) (right node) := by
  intro node selected
  rw [BidirectedComponent.partialNestedTargetTranslation, hedgeNestedXorPairBitsWithinFrom_xor,
    outerComponent.partialNestedTargetPairBits_spec G outer inner tested innerComponent subset testedSubset
      balance inside untested left node selected,
    outerComponent.partialNestedTargetPairBits_spec G outer inner tested innerComponent subset testedSubset
      balance inside untested right node selected]

theorem BidirectedComponent.partialNestedTargetTranslation_realizes_eq
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer) (testedSubset : NodeSet.Subset tested outer)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (left right : Fin S.count -> Bool) (pairBits : Fin (pairRootCount G) -> Bool) :
    hedgePartialNestedPairBitsRealizes G outer inner tested right
        (hedgePairBitsXor G pairBits
          (outerComponent.partialNestedTargetTranslation G outer inner innerComponent subset
            balance inside left right)) =
      hedgePartialNestedPairBitsRealizes G outer inner tested left pairBits := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro translated
    apply hedgePartialNestedPairBitsRealizes_of
    intro node selected
    have equation := hedgePartialNestedPairBitsRealizes_spec G outer inner tested right _ translated node selected
    rw [hedgeNestedXorPairBitsWithinFrom_xor,
      outerComponent.partialNestedTargetTranslation_spec G outer inner tested innerComponent subset testedSubset
        balance inside untested left right node selected] at equation
    cases pair : hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits <;>
      cases first : left node <;> cases second : right node <;> simp_all
  · intro original
    apply hedgePartialNestedPairBitsRealizes_of
    intro node selected
    rw [hedgeNestedXorPairBitsWithinFrom_xor,
      outerComponent.partialNestedTargetTranslation_spec G outer inner tested innerComponent subset testedSubset
        balance inside untested left right node selected,
      hedgePartialNestedPairBitsRealizes_spec G outer inner tested left pairBits original node selected]
    cases left node <;> cases right node <;> rfl

/-- All partial nested patterns have equally sized fibres as soon as one
inner coordinate is omitted.  This does not impose a condition on the other
tested outer coordinates or assume that any SCM mechanism ignores them. -/
theorem BidirectedComponent.partialNestedPairBitRealizers_length_eq
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer) (testedSubset : NodeSet.Subset tested outer)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (left right : Fin S.count -> Bool) :
    ((hedgePairBitEnum G).filter (hedgePartialNestedPairBitsRealizes G outer inner tested left)).length =
      ((hedgePairBitEnum G).filter (hedgePartialNestedPairBitsRealizes G outer inner tested right)).length := by
  let delta := outerComponent.partialNestedTargetTranslation G outer inner innerComponent subset
    balance inside left right
  have permutation := (hedgePairBitEnum_map_xor_perm G delta).filter
    (hedgePartialNestedPairBitsRealizes G outer inner tested right)
  have predicateEq : hedgePartialNestedPairBitsRealizes G outer inner tested right ∘
      (fun pairBits => hedgePairBitsXor G pairBits delta) =
      hedgePartialNestedPairBitsRealizes G outer inner tested left := by
    funext pairBits
    exact outerComponent.partialNestedTargetTranslation_realizes_eq G outer inner tested innerComponent subset
      testedSubset balance inside untested left right pairBits
  rw [List.filter_map, predicateEq] at permutation
  simpa using permutation.length_eq

end Causality
end Thesis
