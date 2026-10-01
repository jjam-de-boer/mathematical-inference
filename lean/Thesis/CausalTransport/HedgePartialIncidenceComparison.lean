import Thesis.CausalTransport.HedgePartialIncidence

namespace Thesis
namespace Causality

open Probability

/-!
# Comparing ordinary and nested partial-incidence fibres

`HedgePartialIncidence` proves equal fibre sizes *within* each incidence map.
That alone cannot compare the large and small carrier laws: two uniformly
fibred maps might still have different image sets or different fibre sizes.
Here both maps inspect the same subset of an outer component, with one inner
vertex omitted.  We prove their fibre sizes equal, for arbitrary target bits.

The zero-fibre comparison is constructive.  An internal pair-root correction
cancels the undesired tested inner incidence without changing any outer row
outside the inner set.  The omitted inner row absorbs the correction's parity.
Masking all untested target coordinates makes this section canonical in
exactly the information visible to the partial test.  Applying the other
incidence map to a corrected zero-fibre vector recovers that information, so
the correction map is injective.  The reverse construction is injective by
the same argument.  Duplicate-free finite-list comparison gives equal sizes;
the already proved within-map translations then handle arbitrary targets.

No dimension formula, chosen basis, classical finite-cardinality theorem,
choice, or assumed equality of probability laws is used.  This is the
cross-map counting step for omitted-root interventional marginals.  Actual
SCM evaluation and weighted private-coordinate sums remain separate from
these pair-root equations.
-/

/-! ## A canonical internal section of the tested inner target -/

/-- Retain only target rows that are both inner and tested.  Clearing every
other row ensures the correction depends only on the partial test, not on
arbitrary values assigned to coordinates that its event does not inspect. -/
def hedgeTestedInnerTarget (inner tested : NodeSet S)
    (target : Fin S.count -> Bool) (node : Fin S.count) : Bool :=
  if inner node && tested node then target node else false

/-- Normalize the masked target at the omitted inner row, solve its even
incidence equations, and restrict the resulting vector to internal pair
roots.  This is total finite data; `untested` is needed only by its spec. -/
def BidirectedComponent.internalPartialTargetPairBits
    (G : ObservedGraph S) (inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true)
    (target : Fin S.count -> Bool) : Fin (pairRootCount G) -> Bool :=
  component.internalEvenTargetPairBits G inner
    (hedgeDefectAdjustedTarget inner balance (hedgeTestedInnerTarget inner tested target))
    (hedgeDefectAdjustedTarget_even inner balance inside _)

/-- Every tested inner row is realized literally.  The correction of total
parity changes only the omitted row and therefore cannot alter a tested row. -/
theorem BidirectedComponent.internalPartialTargetPairBits_spec
    (G : ObservedGraph S) (inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (target : Fin S.count -> Bool)
    (node : Fin S.count) (inInner : inner node = true) (selected : tested node = true) :
    hedgeXorPairBitsWithinFrom G inner node
        (component.internalPartialTargetPairBits G inner tested balance inside target) = target node := by
  have different : node ≠ balance := by
    intro equal
    subst node
    rw [untested] at selected
    cases selected
  rw [BidirectedComponent.internalPartialTargetPairBits,
    component.internalEvenTargetPairBits_spec G inner _ _ node inInner]
  simp only [hedgeDefectAdjustedTarget, if_neg different, Bool.xor_false,
    hedgeTestedInnerTarget, inInner, selected, Bool.true_and, if_true]

/-- Internal corrections have the same incidence when measured in a
containing outer component.  This is the row identity used to recover the
correction from an ordinary partial zero-fibre vector. -/
theorem BidirectedComponent.internalPartialTargetPairBits_outer_spec
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (subset : NodeSet.Subset inner outer) (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (target : Fin S.count -> Bool)
    (node : Fin S.count) (inInner : inner node = true) (selected : tested node = true) :
    hedgeXorPairBitsWithinFrom G outer node
        (component.internalPartialTargetPairBits G inner tested balance inside target) = target node := by
  have innerRow := component.internalPartialTargetPairBits_spec G inner tested balance inside untested
    target node inInner selected
  unfold BidirectedComponent.internalPartialTargetPairBits BidirectedComponent.internalEvenTargetPairBits
    at innerRow ⊢
  rw [hedgePairBitsRestrict_inside G outer inner subset]
  simpa only [hedgePairBitsRestrict_same] using innerRow

/-- The internal correction is invisible to every outer row outside the
inner set, whether or not that outer row belongs to the tested set. -/
theorem BidirectedComponent.internalPartialTargetPairBits_outside
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true)
    (target : Fin S.count -> Bool) (node : Fin S.count) (outside : inner node = false) :
    hedgeXorPairBitsWithinFrom G outer node
        (component.internalPartialTargetPairBits G inner tested balance inside target) = false := by
  unfold BidirectedComponent.internalPartialTargetPairBits BidirectedComponent.internalEvenTargetPairBits
  exact hedgePairBitsRestrict_outside G outer inner _ node outside

/-- Equal tested inner targets give exactly the same correction vector.
Neither target is required to agree at untested rows: the canonical mask
clears those rows before the parity normalization or finite search is run. -/
theorem BidirectedComponent.internalPartialTargetPairBits_congr
    (G : ObservedGraph S) (inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true)
    (left right : Fin S.count -> Bool)
    (agrees : forall node, inner node = true -> tested node = true -> left node = right node) :
    component.internalPartialTargetPairBits G inner tested balance inside left =
      component.internalPartialTargetPairBits G inner tested balance inside right := by
  have masked : hedgeTestedInnerTarget inner tested left = hedgeTestedInnerTarget inner tested right := by
    funext node
    cases innerAt : inner node <;> cases testedAt : tested node
    all_goals simp only [hedgeTestedInnerTarget, innerAt, testedAt, Bool.false_and,
      Bool.true_and, Bool.false_eq_true, if_false, if_true]
    exact agrees node innerAt testedAt
  unfold BidirectedComponent.internalPartialTargetPairBits
  exact component.internalEvenTargetPairBits_congr G inner
    (congrArg (hedgeDefectAdjustedTarget inner balance) masked) _ _

/-! ## Explicit injections between the two partial zero fibres -/

/-- Cancel tested inner incidence while preserving all outer-only rows.
On the ordinary zero fibre this produces a nested zero-fibre vector. -/
def BidirectedComponent.partialLargeKernelToNestedPairBits
    (G : ObservedGraph S) (inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true)
    (pairBits : Fin (pairRootCount G) -> Bool) : Fin (pairRootCount G) -> Bool :=
  hedgePairBitsXor G pairBits (component.internalPartialTargetPairBits G inner tested balance inside
    (fun node => hedgeXorPairBitsWithinFrom G inner node pairBits))

/-- The correction leaves tested outer-only zero equations unchanged and
cancels each tested inner equation by XORing its original incidence with
itself.  The untested balancing equation is deliberately not checked. -/
theorem BidirectedComponent.partialLargeKernelToNestedPairBits_realizes
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (pairBits : Fin (pairRootCount G) -> Bool)
    (zero : hedgePartialPairBitsRealizes G outer tested (hedgeZeroIncidenceTarget S) pairBits = true) :
    hedgePartialNestedPairBitsRealizes G outer inner tested (hedgeZeroIncidenceTarget S)
        (component.partialLargeKernelToNestedPairBits G inner tested balance inside pairBits) = true := by
  apply hedgePartialNestedPairBitsRealizes_of
  intro node selected
  cases inInner : inner node with
  | false =>
      simp only [hedgeNestedXorPairBitsWithinFrom, inInner, Bool.false_eq_true, if_false]
      rw [BidirectedComponent.partialLargeKernelToNestedPairBits, hedgeXorPairBitsWithinFrom_xor,
        hedgePartialPairBitsRealizes_spec G outer tested (hedgeZeroIncidenceTarget S) pairBits zero node selected,
        component.internalPartialTargetPairBits_outside G outer inner tested balance inside _ node inInner]
      rfl
  | true =>
      simp only [hedgeNestedXorPairBitsWithinFrom, inInner, if_true]
      rw [BidirectedComponent.partialLargeKernelToNestedPairBits, hedgeXorPairBitsWithinFrom_xor,
        component.internalPartialTargetPairBits_spec G inner tested balance inside untested _ node inInner selected]
      cases hedgeXorPairBitsWithinFrom G inner node pairBits <;> rfl

/-- On the ordinary zero fibre, inspecting the translated vector with the
ordinary incidence map recovers its tested inner correction target.  Its
canonical correction is therefore determined, and XOR cancellation recovers
the original vector.  Untested rows supply no extra injectivity premise. -/
theorem BidirectedComponent.partialLargeKernelToNestedPairBits_injective
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (subset : NodeSet.Subset inner outer) (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (left right : Fin (pairRootCount G) -> Bool)
    (leftZero : hedgePartialPairBitsRealizes G outer tested (hedgeZeroIncidenceTarget S) left = true)
    (rightZero : hedgePartialPairBitsRealizes G outer tested (hedgeZeroIncidenceTarget S) right = true)
    (equal : component.partialLargeKernelToNestedPairBits G inner tested balance inside left =
      component.partialLargeKernelToNestedPairBits G inner tested balance inside right) : left = right := by
  let leftTarget := fun node => hedgeXorPairBitsWithinFrom G inner node left
  let rightTarget := fun node => hedgeXorPairBitsWithinFrom G inner node right
  let leftCorrection := component.internalPartialTargetPairBits G inner tested balance inside leftTarget
  let rightCorrection := component.internalPartialTargetPairBits G inner tested balance inside rightTarget
  have expanded : hedgePairBitsXor G left leftCorrection = hedgePairBitsXor G right rightCorrection := equal
  have targetsAgree : forall node, inner node = true -> tested node = true -> leftTarget node = rightTarget node := by
    intro node inInner selected
    have row := congrArg (fun bits => hedgeXorPairBitsWithinFrom G outer node bits) expanded
    change hedgeXorPairBitsWithinFrom G outer node (hedgePairBitsXor G left leftCorrection) =
      hedgeXorPairBitsWithinFrom G outer node (hedgePairBitsXor G right rightCorrection) at row
    rw [hedgeXorPairBitsWithinFrom_xor, hedgeXorPairBitsWithinFrom_xor,
      hedgePartialPairBitsRealizes_spec G outer tested (hedgeZeroIncidenceTarget S) left leftZero node selected,
      hedgePartialPairBitsRealizes_spec G outer tested (hedgeZeroIncidenceTarget S) right rightZero node selected,
      component.internalPartialTargetPairBits_outer_spec G outer inner tested subset balance inside untested
        leftTarget node inInner selected,
      component.internalPartialTargetPairBits_outer_spec G outer inner tested subset balance inside untested
        rightTarget node inInner selected] at row
    simpa only [hedgeZeroIncidenceTarget, Bool.false_xor] using row
  have correctionEq := component.internalPartialTargetPairBits_congr G inner tested balance inside
    leftTarget rightTarget targetsAgree
  change leftCorrection = rightCorrection at correctionEq
  rw [correctionEq] at expanded
  have recovered := congrArg (fun bits => hedgePairBitsXor G bits rightCorrection) expanded
  simpa only [hedgePairBitsXor_self_right] using recovered

/-- The reverse correction cancels the tested ordinary outer incidence
inside the inner component, again without changing outer-only rows. -/
def BidirectedComponent.partialNestedKernelToLargePairBits
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true)
    (pairBits : Fin (pairRootCount G) -> Bool) : Fin (pairRootCount G) -> Bool :=
  hedgePairBitsXor G pairBits (component.internalPartialTargetPairBits G inner tested balance inside
    (fun node => hedgeXorPairBitsWithinFrom G outer node pairBits))

/-- Tested outer-only rows are zero by the nested premise.  On tested inner
rows the containing-outer incidence of the internal section cancels the
original ordinary incidence, giving the required ordinary partial zero test. -/
theorem BidirectedComponent.partialNestedKernelToLargePairBits_realizes
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (subset : NodeSet.Subset inner outer) (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (pairBits : Fin (pairRootCount G) -> Bool)
    (zero : hedgePartialNestedPairBitsRealizes G outer inner tested (hedgeZeroIncidenceTarget S) pairBits = true) :
    hedgePartialPairBitsRealizes G outer tested (hedgeZeroIncidenceTarget S)
        (component.partialNestedKernelToLargePairBits G outer inner tested balance inside pairBits) = true := by
  apply hedgePartialPairBitsRealizes_of
  intro node selected
  rw [BidirectedComponent.partialNestedKernelToLargePairBits, hedgeXorPairBitsWithinFrom_xor]
  cases inInner : inner node with
  | false =>
      have row := hedgePartialNestedPairBitsRealizes_spec G outer inner tested (hedgeZeroIncidenceTarget S)
        pairBits zero node selected
      simp only [hedgeNestedXorPairBitsWithinFrom, inInner, Bool.false_eq_true, if_false] at row
      rw [row, component.internalPartialTargetPairBits_outside G outer inner tested balance inside _ node inInner]
      rfl
  | true =>
      rw [component.internalPartialTargetPairBits_outer_spec G outer inner tested subset balance inside untested
        _ node inInner selected]
      cases hedgeXorPairBitsWithinFrom G outer node pairBits <;> rfl

/-- The nested zero-fibre equations similarly recover the reverse
correction by inspecting inner incidence after translation. -/
theorem BidirectedComponent.partialNestedKernelToLargePairBits_injective
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (left right : Fin (pairRootCount G) -> Bool)
    (leftZero : hedgePartialNestedPairBitsRealizes G outer inner tested (hedgeZeroIncidenceTarget S) left = true)
    (rightZero : hedgePartialNestedPairBitsRealizes G outer inner tested (hedgeZeroIncidenceTarget S) right = true)
    (equal : component.partialNestedKernelToLargePairBits G outer inner tested balance inside left =
      component.partialNestedKernelToLargePairBits G outer inner tested balance inside right) : left = right := by
  let leftTarget := fun node => hedgeXorPairBitsWithinFrom G outer node left
  let rightTarget := fun node => hedgeXorPairBitsWithinFrom G outer node right
  let leftCorrection := component.internalPartialTargetPairBits G inner tested balance inside leftTarget
  let rightCorrection := component.internalPartialTargetPairBits G inner tested balance inside rightTarget
  have expanded : hedgePairBitsXor G left leftCorrection = hedgePairBitsXor G right rightCorrection := equal
  have targetsAgree : forall node, inner node = true -> tested node = true -> leftTarget node = rightTarget node := by
    intro node inInner selected
    have row := congrArg (fun bits => hedgeXorPairBitsWithinFrom G inner node bits) expanded
    change hedgeXorPairBitsWithinFrom G inner node (hedgePairBitsXor G left leftCorrection) =
      hedgeXorPairBitsWithinFrom G inner node (hedgePairBitsXor G right rightCorrection) at row
    have leftRow := hedgePartialNestedPairBitsRealizes_spec G outer inner tested (hedgeZeroIncidenceTarget S)
      left leftZero node selected
    have rightRow := hedgePartialNestedPairBitsRealizes_spec G outer inner tested (hedgeZeroIncidenceTarget S)
      right rightZero node selected
    simp only [hedgeNestedXorPairBitsWithinFrom, inInner, if_true] at leftRow rightRow
    rw [hedgeXorPairBitsWithinFrom_xor, hedgeXorPairBitsWithinFrom_xor, leftRow, rightRow,
      component.internalPartialTargetPairBits_spec G inner tested balance inside untested leftTarget node inInner selected,
      component.internalPartialTargetPairBits_spec G inner tested balance inside untested rightTarget node inInner selected] at row
    simpa only [hedgeZeroIncidenceTarget, Bool.false_xor] using row
  have correctionEq := component.internalPartialTargetPairBits_congr G inner tested balance inside
    leftTarget rightTarget targetsAgree
  change leftCorrection = rightCorrection at correctionEq
  rw [correctionEq] at expanded
  have recovered := congrArg (fun bits => hedgePairBitsXor G bits rightCorrection) expanded
  simpa only [hedgePairBitsXor_self_right] using recovered

/-! ## Cross-map fibre equality, with no complete-target parity premise -/

/-- The two partial zero fibres have equal size.  The explicit injections
above are mapped over their duplicate-free exhaustive filtered lists;
constructive finite-list bounds in both directions finish the comparison. -/
theorem BidirectedComponent.partialPairBitKernel_length_eq_nested
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (subset : NodeSet.Subset inner outer) (component : BidirectedComponent G inner)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false) :
    ((hedgePairBitEnum G).filter
        (hedgePartialPairBitsRealizes G outer tested (hedgeZeroIncidenceTarget S))).length =
      ((hedgePairBitEnum G).filter
        (hedgePartialNestedPairBitsRealizes G outer inner tested (hedgeZeroIncidenceTarget S))).length := by
  let large := (hedgePairBitEnum G).filter (hedgePartialPairBitsRealizes G outer tested (hedgeZeroIncidenceTarget S))
  let nested := (hedgePairBitEnum G).filter
    (hedgePartialNestedPairBitsRealizes G outer inner tested (hedgeZeroIncidenceTarget S))
  let forward := component.partialLargeKernelToNestedPairBits G inner tested balance inside
  let backward := component.partialNestedKernelToLargePairBits G outer inner tested balance inside
  have largeNodup : large.Nodup := List.Sublist.nodup List.filter_sublist (hedgePairBitEnum_nodup G)
  have nestedNodup : nested.Nodup := List.Sublist.nodup List.filter_sublist (hedgePairBitEnum_nodup G)
  have forwardNodup : (large.map forward).Nodup := by
    apply ConstructivePermutation.nodup_map_of_injective_on forward large
    · intro left leftMem right rightMem equal
      exact component.partialLargeKernelToNestedPairBits_injective G outer inner tested subset balance inside untested
        left right (List.mem_filter.mp leftMem).2 (List.mem_filter.mp rightMem).2 equal
    · exact largeNodup
  have forwardSubset : forall value, value ∈ large.map forward -> value ∈ nested := by
    intro value listed
    rcases List.mem_map.mp listed with ⟨source, sourceListed, equal⟩
    subst value
    exact List.mem_filter.mpr ⟨hedgePairBitEnum_complete G _,
      component.partialLargeKernelToNestedPairBits_realizes G outer inner tested balance inside untested
        source (List.mem_filter.mp sourceListed).2⟩
  have forwardLe : large.length ≤ nested.length := by
    have bound := ConstructivePermutation.length_le_of_nodup_subset forwardNodup forwardSubset
    simpa only [List.length_map] using bound
  have backwardNodup : (nested.map backward).Nodup := by
    apply ConstructivePermutation.nodup_map_of_injective_on backward nested
    · intro left leftMem right rightMem equal
      exact component.partialNestedKernelToLargePairBits_injective G outer inner tested balance inside untested
        left right (List.mem_filter.mp leftMem).2 (List.mem_filter.mp rightMem).2 equal
    · exact nestedNodup
  have backwardSubset : forall value, value ∈ nested.map backward -> value ∈ large := by
    intro value listed
    rcases List.mem_map.mp listed with ⟨source, sourceListed, equal⟩
    subst value
    exact List.mem_filter.mpr ⟨hedgePairBitEnum_complete G _,
      component.partialNestedKernelToLargePairBits_realizes G outer inner tested subset balance inside untested
        source (List.mem_filter.mp sourceListed).2⟩
  have backwardLe : nested.length ≤ large.length := by
    have bound := ConstructivePermutation.length_le_of_nodup_subset backwardNodup backwardSubset
    simpa only [List.length_map] using bound
  exact Nat.le_antisymm forwardLe backwardLe

/-- Arbitrary ordinary and nested partial targets have equal numbers of
realizations on the same tested rows.  The omitted inner row also lies in the
outer component, so it supplies both within-map parity normalizations.
Targets need agree neither with each other nor with an even full pattern. -/
theorem BidirectedComponent.partialPairBitRealizers_length_eq_nested
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer) (testedSubset : NodeSet.Subset tested outer)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (largeTarget nestedTarget : Fin S.count -> Bool) :
    ((hedgePairBitEnum G).filter (hedgePartialPairBitsRealizes G outer tested largeTarget)).length =
      ((hedgePairBitEnum G).filter
        (hedgePartialNestedPairBitsRealizes G outer inner tested nestedTarget)).length := by
  calc
    _ = ((hedgePairBitEnum G).filter
        (hedgePartialPairBitsRealizes G outer tested (hedgeZeroIncidenceTarget S))).length :=
      outerComponent.partialPairBitRealizers_length_eq G outer tested testedSubset balance (subset balance inside)
        untested largeTarget (hedgeZeroIncidenceTarget S)
    _ = ((hedgePairBitEnum G).filter
        (hedgePartialNestedPairBitsRealizes G outer inner tested (hedgeZeroIncidenceTarget S))).length :=
      innerComponent.partialPairBitKernel_length_eq_nested G outer inner tested subset balance inside untested
    _ = _ := outerComponent.partialNestedPairBitRealizers_length_eq G outer inner tested innerComponent subset
      testedSubset balance inside untested (hedgeZeroIncidenceTarget S) nestedTarget

end Causality
end Thesis
