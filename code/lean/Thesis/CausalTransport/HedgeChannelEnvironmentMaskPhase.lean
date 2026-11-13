import Thesis.CausalTransport.HedgeChannelEnvironmentRouting

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability FiniteBooleanInteraction

/-!
# Actual observed-mask characters on the original two-block cube

Path conservation describes a character on the complete cube; forest
conservation describes an XOR of observed bits.  Their comparison must
retain the literal environment prefix and observed suffix, rather than
silently evaluating a smaller cube or discarding original reserved inputs.
The basis calculation below proves the bridge at every cube assignment.

The finite mask identities also account for overlap by XOR, not Boolean
union.  They preserve the original once-only observed enumeration, and are
used to cancel the actual collider mask when activation rows are installed.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

/-- The selected observed XOR is exactly its full ascending masked fold.
Omitted rows contribute zero, and every observed coordinate occurs once. -/
theorem nodeXor_value_eq_full_fold (nodes : NodeSet S) (bits : Fin S.count -> Bool) :
    hedgeNodeXor nodes bits = (List.finRange S.count).foldl (fun total child => Bool.xor total
      (if nodes child then bits child else false)) false := by
  unfold hedgeNodeXor NodeSet.members
  rw [List.foldl_filter]
  change (List.finRange S.count).foldl _ false = _
  apply foldl_congr
  intro total child
  cases nodes child <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.xor_false]

/-- A selection whose actual coordinates are all zero contributes no
phase.  The premise concerns real coordinate values, not an assumed phase. -/
theorem nodeXor_of_zero (nodes : NodeSet S) (bits : Fin S.count -> Bool)
    (zero : forall child, nodes child = true -> bits child = false) : hedgeNodeXor nodes bits = false := by
  unfold hedgeNodeXor
  have actualFold : (NodeSet.members nodes).foldl (fun total child => Bool.xor total (bits child)) false =
      (NodeSet.members nodes).foldl (fun total _child => total) false := by
    apply foldl_congr_of_mem
    intro total child member
    rw [zero child ((NodeSet.mem_members_iff nodes child).mp member), Bool.xor_false]
  exact actualFold.trans (foldl_unchanged _ _ _ (fun _total _child => rfl))

private def observedMaskPhase (nodes : NodeSet S) : HomogeneousPhase (pairRootCount G.binary + S.count) where
  value := fun point => hedgeNodeXor nodes (cubeSample G point)
  at_zero := nodeXor_of_zero nodes _ (fun _child _selected => rfl)
  xor_additive := by
    intro left right
    change (NodeSet.members nodes).foldl (fun total child => Bool.xor total
      (Bool.xor (cubeSample G left child) (cubeSample G right child))) false = _
    exact foldl_xor_pointwise _ _ _

private theorem nodeXor_basis (nodes : NodeSet S) (child : Fin S.count) :
    hedgeNodeXor nodes (basisAssignment S.count child) = nodes child := by
  rw [nodeXor_value_eq_full_fold]
  exact basisAssignment_masked_foldl S.count child nodes

/-- The actual character of an observed cube mask is precisely the XOR of
its observed suffix coordinates.  The environment-prefix coefficients are
proved zero on the complete original cube, not omitted by a support change. -/
theorem cubeMaskPhase_value (nodes : NodeSet S) (point : Cube G) :
    (maskPhase _ (cubeMask G nodes)).value point = hedgeNodeXor nodes (cubeSample G point) := by
  change (maskPhase _ (cubeMask G nodes)).value point = (observedMaskPhase (G := G) nodes).value point
  apply HomogeneousPhase.value_eq_of_basis _ _ (fun _ => false) (sample := point)
  · intro coordinate _free
    rw [maskPhase_basis]
    by_cases earlier : coordinate.val < pairRootCount G.binary
    · let root : Fin (pairRootCount G.binary) := ⟨coordinate.val, earlier⟩
      have embedded : root.castAdd S.count = coordinate := Fin.ext rfl
      rw [← embedded]
      change FiniteProduct.BooleanBlocks.leftBlock _ _ (cubeMask G nodes) root =
        hedgeNodeXor nodes (cubeSample G (basisAssignment _ (root.castAdd S.count)))
      rw [cubeMask, FiniteProduct.BooleanBlocks.leftBlock_join, cubeSample, rightBlock_basis_left]
      exact (nodeXor_of_zero nodes _ (fun _child _selected => rfl)).symm
    · let child : Fin S.count := ⟨coordinate.val - pairRootCount G.binary, by have bound := coordinate.isLt; omega⟩
      have embedded : Fin.natAdd (pairRootCount G.binary) child = coordinate := by
        apply Fin.ext
        dsimp only [child, Fin.natAdd]
        omega
      rw [← embedded]
      change FiniteProduct.BooleanBlocks.rightBlock _ _ (cubeMask G nodes) child =
        hedgeNodeXor nodes (cubeSample G (basisAssignment _ (Fin.natAdd (pairRootCount G.binary) child)))
      rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join, cubeSample, rightBlock_basis_right, nodeXor_basis]
  · intro coordinate impossible
    cases impossible

/-- XOR of actual selection masks is XOR of their observed characters.
At an overlap the real coordinate cancels; it is not counted twice under
separate copies of a row or replaced by Boolean union. -/
theorem nodeXor_xor_masks (left right : NodeSet S) (bits : Fin S.count -> Bool) :
    hedgeNodeXor (fun child => Bool.xor (left child) (right child)) bits =
      Bool.xor (hedgeNodeXor left bits) (hedgeNodeXor right bits) := by
  rw [nodeXor_value_eq_full_fold, nodeXor_value_eq_full_fold, nodeXor_value_eq_full_fold]
  calc
    _ = (List.finRange S.count).foldl (fun total child => Bool.xor total
        (Bool.xor (if left child then bits child else false) (if right child then bits child else false))) false := by
      apply foldl_congr
      intro total child
      cases left child <;> cases right child <;> cases bits child <;> rfl
    _ = _ := foldl_xor_pointwise _ _ _

/-- A singleton character retains exactly its supplied observed bit. -/
theorem nodeXor_singleton (child : Fin S.count) (bits : Fin S.count -> Bool) :
    hedgeNodeXor (NodeSet.singleton child) bits = bits child := by
  rw [nodeXor_value_eq_full_fold]
  have same : forall index, (if NodeSet.singleton child index then bits index else false) =
      (if bits index then basisAssignment S.count child index else false) := by
    intro index
    unfold NodeSet.singleton basisAssignment
    cases bits index <;> cases decide (index = child) <;> rfl
  have actualFold := foldl_congr _ _ false (List.finRange S.count)
    (fun total index => congrArg (Bool.xor total) (same index))
  exact actualFold.trans (basisAssignment_masked_foldl S.count child bits)

/-- An actual observed submask is an allowed outcome character on the
original cube.  Its reserved-input prefix is zero, and no observed bit
outside the queried outcome is introduced by the block embedding. -/
theorem cubeMask_member_outcomeMasks (nodes outcome : NodeSet S) (subset : NodeSet.Subset nodes outcome) :
    cubeMask G nodes ∈ outcomeMasks (pairRootCount G.binary + S.count) (cubeMask G outcome) := by
  apply (FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mpr
  intro coordinate omitted
  have absent : cubeMask G outcome coordinate = false := by
    simpa only [Bool.not_eq_true'] using omitted
  unfold cubeMask FiniteProduct.BooleanBlocks.join at absent ⊢
  by_cases earlier : coordinate.val < pairRootCount G.binary
  · rw [dif_pos earlier]
  · rw [dif_neg earlier] at absent ⊢
    apply Bool.eq_false_iff.mpr
    intro selected
    exact Bool.false_ne_true (absent.symm.trans (subset _ selected))

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
