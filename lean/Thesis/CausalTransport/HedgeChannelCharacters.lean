import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

/-!
# Local parity characters for a finite multi-channel hedge construction

The carrier readout construction cannot cover every hedge: a route from a
common root to the original outcome may leave the forest and then enter an
outer-only vertex.  Restricting such routes loses valid original queries.

A different construction can expand the background kernels at the outer
vertices into finitely many local character terms.  An expansion term selects
some vertices of `large \ small`.  Its large-forest character must equal the
small-forest character times those selected background characters.  The
identity below proves exactly that parity equality, using the hedge's existing
kept arrows to transfer each selected vertex bit to its unique child.

The small character's parent signal is arbitrary.  It need not be the old
small-forest incoming parity, and may read declared parents on routes that
leave and re-enter either forest.  Every correction in `channelParentSignal`
still reads only actual typed directed parents; a global parity identity is
not used to give a mechanism access to an unavailable observed coordinate.

This is the local-character part of the independent-channel construction,
not a counterexample theorem.  Complete finite expansion, independent hidden
integration and positive normalized actual tables are developed in the
subsequent channel modules.  `HedgeChannelCoefficients` supplies positive
natural-power tables and their complete mask-coefficient identity.
`HedgeChannelInstallation` installs their explicit channel slots and typed
signals for an arbitrary hedge.  Its complete observational assembly and
original-query gap remain open.  A common mixing latent is not supplied, and
observational equivalence is not assumed as a replacement for integration.
No channel enumeration or private response-function space is evaluated here.

The intended countermodel family is specific.  Give each outer expansion
mask its own independent pair-bit block on the large component, and give
the small component a separate block.  Each local row is a sum of its common
background and channel characters.  Partial selections of any one connected
block cancel by `HedgeChannelOrthogonality`; `HedgeChannelMonomial` regroups
actual row terms and performs independent integration on the actual
pair-root prior, not a common switch.  The surviving large-channel terms
must be assembled into the actual likelihood's small-character times outer-
background product.  `HedgeChannelCoefficients` constructs common-capacity
amplitudes, proves their positive baselines, and matches every finite mask
coefficient literally.  The separate general graph-indexed installation is
supplied by `HedgeChannelInstallation`; its complete likelihood still needs
to be assembled from the surviving terms.

The original intervention meets the large component and avoids the small
one.  `HedgeChannelMonomial` proves that omission of any support row kills
every term selecting that connected channel.  The complete small term must
be shown to remain, and still needs a checked
nonzero original-outcome marginal through an action-avoiding directed flow.
The integrated coefficient and separation obligations do not follow just
by importing the character identity.  Conditional queries additionally need
their actual two conditioning denominators compared, not merely a numerator
difference.
-/

variable {S : ObservedSignature} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Finite parity identities for masked incoming arrows -/

private theorem nodeXor_congr (nodes : NodeSet S) (left right : Fin S.count -> Bool)
    (same : forall node, nodes node = true -> left node = right node) :
    hedgeNodeXor nodes left = hedgeNodeXor nodes right := by
  unfold hedgeNodeXor
  apply foldl_congr_of_mem
  intro total node member
  rw [same node ((NodeSet.mem_members_iff nodes node).mp member)]

private theorem nodeXor_xor (nodes : NodeSet S) (left right : Fin S.count -> Bool) :
    hedgeNodeXor nodes (fun node => Bool.xor (left node) (right node)) =
      Bool.xor (hedgeNodeXor nodes left) (hedgeNodeXor nodes right) :=
  foldl_xor_pointwise left right (NodeSet.members nodes)

private theorem nodeXor_split_subset (small large : NodeSet S)
    (subset : NodeSet.Subset small large) (bits : Fin S.count -> Bool) :
    hedgeNodeXor large bits = Bool.xor (hedgeNodeXor small bits)
      (hedgeNodeXor (NodeSet.diff large small) bits) := by
  have localSplit := nodeXor_congr large bits
    (fun node => Bool.xor (if small node then bits node else false)
      (if NodeSet.diff large small node then bits node else false)) (by
        intro node inside
        cases selected : small node <;> simp [NodeSet.diff, inside, selected])
  rw [localSplit, nodeXor_xor, hedgeNodeXor_mask_of_subset small large subset,
    hedgeNodeXor_mask_of_subset (NodeSet.diff large small) large (NodeSet.diff_subset_left _ _)]

/-- Removing some transmitting parents still gives a well-formed arrow
map on the original receiving set.  The mask need not be child-closed: a
selected outer parent can transmit to an unselected small child. -/
theorem childWellFormedBool_restrict_within (nodes selected : NodeSet S)
    (kept : ForestChild S) (wellFormed : childWellFormedBool nodes kept = true)
    (subset : NodeSet.Subset selected nodes) :
    childWellFormedBool nodes (restrictChild selected kept) = true := by
  apply List.all_eq_true.mpr
  intro parent _member
  cases chosen : selected parent with
  | false =>
      cases nodes parent <;> simp [restrictChild, chosen]
  | true =>
      have inside := subset parent chosen
      cases successor : kept parent with
      | none => simp [restrictChild, chosen, inside, successor]
      | some child =>
          have edge := childWellFormed_edge nodes kept wellFormed successor
          simp [restrictChild, chosen, inside, successor, edge.2.1, edge.2.2]

/-- With no selected sink, each masked bit arrives exactly once at a
receiving vertex.  This counts the actual kept edges, including those that
cross from a selected outer vertex to an unselected small vertex. -/
theorem hedgeNodeXor_routingIncoming_mask (nodes selected : NodeSet S)
    (kept : ForestChild S) (wellFormed : childWellFormedBool nodes kept = true)
    (subset : NodeSet.Subset selected nodes)
    (noSinks : forall node, selected node = true -> kept node ≠ none)
    (bits : Fin S.count -> Bool) :
    hedgeNodeXor nodes (hedgeRoutingIncomingBits kept
      (fun node => if selected node then bits node else false)) =
      hedgeNodeXor selected bits := by
  rw [hedgeNodeXor_routingIncoming_of_wellFormed nodes kept wellFormed,
    hedgeNodeXor_routingNonSink_members]
  have same :
      (NodeSet.members nodes).foldl (fun total node => Bool.xor total
        (match kept node with
        | none => false
        | some _ => if selected node then bits node else false)) false =
      hedgeNodeXor nodes (fun node => if selected node then bits node else false) := by
    apply foldl_congr_of_mem
    intro total node _member
    cases chosen : selected node with
    | false => cases kept node <;> simp [chosen]
    | true =>
        cases successor : kept node with
        | none => exact False.elim (noSinks node chosen successor)
        | some _ => simp [chosen]
  exact same.trans (hedgeNodeXor_mask_of_subset selected nodes subset bits)

private theorem routingIncoming_restrict (selected : NodeSet S) (kept : ForestChild S)
    (bits : Fin S.count -> Bool) (child : Fin S.count) :
    hedgeRoutingIncomingBits (restrictChild selected kept) bits child =
      hedgeRoutingIncomingBits kept (fun node => if selected node then bits node else false) child := by
  unfold hedgeRoutingIncomingBits
  apply foldl_congr
  intro total parent
  cases chosen : selected parent with
  | false => simp [hedgeRoutingParentEntry, restrictChild, chosen]
  | true => simp [hedgeRoutingParentEntry, restrictChild, chosen]

/-- Every outer-only vertex has a kept child: otherwise it would be a
common root, hence belong to the small forest.  This is derived from the
hedge, not added as a new readiness condition. -/
theorem HedgeWitness.channelOuter_no_sinks (w : HedgeWitness G q)
    (node : Fin S.count) (selected : NodeSet.diff w.large w.small node = true) :
    w.child node ≠ none := by
  intro sink
  have inside := (Bool.and_eq_true_iff.mp selected).1
  have root := (w.large_forest.roots_exact node).mpr ⟨inside, sink⟩
  have small := ((w.small_forest.roots_exact node).mp root).1
  have excluded := (Bool.and_eq_true_iff.mp selected).2
  rw [small] at excluded
  cases excluded

/-- On a full sample, the typed masked-parent parity integrates to the
parity of the selected outer vertices.  No route or small-membership
condition is imposed on their receiving children. -/
theorem HedgeWitness.channelParentBits_nodeXor (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (selected : NodeSet S)
    (subset : NodeSet.Subset selected (NodeSet.diff w.large w.small)) (sample : S.Assignment) :
    hedgeNodeXor w.large (fun child => hedgeForestParentBitsFrom rich
      (restrictChild selected w.child) child (fun parent _edge => sample parent)) =
      hedgeNodeXor selected (fun node => hedgeIsSecond rich node (sample node)) := by
  have inLarge := subset.trans (NodeSet.diff_subset_left w.large w.small)
  have wellFormed := childWellFormedBool_restrict_within w.large selected w.child
    w.large_forest.wellFormedBool inLarge
  have incoming := nodeXor_congr w.large _ _ (fun child _inside =>
    hedgeForestParentBitsFrom_eq_routingIncomingBits rich w.large
      (restrictChild selected w.child) wellFormed sample child)
  rw [incoming]
  have masked := nodeXor_congr w.large _ _ (fun child _inside =>
    routingIncoming_restrict selected w.child (fun node => hedgeIsSecond rich node (sample node)) child)
  rw [masked]
  exact hedgeNodeXor_routingIncoming_mask w.large selected w.child w.large_forest.wellFormedBool
    inLarge (fun node chosen => w.channelOuter_no_sinks node (subset node chosen)) _

/-! ## Character of one outer-background expansion term -/

/-- Parent signal for a large-forest channel.  The first correction cancels
all outer bits once globally; the second places the selected outer value
characters at their actual kept children.  The supplied small and background
signals are typed local parent functions, not functions of the whole sample.
The definition is total even for a mask outside the outer forest; only the
factorization theorem requires the mask to be an outer expansion term. -/
def HedgeWitness.channelParentSignal (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (selected : NodeSet S)
    (smallSignal backgroundSignal : (child : Fin S.count) -> S.ParentValues child -> Bool)
    (child : Fin S.count) (parents : S.ParentValues child) : Bool :=
  Bool.xor (if w.small child then smallSignal child parents else false)
    (Bool.xor
      (hedgeForestParentBitsFrom rich (restrictChild (NodeSet.diff w.large w.small) w.child) child parents)
      (Bool.xor (if selected child then backgroundSignal child parents else false)
        (hedgeForestParentBitsFrom rich (restrictChild selected w.child) child parents)))

private theorem cancel_outer (smallValues smallParents outerValues backgroundParents selectedValues : Bool) :
    Bool.xor (Bool.xor smallValues outerValues)
      (Bool.xor smallParents (Bool.xor outerValues (Bool.xor backgroundParents selectedValues))) =
      Bool.xor (Bool.xor smallValues smallParents) (Bool.xor selectedValues backgroundParents) := by
  cases smallValues <;> cases smallParents <;> cases outerValues <;>
    cases backgroundParents <;> cases selectedValues <;> rfl

/-- The character of every large expansion channel is the small character
times precisely its selected outer-background characters (multiplication of
signs is XOR of their Boolean parities).

Unlike the common-replay lemma, this holds for every hedge, every full sample
and arbitrary typed local parent signals.  Responding outer vertices and
incoming routes through those vertices are included.  This supplies the
pointwise sign identity needed by a subsequent finite weighted expansion;
it does not by itself integrate hidden channels or construct positive rows. -/
theorem HedgeWitness.channelCharacter_factorization (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (selected : NodeSet S)
    (subset : NodeSet.Subset selected (NodeSet.diff w.large w.small))
    (smallSignal backgroundSignal : (child : Fin S.count) -> S.ParentValues child -> Bool)
    (sample : S.Assignment) :
    hedgeNodeXor w.large (fun child => Bool.xor (hedgeIsSecond rich child (sample child))
      (w.channelParentSignal rich selected smallSignal backgroundSignal child (fun parent _edge => sample parent))) =
      Bool.xor
        (hedgeNodeXor w.small (fun child => Bool.xor (hedgeIsSecond rich child (sample child))
          (smallSignal child (fun parent _edge => sample parent))))
        (hedgeNodeXor selected (fun child => Bool.xor (hedgeIsSecond rich child (sample child))
          (backgroundSignal child (fun parent _edge => sample parent)))) := by
  let bits := fun child => hedgeIsSecond rich child (sample child)
  let smallParents := fun child => smallSignal child (fun parent _edge => sample parent)
  let backgroundParents := fun child => backgroundSignal child (fun parent _edge => sample parent)
  have selectedInLarge := subset.trans (NodeSet.diff_subset_left w.large w.small)
  change hedgeNodeXor w.large (fun child => Bool.xor (bits child)
    (Bool.xor (if w.small child then smallParents child else false)
      (Bool.xor
        (hedgeForestParentBitsFrom rich (restrictChild (NodeSet.diff w.large w.small) w.child)
          child (fun parent _edge => sample parent))
        (Bool.xor (if selected child then backgroundParents child else false)
          (hedgeForestParentBitsFrom rich (restrictChild selected w.child)
            child (fun parent _edge => sample parent)))))) = _
  rw [nodeXor_xor, nodeXor_xor, nodeXor_xor, nodeXor_xor]
  rw [hedgeNodeXor_mask_of_subset w.small w.large w.small_subset_large,
    hedgeNodeXor_mask_of_subset selected w.large selectedInLarge,
    w.channelParentBits_nodeXor rich (NodeSet.diff w.large w.small) (fun _node chosen => chosen) sample,
    w.channelParentBits_nodeXor rich selected subset sample,
    nodeXor_split_subset w.small w.large w.small_subset_large bits]
  rw [nodeXor_xor, nodeXor_xor]
  exact cancel_outer _ _ _ _ _

end Causality
end Thesis
