import Thesis.CausalTransport.HedgeChannelSurvivors

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Exact full-channel integrals in the installed hedge models

The survivor reduction still refers to actual monomial integrals.  To match
their coefficients and phases, those integrals must be evaluated on the same
root-major prior, rather than replaced by a proposed likelihood polynomial.

A full forest character has even pair incidence for every shared assignment.
Every singleton background has no internal pair root at all.  Consequently a
canonical full choice is pointwise independent of the shared bits after its
row signs are multiplied.  Integration retains the entire literal prior mass,
including every inactive channel slot, times its actual row coefficient and
its observed/parent character.  No probability denominator is cancelled.
The identity holds under arbitrary hard interventions as well: forced-row
indicators and unsupported forced-channel zeros remain in that coefficient.
The original factual theorem is preserved as its `none`-target specialization.

The installed large parent correction then gives the small character times
the selected outer background character.  Backgrounds outside the large
forest remain present independently.  This supplies the actual full-term
phases needed by coefficient matching.  Literal coefficient evaluation and
reindexing the surviving sums are separate steps toward the universal
observational equality, not premises hidden in the phase identities.
The original-outcome gap and universal conditional countermodels remain open.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Singleton backgrounds and full-forest incidence -/

private theorem singleton_pair_off (G : ObservedGraph S) (node : Fin S.count) (root : Fin (pairRootCount G)) :
    hedgePairRootWithin G (NodeSet.singleton node) root = false := by
  cases selected : hedgePairRootWithin G (NodeSet.singleton node) root with
  | false => rfl
  | true =>
      have endpoints := Bool.and_eq_true_iff.mp selected
      have first := (NodeSet.singleton_eq_true_iff node _).mp endpoints.1
      have second := (NodeSet.singleton_eq_true_iff node _).mp endpoints.2
      have ordered := ((mem_pairRoots G _ _).mp (List.get_mem (pairRoots G) root)).1
      rw [first, second] at ordered
      exact False.elim (Nat.lt_irrefl _ ordered)

/-- An actual singleton background has no internal shared source.  This
holds at every receiving child, not just at the singleton's own row. -/
theorem singletonIncidence_zero (G : ObservedGraph S) (node child : Fin S.count)
    (bits : Fin (pairRootCount G) -> Bool) :
    hedgeXorPairBitsWithinFrom G (NodeSet.singleton node) child bits = false := by
  unfold hedgeXorPairBitsWithinFrom
  apply foldl_unchanged
  intro total root
  simp only [singleton_pair_off, Bool.and_false, Bool.false_eq_true, if_false]

private theorem backgroundIncidence_zero (w : HedgeWitness G q) (node child : Fin S.count)
    (bits : Fin (pairRootCount G.binary) -> Bool) :
    hedgeXorPairBitsWithinFrom G.binary (@backgroundNodes S G q w node) child bits = false := by
  cases inside : w.small node with
  | false =>
      simpa only [backgroundNodes, inside, Bool.false_eq_true, if_false] using
        singletonIncidence_zero G.binary node child bits
  | true =>
      simp only [backgroundNodes, inside, if_true]
      exact hedgeXorPairBitsWithinFrom_of_child_outside G.binary NodeSet.empty bits child rfl

/-- The observed/parent parity of a supplied local signal over a node set.
The signal itself remains typed and cannot read unavailable coordinates. -/
def signalPhase (nodes : NodeSet S) (signal : ParentSignal S) (sample : S.binary.Assignment) : Bool :=
  hedgeNodeXor nodes (fun child => Bool.xor (sample child) (signal child (fun parent _edge => sample parent)))

/-- A disjoint union of background selections has the XOR of their two
phases, irrespective of how their vertices interleave in topological order.
Disjointness is essential: a selected row must not be counted twice. -/
theorem signalPhase_union_of_disjoint (left right : NodeSet S) (disjoint : NodeSet.Disjoint left right)
    (signal : ParentSignal S) (sample : S.binary.Assignment) :
    signalPhase (NodeSet.union left right) signal sample =
      Bool.xor (signalPhase left signal sample) (signalPhase right signal sample) := by
  let bits := fun child => Bool.xor (sample child) (signal child (fun parent _edge => sample parent))
  have split : forall child,
      (if NodeSet.union left right child then bits child else false) =
        Bool.xor (if left child then bits child else false) (if right child then bits child else false) := by
    intro child
    cases selected : left child with
    | true => simp only [NodeSet.union, selected, disjoint child selected, Bool.true_or,
        if_true, Bool.false_eq_true, if_false, Bool.xor_false]
    | false => cases other : right child <;> simp only [NodeSet.union, selected, other,
        Bool.false_or, Bool.false_eq_true, if_false, if_true, Bool.false_xor]
  have separated := (foldl_congr _ _ false (NodeSet.members (NodeSet.full : NodeSet S))
    (fun total child => congrArg (Bool.xor total) (split child))).trans
    (foldl_xor_pointwise (fun child => if left child then bits child else false)
      (fun child => if right child then bits child else false) (NodeSet.members (NodeSet.full : NodeSet S)))
  change hedgeNodeXor (NodeSet.full : NodeSet S)
      (fun child => if NodeSet.union left right child then bits child else false) =
    Bool.xor (hedgeNodeXor (NodeSet.full : NodeSet S) (fun child => if left child then bits child else false))
      (hedgeNodeXor (NodeSet.full : NodeSet S) (fun child => if right child then bits child else false)) at separated
  rw [hedgeNodeXor_mask_of_subset (NodeSet.union left right) NodeSet.full (fun _ _ => rfl),
    hedgeNodeXor_mask_of_subset left NodeSet.full (fun _ _ => rfl),
    hedgeNodeXor_mask_of_subset right NodeSet.full (fun _ _ => rfl)] at separated
  exact separated

private def rowBits (w : HedgeWitness G q) (signals : HedgeChannelTable.Signals G (channelCount w))
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (shared : (PairRootChannels.extension G.binary (channelCount w)).Assignment) (child : Fin S.count) : Bool :=
  match choice child with
  | none => false
  | some channel => Bool.xor (sample child)
      (signals child (fun parent _edge => sample parent) (fun root _incident => shared root) channel)

private theorem fullChoice_rowParity (w : HedgeWitness G q) (nodes : Fin (channelCount w) -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin (channelCount w) -> Bool)
    (backgroundSignal : ParentSignal S)
    (backgroundSupport : forall child, nodes (backgroundChannel w child) = backgroundNodes w child)
    (backgroundParents : forall child parents, parentSignal child parents (backgroundChannel w child) = backgroundSignal child parents)
    (forest : NodeSet S) (channel : Fin (channelCount w)) (support : nodes channel = forest)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside forest)) (sample : S.binary.Assignment)
    (shared : (PairRootChannels.extension G.binary (channelCount w)).Assignment) :
    hedgeNodeXor (NodeSet.full : NodeSet S)
      (rowBits w (HedgeChannelTable.incidenceSignals G (channelCount w) nodes parentSignal)
        sample (fullChoice w forest channel mask) shared) =
      Bool.xor (signalPhase forest (fun child parents => parentSignal child parents channel) sample)
        (signalPhase mask backgroundSignal sample) := by
  let mainBits := fun child => Bool.xor (sample child)
    (Bool.xor (parentSignal child (fun parent _edge => sample parent) channel)
      (hedgeXorPairBitsWithinFrom G.binary forest child (fun root => shared root channel)))
  let backgroundBits := fun child => Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent))
  have split : forall child,
      rowBits w (HedgeChannelTable.incidenceSignals G (channelCount w) nodes parentSignal)
        sample (fullChoice w forest channel mask) shared child =
      Bool.xor (if forest child then mainBits child else false)
        (if mask child then backgroundBits child else false) := by
    intro child
    cases inside : forest child with
    | true =>
        have absent : mask child = false := by
          cases selected : mask child with
          | false => rfl
          | true =>
              have outsideSelected := subset child selected
              unfold outside NodeSet.diff NodeSet.full at outsideSelected
              have off := (Bool.and_eq_true_iff.mp outsideSelected).2
              rw [inside] at off
              cases off
        simp only [rowBits, fullChoice, inside, if_true, absent, Bool.false_eq_true, if_false,
          Bool.xor_false, HedgeChannelTable.incidenceSignals, mainBits]
        rw [PairRootChannels.inputIncidence_assignment, support]
    | false =>
        cases selected : mask child with
        | false => simp only [rowBits, fullChoice, backgroundChoice, inside, selected, Bool.false_eq_true,
            if_false, Bool.xor_false]
        | true =>
            simp only [rowBits, fullChoice, backgroundChoice, inside, selected, Bool.false_eq_true,
              if_false, if_true, Bool.false_xor, HedgeChannelTable.incidenceSignals, backgroundBits]
            rw [PairRootChannels.inputIncidence_assignment, backgroundSupport, backgroundParents,
              backgroundIncidence_zero, Bool.xor_false]
  have separated := (foldl_congr _ _ false (NodeSet.members (NodeSet.full : NodeSet S))
    (fun total child => congrArg (Bool.xor total) (split child))).trans
    (foldl_xor_pointwise _ _ (NodeSet.members (NodeSet.full : NodeSet S)))
  change hedgeNodeXor (NodeSet.full : NodeSet S)
      (rowBits w (HedgeChannelTable.incidenceSignals G (channelCount w) nodes parentSignal)
        sample (fullChoice w forest channel mask) shared) =
      Bool.xor (hedgeNodeXor (NodeSet.full : NodeSet S) (fun child => if forest child then mainBits child else false))
        (hedgeNodeXor (NodeSet.full : NodeSet S) (fun child => if mask child then backgroundBits child else false)) at separated
  rw [hedgeNodeXor_mask_of_subset forest NodeSet.full (fun _ _ => rfl),
    hedgeNodeXor_mask_of_subset mask NodeSet.full (fun _ _ => rfl)] at separated
  have mainParity := foldl_xor_pointwise
    (fun child => Bool.xor (sample child) (parentSignal child (fun parent _edge => sample parent) channel))
    (fun child => hedgeXorPairBitsWithinFrom G.binary forest child (fun root => shared root channel))
    (NodeSet.members forest)
  have localParity : hedgeNodeXor forest mainBits =
      signalPhase forest (fun child parents => parentSignal child parents channel) sample := by
    have reassociated := foldl_congr _ _ false (NodeSet.members forest) (fun total child =>
      congrArg (Bool.xor total) (Bool.xor_assoc (sample child)
        (parentSignal child (fun parent _edge => sample parent) channel)
        (hedgeXorPairBitsWithinFrom G.binary forest child (fun root => shared root channel))).symm)
    have parity := reassociated.trans mainParity
    change hedgeNodeXor forest mainBits = Bool.xor
      (signalPhase forest (fun child parents => parentSignal child parents channel) sample)
      (hedgeNodeXor forest (fun child => hedgeXorPairBitsWithinFrom G.binary forest child (fun root => shared root channel))) at parity
    have even : hedgeNodeXor forest (fun child =>
        hedgeXorPairBitsWithinFrom G.binary forest child (fun root => shared root channel)) = false :=
      hedgeNodeXor_incidence G.binary forest (fun root => shared root channel)
    rw [even, Bool.xor_false] at parity
    exact parity
  rw [localParity] at separated
  exact separated

/-! ## Actual shared-prior normalization of one full term -/

private theorem monomial_rowFactors_under (w : HedgeWitness G q)
    (tables : Fin S.count -> BooleanChannelTable (Fin (channelCount w)))
    (signals : HedgeChannelTable.Signals G (channelCount w))
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (shared : (PairRootChannels.extension G.binary (channelCount w)).Assignment) :
    HedgeChannelTable.choiceMonomial G (channelCount w) tables signals target sample choice shared =
      HedgeChannelTable.choiceCoefficient tables target sample choice *
        FiniteProbRecord.characterSign (hedgeNodeXor (NodeSet.full : NodeSet S) (rowBits w signals sample choice shared)) := by
  have expanded : HedgeChannelTable.choiceMonomial G (channelCount w) tables signals target sample choice shared =
      HedgeChannelTable.choiceCoefficient tables target sample choice *
        FiniteProduct.iProduct S.count (fun child => FiniteProbRecord.characterSign (rowBits w signals sample choice shared child)) := by
    refine Eq.trans (b := FiniteProduct.iProduct S.count (fun child =>
      (tables child).expansionCoefficientUnder (target child) (sample child) (choice child) *
        FiniteProbRecord.characterSign (rowBits w signals sample choice shared child))) ?_ ?_
    · apply FiniteProduct.iProduct_congr
      intro child
      have localTerm := (tables child).expansionTermUnder_eq_coefficient_mul
        (signals child (fun parent _edge => sample parent) (fun root _incident => shared root)) (target child) (sample child) (choice child)
      cases picked : choice child with
      | none => simpa only [picked, rowBits, FiniteProbRecord.characterSign, Bool.false_eq_true, if_false, Int.mul_one] using localTerm
      | some channel => simpa only [picked, rowBits] using localTerm
    · exact FiniteProduct.iProduct_mul S.count _ _
  have parity : FiniteProduct.iProduct S.count (fun child => FiniteProbRecord.characterSign (rowBits w signals sample choice shared child)) =
      FiniteProbRecord.characterSign (hedgeNodeXor (NodeSet.full : NodeSet S) (rowBits w signals sample choice shared)) := by
    simpa only [hedgeNodeXor, NodeSet.members_full, NodeSet.enumerated, List.finRange] using
      FiniteProduct.iProduct_characterSign S.count (rowBits w signals sample choice shared)
  exact expanded.trans (congrArg (HedgeChannelTable.choiceCoefficient tables target sample choice * ·) parity)

/-- Full forest and background row signs remove shared-input dependence
pointwise under any hard intervention.  Forced indicators, including zero
coefficients at unsupported forced-channel choices, remain in the actual
coefficient.  Integration retains the prior's entire literal mass, including
inactive slots; its factors are not independently renormalized. -/
theorem fullChoice_signedMass_under (w : HedgeWitness G q)
    (tables : Fin S.count -> BooleanChannelTable (Fin (channelCount w)))
    (nodes : Fin (channelCount w) -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin (channelCount w) -> Bool)
    (backgroundSignal : ParentSignal S)
    (backgroundSupport : forall child, nodes (backgroundChannel w child) = backgroundNodes w child)
    (backgroundParents : forall child parents, parentSignal child parents (backgroundChannel w child) = backgroundSignal child parents)
    (forest : NodeSet S) (channel : Fin (channelCount w)) (support : nodes channel = forest)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside forest))
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    (PairRootChannels.prior G.binary (channelCount w)).signedMass
      (HedgeChannelTable.choiceMonomial G (channelCount w) tables
        (HedgeChannelTable.incidenceSignals G (channelCount w) nodes parentSignal)
        target sample (fullChoice w forest channel mask)) =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        HedgeChannelTable.choiceCoefficient tables target sample (fullChoice w forest channel mask) *
        FiniteProbRecord.characterSign
          (Bool.xor (signalPhase forest (fun child parents => parentSignal child parents channel) sample)
            (signalPhase mask backgroundSignal sample)) := by
  have constant := FiniteProbRecord.signedAtomMass_congr (PairRootChannels.prior G.binary (channelCount w)).atoms _ _
    (fun shared => (monomial_rowFactors_under w tables _ target sample (fullChoice w forest channel mask) shared).trans
      (congrArg (HedgeChannelTable.choiceCoefficient tables target sample (fullChoice w forest channel mask) * ·)
        (congrArg FiniteProbRecord.characterSign
          (fullChoice_rowParity w nodes parentSignal backgroundSignal backgroundSupport backgroundParents forest channel support
            mask subset sample shared))))
  exact constant.trans (((PairRootChannels.prior G.binary (channelCount w)).signedMass_const _).trans
    (Int.mul_assoc _ _ _).symm)

/-- Factual specialization of the intervention-aware full-term identity.
The original API and its literal normalization are retained unchanged. -/
theorem fullChoice_signedMass (w : HedgeWitness G q)
    (tables : Fin S.count -> BooleanChannelTable (Fin (channelCount w)))
    (nodes : Fin (channelCount w) -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin (channelCount w) -> Bool)
    (backgroundSignal : ParentSignal S)
    (backgroundSupport : forall child, nodes (backgroundChannel w child) = backgroundNodes w child)
    (backgroundParents : forall child parents, parentSignal child parents (backgroundChannel w child) = backgroundSignal child parents)
    (forest : NodeSet S) (channel : Fin (channelCount w)) (support : nodes channel = forest)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside forest)) (sample : S.binary.Assignment) :
    (PairRootChannels.prior G.binary (channelCount w)).signedMass
      (HedgeChannelTable.choiceMonomial G (channelCount w) tables
        (HedgeChannelTable.incidenceSignals G (channelCount w) nodes parentSignal)
        (fun _ => none) sample (fullChoice w forest channel mask)) =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        HedgeChannelTable.choiceCoefficient tables (fun _ => none) sample (fullChoice w forest channel mask) *
        FiniteProbRecord.characterSign
          (Bool.xor (signalPhase forest (fun child parents => parentSignal child parents channel) sample)
            (signalPhase mask backgroundSignal sample)) :=
  fullChoice_signedMass_under w tables nodes parentSignal backgroundSignal backgroundSupport backgroundParents
    forest channel support mask subset (fun _ => none) sample

/-- The actual large full term has the small character, its selected outer
background character, and its independent outside-large background mask.
Its coefficient remains the literal installed row product, not an assumed
abstract power. -/
theorem left_fullTermIntegral (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment)
    (index : Fin (masks (outer w)).length) (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large)) :
    leftTermIntegral w rich smallSignal backgroundSignal sample (fullChoice w w.large (largeChannel w index) mask) =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        HedgeChannelTable.choiceCoefficient (leftTables w) (fun _ => none) sample
          (fullChoice w w.large (largeChannel w index) mask) *
        FiniteProbRecord.characterSign (Bool.xor
          (Bool.xor (signalPhase w.small smallSignal sample) (signalPhase (selected w index) backgroundSignal sample))
          (signalPhase mask backgroundSignal sample)) := by
  have evaluated := fullChoice_signedMass w (leftTables w) (leftNodes w)
    (leftParentSignal w rich smallSignal backgroundSignal) backgroundSignal
    (by intro child; rw [leftNodes, role_backgroundChannel])
    (by intro child parents; rw [leftParentSignal, role_backgroundChannel])
    w.large (largeChannel w index) (leftNodes_largeChannel w index) mask subset sample
  have phase : signalPhase w.large (fun child parents =>
      leftParentSignal w rich smallSignal backgroundSignal child parents (largeChannel w index)) sample =
      Bool.xor (signalPhase w.small smallSignal sample) (signalPhase (selected w index) backgroundSignal sample) := by
    simp only [signalPhase, leftParentSignal, role_largeChannel]
    exact largeParentSignal_factorization w rich smallSignal backgroundSignal index sample
  rw [phase] at evaluated
  exact evaluated

/-- The actual small full term has the same small character and all its
outside-small backgrounds, retaining the same actual prior normalization. -/
theorem right_fullTermIntegral (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal S)
    (sample : S.binary.Assignment) (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) :
    rightTermIntegral w smallSignal backgroundSignal sample (fullChoice w w.small (smallChannel w) mask) =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        HedgeChannelTable.choiceCoefficient (rightTables w) (fun _ => none) sample (fullChoice w w.small (smallChannel w) mask) *
        FiniteProbRecord.characterSign (Bool.xor (signalPhase w.small smallSignal sample) (signalPhase mask backgroundSignal sample)) := by
  have evaluated := fullChoice_signedMass w (rightTables w) (rightNodes w)
    (rightParentSignal w smallSignal backgroundSignal) backgroundSignal
    (by intro child; rw [rightNodes, role_backgroundChannel])
    (by intro child parents; rw [rightParentSignal, role_backgroundChannel])
    w.small (smallChannel w) (rightNodes_smallChannel w) mask subset sample
  simpa only [signalPhase, rightParentSignal, role_smallChannel] using evaluated

end HedgeChannelInstallation
end Causality
end Thesis
