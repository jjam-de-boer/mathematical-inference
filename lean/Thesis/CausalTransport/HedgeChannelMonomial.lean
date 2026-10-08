import Thesis.CausalTransport.HedgeChannelLikelihood

namespace Thesis
namespace Causality
namespace HedgeChannelTable

open Probability

/-!
# Grouping actual row-choice monomials by independent channel

The likelihood expansion chooses one background or channel term at each
observed row.  Independence, however, is by hidden channel, not by observed
row: several rows may read the same channel vector.  Applying a one-channel
orthogonality theorem directly to that row product would skip this necessary
change of grouping.

Here each local centre has an arbitrary typed directed-parent signal plus
the channel's incidence at the sources actually declared for that child.
The complete row-choice product is factored into its hidden-independent
coefficient and one incidence character per channel.  The row/channel XOR
interchange counts each chosen row exactly once, without changing actual
source grouping or deleting any interaction term.

The resulting signed-mass identity uses the real pair-root prior.  In
particular a proper nonempty selection of a connected channel cancels the
entire actual monomial, even when the other channel selections are arbitrary.
Forced rows and zero coefficients are retained.  Graph-specific amplitudes,
matching surviving full-channel terms, and an original-query gap remain
subsequent countermodel obligations, not hypotheses silently discharged here.
-/

variable {S : ObservedSignature.{0}}

/-- The observed rows at which one complete expansion choice selects a
given channel.  Equality is the explicit decidable equality of finite indices. -/
def selectedNodes (choice : Fin S.count -> Option (Fin channels)) (channel : Fin channels) : NodeSet S :=
  fun child => decide (choice child = some channel)

/-- A term in the complete likelihood can select a channel only inside
its declared support when the actual local choice lists enforce that support.
Forced rows have only the background choice, irrespective of their tables. -/
theorem selectedNodes_subset_of_mem (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (nodes : Fin channels -> NodeSet S)
    (allowed : forall child channel, channel ∈ (tables child).channels -> nodes channel child = true)
    (target : Fin S.count -> Option Bool) (choice : Fin S.count -> Option (Fin channels))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
      (fun child => (tables child).expansionChoicesUnder (target child))) (channel : Fin channels) :
    NodeSet.Subset (selectedNodes choice channel) (nodes channel) := by
  intro child selected
  have picked : choice child = some channel := of_decide_eq_true selected
  have localMember := FiniteProduct.enumeration_coordinate_mem S.count (fun _ => Option (Fin channels))
    (fun child => (tables child).expansionChoicesUnder (target child)) choice member child
  rw [picked] at localMember
  cases forced : target child with
  | none =>
      change some channel ∈ (tables child).expansionChoicesUnder (target child) at localMember
      rw [forced] at localMember
      rcases List.mem_cons.mp localMember with impossible | mapped
      · cases impossible
      · rcases List.mem_map.mp mapped with ⟨chosen, chosenMember, equal⟩
        have same := Option.some.inj equal
        subst chosen
        exact allowed child channel chosenMember
  | some fixed =>
      change some channel ∈ (tables child).expansionChoicesUnder (target child) at localMember
      rw [forced] at localMember
      have impossible := List.mem_singleton.mp localMember
      cases impossible

/-- A genuine likelihood choice never selects a channel at a forced row.
The source is the actual one-element intervention choice list, not a later
heuristic removal of terms that were still present in the expansion. -/
theorem selectedNodes_forced_false (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (choice : Fin S.count -> Option (Fin channels))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
      (fun child => (tables child).expansionChoicesUnder (target child)))
    (channel : Fin channels) (child : Fin S.count) (value : Bool) (forced : target child = some value) :
    selectedNodes choice channel child = false := by
  have localMember := FiniteProduct.enumeration_coordinate_mem S.count (fun _ => Option (Fin channels))
    (fun child => (tables child).expansionChoicesUnder (target child)) choice member child
  change choice child ∈ (tables child).expansionChoicesUnder (target child) at localMember
  rw [forced] at localMember
  have background := List.mem_singleton.mp localMember
  change decide (choice child = some channel) = false
  rw [background]
  rfl

/-- Regroup a product of row signs into one sign per selected channel.
The local Boolean function is arbitrary; no independence or graph premise
is used in this finite combinatorial identity. -/
theorem selected_character_product (choice : Fin S.count -> Option (Fin channels))
    (bits : Fin S.count -> Fin channels -> Bool) :
    FiniteProduct.iProduct S.count (fun child => match choice child with
      | none => 1
      | some channel => FiniteProbRecord.characterSign (bits child channel)) =
    FiniteProduct.iProduct channels (fun channel => FiniteProbRecord.characterSign
      (hedgeNodeXor (selectedNodes choice channel) (fun child => bits child channel))) := by
  let rowBit := fun child => match choice child with | none => false | some channel => bits child channel
  let entry := fun child channel => if choice child = some channel then bits child channel else false
  have rowSum : forall child, (List.finRange channels).foldl
      (fun total channel => Bool.xor total (entry child channel)) false = rowBit child := by
    intro child
    cases chosen : choice child with
    | none =>
        simp only [rowBit, chosen]
        apply foldl_unchanged
        intro total channel
        have different : (none : Option (Fin channels)) ≠ some channel := by intro equal; cases equal
        simp only [entry, chosen, different, if_false, Bool.xor_false]
    | some selected =>
        simp only [rowBit, chosen]
        have same := foldl_congr
          (fun total channel => Bool.xor total (entry child channel))
          (fun total channel => if channel = selected then Bool.xor total (bits child selected) else total)
          false (List.finRange channels) (by
            intro total channel
            by_cases equal : channel = selected
            · subst channel
              simp only [entry, chosen, if_true]
            · have different : selected ≠ channel := Ne.symm equal
              simp only [entry, chosen, Option.some.injEq, equal, different, if_false, Bool.xor_false])
        exact same.trans (foldl_xor_bit_at channels selected (bits child selected))
  have columnSum : forall channel, (List.finRange S.count).foldl
      (fun total child => Bool.xor total (entry child channel)) false =
      hedgeNodeXor (selectedNodes choice channel) (fun child => bits child channel) := by
    intro channel
    have masked := hedgeNodeXor_mask_of_subset (selectedNodes choice channel) NodeSet.full
      (fun _child _selected => rfl) (fun child => bits child channel)
    rw [hedgeNodeXor, NodeSet.members_full] at masked
    simpa only [NodeSet.enumerated, List.finRange, selectedNodes, decide_eq_true_eq] using masked
  have parity : (List.finRange S.count).foldl (fun total child => Bool.xor total (rowBit child)) false =
      (List.finRange channels).foldl (fun total channel => Bool.xor total
        (hedgeNodeXor (selectedNodes choice channel) (fun child => bits child channel))) false :=
    (foldl_congr _ _ false (List.finRange S.count)
      (fun total child => congrArg (Bool.xor total) (rowSum child).symm)).trans
      ((foldl_xor_swap (List.finRange S.count) (List.finRange channels) entry).trans
        (foldl_congr _ _ false (List.finRange channels)
          (fun total channel => congrArg (Bool.xor total) (columnSum channel))))
  have rowSigns := FiniteProduct.iProduct_congr S.count
    (fun child => match choice child with | none => 1 | some channel => FiniteProbRecord.characterSign (bits child channel))
    (fun child => FiniteProbRecord.characterSign (rowBit child)) (fun child => by
      change (match choice child with | none => 1 | some channel => FiniteProbRecord.characterSign (bits child channel)) =
        FiniteProbRecord.characterSign (match choice child with | none => false | some channel => bits child channel)
      cases choice child <;> rfl)
  exact rowSigns.trans ((FiniteProduct.iProduct_characterSign S.count rowBit).trans
    ((congrArg FiniteProbRecord.characterSign parity).trans (FiniteProduct.iProduct_characterSign channels _).symm))

/-- Install each channel's local incidence using only that child's actual
typed shared inputs.  Parent signals may read arbitrary declared parents,
including routes that leave and later re-enter the designated component. -/
def incidenceSignals (G : ObservedGraph S) (channels : Nat) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool) : Signals G channels :=
  fun child parents inputs channel => Bool.xor (parentSignal child parents channel)
    (PairRootChannels.inputIncidence G.binary channels (nodes channel) child inputs channel)

/-- Fixed coefficient of a complete row choice.  Free background capacities,
free channel amplitudes and forced consistency indicators are all retained. -/
def choiceCoefficient (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels)) : Int :=
  FiniteProduct.iProduct S.count (fun child => (tables child).expansionCoefficientUnder
    (target child) (sample child) (choice child))

/-- The observed/parent phase at precisely the rows selecting a channel.
It is independent of all hidden channel bits but uses actual parent labels. -/
def choicePhase (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin channels)) (channel : Fin channels) : Bool :=
  hedgeNodeXor (selectedNodes choice channel) (fun child => Bool.xor (sample child)
    (parentSignal child (fun parent _edge => sample parent) channel))

/-- The exact row-choice monomial appearing in `expandedIntegral_eq_sum`.
This is an actual table expansion term, not an assumed character surrogate. -/
def choiceMonomial (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (shared : (PairRootChannels.extension G.binary channels).Assignment) : Int :=
  FiniteProduct.iProduct S.count (fun child => (tables child).expansionTermUnder
    (signals child (fun parent _edge => sample parent) (fun root _incident => shared root))
    (target child) (sample child) (choice child))

/-- One incidence character per channel after grouping the exact row
choice.  Its phase includes only the rows that chose that same channel. -/
def choiceCharacter (G : ObservedGraph S) (channels : Nat) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin channels))
    (shared : (PairRootChannels.extension G.binary channels).Assignment) : Int :=
  FiniteProduct.iProduct channels (fun channel => FiniteProbRecord.characterSign
    (Bool.xor (choicePhase parentSignal sample choice channel)
      (hedgeChannelIncidenceParity G.binary (nodes channel) (selectedNodes choice channel)
        (fun root => shared root channel))))

/-- The actual whole row-choice term is its complete fixed coefficient
times its grouped channel character.  This identity is total on choices:
unsupported forced channel choices are retained with coefficient zero. -/
theorem choiceMonomial_factorization (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (shared : (PairRootChannels.extension G.binary channels).Assignment) :
    choiceMonomial G channels tables (incidenceSignals G channels nodes parentSignal) target sample choice shared =
      choiceCoefficient tables target sample choice * choiceCharacter G channels nodes parentSignal sample choice shared := by
  let centres := fun child => incidenceSignals G channels nodes parentSignal child
    (fun parent _edge => sample parent) (fun root _incident => shared root)
  let coefficients := fun child => (tables child).expansionCoefficientUnder (target child) (sample child) (choice child)
  let signs := fun child => match choice child with
    | none => 1
    | some channel => FiniteProbRecord.characterSign (Bool.xor (sample child) (centres child channel))
  have expanded := FiniteProduct.iProduct_congr S.count
    (fun child => (tables child).expansionTermUnder (centres child) (target child) (sample child) (choice child))
    (fun child => coefficients child * signs child)
    (fun child => by
      dsimp only [coefficients, signs]
      cases chosen : choice child <;>
        simpa only [chosen] using (tables child).expansionTermUnder_eq_coefficient_mul
          (centres child) (target child) (sample child) (choice child))
  have separated := FiniteProduct.iProduct_mul S.count coefficients signs
  have grouped := selected_character_product choice (fun child channel => Bool.xor (sample child) (centres child channel))
  have phases : forall channel,
      hedgeNodeXor (selectedNodes choice channel) (fun child => Bool.xor (sample child) (centres child channel)) =
      Bool.xor (choicePhase parentSignal sample choice channel)
        (hedgeChannelIncidenceParity G.binary (nodes channel) (selectedNodes choice channel)
          (fun root => shared root channel)) := by
    intro channel
    have localParity : forall child, Bool.xor (sample child) (centres child channel) =
        Bool.xor (Bool.xor (sample child) (parentSignal child (fun parent _edge => sample parent) channel))
          (hedgeXorPairBitsWithinFrom G.binary (nodes channel) child (fun root => shared root channel)) := by
      intro child
      change Bool.xor (sample child) (Bool.xor (parentSignal child (fun parent _edge => sample parent) channel)
        (PairRootChannels.inputIncidence G.binary channels (nodes channel) child (fun root _incident => shared root) channel)) = _
      rw [PairRootChannels.inputIncidence_assignment]
      exact (Bool.xor_assoc _ _ _).symm
    exact (foldl_congr _ _ false (NodeSet.members (selectedNodes choice channel))
      (fun total child => congrArg (Bool.xor total) (localParity child))).trans
      (foldl_xor_pointwise
        (fun child => Bool.xor (sample child) (parentSignal child (fun parent _edge => sample parent) channel))
        (fun child => hedgeXorPairBitsWithinFrom G.binary (nodes channel) child (fun root => shared root channel))
        (NodeSet.members (selectedNodes choice channel)))
  have character := grouped.trans (FiniteProduct.iProduct_congr channels _ _
    (fun channel => congrArg FiniteProbRecord.characterSign (phases channel)))
  exact expanded.trans (separated.trans (congrArg (choiceCoefficient tables target sample choice * ·) character))

/-- Pull the exact fixed row coefficient outside integration on the real
pair-root record.  Neither a row cell nor a possibly zero coefficient is
cancelled, and the remaining integrand still contains every channel. -/
theorem choiceMonomial_signedMass_coefficient (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels)) :
    (PairRootChannels.prior G.binary channels).signedMass
      (choiceMonomial G channels tables (incidenceSignals G channels nodes parentSignal) target sample choice) =
      choiceCoefficient tables target sample choice * (PairRootChannels.prior G.binary channels).signedMass
        (choiceCharacter G channels nodes parentSignal sample choice) :=
  (FiniteProbRecord.signedAtomMass_congr (PairRootChannels.prior G.binary channels).atoms _ _
    (choiceMonomial_factorization G channels tables nodes parentSignal target sample choice)).trans
    ((PairRootChannels.prior G.binary channels).signedMass_mul_left _ _)

/-- Exact independent-channel factorization of an actual row monomial's
integral.  Arbitrary row selections and components are retained; connectedness
is needed only when a selected channel is subsequently proved to cancel. -/
theorem choiceMonomial_signedMass (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels)) :
    (PairRootChannels.prior G.binary channels).signedMass
      (choiceMonomial G channels tables (incidenceSignals G channels nodes parentSignal) target sample choice) =
      choiceCoefficient tables target sample choice * FiniteProduct.iProduct channels
        (fun channel => (hedgeChannelPairBitRecord G.binary).signedMass (fun bits => FiniteProbRecord.characterSign
          (Bool.xor (choicePhase parentSignal sample choice channel)
            (hedgeChannelIncidenceParity G.binary (nodes channel) (selectedNodes choice channel) bits)))) :=
  (choiceMonomial_signedMass_coefficient G channels tables nodes parentSignal target sample choice).trans
    (congrArg (choiceCoefficient tables target sample choice * ·)
      (PairRootChannels.prior_character_signedMass G.binary channels nodes (selectedNodes choice)
        (choicePhase parentSignal sample choice)))

/-- A proper nonempty connected channel cancels the whole actual table
monomial.  Other channel selections, row coefficients and forced cells are
arbitrary; the conclusion concerns the same term in the full likelihood. -/
theorem choiceMonomial_signedMass_zero (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels)) (chosen : Fin channels)
    (component : BidirectedComponent G.binary (nodes chosen))
    (subset : NodeSet.Subset (selectedNodes choice chosen) (nodes chosen))
    (balance : Fin S.count) (inside : nodes chosen balance = true) (excluded : selectedNodes choice chosen balance = false)
    (pivot : Fin S.count) (selected : selectedNodes choice chosen pivot = true) :
    (PairRootChannels.prior G.binary channels).signedMass
      (choiceMonomial G channels tables (incidenceSignals G channels nodes parentSignal) target sample choice) = 0 :=
  (choiceMonomial_signedMass_coefficient G channels tables nodes parentSignal target sample choice).trans
    ((congrArg (choiceCoefficient tables target sample choice * ·)
      (PairRootChannels.prior_character_signedMass_zero G.binary channels nodes (selectedNodes choice)
        (choicePhase parentSignal sample choice) chosen component subset balance inside excluded pivot selected)).trans
      (Int.mul_zero _))

/-- Cutting any row of a connected channel kills every genuine term that
selects that channel somewhere else.  This is the general action-cut step:
the cut need not be a sink, unique action vertex, or protected route point. -/
theorem choiceMonomial_signedMass_zero_of_forced (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (allowed : forall child channel, channel ∈ (tables child).channels -> nodes channel child = true)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
      (fun child => (tables child).expansionChoicesUnder (target child)))
    (chosen : Fin channels) (component : BidirectedComponent G.binary (nodes chosen))
    (cutRow : Fin S.count) (inside : nodes chosen cutRow = true)
    (fixed : Bool) (forced : target cutRow = some fixed)
    (pivot : Fin S.count) (picked : choice pivot = some chosen) :
    (PairRootChannels.prior G.binary channels).signedMass
      (choiceMonomial G channels tables (incidenceSignals G channels nodes parentSignal) target sample choice) = 0 := by
  apply choiceMonomial_signedMass_zero G channels tables nodes parentSignal target sample choice chosen component
    (selectedNodes_subset_of_mem tables nodes allowed target choice member chosen) cutRow inside
    (selectedNodes_forced_false tables target choice member chosen cutRow fixed forced) pivot
  change decide (choice pivot = some chosen) = true
  exact decide_eq_true picked

/-- Any selected connected channel in a nonzero actual likelihood term
must be selected at every vertex of its support.  Local-list membership
provides the subset premise, and each missing vertex would give the explicit
proper-subset cancellation just proved.  Only finite Boolean cases are used. -/
theorem choiceMonomial_nonzero_full (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (allowed : forall child channel, channel ∈ (tables child).channels -> nodes channel child = true)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
      (fun child => (tables child).expansionChoicesUnder (target child)))
    (nonzero : (PairRootChannels.prior G.binary channels).signedMass
      (choiceMonomial G channels tables (incidenceSignals G channels nodes parentSignal) target sample choice) ≠ 0)
    (chosen : Fin channels) (component : BidirectedComponent G.binary (nodes chosen))
    (pivot : Fin S.count) (picked : choice pivot = some chosen) : selectedNodes choice chosen = nodes chosen := by
  have subset := selectedNodes_subset_of_mem tables nodes allowed target choice member chosen
  have selected : selectedNodes choice chosen pivot = true := by
    change decide (choice pivot = some chosen) = true
    exact decide_eq_true picked
  funext balance
  cases inside : nodes chosen balance with
  | false =>
      cases tested : selectedNodes choice chosen balance with
      | false => rfl
      | true => have contradiction := subset balance tested; rw [inside] at contradiction; cases contradiction
  | true =>
      cases tested : selectedNodes choice chosen balance with
      | true => rfl
      | false => exact False.elim (nonzero (choiceMonomial_signedMass_zero G channels tables nodes parentSignal
          target sample choice chosen component subset balance inside tested pivot selected))

/-- Two fully selected channels sharing a vertex must be the same channel:
a row choice has only one channel slot.  This is the finite overlap reason
that two large channels, or a large and nested small channel, cannot survive
simultaneously in the intended countermodel expansion. -/
theorem selectedNodes_full_unique (nodes : Fin channels -> NodeSet S)
    (choice : Fin S.count -> Option (Fin channels)) (left right : Fin channels)
    (pivot : Fin S.count) (leftInside : nodes left pivot = true) (rightInside : nodes right pivot = true)
    (leftFull : selectedNodes choice left = nodes left) (rightFull : selectedNodes choice right = nodes right) : left = right := by
  have leftSelected : selectedNodes choice left pivot = true := by rw [leftFull]; exact leftInside
  have rightSelected : selectedNodes choice right pivot = true := by rw [rightFull]; exact rightInside
  have leftPick : choice pivot = some left := of_decide_eq_true leftSelected
  have rightPick : choice pivot = some right := of_decide_eq_true rightSelected
  exact Option.some.inj (leftPick.symm.trans rightPick)

/-- When every connected channel shares one pivot, every nonzero term
selects at most one distinct channel.  This rules out surviving mixed-channel
interactions by the actual integration theorem, not by omitting them from
the complete row expansion.  Background-only choices are still possible. -/
theorem choiceMonomial_nonzero_single_channel (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (allowed : forall child channel, channel ∈ (tables child).channels -> nodes channel child = true)
    (components : forall channel, BidirectedComponent G.binary (nodes channel))
    (pivot : Fin S.count) (common : forall channel, nodes channel pivot = true)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
      (fun child => (tables child).expansionChoicesUnder (target child)))
    (nonzero : (PairRootChannels.prior G.binary channels).signedMass
      (choiceMonomial G channels tables (incidenceSignals G channels nodes parentSignal) target sample choice) ≠ 0)
    (left right : Fin channels) (leftRow rightRow : Fin S.count)
    (leftPick : choice leftRow = some left) (rightPick : choice rightRow = some right) : left = right :=
  selectedNodes_full_unique nodes choice left right pivot (common left) (common right)
    (choiceMonomial_nonzero_full G channels tables nodes parentSignal allowed target sample choice member nonzero
      left (components left) leftRow leftPick)
    (choiceMonomial_nonzero_full G channels tables nodes parentSignal allowed target sample choice member nonzero
      right (components right) rightRow rightPick)

/-- Complete actual likelihood numerator expanded by independent channel,
not by a row-wise independence assumption.  Every full row choice appears
with its exact coefficient and its actual one-channel integrals. -/
theorem integratedNumerator_channelExpansion (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (nodes : Fin channels -> NodeSet S)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    (integratedNumerator G channels tables (incidenceSignals G channels nodes parentSignal) target sample : Int) =
      ((FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
        (fun child => (tables child).expansionChoicesUnder (target child))).map fun choice =>
          choiceCoefficient tables target sample choice * FiniteProduct.iProduct channels
            (fun channel => (hedgeChannelPairBitRecord G.binary).signedMass (fun bits => FiniteProbRecord.characterSign
              (Bool.xor (choicePhase parentSignal sample choice channel)
                (hedgeChannelIncidenceParity G.binary (nodes channel) (selectedNodes choice channel) bits))))).sum := by
  refine (integratedNumerator_expansion G channels tables (incidenceSignals G channels nodes parentSignal) target sample).trans
    ((expandedIntegral_eq_sum G channels tables (incidenceSignals G channels nodes parentSignal) target sample).trans ?_)
  apply congrArg List.sum
  apply List.map_congr_left
  intro choice _member
  exact choiceMonomial_signedMass G channels tables nodes parentSignal target sample choice

end HedgeChannelTable
end Causality
end Thesis
