import Thesis.Causality.IdentificationKernel
import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

/-!
# Structural progress of current-kernel ID

The replacement recursion adds the published algorithm's action-augmentation
branch.  Its termination argument therefore cannot be borrowed unchanged
from the older engine: augmentation keeps the host fixed but removes free
vertices, and can change the number of free c-components.

The rank below counts host size, free size, and a one-bit product bonus.
A strict host decrease dominates every possible gain in the free-size term.
A strict free-size decrease dominates a possible new product bonus.
A product call keeps the host and selects one free c-component; it never
increases free size and consumes the product bonus.  This gives one uniform
argument for arbitrary nesting, without enumerating branch-name stacks.

Only general graph and finite-list facts are reused from `Completeness`.
No soundness theorem, completeness package, or semantic assumption is used
to establish progress of the corrected program.
-/

/-! ## Finite cardinality bounds and the current-kernel rank -/

/-- Filtering the signature's enumeration cannot introduce more vertices. -/
private theorem kernelMembers_length_le_count (nodes : NodeSet S) :
    (NodeSet.members nodes).length ≤ S.count := by
  have shorter := NodeSet.length_filter_le nodes (NodeSet.enumerated S)
  simpa only [NodeSet.members, NodeSet.length_enumerated] using shorter

/-- Inclusion of Boolean selections is inclusion of their finite member
lists, with their inherited topological order preserved. -/
private theorem kernelMembers_length_le_of_subset {smaller larger : NodeSet S}
    (subset : NodeSet.Subset smaller larger) :
    (NodeSet.members smaller).length ≤ (NodeSet.members larger).length := by
  calc
    (NodeSet.members smaller).length =
        (NodeSet.members (NodeSet.inter larger smaller)).length :=
      congrArg (fun nodes => (NodeSet.members nodes).length)
        (NodeSet.inter_eq_of_subset subset).symm
    _ = ((NodeSet.members larger).filter smaller).length :=
      congrArg List.length (NodeSet.members_inter larger smaller)
    _ ≤ (NodeSet.members larger).length := NodeSet.length_filter_le _ _

/-- Rank of a replacement-engine invocation.  The reused graph-only rank
contributes `2 * |remaining|` and the product bonus; the other two terms make
host and action progress strong enough for the corrected recursion. -/
def kernelIdentificationRank (G : ObservedGraph S)
    (remaining action : NodeSet S) : Nat :=
  2 * S.count * (NodeSet.members remaining).length +
    identificationTraceRank G remaining action +
    2 * (NodeSet.members
      (NodeSet.diff remaining (NodeSet.inter action remaining))).length

/-- Every proper host restriction decreases the new rank, regardless of
how its local action and free-component partition change. -/
theorem kernelIdentificationRank_host_lt (G : ObservedGraph S)
    (remaining action smaller smallerAction : NodeSet S)
    (shorter : (NodeSet.members smaller).length <
      (NodeSet.members remaining).length) :
    kernelIdentificationRank G smaller smallerAction <
      kernelIdentificationRank G remaining action := by
  have childFreeBound := kernelMembers_length_le_count
    (NodeSet.diff smaller (NodeSet.inter smallerAction smaller))
  have childUpper := identificationTraceRank_upper G smaller smallerAction
  have parentLower := identificationTraceRank_lower G remaining action
  have scaled := Nat.mul_le_mul_left (2 * S.count)
    (Nat.succ_le_of_lt shorter)
  rw [Nat.mul_succ] at scaled
  unfold kernelIdentificationRank
  omega

/-- Uncut ancestral pruning is a proper host restriction whenever its
executable equality test requests a recursive shrink. -/
theorem kernelIdentificationRank_shrink_lt (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (different : NodeSet.equal
      (G.ancestralSet remaining (GraphMutilation.none S)
        (NodeSet.inter outcome remaining)) remaining = false) :
    kernelIdentificationRank G
      (G.ancestralSet remaining (GraphMutilation.none S)
        (NodeSet.inter outcome remaining))
      (NodeSet.inter (NodeSet.inter action remaining)
        (G.ancestralSet remaining (GraphMutilation.none S)
          (NodeSet.inter outcome remaining))) <
      kernelIdentificationRank G remaining action :=
  kernelIdentificationRank_host_lt G _ _ _ _
    (NodeSet.length_members_lt_of_subset_of_equal_false
      (ancestralSet_subset G _ _ _) different)

/-- Restriction to a containing c-component is proper when the host is not
itself one c-component.  This uses the graph partition facts, not the shape
or denotation of the input distribution. -/
theorem kernelIdentificationRank_restrict_lt (G : ObservedGraph S)
    (remaining action component larger : NodeSet S)
    (several : G.isSingleCComponent remaining = false)
    (containing : G.containingCComponent remaining component = some larger) :
    kernelIdentificationRank G larger
      (NodeSet.inter (NodeSet.inter action remaining) larger) <
      kernelIdentificationRank G remaining action := by
  have specification := containingCComponent_spec G remaining component containing
  have different : NodeSet.equal larger remaining = false := by
    cases equal : NodeSet.equal larger remaining with
    | false => rfl
    | true =>
        have same := (NodeSet.equal_eq_true_iff larger remaining).mp equal
        have partition := cComponents_eq_of_mem_host G remaining specification.1 same
        have single : G.isSingleCComponent remaining = true := by
          simp only [ObservedGraph.isSingleCComponent, partition]
          exact (NodeSet.equal_eq_true_iff remaining remaining).mpr rfl
        exact False.elim (Bool.false_ne_true (several.symm.trans single))
  exact kernelIdentificationRank_host_lt G _ _ _ _
    (NodeSet.length_members_lt_of_subset_of_equal_false
      (containingCComponent_subset_host G remaining component containing)
      different)

/-- Enlarging the action by the additional block removes exactly that
block from the free host.  The Boolean identity also covers unselected
indices, avoiding hidden assumptions about the ambient signature. -/
private theorem kernelFree_after_augmentation (remaining action added : NodeSet S) :
    NodeSet.diff remaining
      (NodeSet.inter (NodeSet.union (NodeSet.inter action remaining) added)
        remaining) =
      NodeSet.diff (NodeSet.diff remaining (NodeSet.inter action remaining)) added := by
  funext node
  unfold NodeSet.diff NodeSet.inter NodeSet.union
  dsimp only
  cases remaining node <;> cases action node <;> cases added node <;> rfl

/-- A nonempty additional action strictly shortens the free host. -/
private theorem kernelFree_augmentation_shorter (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (nonempty : NodeSet.isEmpty
      (identificationAdditionalAction G remaining outcome action) = false) :
    (NodeSet.members
      (NodeSet.diff remaining
        (NodeSet.inter
          (NodeSet.union (NodeSet.inter action remaining)
            (identificationAdditionalAction G remaining outcome action))
          remaining))).length <
      (NodeSet.members (NodeSet.diff remaining
        (NodeSet.inter action remaining))).length := by
  rw [kernelFree_after_augmentation]
  let free := NodeSet.diff remaining (NodeSet.inter action remaining)
  let added := identificationAdditionalAction G remaining outcome action
  have different : NodeSet.equal (NodeSet.diff free added) free = false := by
    cases equal : NodeSet.equal (NodeSet.diff free added) free with
    | false => rfl
    | true =>
        rcases (NodeSet.isEmpty_eq_false_iff added).mp nonempty with ⟨node, selected⟩
        have inFree : free node = true := (Bool.and_eq_true_iff.mp selected).1
        have absent : NodeSet.diff free added node = false := by
          simp only [NodeSet.diff, selected, Bool.not_true, Bool.and_false]
        have same := (NodeSet.equal_eq_true_iff _ _).mp equal
        have present : NodeSet.diff free added node = true :=
          (congrFun same node).trans inFree
        exact False.elim (Bool.false_ne_true (absent.symm.trans present))
  exact NodeSet.length_members_lt_of_subset_of_equal_false
    (NodeSet.diff_subset_left free added) different

/-- Adding `W` decreases rank even when deleting those free vertices
creates a new multi-component product opportunity. -/
theorem kernelIdentificationRank_augment_lt (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (nonempty : NodeSet.isEmpty
      (identificationAdditionalAction G remaining outcome action) = false) :
    kernelIdentificationRank G remaining
      (NodeSet.union (NodeSet.inter action remaining)
        (identificationAdditionalAction G remaining outcome action)) <
      kernelIdentificationRank G remaining action := by
  have shorter := kernelFree_augmentation_shorter G remaining outcome action nonempty
  have childUpper := identificationTraceRank_upper G remaining
    (NodeSet.union (NodeSet.inter action remaining)
      (identificationAdditionalAction G remaining outcome action))
  have parentLower := identificationTraceRank_lower G remaining action
  unfold kernelIdentificationRank
  omega

/-- A product factor has no larger free set and consumes the product bonus
of the parent's graph-only rank.  Thus arbitrary nested product calls also
make progress without enumerating branch stacks. -/
theorem kernelIdentificationRank_product_lt (G : ObservedGraph S)
    (remaining action component component2 : NodeSet S)
    (rest : List (NodeSet S)) (piece : NodeSet S)
    (components : G.cComponents
      (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        component :: component2 :: rest)
    (member : piece ∈ component :: component2 :: rest) :
    kernelIdentificationRank G remaining (NodeSet.diff remaining piece) <
      kernelIdentificationRank G remaining action := by
  have memberFree : piece ∈ G.cComponents
      (NodeSet.diff remaining (NodeSet.inter action remaining)) := by
    rw [components]
    exact member
  have subsetFree := cComponents_subset G _ memberFree
  have subsetHost := NodeSet.Subset.trans subsetFree (NodeSet.diff_subset_left _ _)
  have actionLocal :
      NodeSet.inter (NodeSet.diff remaining piece) remaining =
        NodeSet.diff remaining piece := by
    rw [NodeSet.inter_comm]
    exact NodeSet.inter_eq_of_subset (NodeSet.diff_subset_left _ _)
  have childFree : NodeSet.diff remaining
      (NodeSet.inter (NodeSet.diff remaining piece) remaining) = piece := by
    rw [actionLocal, NodeSet.diff_diff, NodeSet.inter_eq_of_subset subsetHost]
  have freeLength := kernelMembers_length_le_of_subset subsetFree
  have graphRank := identificationTraceRank_product_lt G remaining action
    component component2 rest piece components member
  unfold kernelIdentificationRank
  rw [childFree]
  omega

/-! ## Exhaustive recursive progress, including product lists -/

/-- A finite product collector cannot become unfinished when none of its
input calls is unfinished.  Failed calls still propagate as failures; this
lemma establishes only the absence of the implementation sentinel. -/
private theorem kernelCollect_ne_unfinished
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (pending : List (IdentificationOutcome S)) (acc : List (ProbabilityTerm S))
    (each : forall result, result ∈ pending -> result ≠ .unfinished) :
    IdentificationOutcome.collect assemble pending acc ≠ .unfinished := by
  induction pending generalizing acc with
  | nil => intro impossible; cases impossible
  | cons result rest inductionHypothesis =>
      have tail : forall result, result ∈ rest -> result ≠ .unfinished :=
        fun result member => each result (List.mem_cons.mpr (Or.inr member))
      cases result with
      | identified term => exact inductionHypothesis (term :: acc) tail
      | failed fail => intro impossible; cases impossible
      | unfinished =>
          exact False.elim (each .unfinished (List.mem_cons_self) rfl)

/-- Every replacement-engine invocation with fuel above its rank terminates
in an identified expression or a failure.  No semantic regularity or query
identifiability premise is needed for this control-flow theorem. -/
theorem identifyKernelFuel_ne_unfinished_of_rank_lt
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S) (current : ProbabilityTerm S)
    (enough : kernelIdentificationRank G remaining action < fuel) :
    identifyKernelFuel fuel G remaining outcome action current ≠ .unfinished := by
  induction fuel generalizing remaining outcome action current with
  | zero => exact False.elim (Nat.not_lt_zero _ enough)
  | succ fuel inductionHypothesis =>
      intro unfinished
      simp only [identifyKernelFuel] at unfinished
      split at unfinished
      · cases unfinished
      · split at unfinished
        · split at unfinished
          · split at unfinished
            · cases unfinished
            · split at unfinished
              · cases unfinished
              · split at unfinished
                · cases unfinished
                · split at unfinished
                  · have decreases := kernelIdentificationRank_restrict_lt
                      G remaining action _ _ (by
                        cases single : G.isSingleCComponent remaining with
                        | false => rfl
                        | true => contradiction) (by assumption)
                    exact inductionHypothesis _ _ _ _ (by omega) unfinished
                  · exact identificationUnfinished_missingHost_impossible
                      G remaining action _ (by assumption) (by assumption)
            · apply kernelCollect_ne_unfinished _ _ [] _ unfinished
              intro result member
              rcases List.mem_map.mp member with ⟨piece, pieceMember, rfl⟩
              have decreases := kernelIdentificationRank_product_lt
                G remaining action _ _ _ piece (by assumption) (by
                  simpa only [show G.cComponents
                    (NodeSet.diff remaining (NodeSet.inter action remaining)) =
                      _ from by assumption] using pieceMember)
              exact inductionHypothesis _ _ _ _ (by omega)
          · have addedNonempty : NodeSet.isEmpty
                (identificationAdditionalAction G remaining outcome action) =
                  false := by
              cases empty : NodeSet.isEmpty
                  (identificationAdditionalAction G remaining outcome action) with
              | false => rfl
              | true => contradiction
            have decreases := kernelIdentificationRank_augment_lt
              G remaining outcome action addedNonempty
            exact inductionHypothesis _ _ _ _ (by omega) unfinished
        · have different : NodeSet.equal
              (G.ancestralSet remaining (GraphMutilation.none S)
                (NodeSet.inter outcome remaining)) remaining = false := by
            cases equal : NodeSet.equal
                (G.ancestralSet remaining (GraphMutilation.none S)
                  (NodeSet.inter outcome remaining)) remaining with
            | false => rfl
            | true => contradiction
          have decreases := kernelIdentificationRank_shrink_lt
            G remaining outcome action different
          exact inductionHypothesis _ _ _ _ (by omega) unfinished

/-- The public quadratic allowance is strictly above every invocation rank
over this signature, including hosts with gaps and arbitrary local actions. -/
theorem kernelIdentificationRank_lt_fuel (G : ObservedGraph S)
    (remaining action : NodeSet S) :
    kernelIdentificationRank G remaining action < kernelIdentificationFuel S := by
  have hostBound := kernelMembers_length_le_count remaining
  have freeBound := kernelMembers_length_le_count
    (NodeSet.diff remaining (NodeSet.inter action remaining))
  have graphBound := identificationTraceRank_upper G remaining action
  have scaled := Nat.mul_le_mul_left (2 * S.count) hostBound
  unfold kernelIdentificationRank kernelIdentificationFuel
  simp only [Nat.mul_add, Nat.mul_assoc] at scaled ⊢
  omega

/-- Public current-kernel joint ID never returns the implementation sentinel.
Together with the action-free theorem this establishes the executable
infrastructure, while supported do-calculus compilation remains separate. -/
theorem identifyJointKernel_ne_unfinished (G : ObservedGraph S)
    (q : JointKernelQuery S) :
    identifyJointKernel G q ≠ .unfinished :=
  identifyKernelFuel_ne_unfinished_of_rank_lt _ _ _ _ _ _
    (kernelIdentificationRank_lt_fuel G NodeSet.full q.action)

end Causality
end Thesis
