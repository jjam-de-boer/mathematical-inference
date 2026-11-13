import Thesis.Causality.QualitativeDoCalculus
import Thesis.Causality.ReachabilityCorrectness

namespace Thesis
namespace Causality

open Probability
open Probability.ClaytonWaddington
open Probability.ClaytonWaddington.UrnRatio
open QualitativeDoCalculus

/-!
World-ticket readings of a finite SCM.

Investigation.  A structure whose primitive is `read I u` with skip-and-continue
fields is a rename of `FiniteLatentSCM.evalUnder`.  That parallel type is not
shipped.  The generating process is the existing SCM: one fixed world pile
(`prior`), print rules (`mechanism`), and `do` as skip-and-continue
(`equationUnder`).  The theorems below name that process in urn language.

Clayton compares events on the world pile and on listing events obtained by
reading.  The three do-rules remain the existing soundness theorems, reread as
ratios by qualitative 2a; they are not proved here.

Listing-bag sentences (Story 2) are corollaries of the ticketwise facts, not a
basis for Pearl.
-/

namespace WorldTicket

/-- Directed reachability along `S.directed`, including the zero-length walk. -/
def directedReachable (S : ObservedSignature) (source target : Fin S.count) :
    Bool :=
  FiniteReachability.within finBeq (NodeSet.enumerated S) S.directed S.count
    source target

/-- Nodes lying on a directed path from some member of `Z`, including `Z`. -/
def descendantsOf (S : ObservedSignature) (Z : NodeSet S) : NodeSet S :=
  fun i =>
    (NodeSet.enumerated S).any (fun z => Z z && directedReachable S z i)

/-- Nodes that are not effects of `Z` along `S.directed`. -/
def nonDescendantsOf (S : ObservedSignature) (Z : NodeSet S) : NodeSet S :=
  fun i => !(descendantsOf S Z i)

theorem directedReachable_self (S : ObservedSignature) (i : Fin S.count) :
    directedReachable S i i = true :=
  (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
      (NodeSet.mem_enumerated S) S.count i i).mpr
    (FiniteReachability.BoundedWalk.refl S.directed S.count i)

theorem ExactWalk.nonempty_snoc {α : Type _} {edge : α → α → Bool}
    {length : Nat} {source middle target : α}
    (walk : FiniteReachability.ExactWalk edge length source middle)
    (last : edge middle target = true) :
    Nonempty (FiniteReachability.ExactWalk edge (length + 1) source target) := by
  induction walk with
  | refl _node =>
      exact ⟨.step last (.refl target)⟩
  | @step _length _source _mid _middle first _rest ih =>
      rcases ih last with ⟨extended⟩
      exact ⟨.step first extended⟩

theorem directedReachable_of_parent (S : ObservedSignature)
    {z parent child : Fin S.count}
    (hreach : directedReachable S z parent = true)
    (hedge : S.directed parent child = true) :
    directedReachable S z child = true := by
  have bounded :
      FiniteReachability.BoundedWalk S.directed S.count z parent :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
        (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
        (NodeSet.mem_enumerated S) S.count z parent).mp hreach
  rcases bounded with ⟨_length, _bound, ⟨walk⟩⟩
  have reachable : FiniteReachability.Reachable S.directed z child :=
    ⟨_length + 1, ExactWalk.nonempty_snoc walk hedge⟩
  have rebound :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
      (NodeSet.mem_enumerated S) reachable
  have boundedChild :
      FiniteReachability.BoundedWalk S.directed S.count z child := by
    simpa [NodeSet.length_enumerated] using rebound
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
      (NodeSet.mem_enumerated S) S.count z child).mpr boundedChild

theorem descendantsOf_of_mem (S : ObservedSignature) (Z : NodeSet S)
    {i : Fin S.count} (hi : Z i = true) :
    descendantsOf S Z i = true := by
  refine List.any_eq_true.mpr ⟨i, NodeSet.mem_enumerated S i, ?_⟩
  exact Bool.and_eq_true_iff.mpr ⟨hi, directedReachable_self S i⟩

theorem descendantsOf_parent (S : ObservedSignature) (Z : NodeSet S)
    {parent child : Fin S.count}
    (hedge : S.directed parent child = true)
    (hparent : descendantsOf S Z parent = true) :
    descendantsOf S Z child = true := by
  rcases List.any_eq_true.mp hparent with ⟨z, zMem, hz⟩
  have hzZ : Z z = true := (Bool.and_eq_true_iff.mp hz).1
  have hzR : directedReachable S z parent = true :=
    (Bool.and_eq_true_iff.mp hz).2
  refine List.any_eq_true.mpr ⟨z, zMem, ?_⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hzZ, directedReachable_of_parent S hzR hedge⟩

theorem not_descendant_parent (S : ObservedSignature) (Z : NodeSet S)
    {parent child : Fin S.count}
    (hedge : S.directed parent child = true)
    (hchild : descendantsOf S Z child = false) :
    descendantsOf S Z parent = false := by
  cases hparent : descendantsOf S Z parent with
  | false => rfl
  | true =>
      have hcontra := descendantsOf_parent S Z hedge hparent
      exact (Bool.false_ne_true (hchild.symm.trans hcontra)).elim

theorem not_mem_of_not_descendant (S : ObservedSignature) (Z : NodeSet S)
    {i : Fin S.count} (h : descendantsOf S Z i = false) :
    Z i = false := by
  cases hi : Z i with
  | false => rfl
  | true =>
      have hdesc := descendantsOf_of_mem S Z hi
      exact (Bool.false_ne_true (h.symm.trans hdesc)).elim

theorem target_eq_none_of_not_descendant
    (target : (i : Fin S.count) → Option (S.Value i)) {child : Fin S.count}
    (hnd : descendantsOf S (fun i => (target i).isSome) child = false) :
    target child = none := by
  have hcut :
      (target child).isSome = false :=
    not_mem_of_not_descendant S (fun i => (target i).isSome) hnd
  cases htarget : target child with
  | none => rfl
  | some _ =>
      simp [htarget] at hcut

/-- Evaluation off the effects of an intervention ignores that intervention. -/
theorem evalNodeUnder_eq_of_not_descendant (M : ExactModel S)
    (target : (i : Fin S.count) → Option (S.Value i))
    (u : M.latent.Assignment) (child : Fin S.count)
    (hnd : descendantsOf S (fun i => (target i).isSome) child = false) :
    M.evalNodeUnder target u child =
      M.evalNodeUnder (FiniteLatentSCM.noIntervention S) u child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  have hnone := target_eq_none_of_not_descendant target hnd
  simp only [FiniteLatentSCM.equationUnder, hnone,
    FiniteLatentSCM.noIntervention]
  congr 1
  funext parent edge
  exact evalNodeUnder_eq_of_not_descendant M target u parent
    (not_descendant_parent S (fun i => (target i).isSome) edge hnd)
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

theorem evalUnder_eq_on_nonDescendants (M : ExactModel S)
    (target : (i : Fin S.count) → Option (S.Value i))
    (u : M.latent.Assignment) {i : Fin S.count}
    (hnd : descendantsOf S (fun i => (target i).isSome) i = false) :
    M.evalUnder target u i =
      M.evalUnder (FiniteLatentSCM.noIntervention S) u i :=
  evalNodeUnder_eq_of_not_descendant M target u i hnd

/-- The world pile of hidden balls.  Forcing knobs does not replace it. -/
def worldPile (model : ExactModel S) : UrnProb model.latent.Assignment :=
  model.prior.toUrn

/-- 1. Fixed world pile. -/
theorem worldPile_fixed (model : ExactModel S) (I : HardIntervention S) :
    model.interventionalDist I.value = model.prior.map (model.evalUnder I.value) :=
  model.interventionalDist_same_worldPile I.value

/-- 2. Effectiveness, ticketwise. -/
theorem reading_effectiveness (model : ExactModel S)
    (I : HardIntervention S) (u : model.latent.Assignment)
    (i : Fin S.count) (value : S.Value i)
    (forced : I.value i = some value) :
    model.evalUnder I.value u i = value :=
  model.evalUnder_effectiveness I.value u i value forced

/-- 3. Skip and continue, ticketwise. -/
theorem reading_unforced (model : ExactModel S)
    (I : HardIntervention S) (u : model.latent.Assignment)
    (child : Fin S.count) (unforced : I.value child = none) :
    model.evalNodeUnder I.value u child =
      model.mechanism child
        (fun parent _edge => model.evalNodeUnder I.value u parent)
        (fun latent _ => u latent) :=
  model.evalNodeUnder_unforced I.value u child unforced

/-- 3. Same forced parents, unforced child: the print agrees on this ticket. -/
theorem reading_parent_modularity (model : ExactModel S)
    (child : Fin S.count) (I J : HardIntervention S)
    (u : model.latent.Assignment)
    (unforcedI : I.value child = none) (unforcedJ : J.value child = none)
    (parentsForced :
      ∀ parent, S.directed parent child = true →
        (I.value parent).isSome = true)
    (parentsAgree :
      ∀ parent, S.directed parent child = true →
        I.value parent = J.value parent) :
    model.evalUnder I.value u child = model.evalUnder J.value u child :=
  model.evalUnder_eq_of_same_forced_parents I.value J.value u child
    unforcedI unforcedJ parentsForced parentsAgree

/-- 4. Wiring: the unforced print ignores non-incident hidden balls, given
the same parent readings. -/
theorem reading_incident_only (model : ExactModel S)
    (I : HardIntervention S) (u v : model.latent.Assignment)
    (child : Fin S.count) (unforced : I.value child = none)
    (parentsAgree :
      ∀ parent, S.directed parent child = true →
        model.evalNodeUnder I.value u parent =
          model.evalNodeUnder I.value v parent)
    (incidentAgree :
      ∀ latent, model.latent.incident latent child = true →
        u latent = v latent) :
    model.evalNodeUnder I.value u child =
      model.evalNodeUnder I.value v child :=
  model.evalNodeUnder_unforced_congr_incident I.value u v child unforced
    parentsAgree incidentAgree

/-- 5. Private balls: a Markovian hidden source feeds at most one node. -/
theorem private_ball_feeds_at_most_one (model : ExactModel S)
    (hMarkov : model.IsMarkovian)
    (latent : Fin model.latent.count) (i j : Fin S.count)
    (hi : model.latent.incident latent i = true)
    (hj : model.latent.incident latent j = true) :
    i = j :=
  hMarkov latent i j hi hj

/-- 5. Shared ball: a hidden source incident to two nodes. -/
def SharedBall (model : ExactModel S) : Prop :=
  ∃ latent i j,
    i ≠ j ∧
      model.latent.incident latent i = true ∧
      model.latent.incident latent j = true

theorem shared_ball_of_bidirected (model : ExactModel S)
    {i j : Fin S.count}
    (h : model.latent.projectedBidirected i j = true) :
    SharedBall model := by
  have hne : i ≠ j := by
    intro equal
    subst j
    have hirrefl := model.latent.projectedBidirected_irreflexive i
    exact Bool.false_ne_true (hirrefl.symm.trans h)
  have hany :
      finAny model.latent.count
          (fun latent =>
            model.latent.incident latent i &&
              model.latent.incident latent j) = true :=
    (Bool.and_eq_true_iff.mp h).2
  rcases (finAny_eq_true_iff _).mp hany with ⟨latent, hlatent⟩
  have parts := Bool.and_eq_true_iff.mp hlatent
  exact ⟨latent, i, j, hne, parts.1, parts.2⟩

/-- 5. Independent hidden factors: the world pile is a Clayton product. -/
theorem worldPile_product (model : ExactModel S)
    (events : (l : Fin model.latent.count) → model.latent.Value l → Bool) :
    QProb.Equiv
      (model.prior.probVal (model.latent.rectangularEvent events))
      (FiniteProduct.qProduct model.latent.count
        (fun l => (model.factor l).probVal (events l))) :=
  model.product_law events

/-- Non-effect invariance, ticketwise. -/
theorem reading_non_effect (model : ExactModel S)
    (I : HardIntervention S) (u : model.latent.Assignment)
    {i : Fin S.count}
    (hnd : descendantsOf S I.targets i = false) :
    model.evalUnder I.value u i =
      model.evalUnder (HardIntervention.empty S).value u i := by
  have h : descendantsOf S (fun j => (I.value j).isSome) i = false := by
    simpa [HardIntervention.targets] using hnd
  simpa [HardIntervention.empty] using
    evalUnder_eq_on_nonDescendants model I.value u h

theorem sameRatio_of_probVal_equiv {X : Type _} (μ ν : UrnProb X)
    (E F : Event X) (h : QProb.Equiv (μ.probVal E) (ν.probVal F)) :
    sameRatio (ofUrnEvent μ E) (ofUrnEvent ν F) := by
  simpa [sameRatio, ofUrnEvent, UrnProb.probVal, QProb.Equiv] using h

/-- Listing-bag effectiveness is the pushforward of ticketwise effectiveness. -/
theorem listing_effectiveness (model : ExactModel S)
    (I : HardIntervention S) (i : Fin S.count) (value : S.Value i)
    (forced : I.value i = some value) :
    sameRatio
      (ofUrnEvent (interventionalUrn model I)
        (fun a => decide (a i = value)))
      (ofUrnEvent (interventionalUrn model I) topEvent) := by
  let μ := interventionalUrn model I
  let forcedE : Event S.Assignment := fun a => decide (a i = value)
  have agreesForced :=
    (model.interventionalDist I.value).toUrn_agrees forcedE
  have agreesTop :=
    (model.interventionalDist I.value).toUrn_agrees topEvent
  have hforced : QProb.Equiv (μ.probVal forcedE) QProb.one :=
    QProb.equiv_trans (QProb.equiv_symm agreesForced)
      (interventionalValue_effectiveness model I i value forced)
  have htop : QProb.Equiv (μ.probVal topEvent) QProb.one :=
    QProb.equiv_trans (QProb.equiv_symm agreesTop)
      (model.interventionalDist I.value).normalization
  have hk : μ.probNum forcedE = μ.n := by
    simpa [QProb.Equiv, UrnProb.probVal, QProb.one] using hforced
  have ht : μ.probNum topEvent = μ.n := μ.probNum_top
  show sameRatio (ofUrnEvent μ forcedE) (ofUrnEvent μ topEvent)
  simp [sameRatio, ofUrnEvent]
  rw [hk, ht]

/-- Listing-bag non-effect invariance from ticketwise non-effect readings. -/
theorem listing_non_effect (model : ExactModel S)
    (I : HardIntervention S) (E : Event S.Assignment)
    (hE : ∀ x y : S.Assignment,
      (∀ i, nonDescendantsOf S I.targets i = true → x i = y i) →
        E x = E y) :
    sameRatio
      (ofUrnEvent (interventionalUrn model I) E)
      (ofUrnEvent (interventionalUrn model (HardIntervention.empty S)) E) := by
  have hpoint :
      (fun u => E (model.evalUnder I.value u)) =
        (fun u => E (model.evalUnder (HardIntervention.empty S).value u)) := by
    funext u
    apply hE
    intro i hi
    exact reading_non_effect model I u (by
      simpa [nonDescendantsOf] using hi)
  have hI := model.interventionalValue_eq I.value E
  have hIdle :=
    model.interventionalValue_eq (HardIntervention.empty S).value E
  have hprior :
      QProb.Equiv
        (model.interventionalValue I.value E)
        (model.interventionalValue (HardIntervention.empty S).value E) := by
    refine QProb.equiv_trans hI (QProb.equiv_trans ?_ (QProb.equiv_symm hIdle))
    simpa [hpoint] using QProb.equiv_refl
      (model.prior.probVal (fun u => E (model.evalUnder I.value u)))
  have agreesI := (model.interventionalDist I.value).toUrn_agrees E
  have agreesIdle :=
    (model.interventionalDist (HardIntervention.empty S).value).toUrn_agrees E
  have hμ :
      QProb.Equiv
        ((interventionalUrn model I).probVal E)
        ((interventionalUrn model (HardIntervention.empty S)).probVal E) :=
    QProb.equiv_trans (QProb.equiv_symm agreesI)
      (QProb.equiv_trans hprior agreesIdle)
  exact sameRatio_of_probVal_equiv _ _ E E hμ

/-- Listing-bag parent modularity from ticketwise skip-and-continue. -/
theorem listing_parent_modularity (model : ExactModel S)
    (child : Fin S.count) (I J : HardIntervention S)
    (E : Event S.Assignment)
    (parentsAgree :
      ∀ parent, S.directed parent child = true →
        I.value parent = J.value parent)
    (parentsForced :
      ∀ parent, S.directed parent child = true →
        (I.value parent).isSome = true)
    (unforcedI : I.value child = none) (unforcedJ : J.value child = none)
    (hE : ∀ x y : S.Assignment,
      x child = y child → E x = E y) :
    sameRatio
      (ofUrnEvent (interventionalUrn model I) E)
      (ofUrnEvent (interventionalUrn model J) E) := by
  have hpoint :
      (fun u => E (model.evalUnder I.value u)) =
        (fun u => E (model.evalUnder J.value u)) := by
    funext u
    apply hE
    exact reading_parent_modularity model child I J u
      unforcedI unforcedJ parentsForced parentsAgree
  have hI := model.interventionalValue_eq I.value E
  have hJ := model.interventionalValue_eq J.value E
  have hprior :
      QProb.Equiv
        (model.interventionalValue I.value E)
        (model.interventionalValue J.value E) := by
    refine QProb.equiv_trans hI (QProb.equiv_trans ?_ (QProb.equiv_symm hJ))
    simpa [hpoint] using QProb.equiv_refl
      (model.prior.probVal (fun u => E (model.evalUnder I.value u)))
  have agreesI := (model.interventionalDist I.value).toUrn_agrees E
  have agreesJ := (model.interventionalDist J.value).toUrn_agrees E
  have hμ :
      QProb.Equiv
        ((interventionalUrn model I).probVal E)
        ((interventionalUrn model J).probVal E) :=
    QProb.equiv_trans (QProb.equiv_symm agreesI)
      (QProb.equiv_trans hprior agreesJ)
  exact sameRatio_of_probVal_equiv _ _ E E hμ

end WorldTicket

end Causality
end Thesis
