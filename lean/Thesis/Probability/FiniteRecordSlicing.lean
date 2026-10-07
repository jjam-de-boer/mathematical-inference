import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Constructive finite fibres of an arbitrary probability event

A finite-valued projection partitions an event into disjoint fibres.  The
source space itself need not be enumerated: only the finite projection image
is listed.  This is useful when a response-function SCM has a very large
private seed space, but its shared latent assignment space is small.

The proof uses the existing finite additivity theorem, an explicit complete
image enumeration, and decidable equality on that image.  It does not select
a representative of a fibre, assume a conditional distribution, or use
excluded middle on an arbitrary proposition.
-/

variable {Ω : Type u} {A : Type v} [DecidableEq A]

/-- The fibre retains the original event as well as its projected label. -/
def fibreEvent (project : Ω -> A) (event : Event Ω) (value : A) : Event Ω :=
  fun unit => decide (project unit = value) && event unit

private theorem unionList_fibreEvents (project : Ω -> A) (event : Event Ω)
    (values : List A) :
    unionList (values.map (fibreEvent project event)) =
      (fun unit => membershipEvent values (project unit) && event unit) := by
  induction values with
  | nil =>
      funext unit
      cases event unit <;> rfl
  | cons head rest inductionHypothesis =>
      funext unit
      simp only [List.map_cons, unionList, union, inductionHypothesis,
        membershipEvent_cons, singletonEvent, fibreEvent]
      exact (Bool.and_or_distrib_right _ _ _).symm

private theorem fibreEvents_pairwise (project : Ω -> A) (event : Event Ω)
    (values : List A) (nodup : values.Nodup) :
    (values.map (fibreEvent project event)).Pairwise disjoint := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head rest inductionHypothesis =>
      have parts := List.nodup_cons.mp nodup
      refine List.pairwise_cons.mpr ⟨?_, inductionHypothesis parts.2⟩
      intro otherEvent listed unit first second
      rcases List.mem_map.mp listed with ⟨other, member, rfl⟩
      have firstEq : project unit = head := of_decide_eq_true (Bool.and_eq_true_iff.mp first).1
      have secondEq : project unit = other := of_decide_eq_true (Bool.and_eq_true_iff.mp second).1
      exact parts.1 ((firstEq.symm.trans secondEq).symm ▸ member)

/-- Exact decomposition of any event over the fibres of a supplied finite
projection.  Positivity of individual fibres is not required. -/
theorem probVal_equiv_listSum_fibres (record : FiniteProbRecord Ω)
    (project : Ω -> A) (event : Event Ω) (values : List A)
    (nodup : values.Nodup) (complete : forall value, value ∈ values) :
    QProb.Equiv (record.probVal event)
      (QProb.listSum (values.map (fun value => record.probVal (fibreEvent project event value)))) := by
  have covered : unionList (values.map (fibreEvent project event)) = event := by
    rw [unionList_fibreEvents]
    funext unit
    have selected : membershipEvent values (project unit) = true := decide_eq_true (complete _)
    rw [selected, Bool.true_and]
  have additive := record.finite_additivity_family
    (values.map (fibreEvent project event)) (fibreEvents_pairwise project event values nodup)
  rw [covered, List.map_map] at additive
  exact additive

end FiniteProbRecord
end Probability
end Thesis
