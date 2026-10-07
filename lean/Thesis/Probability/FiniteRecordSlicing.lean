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

The normalization lemma is the identity-projection specialization at
raw mass level.  It is shared by two-way and full-coordinate conditional
uniqueness: summing all distinct cells recovers the record's actual denominator.
The accompanying support and conditioning transports pull genuine pushforward
events back to their sources; they do not require equality on the image type.
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

/-- Finite normalization as a sum of distinct singleton masses.  Repeated
atoms in the record are allowed; only the supplied complete label enumeration
must be duplicate-free.  The stored positive denominator, rather than a
positive singleton or a matched second denominator, is the quantity cancelled. -/
theorem sum_singletonMass_eq_den (record : FiniteProbRecord A)
    (values : List A) (nodup : values.Nodup) (complete : forall value, value ∈ values) :
    (values.map (fun value => eventMass record.atoms (singletonEvent value))).sum = record.den := by
  have membership : membershipEvent values = topEvent := by
    funext value
    exact decide_eq_true (complete value)
  have sum := record.probVal_membership_equiv_listSum values nodup
  rw [membership] at sum
  have presentation := QProb.listSum_mk_same_den record.den record.den_pos
    (values.map (fun value => eventMass record.atoms (singletonEvent value)))
  have combined : QProb.Equiv (record.probVal topEvent)
      ⟨(values.map (fun value => eventMass record.atoms (singletonEvent value))).sum, record.den, record.den_pos⟩ :=
    QProb.equiv_trans sum (by simpa only [List.map_map, Function.comp_def, probVal] using presentation)
  change eventMass record.atoms topEvent * record.den =
    (values.map (fun value => eventMass record.atoms (singletonEvent value))).sum * record.den at combined
  exact (Nat.eq_of_mul_eq_mul_right record.den_pos combined).symm.trans
    ((eventMass_top record.atoms).trans record.total_mass)

omit [DecidableEq A] in
/-- A pushforward evidence event has exactly its pullback's support.  No
source atom or representative of an image label needs to be selected. -/
theorem map_eventPositive_iff (record : FiniteProbRecord Ω) (encode : Ω -> A) (evidence : Event A) :
    (record.map encode).EventPositive evidence ↔ record.EventPositive (fun unit => evidence (encode unit)) := by
  simp only [EventPositive, map, eventMass_map_labels]

omit [DecidableEq A] in
/-- Conditioning a genuine pushforward record agrees with conditioning its
source on the pulled-back evidence, for every output event.  The support
witness of that source event is derived from the same pushed record; neither
new denominators nor a coupling of unrelated sources are supplied. -/
theorem map_conditionOn_probVal (record : FiniteProbRecord Ω) (encode : Ω -> A)
    (evidence event : Event A) (supported : (record.map encode).EventPositive evidence) :
    QProb.Equiv (((record.map encode).conditionOn evidence supported).probVal event)
      ((record.conditionOn (fun unit => evidence (encode unit))
        ((record.map_eventPositive_iff encode evidence).mp supported)).probVal (fun unit => event (encode unit))) := by
  simp only [conditionOn, map, probVal, eventMass_filter_event, eventMass_map_labels, QProb.Equiv]
  rw [eventMass_filter_event record.atoms (fun unit => evidence (encode unit)) (fun unit => event (encode unit))]

end FiniteProbRecord
end Probability
end Thesis
