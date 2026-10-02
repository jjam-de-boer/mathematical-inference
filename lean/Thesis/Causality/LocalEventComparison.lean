import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# Finite cylinder comparison determines every local event

An exact marginal comparison is often first proved for full-value cylinders.
This module turns those comparisons into equality for every event depending
only on the selected coordinates.  It uses the signature's existing default
values and duplicate-free assignment enumeration: there is no chosen
representative, classical function equality, or selected family of proofs.

The two finite records may have unrelated atoms, weights, and denominators.
Projecting the uninspected coordinates gives literal finite pushforwards;
singleton comparison determines their laws, and event locality removes the
canonical default-coordinate presentation.  The argument includes empty
node sets and zero-mass cylinders.
-/

namespace LocalEventComparison

variable {S : ObservedSignature}

/-- A projected singleton is empty unless its requested full assignment
already has the supplied default values off the selected set.  On the
projection's image it is exactly the original agreement cylinder. -/
private theorem projected_singleton (nodes : NodeSet S) (target sample : S.Assignment) :
    FiniteProbRecord.singletonEvent target (S.project nodes sample) =
      (decide (S.project nodes target = target) && Kernel.agreesOn nodes target sample) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro selected
    have equal : S.project nodes sample = target := of_decide_eq_true selected
    have fits : S.project nodes target = target := by
      rw [← equal, S.project_idempotent]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true fits,
      (Kernel.agreesOn_iff_project_eq nodes target sample).mpr (equal.trans fits.symm)⟩
  · intro selected
    have parts := Bool.and_eq_true_iff.mp selected
    have fits : S.project nodes target = target := of_decide_eq_true parts.1
    exact decide_eq_true (((Kernel.agreesOn_iff_project_eq nodes target sample).mp parts.2).trans fits)

end LocalEventComparison

/-- Agreement of every selected-coordinate cylinder implies probability
equivalence of every event local to those coordinates.  Only finite data
already stored in the observed signature is used to compare the projected
laws; rational denominators need not be equal. -/
theorem FiniteProbRecord.probVal_equiv_of_agreementCylinders
    {S : ObservedSignature} (left right : FiniteProbRecord S.Assignment) (nodes : NodeSet S)
    (cylinders : forall target : S.Assignment,
      QProb.Equiv (left.probVal (Kernel.agreesOn nodes target)) (right.probVal (Kernel.agreesOn nodes target)))
    (event : Event S.Assignment) (localEvent : EventDependsOnlyOn nodes event) :
    QProb.Equiv (left.probVal event) (right.probVal event) := by
  let project := S.project nodes
  have singletons (target : S.Assignment) :
      QProb.Equiv ((left.map project).probVal (FiniteProbRecord.singletonEvent target))
        ((right.map project).probVal (FiniteProbRecord.singletonEvent target)) := by
    have leftPreimage := left.probVal_congr
      (fun sample => FiniteProbRecord.singletonEvent target (project sample))
      (fun sample => decide (project target = target) && Kernel.agreesOn nodes target sample)
      (LocalEventComparison.projected_singleton nodes target)
    have rightPreimage := right.probVal_congr
      (fun sample => FiniteProbRecord.singletonEvent target (project sample))
      (fun sample => decide (project target = target) && Kernel.agreesOn nodes target sample)
      (LocalEventComparison.projected_singleton nodes target)
    have compared : QProb.Equiv
        (left.probVal (fun sample => decide (project target = target) && Kernel.agreesOn nodes target sample))
        (right.probVal (fun sample => decide (project target = target) && Kernel.agreesOn nodes target sample)) := by
      cases fits : decide (project target = target) with
      | false =>
          simp only [Bool.false_and, QProb.Equiv, FiniteProbRecord.probVal, FiniteProbRecord.eventMass_false, Nat.zero_mul]
      | true =>
          simp only [Bool.true_and]
          exact cylinders target
    exact QProb.equiv_trans (left.map_probVal project (FiniteProbRecord.singletonEvent target))
      (QProb.equiv_trans leftPreimage (QProb.equiv_trans compared
        (QProb.equiv_trans (QProb.equiv_symm rightPreimage)
          (QProb.equiv_symm (right.map_probVal project (FiniteProbRecord.singletonEvent target))))))
  have projected := FiniteProbRecord.probVal_extensional_of_singletons
    (left.map project) (right.map project) S.assignmentEnumeration
    S.assignmentEnumeration_nodup S.assignmentEnumeration_complete singletons event
  have preserved (sample : S.Assignment) : event sample = event (project sample) := by
    apply localEvent
    intro child selected
    simp only [project, ObservedSignature.project, selected, if_true]
  exact QProb.equiv_trans (left.probVal_congr _ _ preserved)
    (QProb.equiv_trans (QProb.equiv_symm (left.map_probVal project event))
      (QProb.equiv_trans projected
        (QProb.equiv_trans (right.map_probVal project event)
          (QProb.equiv_symm (right.probVal_congr _ _ preserved)))))

end Causality
end Thesis
