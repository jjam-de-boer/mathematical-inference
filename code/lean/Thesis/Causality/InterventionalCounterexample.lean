import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# Event separation refutes equality of the original causal kernel

A local event can witness inequality of two whole interventional outcome laws.
The bridge below uses the actual finite outcome projection and singleton-mass
extensionality. It keeps the original signature, intervention and query; it
does not select a new event or assume a countermodel exists.

This lemma is independent of the particular hedge or parity circuit that
supplies separated models. Keeping it here lets finite-alphabet refinements use
the bridge without importing a particular completeness construction.
-/

/-- Event-level disagreement for a local interventional query refutes
equivalence of its entire distributional kernel.  The forward implication is
proved constructively: kernel cells determine all singleton masses of the
projected outcome law, and finite singleton extensionality determines the
local event. -/
theorem InterventionalQuery.not_kernelValueEquivalent_of_not_value
    (q : InterventionalQuery S) (left right : ExactModel S)
    (separated : Not (QProb.Equiv (q.value left) (q.value right))) :
    Not (q.kernelQuery.ValueEquivalent left right) := by
  intro kernelEquivalent
  apply separated
  have projectedEquivalent : QProb.Equiv
      ((q.projectedDistribution left).probVal q.event)
      ((q.projectedDistribution right).probVal q.event) :=
    FiniteProbRecord.probVal_extensional_of_singletons
      (q.projectedDistribution left) (q.projectedDistribution right)
      S.assignmentEnumeration S.assignmentEnumeration_nodup
      S.assignmentEnumeration_complete
      (q.projectedSingleton_equiv left right kernelEquivalent) q.event
  exact QProb.equiv_trans
    (QProb.equiv_symm (q.projectedEvent_equiv_value left))
    (QProb.equiv_trans projectedEquivalent
      (q.projectedEvent_equiv_value right))

end Causality
end Thesis
