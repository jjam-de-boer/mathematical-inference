import Thesis.Examples.HedgeChannelLatentBoundary
import Thesis.CausalTransport.HedgeConditionalLatentCollider
import Thesis.CausalTransport.ConditionalCounterexampleFailure

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelLatentBoundary

/-!
# Non-identifiability despite the independent-channel family obstruction

The companion fixture and projection module proves whole-conditional
agreement for every typed small/background parent signal in the current
independent-channel family.  That agreement does not quantify over all
graph-compatible SCMs.  Here the already verified shared-latent construction
provides a different pair on the same original three-valued signature.

The two real models have full label support, exactly the original projected
graph, a common whole observational law, and a separated original conditional
query.  No observed `U -> R` arrow is inserted.  The actual IDC entry point
therefore fails by its independent soundness and termination theorems; the
fixture's exhausted exchange test makes this a genuine irreducible example.

This is a one-way semantic assembly, not a new proof-time computation over
augmented response functions.  Its heavier carrier and soundness imports
are intentionally kept out of the finite channel-projection checker.
-/

/-- The conditioned common root has an actual queried outside neighbour
through the declared bidirected edge.  Only this small graph lookup is
computed; no root or shared source is chosen from a proposition. -/
theorem shared_parent_available (root : Fin signature.count) (selected : witness.roots root = true) :
    NodeSet.meetsBool query.outcome (HedgeConditionalRoot.sharedLatentParentMask witness root) = true := by
  have selectedCondition := (congrFun roots_are_condition root).symm.trans selected
  have same := (NodeSet.singleton_eq_true_iff rootNode root).mp selectedCondition
  subst root
  decide +kernel

/-- A genuinely different positive pair uses the already declared shared
latent entry.  Its original-query separation comes from the general root-
specific latent constructor, not from the obstructed channel installation. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfRootSpecificLatentParents rich
    roots_are_condition shared_parent_available

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

/-- Failure of the actual corrected entry point, not an assumed fail
record or a decision computation over augmented latent assignments. -/
theorem original_query_failed :
    (match identifyConditionalKernel graph query with | .failed _ => true | _ => false) = true :=
  counterexample.identifyConditionalKernel_failed (fun member => member.2)

end HedgeChannelLatentBoundary
end Examples
end Causality
end Thesis
