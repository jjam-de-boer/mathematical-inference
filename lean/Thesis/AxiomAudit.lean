import Thesis

/-!
Build-time audit targets for the constructive-extensional theorem surface.

The accepted fallback boundary is `propext` and `Quot.sound`, both inherited
from ordinary Lean/Std extensional infrastructure.  `Classical.choice`, an
excluded-middle axiom, or `Lean.ofReduceBool` would violate the project policy.
The source tree is separately searched for `Classical.*` and `native_decide`.
-/

#print axioms Thesis.Probability.FiniteProbRecord.conditionOn_probVal
#print axioms Thesis.Causality.FiniteLatentSCM.counterfactualValue_eq
#print axioms Thesis.Causality.FiniteTableSCM.evalNodeUnder_preserved
#print axioms Thesis.Causality.FiniteTableLatent.interpret
#print axioms Thesis.Causality.FiniteTableSCM.kernelDenote_preserved
#print axioms Thesis.Causality.finiteSourceCompatible_iff
#print axioms Thesis.Causality.finiteSourceConditionalKernelEquivalent_iff
#print axioms Thesis.Causality.FiniteSourceCounterexample.toTarget
#print axioms Thesis.Causality.FiniteTableSCM.evalNodeUnder
#print axioms Thesis.Causality.FiniteTableSCM.interpret
#print axioms Thesis.Causality.FiniteLatentSCM.evalNodeUnder
#print axioms Thesis.Causality.FiniteTableSignature.toObserved
#print axioms Thesis.Causality.FiniteTableSCM.observational_preserved
#print axioms Thesis.Causality.finiteSource_identifiable_iff
#print axioms Thesis.Causality.finiteSource_conditionalIdentifiable_iff
#print axioms Thesis.Causality.finiteSource_completeness_transport
#print axioms Thesis.Causality.finiteSource_transported_joint_iff
#print axioms Thesis.Causality.finiteSource_transported_conditional_iff
#print axioms Thesis.Causality.DoCalculusDerivation.denotational_soundAt
#print axioms Thesis.Causality.CausalMode.transported_joint_iff
#print axioms Thesis.Causality.CausalMode.transported_conditional_iff
#print axioms Thesis.Causality.CausalMode.finiteSource_transported_joint_iff
#print axioms Thesis.Causality.CausalTransition.jointIdentifiable_iff
#print axioms Thesis.Causality.CausalTransition.compatibleWith_iff
#print axioms Thesis.Causality.Examples.TenureTrack.prob_offer_do_fit_true
#print axioms Thesis.Causality.Examples.TenureTrack.counterfactual_offer_do_fit_given_evidence
#print axioms Thesis.Causality.FiniteRationalCPT.toSCM_preserves_row
#print axioms Thesis.Probability.CommonDenominator.FiniteQMass.toRecord_preserves

/- `Nat.mul_assoc` demonstrates why literal axiom-freedom is not the boundary. -/
#print axioms Nat.mul_assoc
