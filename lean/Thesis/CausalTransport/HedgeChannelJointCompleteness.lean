import Thesis.CausalTransport.HedgeChannelCounterexample
import Thesis.CausalTransport.CompletenessAssembly

namespace Thesis
namespace Causality

/-!
# Published joint completeness from the unrestricted hedge construction

This one-way assembly boundary connects the general channel countermodels to
the already proved original-query failure extractor and literal-output success
compiler.  The countermodel core remains independent of soundness.  Only this
certificate assembly imports the boundary which uses published soundness to
verify successful derivations.

For the positive model class on any supplied value-rich finite signature,
failure refutes joint identifiability and identifiability supplies a published
joint certificate.  The engine's own computed result is matched constructively;
there is no excluded-middle test of identifiability and no selection from a
mere existence proposition.  These declarations discharge the joint field
and hedge field of `PublishedCompleteness`, but not its conditional field.
-/

variable {S : ObservedSignature.{0}}

/-- A failed original joint invocation is genuinely non-identifiable in
the full-alphabet positive class.  The extractor supplies the original query's
hedge; the unrestricted construction supplies both actual countermodels. -/
theorem ObservedGraph.identifyJointKernel_failed_not_identifiable
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) {fail : IdentificationFail S}
    (result : identifyJointKernel graph query = .failed fail) :
    ¬ (GraphModelClass.positive graph).identifiable query :=
  identifyJointKernel_failed_not_identifiable_of_hedgeCounterexamples
    (C := GraphModelClass.positive graph)
    (fun _ witness => HedgeChannelInstallation.counterexample witness rich) query result

/-- The published joint-completeness theorem for every value-rich finite
signature, with no assumed countermodel family.  The certificate concerns the
original kernel and the actual identified expression, in the same positive
model class.  Universal conditional completeness remains separate. -/
noncomputable def ObservedGraph.publishedJointCompleteness
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S)
    (identifiable : (GraphModelClass.positive graph).identifiable query) :
    PublishedJointCertificate (GraphModelClass.positive graph) graph.dSeparationCorrectness query :=
  publishedJointCertificateOfIdentifiableOfHedgeCounterexamples
    (C := GraphModelClass.positive graph) graph.dSeparationCorrectness
    (fun member => member.2) (fun _ witness => HedgeChannelInstallation.counterexample witness rich)
    query identifiable

end Causality
end Thesis
