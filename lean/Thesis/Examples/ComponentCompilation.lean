import Thesis.CausalTransport.ComponentCompilation
import Thesis.Examples.KernelCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentKernelComponentCompilation

open Probability
open FrontDoorIdentification
open CurrentKernelCompilation

/-!
# Regression checks for current-kernel component extraction

The front-door graph has the gapped component `{X,Y}` and the separate
mediator component.  Extracting `{X,Y}` must fix the mediator while still
using prefix quotients of the full observational current expression.  This
is the graph-dependent step that whole-host chain compilation cannot supply.

A second extraction consumes a genuinely recursive input: first extract
the mediator, then compile its singleton host again under the nonempty
external action `{X,Y}`.  Its target quotients read the already extracted
product, rather than silently restarting from observational marginals.

The denotational checks use completed soundness only in this regression
module.  Every certificate constructor in the implementation remains
independent of the soundness module and carries its own support tree.
-/

/-! ## Extract the gapped bidirected component from the full host -/

/-- Function-valued node sets have a constructive Boolean equality test.
Use that test to check membership, instead of requesting a classical
`DecidableEq` instance for functions. -/
private theorem component_mem_of_any_equal (components : List (NodeSet S))
    (component : NodeSet S)
    (found : components.any (fun piece => NodeSet.equal piece component) = true) :
    component ∈ components := by
  rcases List.any_eq_true.mp found with ⟨piece, member, equal⟩
  have same := (NodeSet.equal_eq_true_iff piece component).mp equal
  rw [same] at member
  exact member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The executable partition, not merely a connected-subset witness,
certifies that `{X,Y}` is an entire component of the full host. -/
theorem gappedHost_mem_cComponents : gappedHost ∈ graph.cComponents NodeSet.full := by
  apply component_mem_of_any_equal
  decide +kernel

/-- A positive certified observational input seeds the general extraction.
The new source is `P(X,Y | do(M))`, and its current-input quotients still use
all three observational variables. -/
noncomputable def gappedComponentCompilation :
    PublishedCurrentKernelComponentCompilation (GraphModelClass.positive graph)
      graph.dSeparationCorrectness NodeSet.full NodeSet.empty gappedHost
      (observationalJointTerm signature) :=
  PublishedCurrentKernelComponentCompilation.ofComponent (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    NodeSet.full NodeSet.empty (ObservedGraph.KernelHostClosed.full graph)
    gappedHost_mem_cComponents observationalInput
    (fun _model member reference => member.2.kernelPositiveSupportedValue
      ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference)

/-- The component output keeps the full host in its prefix quotients;
only the selected factor list is restricted to `{X,Y}`. -/
theorem gappedComponentCompilation_formula :
    gappedComponentCompilation.certificate.formula =
      chainProductFrom NodeSet.full (observationalJointTerm signature) gappedHost :=
  gappedComponentCompilation.formula_eq

/-- Interpret the assembled derivation throughout the positive graph-model
class.  This exercises both graph-derived do-rules and the complete recursive
support tree, not just a numerical equality at one assignment. -/
noncomputable def gappedComponentCompilation_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨gappedHost, NodeSet.union NodeSet.empty
        (NodeSet.diff NodeSet.full gappedHost), NodeSet.empty⟩)
      gappedComponentCompilation.certificate.formula reference :=
  let certificate := gappedComponentCompilation.certificate.compile
  DoCalculusDerivation.denotational_soundAt
    (graph.publishedSoundness.primitive model member.1) certificate.derivation
    (certificate.supported model member reference
      (member.2.kernelPositiveSupportedValue
        ⟨gappedHost, NodeSet.union NodeSet.empty
          (NodeSet.diff NodeSet.full gappedHost), NodeSet.empty⟩ reference).toSupported)

/-! ## A recursive input and a nonempty retained external intervention -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The mediator is the other complete host component.  Its incoming
directed parent `X` will become an external action after restriction. -/
theorem mediator_mem_cComponents :
    NodeSet.singleton mediator ∈ graph.cComponents NodeSet.full := by
  apply component_mem_of_any_equal
  decide +kernel

/-- First extract `P(M | do(X,Y))` from the full current input. -/
noncomputable def mediatorComponentCompilation :
    PublishedCurrentKernelComponentCompilation (GraphModelClass.positive graph)
      graph.dSeparationCorrectness NodeSet.full NodeSet.empty (NodeSet.singleton mediator)
      (observationalJointTerm signature) :=
  PublishedCurrentKernelComponentCompilation.ofComponent (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    NodeSet.full NodeSet.empty (ObservedGraph.KernelHostClosed.full graph)
    mediator_mem_cComponents observationalInput
    (fun _model member reference => member.2.kernelPositiveSupportedValue
      ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The singleton mediator host is itself a complete component after
restriction.  No assumption about the old full-host partition is reused. -/
theorem mediator_mem_restricted_cComponents :
    NodeSet.singleton mediator ∈ graph.cComponents (NodeSet.singleton mediator) := by
  apply component_mem_of_any_equal
  decide +kernel

/-- Compile a second component extraction using the first extraction's
actual formula and positive-support field.  Host parent closure is obtained
by restriction, so its nonempty external parent is handled explicitly. -/
noncomputable def recursiveMediatorCompilation :
    PublishedCurrentKernelComponentCompilation (GraphModelClass.positive graph)
      graph.dSeparationCorrectness (NodeSet.singleton mediator)
      (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full (NodeSet.singleton mediator)))
      (NodeSet.singleton mediator) mediatorComponentCompilation.certificate.formula :=
  PublishedCurrentKernelComponentCompilation.ofComponent (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    (NodeSet.singleton mediator)
    (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full (NodeSet.singleton mediator)))
    ((ObservedGraph.KernelHostClosed.full graph).restrict (NodeSet.singleton mediator)
      (fun _ _ => rfl)) mediator_mem_restricted_cComponents
    mediatorComponentCompilation.certificate mediatorComponentCompilation.positive

/-- The nested formula reads the first extracted component product through
new singleton-host marginals.  It is not a fresh observational chain factor. -/
theorem recursiveMediatorCompilation_formula :
    recursiveMediatorCompilation.certificate.formula =
      chainProductFrom (NodeSet.singleton mediator)
        (chainProductFrom NodeSet.full (observationalJointTerm signature)
          (NodeSet.singleton mediator)) (NodeSet.singleton mediator) :=
  recursiveMediatorCompilation.formula_eq

/-- Published soundness checks the recursive certificate with its retained
external actions and its already extracted current expression.  This also
checks every support node in the second extraction throughout the positive
model class, not only the first extraction's support tree. -/
noncomputable def recursiveMediatorCompilation_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨NodeSet.singleton mediator,
        NodeSet.union
          (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full (NodeSet.singleton mediator)))
          (NodeSet.diff (NodeSet.singleton mediator) (NodeSet.singleton mediator)),
        NodeSet.empty⟩)
      recursiveMediatorCompilation.certificate.formula reference :=
  let certificate := recursiveMediatorCompilation.certificate.compile
  DoCalculusDerivation.denotational_soundAt
    (graph.publishedSoundness.primitive model member.1) certificate.derivation
    (certificate.supported model member reference
      (member.2.kernelPositiveSupportedValue
        ⟨NodeSet.singleton mediator,
          NodeSet.union
            (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full (NodeSet.singleton mediator)))
            (NodeSet.diff (NodeSet.singleton mediator) (NodeSet.singleton mediator)),
          NodeSet.empty⟩ reference).toSupported)

/-- The general terminal extraction assembler also preserves the engine's
explicit complementary marginal when selecting only `Y` from `{X,Y}`. -/
noncomputable def extractedYCertificate :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨NodeSet.singleton y,
        NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost), NodeSet.empty⟩) :=
  currentKernelComponentMarginalPublishedCertificate (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2) NodeSet.full NodeSet.empty
    (ObservedGraph.KernelHostClosed.full graph) gappedHost_mem_cComponents
    (NodeSet.singleton y)
    (NodeSet.singleton_subset_of_mem (by decide : gappedHost y = true)) observationalInput
    (fun _model member reference => member.2.kernelPositiveSupportedValue
      ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference)

/-- The complementary marginal remains explicit even after the two
graph-to-kernel conversions have been assembled into an action-free formula. -/
theorem extractedYCertificate_formula : extractedYCertificate.formula =
    .marginalize (NodeSet.diff gappedHost (NodeSet.singleton y))
      (chainProductFrom NodeSet.full (observationalJointTerm signature) gappedHost) := rfl

/-! ## A union of components does not need to be connected -/

/-- The whole front-door host contains two c-components, yet the general
closed-subset constructor can extract their union.  This exercises its
intentional generality beyond membership in the listed partition. -/
noncomputable def wholeHostUnionCompilation :
    PublishedCurrentKernelComponentCompilation (GraphModelClass.positive graph)
      graph.dSeparationCorrectness NodeSet.full NodeSet.empty NodeSet.full
      (observationalJointTerm signature) :=
  PublishedCurrentKernelComponentCompilation.ofClosed (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    NodeSet.full NodeSet.empty NodeSet.full (ObservedGraph.KernelHostClosed.full graph)
    (fun _ _ => rfl) (fun _ _ _ => rfl) observationalInput
    (fun _model member reference => member.2.kernelPositiveSupportedValue
      ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference)

/-! ## Empty subsets and the zero-node signature remain constructive -/

/-- Extract the empty subset of a genuinely empty observed signature.
The general union-of-components constructor does not demand a representative
vertex, connectedness, or a nonempty factor list. -/
noncomputable def zeroComponentCompilation :
    PublishedCurrentKernelComponentCompilation (GraphModelClass.positive zeroGraph)
      zeroGraph.dSeparationCorrectness NodeSet.full NodeSet.empty NodeSet.empty
      (observationalJointTerm zeroSignature) :=
  PublishedCurrentKernelComponentCompilation.ofClosed (C := GraphModelClass.positive zeroGraph)
    zeroGraph.dSeparationCorrectness (fun member => member.2)
    NodeSet.full NodeSet.empty NodeSet.empty (ObservedGraph.KernelHostClosed.full zeroGraph)
    (fun _ selected => by cases selected)
    (fun selected _ _ => by cases selected)
    (PublishedIdentificationCertificate.refl (observationalJointTerm zeroSignature)
      (observationalJointTerm_actionFree zeroSignature))
    (fun _model member reference => member.2.kernelPositiveSupportedValue
      ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference)

end CurrentKernelComponentCompilation
end Examples
end Causality
end Thesis
