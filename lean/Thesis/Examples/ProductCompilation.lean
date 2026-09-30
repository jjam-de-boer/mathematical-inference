import Thesis.CausalTransport.ProductCompilation
import Thesis.Examples.KernelCompilation
import Thesis.Causality.ModalDerivation

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentKernelProductCompilation

open Probability
open FrontDoorIdentification

/-!
# Regression checks for finite product regrouping

The front-door graph has the interleaving component `{X,Y}`: its reverse
topological vertex list is `[Y,M,X]`, whereas grouping by component gives
`[[Y,X],[M]]`.  This is a real factor permutation, not just a different
association of an already component-compatible chain.

The examples below exercise the general finite compiler.  They retain the
engine's singleton-product convention, test duplicate indices explicitly,
and admit the empty outer partition on a signature with no observed nodes.
Their certificates work throughout the compatible model class whenever the
source product has local support; observational positivity is not required
by the algebra itself.  Completed soundness is imported only through the
existing example module to verify the assembled derivation trees.
-/

/-! ## Interleaving the two front-door components -/

/-- Each displayed factor reads the full current expression, retaining the
replacement engine's prefix quotient and total-mass denominator. -/
def factor (node : Fin signature.count) : ProbabilityTerm signature :=
  chainFactorFrom NodeSet.full (observationalJointTerm signature) node

theorem factor_actionFree (node : Fin signature.count) : (factor node).ActionFree :=
  chainFactorFrom_actionFree NodeSet.full (observationalJointTerm signature) node
    (observationalJointTerm_actionFree signature)

/-- The component order intentionally does not coincide with the vertex
order.  The certificate must move `M` past the `X` factor. -/
noncomputable def interleavingCompilation :
    PublishedProductCompilation (GraphModelClass.all graph) graph.dSeparationCorrectness
      (productTerms ([y, mediator, x].map factor))
      (productTerms ([[y, x], [mediator]].map (fun block => productTerms (block.map factor)))) :=
  productTermsRegroupingCompilation [y, mediator, x] [[y, x], [mediator]]
    (.cons y (.swap x mediator []))
    (by
      intro block member
      rcases List.mem_cons.mp member with first | later
      · rw [first]; intro impossible; cases impossible
      · rcases List.mem_cons.mp later with second | absent
        · rw [second]; intro impossible; cases impossible
        · exact False.elim (List.not_mem_nil absent))
    factor (fun node _member => factor_actionFree node)

/-- The grouping retains the exact component product syntax; it does not
reintroduce a multiplication by one after the singleton mediator block. -/
theorem interleavingCompilation_formula :
    interleavingCompilation.certificate.formula =
      .multiply (.multiply (factor y) (factor x)) (factor mediator) :=
  interleavingCompilation.formula_eq

/-- Apply the completed soundness theorem to every compatible model and
every locally supported source valuation, checking all intermediate support.
This verifies a general certificate, not a numerical equality at one model. -/
noncomputable def interleavingCompilation_soundAt
    (model : ExactModel signature) (compatible : Compatible model graph)
    (reference : signature.Assignment)
    (sourceSupported : (productTerms ([y, mediator, x].map factor)).SupportedAt model reference) :
    ProbabilityTerm.EquivalentAt model (productTerms ([y, mediator, x].map factor))
      interleavingCompilation.certificate.formula reference :=
  let certificate := interleavingCompilation.certificate.compile
  certificate.derivation.denotational_soundAt
    (graph.publishedSoundness.primitive model compatible)
    (certificate.supported model compatible reference sourceSupported)

/-! ## Multiplicity, substitution, and an empty partition -/

/-- Repeated `Y` factors are distinct occurrences and must both survive.
The three explicit adjacent exchanges validate the finite compiler's search. -/
noncomputable def repeatedFactorCompilation :
    PublishedProductCompilation (GraphModelClass.all graph) graph.dSeparationCorrectness
      (productTerms ([y, mediator, x, y].map factor))
      (productTerms ([[y, y], [x, mediator]].map (fun block => productTerms (block.map factor)))) :=
  productTermsRegroupingCompilation [y, mediator, x, y] [[y, y], [x, mediator]]
    (List.Perm.cons y ((List.Perm.cons mediator (List.Perm.swap y x [])).trans
      ((List.Perm.swap y mediator [x]).trans
        (List.Perm.cons y (List.Perm.swap x mediator [])))))
    (by
      intro block member
      rcases List.mem_cons.mp member with first | later
      · rw [first]; intro impossible; cases impossible
      · rcases List.mem_cons.mp later with second | absent
        · rw [second]; intro impossible; cases impossible
        · exact False.elim (List.not_mem_nil absent))
    factor (fun node _member => factor_actionFree node)

/-- Certificate substitution preserves the target function even when a
finite index appears more than once.  Reflexive factors isolate this fold
from any graph assumption or positivity side condition. -/
noncomputable def repeatedFactorSubstitution :
    PublishedProductCompilation (GraphModelClass.all graph) graph.dSeparationCorrectness
      (productTerms ([y, mediator, y].map factor))
      (productTerms ([y, mediator, y].map factor)) :=
  productTermsMapPublishedCompilation [y, mediator, y] factor factor
    (fun node _member => PublishedIdentificationCertificate.refl (factor node)
      (factor_actionFree node)) (fun _node _member => rfl)

/-- Comparing two certified formulas reuses a supported common source.
The comparison tree must retain the reversed first certificate as well as
the second one; this regression checks the positive gapped-host instance. -/
noncomputable def gappedChainComparison :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness CurrentKernelCompilation.gappedChainCompilation.certificate.formula :=
  PublishedIdentificationCertificate.compareWithSupport
    CurrentKernelCompilation.gappedChainCompilation.certificate
    CurrentKernelCompilation.gappedInput
    (fun _model member reference => member.2.kernelPositiveSupportedValue
      ⟨CurrentKernelCompilation.gappedHost, NodeSet.empty, NodeSet.empty⟩ reference |>.toSupported)

/-- The compared gapped-host expressions agree at every positive compatible
model.  Source support is obtained from the first certificate's actual tree,
not postulated for its compiled expression. -/
noncomputable def gappedChainComparison_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model
      CurrentKernelCompilation.gappedChainCompilation.certificate.formula
      gappedChainComparison.formula reference := by
  let commonSupported := (member.2.kernelPositiveSupportedValue
    ⟨CurrentKernelCompilation.gappedHost, NodeSet.empty, NodeSet.empty⟩ reference).toSupported
  let firstSupported := CurrentKernelCompilation.gappedChainCompilation.certificate.supported
    model member reference commonSupported
  let certificate := gappedChainComparison.compile
  exact certificate.derivation.denotational_soundAt
    (graph.publishedSoundness.primitive model member.1)
    (certificate.supported model member reference firstSupported.endpoints.2)

/-- The empty outer family remains the explicit empty-outcome unit, even
when the observed signature itself is empty.  No nonempty-block witness or
chosen index is required in this case. -/
noncomputable def emptyPartitionCompilation :
    PublishedProductCompilation (GraphModelClass.all CurrentKernelCompilation.zeroGraph)
      CurrentKernelCompilation.zeroGraph.dSeparationCorrectness
      (unitProbabilityTerm CurrentKernelCompilation.zeroSignature)
      (unitProbabilityTerm CurrentKernelCompilation.zeroSignature) :=
  productTermsRegroupingCompilation ([] : List (Fin CurrentKernelCompilation.zeroSignature.count)) []
    .nil (fun _block absent => False.elim (List.not_mem_nil absent))
    (fun _node => unitProbabilityTerm CurrentKernelCompilation.zeroSignature)
    (fun _node absent => False.elim (List.not_mem_nil absent))

/-- The elementary partial law also handles failed support, rather than
coercing an undefined factor to zero.  This checks the semantic rule below
the locally supported certificate layer. -/
def unsupportedAssociation : ProbabilityResult.Equivalent
    (ProbabilityResult.multiply (ProbabilityResult.multiply none (some QProb.zero))
      (some QProb.one))
    (ProbabilityResult.multiply none
      (ProbabilityResult.multiply (some QProb.zero) (some QProb.one))) :=
  ProbabilityResult.multiply_assoc _ _ _

/-- Pure multiplication steps remain visible in modal annotations but do
not invent Pearl-rule cells or action/observation operations. -/
theorem multiplicationComm_modalRuleKinds :
    (DoCalculusDerivation.multiplyComm (G := graph) (factor x) (factor y)).toModalTrace.ruleKinds = [] :=
  rfl

theorem multiplicationAssoc_modalRuleKinds :
    (DoCalculusDerivation.multiplyAssoc (G := graph)
      (factor x) (factor mediator) (factor y)).toModalTrace.ruleKinds = [] :=
  rfl

end CurrentKernelProductCompilation
end Examples
end Causality
end Thesis
