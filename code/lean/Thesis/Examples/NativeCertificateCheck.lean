import Thesis.CausalTransport.NativeCertificateCheck
import Thesis.Examples.NativeSupportProfiles

namespace Thesis.Causality.Examples.NativeCertificateCheck

open Probability ProbabilityCode NativeSupportProfiles

/-!
# Serialized proof checks, hidden intermediate failures and observable guards

The three-valued native fixture keeps its declared null value. We check
malformed dictionary references, false graphical leaves, incompatible proof
joins and source mismatches. A strict chain followed by its inverse has
defined printed endpoints at the null value, but an undefined intermediate
conditional: syntax succeeds and full support certification correctly fails.
The weighted congruence instead skips its null factor at a defined zero.

Only tiny explicitly supplied actual-profile lists are executed here. The
fixed-DAG and projection-wide adapters are exercised symbolically, rather
than expanding their enormous complete catalogues. The small-list soundness
example supplies its actual representative and proved support agreement.
-/

def source : TermCode := .kernel ⟨1, 0, 0⟩
def nullTerm : TermCode := .kernel ⟨1, 0, 1⟩
def chainStep : DerivationCode := .primitive .chain ⟨0, 0, 1, 0⟩
def strictCycle : DerivationCode := .trans chainStep (.symm chainStep)
def weighted : DerivationCode := .congr .weightedMultiply (.refl .zero) (.refl nullTerm)
def nullCell : NativeSupportGuard.Cell := ⟨[true, true, false], 2⟩
def profiles : List (NativeTemplateInstance projection) := [entry.uniformSupport]

example : ProbabilityCode.mask signature 2 = none := by decide +kernel
example : ProbabilityCode.assignment signature 3 = none := by decide +kernel
example : (TermCode.evaluateAt 3 source).decode signature = none := by decide +kernel
example : (TermCode.kernel ⟨2, 0, 0⟩).decode signature = none := by decide +kernel
example : ((DerivationCode.primitive .rule1 ⟨1, 1, 0, 0⟩).check projection.observedGraph).isSome = false := by decide +kernel
example : ((DerivationCode.trans (.refl .zero) (.refl source)).check projection.observedGraph).isSome = false := by decide +kernel
example : ((DerivationCode.eqCongr .zero source (.refl source)).check projection.observedGraph).isSome = false := by decide +kernel

/-- Every existing algebraic primitive and congruence is represented, not
just the do-rule leaf used by one happy-path example. -/
example : ([.rule1, .rule2, .rule3, .marginalization, .conditioning, .chain, .weightedChain] : List PrimitiveCode).all
    (fun kind => ((DerivationCode.primitive kind ⟨0, 1, 0, 0⟩).check projection.observedGraph).isSome) = true := by decide +kernel
example : ([.add, .multiply, .weightedMultiply, .divide] : List CongruenceCode).all
    (fun kind => ((DerivationCode.congr kind (.refl source) (.refl source)).check projection.observedGraph).isSome) = true := by decide +kernel
example : ([.symm (.refl source), .multiplyComm source .zero, .multiplyAssoc source .zero source,
    .marginalizeCongr 1 (.refl source), .evaluateAtCongr 2 (.refl source), .eqCongr source source (.refl source)] : List DerivationCode).all
    (fun code => (code.check projection.observedGraph).isSome) = true := by decide +kernel

def goodCode : NativeCertificateCode := ⟨source, .derivation (.refl source), [nullCell]⟩
def badIntermediateCode : NativeCertificateCode := ⟨source, .derivation strictCycle, [nullCell]⟩
def weightedCode : NativeCertificateCode :=
  ⟨.weightedMultiply .zero nullTerm, .derivation weighted, [nullCell]⟩

theorem strict_syntax_passes : (strictCycle.check projection.observedGraph).isSome = true := by decide +kernel
theorem printed_endpoints_have_values : (entry.model.termDenote (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩) (reference 2)).isSome = true := by decide +kernel
theorem hidden_intermediate_rejected : (badIntermediateCode.checkOn projection.observedGraph profiles).isSome = false := by decide +kernel
theorem weighted_null_factor_accepted : (weightedCode.checkOn projection.observedGraph profiles).isSome = true := by decide +kernel
theorem unchanged_source_accepted : (goodCode.checkOn projection.observedGraph profiles).isSome = true := by decide +kernel

example : (({ goodCode with source := .zero }).checkOn projection.observedGraph profiles).isSome = false := by decide +kernel
example : (({ goodCode with guard := [⟨[true, true, false], 3⟩] }).checkOn projection.observedGraph profiles).isSome = false := by decide +kernel

def actionful : TermCode := .weightedMultiply .zero (.kernel ⟨1, 1, 0⟩)
example : ((⟨actionful, .derivation (.refl actionful), [nullCell]⟩ : NativeCertificateCode).checkOn projection.observedGraph profiles).isSome = false := by decide +kernel

/-- A conditional certificate may be syntactically valid yet unavailable at
its null conditioner. Guard checking never invents its source support. -/
def conditionalCode : NativeCertificateCode := ⟨nullTerm, .derivation (.refl nullTerm), [nullCell]⟩
def conditional : CheckedNativeFormula projection.observedGraph profiles :=
  (conditionalCode.checkOn projection.observedGraph profiles).get (by decide +kernel)
example : conditional.available entry.model.observationalDist (reference 2) = false := by decide +kernel

def good : CheckedNativeFormula projection.observedGraph profiles :=
  (goodCode.checkOn projection.observedGraph profiles).get (by decide +kernel)

theorem good_available : good.available entry.model.observationalDist (reference 2) = true := by decide +kernel

noncomputable def good_sound : entry.model.TermEquivalentAt good.source good.formula (reference 2) :=
  good.soundAt entry.model rfl ⟨entry.uniformSupport, List.mem_cons_self, entry.uniformSupport_agreement⟩ (reference 2)
    (ProbabilityResult.supportedOfIsSome _ (by decide +kernel)) good_available

/-- Rule 1 can remove a null conditioner from an empty outcome. Its printed
answer is one, but the original conditional query still has no value. This
must not become a soundness theorem without the separate source premise. -/
def nullSourceCode : NativeCertificateCode :=
  ⟨.kernel ⟨0, 0, 1⟩, .derivation (.primitive .rule1 ⟨0, 0, 1, 0⟩), [nullCell]⟩
def nullSource : CheckedNativeFormula projection.observedGraph profiles :=
  (nullSourceCode.checkOn projection.observedGraph profiles).get (by decide +kernel)
example : nullSource.available entry.model.observationalDist (reference 2) = true := by decide +kernel
theorem null_source_has_no_support : ¬ Nonempty (entry.model.TermSupportedAt nullSource.source (reference 2)) := by
  intro ⟨supported⟩
  have actual : (entry.model.termDenote nullSource.source (reference 2)).isSome = false := by decide +kernel
  have impossible := ProbabilityResult.supported_isSome supported
  rw [actual] at impossible
  cases impossible

def pointZero : FiniteProbRecord (Fin 3) where
  atoms := [(0, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

def almostSureEntry : NativeTemplateInstance projection := ⟨entry.template, fun _ => pointZero⟩
def almostSureCode : NativeCertificateCode :=
  ⟨.kernel ⟨1, 1, 0⟩, .actionOne ⟨1, 1, 0⟩, [⟨[true, false, false], 0⟩]⟩

example : (almostSureCode.checkOn projection.observedGraph [almostSureEntry]).isSome = true := by decide +kernel

/-- An irrelevant first profile must not conceal the later matching profile
where the probability-one action guard fails. This is a universal check. -/
example : (({ almostSureCode with guard := [⟨[true, true, false], 0⟩] }).checkOn
    projection.observedGraph [almostSureEntry, entry.uniformSupport]).isSome = false := by decide +kernel

/-- Both complete-model-class application theorems remain usable without
an external support-profile coverage interface. The source premise stays
explicit, independently of observed guard and printed availability. -/
noncomputable def fixed_original_sound
    (checked : CheckedNativeFormula projection.observedGraph projection.completeSupportCatalogue)
    (supported : entry.model.TermSupportedAt checked.source (reference 2))
    (accepted : checked.available entry.model.observationalDist (reference 2) = true) :
    entry.model.TermEquivalentAt checked.source checked.formula (reference 2) :=
  checked.fixed_soundAt entry.model (reference 2) supported accepted

noncomputable def projection_original_sound
    (checked : CheckedNativeFormula projection.observedGraph projection.observedGraph.cliqueRootProjection.completeSupportCatalogue)
    (supported : projected.model.TermSupportedAt checked.source (reference 2))
    (accepted : checked.available projected.model.observationalDist (reference 2) = true) :
    projected.model.TermEquivalentAt checked.source checked.formula (reference 2) :=
  checked.projected_soundAt projected (reference 2) supported accepted

namespace DirectedPair

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> decide
  value_nodup := by intro _; decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by
    intro parent child edge
    have pair := of_decide_eq_true edge
    rw [pair.1, pair.2]
    decide

def graph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ impossible; cases impossible
  bidirected_irreflexive := fun _ => rfl

def quad : QuadCode := ⟨0, 2, 1, 0⟩

example : ((DerivationCode.primitive .rule1 quad).check graph).isSome = false := by decide +kernel
example : ((DerivationCode.primitive .rule2 quad).check graph).isSome = true := by decide +kernel
/-- Cutting incoming arrows to the proposed action does not erase its
outgoing causal path. Using an outgoing cut for rule 3 would wrongly pass. -/
example : ((DerivationCode.primitive .rule3 quad).check graph).isSome = false := by decide +kernel

end DirectedPair
end Thesis.Causality.Examples.NativeCertificateCheck
