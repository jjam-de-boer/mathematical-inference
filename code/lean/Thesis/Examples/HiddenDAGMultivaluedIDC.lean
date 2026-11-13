import Thesis.CausalTransport.GuardedAdmissibleCertificates
import Thesis.Examples.HiddenDAGMultivaluedPresentation

namespace Thesis.Causality.Examples.HiddenDAGMultivaluedIDC

open Probability Probability.Distros
open HiddenDAGMultivaluedPresentation
  (DeclaredValue witness conversion zeroValue zeroCode nullCode readValue counts coded domain_card)

/-!
# A named multivalued law through the actual conditional identification engine

Retain the declared count domain `{0, 1, 2}` of the hypergeometric fixture,
including its null value two. There are now three independent observed nodes:
`X` is factually zero, and `Y` and `Z` read independent copies of the named
finite-population count. The query has a nonempty action and a separate,
nonempty conditioner. At `Z = 0`, its evidence has probability one half and
the conditional outcome `Y = 1` also has probability one half.

The public guarded IDC program promotes the conditioner and really returns
the formula used below. Its published certificate is constructed from that
computed success, not from an independently supplied semantic equation or
handwritten support tree. The end-to-end value theorem then uses the
certificate's native soundness and its actual printed value.

Finally `Z = 2` is an unsupported original conditioner. Promotion can leave
the printed observational formula defined there, but does not create a value
for the original conditional query. These separate checks retain both the
named law's zero cells and the source-support boundary of the public API.
-/

def oneCode : Fin witness.card := witness.encode ⟨1, by decide⟩

def signature : ObservedSignature where
  count := 3
  Value := fun _ => Fin witness.card
  valueEnumeration := fun _ => List.finRange witness.card
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := by intro _; rw [domain_card]; decide
  defaultValue := fun _ => zeroCode
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩
def z : Fin signature.count := ⟨2, by decide⟩

def fullGraph : FiniteHiddenDAG signature where
  count := 3
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := fun _ => rfl
  node_classified := fun node => Or.inr ⟨node, rfl⟩
  edge := fun _ _ => false
  rank := Fin.val
  edge_rank_lt := by intro _ _ impossible; cases impossible

private theorem no_path {first second : Fin fullGraph.count}
    (path : fullGraph.HiddenInternalPath first second) : False := by
  cases path with
  | direct impossible => cases impossible
  | tail _ _ impossible => cases impossible

def projection : FiniteLatentProjection signature where
  hiddenDAG := fullGraph
  directed_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · intro path; exact False.elim (no_path path)
  bidirected := fun _ _ => false
  bidirected_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · rintro ⟨_, _, impossible, _, _⟩; cases impossible

/-- Independent copies of the actual named record supply the private noise.
The native subtype and observed codes remain connected by the proved
two-sided finite-domain conversion, rather than an occurrence decoder. -/
def model : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => DeclaredValue
  nodeEnumeration := fun _ => HiddenDAGMultivaluedPresentation.domain.attach
  node_complete := fun _ value => List.mem_attach _ value
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => conversion
  observedIndex := some
  observedIndex_observed := fun _ => rfl
  observedIndex_sound := fun _ _ same => (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ impossible; cases impossible
  Noise := fun _ => Fin witness.card
  noiseEnumeration := fun _ => List.finRange witness.card
  noise_complete := fun _ value => List.mem_finRange value
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => coded.record
  prior := FiniteProduct.record 3 (fun _ => Fin witness.card) (fun _ => coded.record)
  product_law := FiniteProduct.record_rectangular_probVal 3 (fun _ => Fin witness.card) (fun _ => coded.record)
  mechanism := fun child _parents noise => if child.val = 0 then zeroValue else witness.decode noise

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  condition := NodeSet.singleton z
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def reference : signature.Assignment := fun node => if node = y then oneCode else zeroCode

def half : QProb := ⟨1, 2, by decide⟩

/-- The reference value is the named distribution's genuine first-colour
mass, rather than a separately postulated probability table. -/
theorem named_outcome_half : QProb.Equiv (counts.record.probVal (fun value => value == 1)) half := by
  decide +kernel

/-- This is a recursive IDC example: the separate conditioner is promoted
before the joint identification call, rather than only taking a Bayes leaf. -/
theorem conditioner_promoted : (conditionalExchangeStep? projection.observedGraph query).isSome = true := by
  decide +kernel

/-- Elaborating `rfl` computes the actual public engine's successful output.
The inferred term is retained literally in the certificate's `result` field;
no fallback formula is substituted for a failed or unfinished computation. -/
noncomputable def certificate : PublishedAdmissibleConditionalCertificate projection query :=
  identifyGuardedConditionalKernel_admissibleCertificate query (by rfl)

theorem engine_identified :
    identifyGuardedConditionalKernel projection.observedGraph query = .identified certificate.formula :=
  certificate.result

/-- The original causal evidence is positive and genuinely non-certain. -/
theorem original_evidence_half : QProb.Equiv
    ((model.kernelDistribution query.operationKernel reference).probVal
      (query.operationKernel.conditionEvent reference)) half := by
  decide +kernel

theorem source_admissible : model.ConditioningAdmissibleAt query.operationKernel reference := by
  unfold FiniteHiddenDAGSCM.ConditioningAdmissibleAt
  decide +kernel

/-- Kernel-check the value without asking elaborator unification to expand
the entire nested native marginal. The following finite case split reads
that same result; it neither changes a recursion limit nor chooses a value. -/
theorem printed_half_check :
    (model.termDenote certificate.formula reference).map (fun value => decide (QProb.Equiv value half)) = some true := by
  decide +kernel

private def equivalentOfHalf (result : ProbabilityResult.Result)
    (checked : result.map (fun value => decide (QProb.Equiv value half)) = some true) :
    ProbabilityResult.Equivalent result (some half) := by
  cases result with
  | none => cases checked
  | some value =>
      refine ProbabilityResult.Equivalent.value ?_
      exact of_decide_eq_true (Option.some.inj checked)

/-- Read the actual printed output in the original nonpositive native model.
This carries a value in `Type`, without choosing one from an existence proof. -/
noncomputable def printed : model.TermSupportedAt certificate.formula reference :=
  ⟨half, equivalentOfHalf _ printed_half_check⟩

theorem used_conditionals : model.UsedConditionalsAdmissibleAt certificate.formula reference :=
  (model.usedConditionalsAdmissibleAt_iff_supported _ _).mpr ⟨printed⟩

/-- Engine output, certificate construction, primitive source/printed checks
and native soundness together compute the unchanged original query. -/
noncomputable def end_to_end_value :
    ProbabilityResult.Equivalent (model.termDenote query.sourceTerm reference) (some half) :=
  ProbabilityResult.trans (certificate.intrinsic_soundAt model reference source_admissible used_conditionals) printed.2

def nullReference : signature.Assignment := fun node => if node = z then nullCode else reference node

theorem null_original_evidence : ¬ model.ConditioningAdmissibleAt query.operationKernel nullReference := by
  unfold FiniteHiddenDAGSCM.ConditioningAdmissibleAt
  decide +kernel

/-- A defined printed expression is insufficient when the original causal
conditioner is null. The certificate's explicit source premise still applies. -/
noncomputable def printed_at_null_evidence : model.TermSupportedAt certificate.formula nullReference :=
  ⟨half, equivalentOfHalf _ (by decide +kernel)⟩

end Thesis.Causality.Examples.HiddenDAGMultivaluedIDC
