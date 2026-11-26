import Thesis.Examples.CatalogueSampling
import Thesis.Examples.FiniteSymmetry
import Thesis.Probability.FiniteProductExtensional

namespace Thesis.Causality.Examples.InferenceWorkflowSymmetry
open Probability Probability.Distros FiniteProduct BinaryBow
open Causality.FiniteSymmetry Causality.CatalogueInference
open Examples.CatalogueInference Examples.CatalogueSampling

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# Structural symmetry of the executable inference catalogue

The two actual SCMs are precisely `CatalogueSampling.twoModels`: the fair
copy-chain and the independent fair pair. Complementation fixes each model
hypothesis and acts on observed bits, hard settings, and every private latent
bit together. The local transport checks below derive all interventional
event laws; no equality of those laws is supplied as an input certificate.

The same action takes the six-success cohort at `do(X=true)` to six failures
at `do(X=false)`. Both generative hypotheses assign the transformed cohort
the original likelihood. A representation-invariant complexity score can
therefore be used by the executable workflow on this very same catalogue.
-/

/-- Complement every coordinate, with the identity group element leaving
the assignment unchanged. -/
def outcomes : Action bitGroup signature.Assignment where
  act g state := fun node => Bool.xor g (state node)
  one_act := by intro state; funext node; exact bitAction.one_act _
  mul_act := by intro g h state; funext node; exact bitAction.mul_act g h _

/-- Complement only the values actually forced by a hard intervention.
The selected target set is retained and every unforced node stays unforced. -/
def transformIntervention (g : Bool) (action : HardIntervention signature) :
    HardIntervention signature where
  value node := (action.value node).map (Bool.xor g)

def experiments : Action bitGroup (HardIntervention signature) where
  act := transformIntervention
  one_act := by
    intro action
    apply HardIntervention.extensional
    intro node
    cases setting : action.value node with
    | none => simp [transformIntervention, setting, bitGroup] <;> rfl
    | some value => cases value <;> simp [transformIntervention, setting, bitGroup] <;> rfl
  mul_act := by
    intro g h action
    apply HardIntervention.extensional
    intro node
    cases setting : action.value node with
    | none => simp [transformIntervention, setting, bitGroup] <;> rfl
    | some value => cases g <;> cases h <;> cases value <;> simp [transformIntervention, setting, bitGroup] <;> rfl

/-- This pointwise operation works for either one or two private sources.
It is defined before choosing a probability law on their assignments. -/
def noiseFlip (count : Nat) (g : Bool) (unit : Fin count → Bool) : Fin count → Bool :=
  fun source => Bool.xor g (unit source)

private theorem noiseFlip_involutive (count : Nat) (g : Bool) (unit : Fin count → Bool) :
    noiseFlip count g (noiseFlip count g unit) = unit := by
  funext source
  change Bool.xor g (Bool.xor g (unit source)) = unit source
  cases g <;> cases unit source <;> rfl

private theorem fairBit_flip (g : Bool) (event : Event Bool) :
    QProb.Equiv (Examples.CatalogueInference.fairBit.probVal event)
      (Examples.CatalogueInference.fairBit.probVal (fun value => event (Bool.xor g value))) := by
  cases g with
  | false => rfl
  | true =>
      cases first : event false <;> cases second : event true <;>
        simp [Examples.CatalogueInference.fairBit, FiniteProbRecord.probVal,
          FiniteProbRecord.eventMass, QProb.Equiv, first, second]

private theorem rectangle_noiseFlip (count : Nat) (g : Bool)
    (events : (source : Fin count) → Bool → Bool) (unit : Fin count → Bool) :
    rectangularEvent count (fun _ => Bool) events (noiseFlip count g unit) =
      rectangularEvent count (fun _ => Bool)
        (fun source value => events source (Bool.xor g value)) unit := by
  apply Bool.eq_iff_iff.mpr
  rw [rectangularEvent_eq_true_iff, rectangularEvent_eq_true_iff]
  rfl

/-- Independent fair source bits are jointly invariant. Rectangle
factorization proves this for every finite source count, and constructive
finite extensionality extends it to every event, including null events. -/
theorem fairProduct_flip (count : Nat) (g : Bool) (event : Event (Fin count → Bool)) :
    QProb.Equiv
      ((record count (fun _ => Bool) (fun _ => Examples.CatalogueInference.fairBit)).probVal event)
      ((record count (fun _ => Bool) (fun _ => Examples.CatalogueInference.fairBit)).probVal
        (fun unit => event (noiseFlip count g unit))) := by
  let prior := record count (fun _ => Bool) (fun _ => Examples.CatalogueInference.fairBit)
  let renamed := prior.map (noiseFlip count g)
  have rectangles (events : (source : Fin count) → Bool → Bool) :
      QProb.Equiv (prior.probVal (rectangularEvent count (fun _ => Bool) events))
        (renamed.probVal (rectangularEvent count (fun _ => Bool) events)) := by
    have mapped : QProb.Equiv
        (renamed.probVal (rectangularEvent count (fun _ => Bool) events))
        (qProduct count (fun source => Examples.CatalogueInference.fairBit.probVal
          (fun value => events source (Bool.xor g value)))) :=
      QProb.equiv_trans (prior.map_probVal _ _)
        (QProb.equiv_trans (prior.probVal_congr _ _ (rectangle_noiseFlip count g events))
          (record_rectangular_probVal count (fun _ => Bool) _ _))
    exact QProb.equiv_trans (record_rectangular_probVal count (fun _ => Bool) _ events)
      (QProb.equiv_trans (qProduct_congr count (fun source => fairBit_flip g (events source)))
        (QProb.equiv_symm mapped))
  have whole := probVal_extensional_of_rectangles prior renamed
    (fun _ => [false, true]) (by intro _ value; cases value <;> simp)
    (fun _ => inferInstance) rectangles event
  exact QProb.equiv_trans whole (prior.map_probVal (noiseFlip count g) event)

private def observedEquivalence (g : Bool) :
    ValueEquivalence signature.Assignment signature.Assignment where
  forward := outcomes.act g
  backward := outcomes.act g
  backward_forward := by
    intro state
    funext node
    change Bool.xor g (Bool.xor g (state node)) = state node
    cases g <;> cases state node <;> rfl
  forward_backward := by
    intro state
    funext node
    change Bool.xor g (Bool.xor g (state node)) = state node
    cases g <;> cases state node <;> rfl

private def interventionEquivalence (g : Bool) :
    ValueEquivalence (HardIntervention signature) (HardIntervention signature) where
  forward := transformIntervention g
  backward := transformIntervention g
  backward_forward := by
    intro action
    apply HardIntervention.extensional
    intro node
    cases setting : action.value node with
    | none => simp [transformIntervention, setting, bitGroup] <;> rfl
    | some value => cases g <;> cases value <;> simp [transformIntervention, setting, bitGroup] <;> rfl
  forward_backward := by
    intro action
    apply HardIntervention.extensional
    intro node
    cases setting : action.value node with
    | none => simp [transformIntervention, setting, bitGroup] <;> rfl
    | some value => cases g <;> cases value <;> simp [transformIntervention, setting, bitGroup] <;> rfl

private def sourceEquivalence (count : Nat) (g : Bool) :
    ValueEquivalence (Fin count → Bool) (Fin count → Bool) :=
  ⟨noiseFlip count g, noiseFlip count g, noiseFlip_involutive count g, noiseFlip_involutive count g⟩

/-- The copy child's local equation commutes with the bit flip because it
reads the transformed actual parent. The source-law premise follows from
the independent fair source construction above. -/
def chainTransport (g : Bool) : ModelTransport chainModel chainModel where
  nodes := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  values _ := ⟨Bool.xor g, Bool.xor g,
    by intro value; cases g <;> cases value <;> rfl,
    by intro value; cases g <;> cases value <;> rfl⟩
  assignments := observedEquivalence g
  assignment_at _ _ := rfl
  interventions := interventionEquivalence g
  forced _ _ := rfl
  units := sourceEquivalence 1 g
  directed _ _ := rfl
  bidirected _ _ := rfl
  prior := fairProduct_flip 1 g
  mechanisms := by
    intro child source target unit agree
    rcases node_cases child with rfl | rfl
    · rfl
    · exact agree x rfl rfl

/-- Each independent node returns its own flipped source. Its mechanism
ignores the allowed directed edge both before and after relabelling. -/
def independentTransport (g : Bool) : ModelTransport independenceModel independenceModel where
  nodes := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  values _ := ⟨Bool.xor g, Bool.xor g,
    by intro value; cases g <;> cases value <;> rfl,
    by intro value; cases g <;> cases value <;> rfl⟩
  assignments := observedEquivalence g
  assignment_at _ _ := rfl
  interventions := interventionEquivalence g
  forced _ _ := rfl
  units := sourceEquivalence 2 g
  directed _ _ := rfl
  bidirected _ _ := rfl
  prior := fairProduct_flip 2 g
  mechanisms := by intro child source target unit agree; rfl

def catalogueTransport (g : Bool) (hypothesis : Fin 2) :
    ModelTransport (twoModels hypothesis) (twoModels hypothesis) := by
  by_cases first : hypothesis.val = 0
  · simpa only [twoModels, if_pos first] using chainTransport g
  · simpa only [twoModels, if_neg first] using independentTransport g

/-- Split the finite index before reducing its dependent source carrier. -/
private theorem hypothesis_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have bounded := i.isLt
  by_cases atCopy : i.val = 0
  · exact Or.inl (Fin.ext atCopy)
  · exact Or.inr (Fin.ext (by change i.val = 1; omega))

/-- The action is closed on the actual two-model catalogue. Both models
are individually symmetric, so this action fixes the hypothesis indices. -/
def modelFamily : ModelFamilyAction bitGroup (Fin 2) signature where
  hypotheses := Action.trivial bitGroup _
  outcomes := outcomes
  experiments := experiments
  models := twoModels
  transport := catalogueTransport
  outcomes_agree := by
    intro g hypothesis state
    rcases hypothesis_cases hypothesis with rfl | rfl <;> rfl
  experiments_agree := by
    intro g hypothesis action
    rcases hypothesis_cases hypothesis with rfl | rfl <;> rfl

def signatureAction : SignatureAction bitGroup signature where
  nodes := Action.trivial bitGroup _
  values :=
    { act := fun g value => ⟨value.1, Bool.xor g value.2⟩
      one_act := by intro ⟨node, value⟩; cases value <;> rfl
      mul_act := by intro g h ⟨node, value⟩; cases g <;> cases h <;> cases value <;> rfl }
  coordinate := by intro _ _ _; rfl

/-- Packed latent states retain their hypothesis-dependent source count.
The local transports provide the primitive flip at that actual count. -/
private theorem pack_same {i : Fin 2} {first second : (twoModels i).latent.Assignment}
    (equal : first = second) :
    (⟨i, first⟩ : Sigma (fun k : Fin 2 => (twoModels k).latent.Assignment)) = ⟨i, second⟩ :=
  congrArg (fun unit =>
    (⟨i, unit⟩ : Sigma (fun k : Fin 2 => (twoModels k).latent.Assignment))) equal

def sourceAction : Action bitGroup
    (Sigma fun hypothesis : Fin 2 => (twoModels hypothesis).latent.Assignment) where
  act g packed := ⟨packed.1, (catalogueTransport g packed.1).units.forward packed.2⟩
  one_act := by
    intro ⟨hypothesis, unit⟩
    rcases hypothesis_cases hypothesis with same | same <;> subst hypothesis <;>
      apply pack_same <;> funext source <;> exact bitAction.one_act (unit source)
  mul_act := by
    intro g h ⟨hypothesis, unit⟩
    rcases hypothesis_cases hypothesis with same | same <;> subst hypothesis <;>
      apply pack_same <;> funext source <;> exact bitAction.mul_act g h (unit source)

def coherentModelFamily : CoherentModelFamilyAction bitGroup (Fin 2) signature where
  family := modelFamily
  signature := signatureAction
  assignments := by intro _ _ _; rfl
  nodes_agree := by
    intro g hypothesis node
    rcases hypothesis_cases hypothesis with rfl | rfl <;> rfl
  values_agree := by
    intro g hypothesis node value
    rcases hypothesis_cases hypothesis with rfl | rfl <;> rfl
  noise := sourceAction
  noise_agree := by intro _ _ _; rfl

/-- Every event and every hard action of the workflow catalogue transforms
correctly, with the action changed along with the observed labels. -/
theorem all_interventions_equivariant (g : Bool) (hypothesis : Fin 2)
    (action : HardIntervention signature) (event : Event signature.Assignment) :
    QProb.Equiv
      ((twoModels hypothesis).interventionalValue (transformIntervention g action).value event)
      ((twoModels hypothesis).interventionalValue action.value
        (fun state => event (outcomes.act g state))) :=
  modelFamily.interventionalValue g hypothesis action event

/-- Simpler copy-chain descriptions receive twice the mass of the
independent-pair description at budget one in the workflow prior. -/
def complexityScore (hypothesis : Fin 2) : Nat := if hypothesis.val = 0 then 0 else 1

theorem complexityScore_invariant : modelFamily.hypotheses.ScoreInvariant complexityScore := by
  intro _ _
  rfl

/-- The catalogue action fixes each hypothesis, so every declared prior on
these two models is invariant. In particular this applies to the workflow's
unequal complexity-sensitive prior, without requiring equal model masses. -/
theorem prior_invariant (prior : Distro (Fin 2)) :
    PriorInvariant modelFamily.hypotheses prior := by
  intro g event
  exact prior.map_probVal (modelFamily.hypotheses.act g) event

def doXFalse : HardIntervention signature :=
  (HardIntervention.empty signature).set x false

theorem flip_doX : transformIntervention true doX = doXFalse := by
  apply HardIntervention.extensional
  intro node
  rcases node_cases node with rfl | rfl <;> decide +kernel

/-- The full transformed count object retains all four joint cells in the
same declared order; six observations move from `(true,true)` to `(false,false)`. -/
def sixFailures : CountSample signature where
  bins := signature.assignmentEnumeration.map fun state =>
    if decide (state x = false) && decide (state y = false) then 6 else 0
  dimension := by simp

def failureExperiment : CountExperiment signature := ⟨.intervene doXFalse, sixFailures⟩

/-- Pull back the count at each transformed label through the inverse
outcome action. This explicit histogram transport keeps the declared alphabet
and its zero-count cells, rather than recording only the occupied label. -/
def transformSample (g : Bool) (sample : CountSample signature) : CountSample signature where
  bins := signature.assignmentEnumeration.map fun state =>
    sample.bins.getD
      (signature.assignmentEnumeration.idxOf (outcomes.act (bitGroup.inv g) state)) 0
  dimension := by simp

theorem flip_sixSuccesses : (transformSample true sixSuccesses).bins = sixFailures.bins := by
  decide +kernel

/-- Rename the experiment's setting together with its complete observed
histogram. Observation remains observation; a forced value is complemented. -/
def transformCohort (g : Bool) (cohort : CountExperiment signature) :
    CountExperiment signature where
  tag := match cohort.tag with
    | .observational => .observational
    | .intervene action => .intervene (transformIntervention g action)
  sample := transformSample g cohort.sample

private theorem countSample_eq_of_bins {left right : CountSample signature}
    (same : left.bins = right.bins) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- Equality concerns the whole typed cohort, including its hard setting
and all count cells; it is stronger than merely matching one sample total. -/
theorem flip_successExperiment :
    transformCohort true successExperiment = failureExperiment := by
  change CountExperiment.mk (.intervene (transformIntervention true doX))
      (transformSample true sixSuccesses) = CountExperiment.mk (.intervene doXFalse) sixFailures
  rw [flip_doX, countSample_eq_of_bins flip_sixSuccesses]

/-- Both actual SCM likelihoods retain their values after the action and
the complete joint cohort are complemented together. -/
theorem failure_likelihoods (hypothesis : Fin 2) :
    QProb.Equiv (iidModelCountLikelihood (twoModels hypothesis) failureExperiment)
      (twoLikelihoods hypothesis) := by
  by_cases first : hypothesis.val = 0
  · simp only [twoModels, twoLikelihoods, if_pos first]
    decide +kernel
  · simp only [twoModels, twoLikelihoods, if_neg first]
    decide +kernel

theorem cohort_likelihoods_unchanged (hypothesis : Fin 2) :
    QProb.Equiv (iidModelCountLikelihood (twoModels hypothesis) failureExperiment)
      (iidModelCountLikelihood (twoModels hypothesis) successExperiment) :=
  QProb.equiv_trans (failure_likelihoods hypothesis)
    (QProb.equiv_symm (twoLikelihoods_sampling hypothesis))

/-- Runtime checks display the actual transformed setting and full count
cohort. The two model likelihood comparisons execute the fixed-SCM sampling
programs whose equality is also checked by `cohort_likelihoods_unchanged`. -/
def report : String :=
  let settingFlipped := (transformIntervention true doX).value x == some false
  let countsFlipped := (transformSample true sixSuccesses).bins == sixFailures.bins
  let likelihoodsRetained := (List.finRange 2).all fun hypothesis =>
    decide (QProb.Equiv (iidModelCountLikelihood (twoModels hypothesis) failureExperiment)
      (iidModelCountLikelihood (twoModels hypothesis) successExperiment))
  s!"Symmetry of both actual SCMs: flipped do(X=true) to do(X=false) = {settingFlipped}; " ++
    s!"transformed six-success cohort = six failures: {countsFlipped}; " ++
    s!"same likelihoods after transforming setting and cohort: {likelihoodsRetained}."

end Thesis.Causality.Examples.InferenceWorkflowSymmetry
