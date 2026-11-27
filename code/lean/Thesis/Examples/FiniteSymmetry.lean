import Thesis.Causality.ModelSymmetry
import Thesis.CausalTransport.CatalogueSymmetry

namespace Thesis.Examples.FiniteSymmetry
open Probability Probability.Distros Causality Causality.FiniteSymmetry

/-!
# Symmetry acceptance examples with causal and Bayesian content

The copy-chain example is structurally symmetric under flipping the root
bit, both observed bits, and any forced intervention values together. Its
law at the *unchanged* action `do(X=true)` is not invariant under that flip.
The distinction is therefore witnessed by an actual responding SCM, not
only by a law-level premise in the symmetry API.

The Bayesian example separately shows what symmetric knowledge means. A
fair prior is invariant; one asymmetric observation yields a non-invariant
posterior. Renaming that observation yields the renamed posterior, exactly
as the general transport theorem promises.
-/

def fairBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def copySignature : ObservedSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ b; cases b <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by decide +kernel

/-- The root and responding child are named by explicit finite indices.
Their bounds reduce from the declared two-node signature. -/
def x : Fin copySignature.count := ⟨0, by decide⟩
def y : Fin copySignature.count := ⟨1, by decide⟩

private theorem node_cases (node : Fin copySignature.count) : node = x ∨ node = y := by
  have bounded : node.val < 2 := node.isLt
  by_cases atRoot : node.val = 0
  · exact Or.inl (Fin.ext atRoot)
  · exact Or.inr (Fin.ext (by change node.val = 1; omega))

def copyLatent : LatentExtension copySignature where
  count := 1
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ b; cases b <;> simp
  valueDecidableEq _ := inferInstance
  incident _ child := decide (child.val = 0)

def unit (b : Bool) : copyLatent.Assignment := fun _ => b

def rootPrior : FiniteProbRecord copyLatent.Assignment := fairBit.map unit

/-- One private fair root feeds X, and Y responds by copying its actual
parent X. The outcome equation continues responding after an intervention;
the example is not two independently declared experimental tables. -/
def copyModel : ExactModel copySignature where
  latent := copyLatent
  factor _ := fairBit
  prior := rootPrior
  product_law := by
    intro events
    simpa [rootPrior, copyLatent, LatentExtension.rectangularEvent,
      FiniteProduct.rectangularEvent, FiniteProduct.qProduct,
      QProb.mul, QProb.one, QProb.Equiv] using
      (fairBit.map_probVal unit (copyLatent.rectangularEvent events))
  mechanism child parents inputs :=
    if root : child = x then
      inputs (0 : Fin 1) (by simp [copyLatent, root, x])
    else parents x (by
      rcases node_cases child with same | same
      · exact (root same).elim
      · simp [copySignature, x, y, same])

/-- The same group element flips every observed coordinate. Pointwise group
laws are inherited from the one-bit action; no observational law is used. -/
def observedAction : Action bitGroup copySignature.Assignment where
  act g state := fun node => Bool.xor g (state node)
  one_act := by intro state; funext node; exact bitAction.one_act _
  mul_act := by intro g h state; funext node; exact bitAction.mul_act g h _

def actionFlip (g : Bool) (action : HardIntervention copySignature) :
    HardIntervention copySignature where
  value node := (action.value node).map (Bool.xor g)

/-- Hard settings are transformed along with outcomes. In particular,
the group element `true` takes `do(X=true)` to `do(X=false)`. -/
def experimentAction : Action bitGroup (HardIntervention copySignature) where
  act := actionFlip
  one_act := by
    intro action
    apply HardIntervention.extensional
    intro node
    cases setting : action.value node with
    | none => simp [actionFlip, setting, bitGroup] <;> rfl
    | some b => cases b <;> simp [actionFlip, setting, bitGroup] <;> rfl
  mul_act := by
    intro g h action
    apply HardIntervention.extensional
    intro node
    cases setting : action.value node with
    | none => simp [actionFlip, setting, bitGroup] <;> rfl
    | some b => cases g <;> cases h <;> cases b <;> simp [actionFlip, setting, bitGroup] <;> rfl

def noiseFlip (g : Bool) (u : copyLatent.Assignment) : copyLatent.Assignment :=
  fun node => Bool.xor g (u node)

private theorem noiseFlip_involutive (g : Bool) (u : copyLatent.Assignment) :
    noiseFlip g (noiseFlip g u) = u := by
  funext node
  change Bool.xor g (Bool.xor g (u node)) = u node
  cases g <;> cases u node <;> rfl

private theorem observedFlip_involutive (g : Bool) (state : copySignature.Assignment) :
    observedAction.act g (observedAction.act g state) = state := by
  funext node
  change Bool.xor g (Bool.xor g (state node)) = state node
  cases g <;> cases state node <;> rfl

private theorem experimentFlip_involutive (g : Bool) (action : HardIntervention copySignature) :
    actionFlip g (actionFlip g action) = action := by
  apply HardIntervention.extensional
  intro node
  cases setting : action.value node with
  | none => simp [actionFlip, setting] <;> rfl
  | some b => cases g <;> cases b <;> simp [actionFlip, setting] <;> rfl

private theorem rootPrior_flip (g : Bool) (event : Event copyLatent.Assignment) :
    QProb.Equiv (rootPrior.probVal event)
      (rootPrior.probVal (fun u => event (noiseFlip g u))) := by
  cases g with
  | false => rfl
  | true =>
      have flipFalse : noiseFlip true (unit false) = unit true := rfl
      have flipTrue : noiseFlip true (unit true) = unit false := rfl
      cases left : event (unit false) <;> cases right : event (unit true) <;>
        simp [rootPrior, fairBit, FiniteProbRecord.map, FiniteProbRecord.probVal,
          FiniteProbRecord.eventMass, QProb.Equiv, flipFalse, flipTrue, left, right]

/-- All fields concern primitive mechanism inputs, the actual prior, and
inverse-bearing names. Full interventional equivariance below is derived
by the generic structural theorem. -/
def copyTransport (g : Bool) : ModelTransport copyModel copyModel where
  nodes := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  values _ := ⟨Bool.xor g, Bool.xor g,
    by intro b; cases g <;> cases b <;> rfl,
    by intro b; cases g <;> cases b <;> rfl⟩
  assignments := ⟨observedAction.act g, observedAction.act g,
    observedFlip_involutive g, observedFlip_involutive g⟩
  assignment_at _ _ := rfl
  interventions := ⟨actionFlip g, actionFlip g,
    experimentFlip_involutive g, experimentFlip_involutive g⟩
  forced _ _ := rfl
  units := ⟨noiseFlip g, noiseFlip g, noiseFlip_involutive g, noiseFlip_involutive g⟩
  directed _ _ := rfl
  bidirected _ _ := rfl
  prior := rootPrior_flip g
  mechanisms := by
    intro child source target u agree
    rcases node_cases child with rfl | rfl
    · rfl
    · exact agree x rfl rfl

/-- The group action is coherent already on labelled values: node names
are fixed while their Boolean values are complemented together. Keeping
the labels in a dependent pair makes the definition type-correct for the
general heterogeneous-signature interface as well. -/
def copySignatureAction : SignatureAction bitGroup copySignature where
  nodes := Action.trivial bitGroup _
  values :=
    { act := fun g value => ⟨value.1, Bool.xor g value.2⟩
      one_act := by intro ⟨node, value⟩; cases value <;> rfl
      mul_act := by
        intro g h ⟨node, value⟩
        cases g <;> cases h <;> cases value <;> rfl }
  coordinate := by intro _ _ _; rfl

/-- There is one physical model hypothesis in this fixture; value and
intervention labels move, while its equations are structurally symmetric.
The family interface is also available for genuinely different models. -/
def copyFamily : ModelFamilyAction bitGroup Unit copySignature where
  hypotheses := Action.trivial bitGroup Unit
  outcomes := observedAction
  experiments := experimentAction
  models _ := copyModel
  transport g _ := copyTransport g
  outcomes_agree := by intro _ _ _; rfl
  experiments_agree := by intro _ _ _; rfl

/-- The same relabelling acts on the packed hypothesis/noise carrier. Its
group laws concern each actual latent state, independently of the prior. -/
def copyNoiseAction : Action bitGroup
    (Sigma fun h : Unit => (copyFamily.models h).latent.Assignment) where
  act g packed := ⟨packed.1, noiseFlip g packed.2⟩
  one_act := by
    intro ⟨hypothesis, u⟩
    let pack (state : copyLatent.Assignment) :
        Sigma (fun h : Unit => (copyFamily.models h).latent.Assignment) := ⟨hypothesis, state⟩
    exact congrArg pack (funext fun node => bitAction.one_act (u node))
  mul_act := by
    intro g h ⟨hypothesis, u⟩
    let pack (state : copyLatent.Assignment) :
        Sigma (fun model : Unit => (copyFamily.models model).latent.Assignment) := ⟨hypothesis, state⟩
    exact congrArg pack (funext fun node => bitAction.mul_act g h (u node))

/-- A complete inhabitant of the primitive-name coherence interface. The
resulting law theorem is derived from local mechanism commutation, not
inserted as an unexplained equality of experimental distributions. -/
def coherentCopyFamily : CoherentModelFamilyAction bitGroup Unit copySignature where
  family := copyFamily
  signature := copySignatureAction
  assignments := by
    intro g state node
    rfl
  nodes_agree := by intro _ _ _; rfl
  values_agree := by intro _ _ _ _; rfl
  noise := copyNoiseAction
  noise_agree := by intro _ _ _; rfl

/-- Every hard intervention and every whole observed event is covered by
the structural symmetry, not just the numerical example displayed below. -/
theorem copy_interventional_equivariance (g : Bool)
    (action : HardIntervention copySignature) (event : Event copySignature.Assignment) :
    QProb.Equiv (copyModel.interventionalValue (actionFlip g action).value event)
      (copyModel.interventionalValue action.value
        (fun state => event (observedAction.act g state))) :=
  (copyTransport g).interventionalValue action event

def doXTrue : HardIntervention copySignature :=
  (HardIntervention.empty copySignature).set x true

theorem flip_changes_forced_value :
    (experimentAction.act true doXTrue).value x = some false := by decide +kernel

/-- The individual copy model is structurally symmetric, but this hard
setting is moved by that symmetry. The API's fixed-experiment hypothesis
therefore cannot be supplied for this action. -/
theorem copy_flip_does_not_fix_experiment :
    ¬ (copyTransport true).FixesExperiment doXTrue := by
  intro fixed
  have sameValue := congrArg (fun action : HardIntervention copySignature => action.value x) fixed
  have different :
      ((copyTransport true).interventions.forward doXTrue).value x ≠ doXTrue.value x := by
    decide +kernel
  exact different sameValue

/-- Flipping only the outcome at the same action changes a sure event to
an impossible event. This does not contradict causal equivariance, which
also transforms the action. -/
theorem fixed_experiment_is_not_invariant :
    QProb.Equiv (copyModel.interventionalValue doXTrue.value (fun state => state y)) QProb.one ∧
    QProb.Equiv (copyModel.interventionalValue doXTrue.value
      (fun state => observedAction.act true state y)) QProb.zero := by decide +kernel

/-- Constant node maps cannot satisfy the inverse-bearing action interface. -/
theorem constant_map_is_not_a_permutation :
    ¬ ∃ (A : Action bitGroup Bool), ∀ b, A.act true b = false := by
  rintro ⟨A, constant⟩
  exact A.not_constant true false true (by decide)
    ((constant false).trans (constant true).symm)

/-- Two exchangeable parent nodes feed a third node. Swapping the parents
is a nontrivial node symmetry preserving this entire directed graph. -/
def swapParents (node : Fin 3) : Fin 3 :=
  if node = 0 then 1 else if node = 1 then 0 else node

private theorem swapParents_involutive : ∀ node, swapParents (swapParents node) = node := by
  decide +kernel

def nodeAction : Action bitGroup (Fin 3) := involutionAction swapParents swapParents_involutive

def twoParents (parent child : Fin 3) : Bool := decide (parent.val < 2 ∧ child.val = 2)

theorem nontrivial_node_symmetry :
    nodeAction.act true 0 = 1 ∧
      ∀ parent child, twoParents (nodeAction.act true parent) (nodeAction.act true child) =
        twoParents parent child := by decide +kernel

/-- Swapping the two root presentations preserves their description cost,
while the fixed merge node may carry a different cost. The fixture therefore
checks constancy on symmetry orbits, rather than requiring one global score. -/
def descriptionCost (hypothesis : Fin 3) : Nat :=
  if hypothesis = 2 then 4 else 2

theorem descriptionCost_invariant : nodeAction.ScoreInvariant descriptionCost := by
  change ∀ (g : Bool) (h : Fin 3), descriptionCost (nodeAction.act g h) = descriptionCost h
  decide +kernel

/-- The declared score invariant is passed into the generic complexity
weight theorem. A label-sensitive score would need a separate proof and
cannot be accepted merely because a permutation was supplied. -/
theorem complexity_prior_weights_invariant (budget : Nat) (g : Bool) (h : Fin 3) :
    CatalogueInference.complexityWeight budget (descriptionCost (nodeAction.act g h)) =
      CatalogueInference.complexityWeight budget (descriptionCost h) :=
  complexityWeight_invariant nodeAction descriptionCost descriptionCost_invariant budget g h

def symmetricPrior : Distro Bool := ⟨fairBit⟩

theorem symmetricPrior_invariant : PriorInvariant bitAction symmetricPrior := by
  intro g event
  cases g with
  | false => exact QProb.equiv_refl _
  | true =>
      cases left : event false <;> cases right : event true <;>
        simp [symmetricPrior, fairBit, Distro.map, FiniteProbRecord.map,
          FiniteProbRecord.probVal, FiniteProbRecord.eventMass, QProb.Equiv,
          bitAction, left, right]

/-- A noisy binary observation is three times as likely to agree with the
hypothesis as disagree. Both hypotheses remain supported after either datum. -/
def likelihood (datum hypothesis : Bool) : Nat := if datum = hypothesis then 3 else 1

theorem likelihood_equivariant : LikelihoodEquivariant bitAction bitAction likelihood := by
  intro g datum hypothesis
  cases g <;> cases datum <;> cases hypothesis <;> rfl

def posteriorTrue : Distro Bool := symmetricPrior.reweightNat (likelihood true) (by decide +kernel)

theorem asymmetric_data_changes_posterior :
    QProb.Equiv (posteriorTrue.pmf true) ⟨3, 4, by decide⟩ ∧
      QProb.Equiv ((posteriorTrue.map (bitAction.act true)).pmf true) ⟨1, 4, by decide⟩ := by
  decide +kernel

/-- A fixed asymmetric datum genuinely destroys prior symmetry. An event
selecting `true` witnesses different posterior masses after the flip. -/
theorem asymmetric_posterior_not_invariant : ¬ PriorInvariant bitAction posteriorTrue := by
  intro invariant
  have falseEquality := invariant true (fun hypothesis => hypothesis)
  have disagreement : ¬ QProb.Equiv
      ((posteriorTrue.map (bitAction.act true)).record.probVal (fun hypothesis => hypothesis))
      (posteriorTrue.record.probVal (fun hypothesis => hypothesis)) := by decide +kernel
  exact disagreement falseEquality

/-- The fixed posterior is asymmetric, while relabelling the datum still
produces precisely the relabelled posterior. This is an instance of the
general theorem, rather than a second manually supplied Bayesian engine. -/
theorem asymmetric_posterior_transports :
    ∃ positive : 0 < natIntegral symmetricPrior.record.atoms (transportWeight bitAction true (likelihood true)),
      (posteriorTrue.map (bitAction.act true)).SameLaw
        (symmetricPrior.reweightNat (transportWeight bitAction true (likelihood true)) positive) :=
  invariant_prior_posterior bitAction true symmetricPrior symmetricPrior_invariant
    (likelihood true) (by decide +kernel)

/-- The false hypothesis has two encodings with unequal weights, while
the true hypothesis has one. Their *combined* class masses are nevertheless
equal. Counting encodings and resetting a uniform prior would change that
declared knowledge. -/
def splitPresentation : Distro (Fin 3) where
  record :=
    { atoms := [(0, 1), (1, 2), (2, 3)]
      den := 6
      den_pos := by decide
      total_mass := rfl }

def hypothesisClass (encoding : Fin 3) : Bool := decide (encoding.val = 2)

theorem split_encodings_preserve_class_mass :
    QProb.Equiv ((aggregateClasses splitPresentation hypothesisClass).pmf false)
      ⟨1, 2, by decide⟩ ∧
    QProb.Equiv ((aggregateClasses splitPresentation hypothesisClass).pmf true)
      ⟨1, 2, by decide⟩ := by decide +kernel

/-- The same class-level observation can update either presentation.
The equality invokes the general pushforward/update theorem; it is not a
second numerical posterior implementation for the duplicate-encoding case. -/
theorem split_presentation_update_commutes :
    aggregateClasses
      (splitPresentation.reweightNat (fun encoding => likelihood true (hypothesisClass encoding))
        (by decide +kernel)) hypothesisClass =
      (aggregateClasses splitPresentation hypothesisClass).reweightNat (likelihood true)
        (by decide +kernel) :=
  aggregateClasses_reweight splitPresentation hypothesisClass (likelihood true) (by decide +kernel)

/-! ## Construct the encoding law from a fixed class prior -/

private def unduplicatedClass (i : Fin 2) : Bool := decide (i.val = 1)

private theorem twoClassesRepresented : ∀ label, ∃ i, unduplicatedClass i = label := by
  intro label
  cases label
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

private theorem duplicatedClassesRepresented : ∀ label, ∃ i, hypothesisClass i = label := by
  intro label
  cases label
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

private def unsplitCatalogue :=
  catalogueOfClassPrior unduplicatedClass symmetricPrior unduplicatedClass twoClassesRepresented

private def duplicatedCatalogue :=
  catalogueOfClassPrior hypothesisClass symmetricPrior hypothesisClass duplicatedClassesRepresented

/-- Duplicating the false class splits its fixed half into two quarters.
The single encoding of the true class retains its half. -/
theorem duplicated_catalogue_prior :
    QProb.Equiv (unsplitCatalogue.prior.pmf 0) ⟨1, 2, by decide⟩ ∧
    QProb.Equiv (duplicatedCatalogue.prior.pmf 0) ⟨1, 4, by decide⟩ ∧
    QProb.Equiv (duplicatedCatalogue.prior.pmf 1) ⟨1, 4, by decide⟩ ∧
    QProb.Equiv (duplicatedCatalogue.prior.pmf 2) ⟨1, 2, by decide⟩ := by
  decide +kernel

/-- Under one class-level likelihood the two catalogues return the same
posterior class probabilities even though their index spaces differ. -/
theorem duplicated_catalogue_posterior :
    ((CatalogueInference.posterior? unsplitCatalogue.prior
      (fun i => likelihood true (unduplicatedClass i))).map
      (fun law => (aggregateClasses law unduplicatedClass).pmf true)).any
      (fun p => decide (QProb.Equiv p ⟨3, 4, by decide⟩)) = true ∧
    ((CatalogueInference.posterior? duplicatedCatalogue.prior
      (fun i => likelihood true (hypothesisClass i))).map
      (fun law => (aggregateClasses law hypothesisClass).pmf true)).any
      (fun p => decide (QProb.Equiv p ⟨3, 4, by decide⟩)) = true := by
  decide +kernel

/-- A zero-mass class stays zero before and after splitting. -/
theorem duplicate_zero_class :
    QProb.Equiv ((splitClassPrior (Distro.pointMass true) hypothesisClass duplicatedClassesRepresented).pmf 0)
      QProb.zero := by
  decide +kernel

end Thesis.Examples.FiniteSymmetry
