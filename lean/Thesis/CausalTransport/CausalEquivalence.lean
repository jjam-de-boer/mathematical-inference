import Thesis.Causality.CausalAbstraction

namespace Thesis
namespace Causality
namespace CausalEquivalence

open Probability

/-!
# Support-aware observational, interventional and exact-abstraction relations

Three nested relations on finite SCMs. Observational and interventional
agreement compare models of one observed signature. Exact abstraction may
change the signature through an existing assignment map τ and a partial
intervention map ω.

Observational agreement is equality of the actual finite joints, zeros
included. It is not sameness of d-separations. A conditioner that is
undefined in one joint (`EventPositive` fails) and defined in the other
(including defined-zero) already breaks observational agreement. Catalogue
`recordsAgree` is the same singleton test on supplied tables; this module
does not rank graphs or recover a unique DAG.

Interventional agreement is equality of `P(· | do(a))` for a declared
family `A` of `HardIntervention`s. Exact `CausalInterventionMap` is
agreement of the pushed micro law with the macro law on the image of ω.
Empty `do` is the observational law, so the implications
exact ω ⇒ agreement on the allowed family ⇒ observational agreement
hold when the empty intervention is admitted. Converses fail.

These relations are not classical Markov equivalence, not value-rich
identification completeness, and not a Shannon or BIC ranking.
-/

variable {S : ObservedSignature}

/-- Empty hard intervention is the unforced evaluator, so its pushforward
is the observational joint. -/
theorem interventionalDist_empty (M : ExactModel S) :
    M.interventionalDist (HardIntervention.empty S).value = M.observationalDist :=
  rfl

theorem interventionalValue_empty (M : ExactModel S) (event : Event S.Assignment) :
    M.interventionalValue (HardIntervention.empty S).value event =
      M.observationalValue event :=
  rfl

/-- Same finite observational joint, including zeros. -/
def ObservationalEquiv (M N : ExactModel S) : Prop :=
  ∀ event, QProb.Equiv (M.observationalValue event) (N.observationalValue event)

/-- Same finite interventional joints on every action in a declared family. -/
def InterventionalEquiv (A : HardIntervention S → Prop) (M N : ExactModel S) : Prop :=
  ∀ action, A action → ∀ event,
    QProb.Equiv (M.interventionalValue action.value event)
      (N.interventionalValue action.value event)

/-- Coarse observational joint versus a τ-pushforward of the micro joint. -/
def ObservationalAgreeAlong {micro coarse : ObservedSignature}
    (M : ExactModel micro) (N : ExactModel coarse)
    (τ : micro.Assignment → coarse.Assignment) : Prop :=
  ∀ event, QProb.Equiv (N.observationalValue event)
    ((M.observationalDist.map τ).probVal event)

/-- Coarse interventional joint versus a τ-pushforward of one micro surgery. -/
def InterventionalAgreeAlong {micro coarse : ObservedSignature}
    (M : ExactModel micro) (N : ExactModel coarse)
    (τ : micro.Assignment → coarse.Assignment)
    (fine : HardIntervention micro) (coarseAction : HardIntervention coarse) : Prop :=
  ∀ event, QProb.Equiv (N.interventionalValue coarseAction.value event)
    ((M.interventionalDist fine.value).map τ |>.probVal event)

/-- Coarse actions that some defined ω sends a micro surgery to. -/
def allowedFamily {micro coarse : ObservedSignature}
    (mapping : CausalInterventionMap micro coarse)
    (action : HardIntervention coarse) : Prop :=
  ∃ intervention, mapping.omega intervention = some action

/-- Existence of an exact ω from one realized SCM to another. Signatures
may differ. This is not unique-DAG recovery. -/
def ExactAbstracts {micro coarse : ObservedSignature}
    (M : ExactModel micro) (N : ExactModel coarse) : Prop :=
  ∃ mapping : CausalInterventionMap micro coarse,
    mapping.microModel = M ∧ mapping.macroModel = N ∧ mapping.Exact

/-- Both directions of exact abstraction, with inverse assignment maps. -/
def ExactIso {S T : ObservedSignature} (M : ExactModel S) (N : ExactModel T) : Prop :=
  ∃ forward : CausalInterventionMap S T, ∃ backward : CausalInterventionMap T S,
    forward.microModel = M ∧ forward.macroModel = N ∧
      backward.microModel = N ∧ backward.macroModel = M ∧
      forward.Exact ∧ backward.Exact ∧
      (∀ assignment, backward.assignmentMap (forward.assignmentMap assignment) = assignment) ∧
      (∀ assignment, forward.assignmentMap (backward.assignmentMap assignment) = assignment)

/-- Singleton masses of the observational joints, zeros included. -/
def observationalAgreeBool (M N : ExactModel S) : Bool :=
  S.assignmentEnumeration.all fun assignment =>
    decide (QProb.Equiv
      (M.observationalValue (FiniteProbRecord.singletonEvent assignment))
      (N.observationalValue (FiniteProbRecord.singletonEvent assignment)))

/-- Singleton masses of the τ-pushed observational joints. -/
def observationalAgreeAlongBool {micro coarse : ObservedSignature}
    (M : ExactModel micro) (N : ExactModel coarse)
    (τ : micro.Assignment → coarse.Assignment) : Bool :=
  coarse.assignmentEnumeration.all fun assignment =>
    decide (QProb.Equiv
      (N.observationalValue (FiniteProbRecord.singletonEvent assignment))
      ((M.observationalDist.map τ).probVal (FiniteProbRecord.singletonEvent assignment)))

theorem observationalEquiv_refl (M : ExactModel S) : ObservationalEquiv M M :=
  fun _ => QProb.equiv_refl _

theorem observationalEquiv_symm {M N : ExactModel S}
    (h : ObservationalEquiv M N) : ObservationalEquiv N M :=
  fun event => QProb.equiv_symm (h event)

theorem observationalEquiv_trans {M N P : ExactModel S}
    (hMN : ObservationalEquiv M N) (hNP : ObservationalEquiv N P) :
    ObservationalEquiv M P :=
  fun event => QProb.equiv_trans (hMN event) (hNP event)

theorem interventionalEquiv_refl (A : HardIntervention S → Prop) (M : ExactModel S) :
    InterventionalEquiv A M M :=
  fun _ _ _ => QProb.equiv_refl _

theorem interventionalEquiv_symm {A : HardIntervention S → Prop} {M N : ExactModel S}
    (h : InterventionalEquiv A M N) : InterventionalEquiv A N M :=
  fun action ha event => QProb.equiv_symm (h action ha event)

theorem interventionalEquiv_trans {A : HardIntervention S → Prop} {M N P : ExactModel S}
    (hMN : InterventionalEquiv A M N) (hNP : InterventionalEquiv A N P) :
    InterventionalEquiv A M P :=
  fun action ha event => QProb.equiv_trans (hMN action ha event) (hNP action ha event)

/-- Agreement on a larger family is stronger. -/
theorem interventionalEquiv_mono {A B : HardIntervention S → Prop}
    (sub : ∀ action, A action → B action) {M N : ExactModel S}
    (h : InterventionalEquiv B M N) : InterventionalEquiv A M N :=
  fun action ha event => h action (sub action ha) event

theorem observationalEquiv_of_singletons [DecidableEq S.Assignment]
    {M N : ExactModel S}
    (h : ∀ assignment, QProb.Equiv
      (M.observationalValue (FiniteProbRecord.singletonEvent assignment))
      (N.observationalValue (FiniteProbRecord.singletonEvent assignment))) :
    ObservationalEquiv M N :=
  FiniteProbRecord.probVal_extensional_of_singletons
    M.observationalDist N.observationalDist
    S.assignmentEnumeration S.assignmentEnumeration_nodup
    S.assignmentEnumeration_complete h

theorem observationalEquiv_of_bool {M N : ExactModel S}
    (h : observationalAgreeBool M N = true) : ObservationalEquiv M N := by
  refine observationalEquiv_of_singletons (fun assignment =>
    of_decide_eq_true ((List.all_eq_true.mp h) assignment
      (S.assignmentEnumeration_complete assignment)))

theorem observationalAgreeAlong_of_singletons {micro coarse : ObservedSignature}
    [DecidableEq coarse.Assignment]
    {M : ExactModel micro} {N : ExactModel coarse}
    {τ : micro.Assignment → coarse.Assignment}
    (h : ∀ assignment, QProb.Equiv
      (N.observationalValue (FiniteProbRecord.singletonEvent assignment))
      ((M.observationalDist.map τ).probVal (FiniteProbRecord.singletonEvent assignment))) :
    ObservationalAgreeAlong M N τ :=
  FiniteProbRecord.probVal_extensional_of_singletons
    N.observationalDist (M.observationalDist.map τ)
    coarse.assignmentEnumeration coarse.assignmentEnumeration_nodup
    coarse.assignmentEnumeration_complete h

theorem observationalAgreeAlong_of_bool {micro coarse : ObservedSignature}
    {M : ExactModel micro} {N : ExactModel coarse}
    {τ : micro.Assignment → coarse.Assignment}
    (h : observationalAgreeAlongBool M N τ = true) : ObservationalAgreeAlong M N τ := by
  refine observationalAgreeAlong_of_singletons (fun assignment =>
    of_decide_eq_true ((List.all_eq_true.mp h) assignment
      (coarse.assignmentEnumeration_complete assignment)))

/-- Joint agreement, including zeros, decides support of every conditioner. -/
theorem observationalEquiv_eventPositive {M N : ExactModel S}
    (h : ObservationalEquiv M N) (evidence : Event S.Assignment) :
    M.observationalDist.EventPositive evidence ↔
      N.observationalDist.EventPositive evidence := by
  change 0 < (M.observationalDist.probVal evidence).num ↔
    0 < (N.observationalDist.probVal evidence).num
  exact QProb.equiv_num_pos_iff (h evidence)

/-- When both conditioners are supported, the actual conditionals agree.
Defined-zero cells are included; no undefined conditional is completed. -/
theorem observationalEquiv_conditionOn {M N : ExactModel S}
    (h : ObservationalEquiv M N) (evidence event : Event S.Assignment)
    (hM : M.observationalDist.EventPositive evidence)
    (hN : N.observationalDist.EventPositive evidence) :
    QProb.Equiv
      ((M.observationalDist.conditionOn evidence hM).probVal event)
      ((N.observationalDist.conditionOn evidence hN).probVal event) :=
  QProb.equiv_trans (M.observationalDist.conditionOn_probVal evidence event hM)
    (QProb.equiv_trans
      (QProb.div_congr (h (fun assignment => evidence assignment && event assignment))
        (h evidence) hM hN)
      (QProb.equiv_symm (N.observationalDist.conditionOn_probVal evidence event hN)))

/-- Undefined versus defined (including defined-zero) is not observational
agreement: the conditioner has mass in one joint and none in the other. -/
theorem not_observationalEquiv_of_undefined_vs_defined {M N : ExactModel S}
    (evidence : Event S.Assignment)
    (defined : M.observationalDist.EventPositive evidence)
    (undefined : ¬ N.observationalDist.EventPositive evidence) :
    ¬ ObservationalEquiv M N :=
  fun h => undefined ((observationalEquiv_eventPositive h evidence).mp defined)

/-- Interventional agreement on a family that contains empty `do` is
observational agreement of the joints. -/
theorem observationalEquiv_of_interventionalEquiv {A : HardIntervention S → Prop}
    {M N : ExactModel S} (containsEmpty : A (HardIntervention.empty S))
    (h : InterventionalEquiv A M N) : ObservationalEquiv M N :=
  fun event => h (HardIntervention.empty S) containsEmpty event

/-- Exact ω is interventional agreement of the pushed micro law with the
macro law, at every pair in the image of ω. -/
theorem interventionalAgreeAlong_of_exact {micro coarse : ObservedSignature}
    (mapping : CausalInterventionMap micro coarse) (hExact : mapping.Exact)
    (intervention : HardIntervention micro) (action : HardIntervention coarse)
    (defined : mapping.omega intervention = some action) :
    InterventionalAgreeAlong mapping.microModel mapping.macroModel
      mapping.assignmentMap intervention action := by
  intro event
  exact QProb.equiv_trans (hExact intervention action defined event)
    (QProb.equiv_symm (FiniteProbRecord.map_probVal _ _ _))

/-- Empty `do` in the domain of an exact ω yields observational agreement
along τ. -/
theorem observationalAgreeAlong_of_exact_empty {micro coarse : ObservedSignature}
    (mapping : CausalInterventionMap micro coarse) (hExact : mapping.Exact)
    (hEmpty : mapping.omega (HardIntervention.empty micro) =
      some (HardIntervention.empty coarse)) :
    ObservationalAgreeAlong mapping.microModel mapping.macroModel
      mapping.assignmentMap := by
  intro event
  simpa [interventionalDist_empty] using
    interventionalAgreeAlong_of_exact mapping hExact
      (HardIntervention.empty micro) (HardIntervention.empty coarse) hEmpty event

/-- Same-signature identity τ: exact ω that fixes an action compares that
action's interventional joints in the two models. -/
theorem interventionalEquiv_of_exact_fix
    (mapping : CausalInterventionMap S S)
    (hId : ∀ assignment, mapping.assignmentMap assignment = assignment)
    (hExact : mapping.Exact) :
    InterventionalEquiv (fun action => mapping.omega action = some action)
      mapping.microModel mapping.macroModel := by
  intro action hFix event
  have pull :
      (fun assignment => event (mapping.assignmentMap assignment)) = event := by
    funext assignment
    rw [hId]
  exact QProb.equiv_symm (by simpa [pull] using hExact action action hFix event)

/-- Identity ω on one SCM is exact, so the model abstracts itself. -/
def identityMap (M : ExactModel S) : CausalInterventionMap S S where
  microModel := M
  macroModel := M
  assignmentMap := id
  omega := fun action => some action
  respects := by
    intro intervention action defined
    injection defined with equal
    subst equal
    exact fun _ realizes => realizes

theorem identityMap_exact (M : ExactModel S) : (identityMap M).Exact := by
  intro intervention action defined event
  injection defined with equal
  subst equal
  exact QProb.equiv_refl _

theorem exactAbstracts_refl (M : ExactModel S) : ExactAbstracts M M :=
  ⟨identityMap M, rfl, rfl, identityMap_exact M⟩

theorem exactAbstracts_trans {fine middle coarse : ObservedSignature}
    {M : ExactModel fine} {N : ExactModel middle} {P : ExactModel coarse}
    (hMN : ExactAbstracts M N) (hNP : ExactAbstracts N P) : ExactAbstracts M P := by
  rcases hMN with ⟨forward, forwardMicro, forwardMacro, forwardExact⟩
  rcases hNP with ⟨backward, backwardMicro, backwardMacro, backwardExact⟩
  refine ⟨forward.comp backward (forwardMacro.trans backwardMicro.symm), ?_, ?_, ?_⟩
  · simp [CausalInterventionMap.comp, forwardMicro]
  · simp [CausalInterventionMap.comp, backwardMacro]
  · exact CausalInterventionMap.comp_exact forward backward
      (forwardMacro.trans backwardMicro.symm) forwardExact backwardExact

theorem exactIso_symm {S T : ObservedSignature} {M : ExactModel S} {N : ExactModel T}
    (h : ExactIso M N) : ExactIso N M := by
  rcases h with ⟨forward, backward, fM, fN, bN, bM, fE, bE, left, right⟩
  exact ⟨backward, forward, bN, bM, fM, fN, bE, fE, right, left⟩

theorem exactAbstracts_of_iso {S T : ObservedSignature} {M : ExactModel S} {N : ExactModel T}
    (h : ExactIso M N) : ExactAbstracts M N := by
  rcases h with ⟨forward, _, fM, fN, _, _, fE, _, _, _⟩
  exact ⟨forward, fM, fN, fE⟩

end CausalEquivalence
end Causality
end Thesis
