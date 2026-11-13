import Thesis.CausalTransport.GuardedComponentCompilation
import Thesis.CausalTransport.GuardedComponentFamilyCompilation
import Thesis.CausalTransport.KernelIdentification

namespace Thesis
namespace Causality

/-!
# Guarded current-kernel ID: the complete executable branch structure

The graph decisions are those of the corrected current-kernel ID engine.
Uncut ancestry prunes the input, incoming-cut ancestry supplies additional
actions, and actual c-components determine terminal extraction, containing-
component restriction and recursive multi-component assembly.  The current
expression is retained at every recursive call.

Only probability syntax changes: extracted component inputs are prefix-first
guarded folds, and the multi-component branch emits the proved host-order
fold of its recursive component quotients.  It does not commute that fold
into the older strict product.  Successful child formulas are collected once
and looked up by the finite Boolean component equality test; no formula or
certificate is chosen from a propositional existence witness.

This file computes candidate expressions and proves their action-free and
decision invariants.  An `identified` constructor alone does not assert that
the candidate is supported or semantically correct in a distribution with
zeros: the recursive support-carrying success compiler is a separate step.
The established positive engine and its completeness theorem are unchanged.
-/

/-! ## Deterministic lookup of already collected recursive formulas -/

/-- Read a component from a successfully collected component/formula table.
The unit fallback is syntactic and is irrelevant for actual listed entries.
It is not a value assigned to an undefined conditional probability. -/
def componentFormulaLookup : List (NodeSet S × ProbabilityTerm S) → NodeSet S → ProbabilityTerm S
  | [], _requested => unitProbabilityTerm S
  | (component, formula) :: rest, requested =>
      if NodeSet.equal requested component then formula else componentFormulaLookup rest requested

theorem componentFormulaLookup_actionFree
    (entries : List (NodeSet S × ProbabilityTerm S))
    (free : forall entry, entry ∈ entries → entry.2.ActionFree) (requested : NodeSet S) :
    (componentFormulaLookup entries requested).ActionFree := by
  induction entries with
  | nil => exact unitProbabilityTerm_actionFree S
  | cons entry rest inductionHypothesis =>
      simp only [componentFormulaLookup]
      split
      · exact free entry List.mem_cons_self
      · exact inductionHypothesis (fun value listed => free value (List.mem_cons_of_mem _ listed))

/-- A zipped table of computed formulas returns the exact listed formula,
even if the input list contains repetitions.  Equality of functional node
sets is established by the existing finite Boolean test, not by choice. -/
theorem componentFormulaLookup_zip_map (components : List (NodeSet S))
    (formula : NodeSet S → ProbabilityTerm S) {component : NodeSet S}
    (listed : component ∈ components) :
    componentFormulaLookup (components.zip (components.map formula)) component = formula component := by
  induction components with
  | nil => exact False.elim (List.not_mem_nil listed)
  | cons head rest inductionHypothesis =>
      if sameComponent : NodeSet.equal component head = true then
        simp only [List.map_cons, List.zip_cons_cons, componentFormulaLookup, sameComponent, if_true]
        exact congrArg formula ((NodeSet.equal_eq_true_iff _ _).mp sameComponent).symm
      else
        have inRest : component ∈ rest := by
          rcases List.mem_cons.mp listed with first | later
          · exact False.elim (sameComponent ((NodeSet.equal_eq_true_iff _ _).mpr first))
          · exact later
        have absent : NodeSet.equal component head = false := by
          cases value : NodeSet.equal component head with
          | false => rfl
          | true => exact False.elim (sameComponent value)
        simpa only [List.map_cons, List.zip_cons_cons, componentFormulaLookup, absent,
          Bool.false_eq_true, if_false] using inductionHypothesis inRest

/-- The collected terms stay in the graph's actual component-list order.
Lookup reuses them without recomputing any recursive child invocation. -/
def assembleGuardedComponents (G : ObservedGraph S) (remaining : NodeSet S)
    (terms : List (ProbabilityTerm S)) : ProbabilityTerm S :=
  guardedComponentFamilyTerm G remaining (componentFormulaLookup ((G.cComponents remaining).zip terms))

theorem assembleGuardedComponents_actionFree (G : ObservedGraph S) (remaining : NodeSet S)
    (terms : List (ProbabilityTerm S)) (free : forall term, term ∈ terms → term.ActionFree) :
    (assembleGuardedComponents G remaining terms).ActionFree :=
  guardedComponentFamilyTerm_actionFree G remaining _ (fun component _listed =>
    componentFormulaLookup_actionFree _ (fun entry member => free entry.2 (List.of_mem_zip member).2) component)

/-- Align executable assembly with a formula-indexed component family.
This lemma will align the actual recursive outputs with the proved family
constructor, without replacing those outputs by observational kernels. -/
theorem assembleGuardedComponents_map (G : ObservedGraph S) (remaining : NodeSet S)
    (formula : NodeSet S → ProbabilityTerm S) :
    assembleGuardedComponents G remaining ((G.cComponents remaining).map formula) =
      guardedComponentFamilyTerm G remaining formula := by
  unfold assembleGuardedComponents guardedComponentFamilyTerm
  apply GuardedHostChain.term_congr
  intro node selected
  rw [componentFormulaLookup_zip_map _ formula (G.componentAt_spec remaining node selected).1]

/-! ## Complete guarded recursion, with the corrected graph decisions -/

def identifyGuardedKernelFuel (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S) (current : ProbabilityTerm S) : IdentificationOutcome S :=
  match fuel with
  | 0 => .unfinished
  | fuel + 1 =>
      let identifyNext := identifyGuardedKernelFuel fuel
      let y := NodeSet.inter outcome remaining
      let x := NodeSet.inter action remaining
      if NodeSet.isEmpty x then
        .identified (.marginalize (NodeSet.diff remaining y) current)
      else
        let kept := G.ancestralSet remaining (GraphMutilation.none S) y
        if NodeSet.equal kept remaining then
          let additional := identificationAdditionalAction G remaining outcome action
          if NodeSet.isEmpty additional then
            let free := NodeSet.diff remaining x
            match G.cComponents free with
            | [] => .identified (.marginalize remaining current)
            | [component] =>
                if G.isSingleCComponent remaining then
                  .failed ⟨remaining, component⟩
                else if (G.cComponents remaining).any (fun piece => NodeSet.equal piece component) then
                  .identified (.marginalize (NodeSet.diff component y)
                    (guardedComponentTerm remaining current component))
                else
                  match G.containingCComponent remaining component with
                  | some larger => identifyNext G larger outcome (NodeSet.inter x larger)
                      (guardedComponentTerm remaining current larger)
                  | none => .unfinished
            | _ :: _ :: _ =>
                IdentificationOutcome.combine
                  ((G.cComponents free).map (fun component =>
                    identifyNext G remaining component (NodeSet.diff remaining component) current))
                  (fun terms => .marginalize (NodeSet.diff remaining (NodeSet.union y x))
                    (assembleGuardedComponents G free terms))
          else identifyNext G remaining outcome (NodeSet.union x additional) current
        else identifyNext G kept outcome (NodeSet.inter x kept)
          (.marginalize (NodeSet.diff remaining kept) current)

def identifyGuardedJointKernel (G : ObservedGraph S) (query : JointKernelQuery S) : IdentificationOutcome S :=
  identifyGuardedKernelFuel (kernelIdentificationFuel S) G NodeSet.full query.outcome query.action
    (observationalJointTerm S)

/-- Every identified candidate has action-free syntax.  This is not an
assertion of support, and the proof follows every recursive graph branch. -/
theorem identifyGuardedKernelFuel_identified_actionFree
    (fuel : Nat) (G : ObservedGraph S) (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S) (inputFree : current.ActionFree) {term : ProbabilityTerm S}
    (result : identifyGuardedKernelFuel fuel G remaining outcome action current = .identified term) : term.ActionFree := by
  induction fuel generalizing remaining outcome action current term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      simp only [identifyGuardedKernelFuel] at result
      split at result
      · cases result; exact inputFree
      · split at result
        · split at result
          · split at result
            · cases result; exact inputFree
            · split at result
              · cases result
              · split at result
                · cases result
                  exact guardedComponentTerm_actionFree _ _ _ inputFree
                · split at result
                  · exact inductionHypothesis _ _ _ _ (guardedComponentTerm_actionFree _ _ _ inputFree) result
                  · cases result
            · apply IdentificationOutcome.combine_identified_actionFree _
                (fun terms => .marginalize (NodeSet.diff remaining
                  (NodeSet.union (NodeSet.inter outcome remaining) (NodeSet.inter action remaining)))
                  (assembleGuardedComponents G (NodeSet.diff remaining (NodeSet.inter action remaining)) terms))
                (fun terms free => assembleGuardedComponents_actionFree _ _ terms free) _ result
              intro factor member
              rcases List.mem_map.mp member with ⟨component, _listed, componentResult⟩
              exact inductionHypothesis _ _ _ _ inputFree componentResult
          · exact inductionHypothesis _ _ _ _ inputFree result
        · exact inductionHypothesis _ _ _ (.marginalize _ current) inputFree result

theorem identifyGuardedJointKernel_identified_actionFree (G : ObservedGraph S) (query : JointKernelQuery S)
    {term : ProbabilityTerm S} (result : identifyGuardedJointKernel G query = .identified term) : term.ActionFree :=
  identifyGuardedKernelFuel_identified_actionFree _ _ _ _ _ _ (observationalJointTerm_actionFree S) result

/-! ## Formula-independent decisions preserve totality and exact failures -/

/-- Forget only an identified formula, retaining the exact failure witness
and distinguishing genuine failure from the fuel/containment sentinel. -/
inductive KernelIdentificationDecision (S : ObservedSignature) where
  | identified
  | failed (failure : IdentificationFail S)
  | unfinished

def IdentificationOutcome.decision : IdentificationOutcome S → KernelIdentificationDecision S
  | .identified _term => .identified
  | .failed failure => .failed failure
  | .unfinished => .unfinished

/-- Changing successful formulas or their assembly cannot change the
collector's first failed/sentinel child.  Accumulators need not agree. -/
private theorem collect_decision_eq
    (first second : List (IdentificationOutcome S))
    (same : first.map IdentificationOutcome.decision = second.map IdentificationOutcome.decision)
    (assembleFirst assembleSecond : List (ProbabilityTerm S) → ProbabilityTerm S)
    (accFirst accSecond : List (ProbabilityTerm S)) :
    (IdentificationOutcome.collect assembleFirst first accFirst).decision =
      (IdentificationOutcome.collect assembleSecond second accSecond).decision := by
  induction first generalizing second accFirst accSecond with
  | nil =>
      cases second with
      | nil => rfl
      | cons head rest => cases same
  | cons head rest inductionHypothesis =>
      cases second with
      | nil => cases same
      | cons other others =>
          have heads := (List.cons.inj same).1
          have tails := (List.cons.inj same).2
          cases head with
          | identified term =>
              cases other with
              | identified otherTerm => exact inductionHypothesis others tails (term :: accFirst) (otherTerm :: accSecond)
              | failed _ => cases heads
              | unfinished => cases heads
          | failed failure =>
              cases other with
              | identified _ => cases heads
              | failed otherFailure => exact heads
              | unfinished => cases heads
          | unfinished =>
              cases other with
              | identified _ => cases heads
              | failed _ => cases heads
              | unfinished => rfl

private theorem combine_decision_eq
    (first second : List (IdentificationOutcome S))
    (same : first.map IdentificationOutcome.decision = second.map IdentificationOutcome.decision)
    (assembleFirst assembleSecond : List (ProbabilityTerm S) → ProbabilityTerm S) :
    (IdentificationOutcome.combine first assembleFirst).decision =
      (IdentificationOutcome.combine second assembleSecond).decision :=
  collect_decision_eq first second same assembleFirst assembleSecond [] []

/-- Every graph branch has the same decision as corrected positive ID,
even with unrelated current expressions.  This generalization covers both
the changed component-restriction input and later ancestral marginals. -/
theorem identifyGuardedKernelFuel_decision_eq
    (fuel : Nat) (G : ObservedGraph S) (remaining outcome action : NodeSet S)
    (guardedCurrent strictCurrent : ProbabilityTerm S) :
    (identifyGuardedKernelFuel fuel G remaining outcome action guardedCurrent).decision =
      (identifyKernelFuel fuel G remaining outcome action strictCurrent).decision := by
  induction fuel generalizing remaining outcome action guardedCurrent strictCurrent with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [identifyGuardedKernelFuel, identifyKernelFuel]
      cases emptyAction : NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true => simp only [if_true, IdentificationOutcome.decision]
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases sameHost : NodeSet.equal
              (G.ancestralSet remaining (.none S) (NodeSet.inter outcome remaining)) remaining with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact inductionHypothesis _ _ _ _ _
          | true =>
              simp only [if_true]
              cases emptyAdditional : NodeSet.isEmpty (identificationAdditionalAction G remaining outcome action) with
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  exact inductionHypothesis _ _ _ _ _
              | true =>
                  simp only [if_true]
                  cases partition : G.cComponents (NodeSet.diff remaining (NodeSet.inter action remaining)) with
                  | nil => simp only [IdentificationOutcome.decision]
                  | cons component rest =>
                      cases rest with
                      | nil =>
                          cases singleHost : G.isSingleCComponent remaining with
                          | true => simp only [if_true, IdentificationOutcome.decision]
                          | false =>
                              simp only [Bool.false_eq_true, if_false]
                              cases listed : (G.cComponents remaining).any (fun piece => NodeSet.equal piece component) with
                              | true => simp only [if_true, IdentificationOutcome.decision]
                              | false =>
                                  simp only [Bool.false_eq_true, if_false]
                                  cases containing : G.containingCComponent remaining component with
                                  | none => rfl
                                  | some larger => exact inductionHypothesis _ _ _ _ _
                      | cons next tail =>
                          apply combine_decision_eq
                          simp only [List.map_map]
                          apply List.map_congr_left
                          intro component _listed
                          exact inductionHypothesis _ _ _ _ _

theorem identifyGuardedJointKernel_decision_eq (G : ObservedGraph S) (query : JointKernelQuery S) :
    (identifyGuardedJointKernel G query).decision = (identifyJointKernel G query).decision :=
  identifyGuardedKernelFuel_decision_eq _ _ _ _ _ _ _

/-- Public guarded ID uses the same proved finite allowance, so no sentinel
is exposed for a well-formed public joint query. -/
theorem identifyGuardedJointKernel_ne_unfinished (G : ObservedGraph S) (query : JointKernelQuery S) :
    identifyGuardedJointKernel G query ≠ .unfinished := by
  intro unfinished
  have same := identifyGuardedJointKernel_decision_eq G query
  rw [unfinished] at same
  cases original : identifyJointKernel G query with
  | identified _term => simp only [original, IdentificationOutcome.decision] at same; cases same
  | failed _failure => simp only [original, IdentificationOutcome.decision] at same; cases same
  | unfinished => exact identifyJointKernel_ne_unfinished G query original

/-- The guarded program reports exactly the original hedge failure witness,
not merely a Boolean failure flag.  Existing failure/countermodel transport
can therefore be applied without another stack of nested-failure unpackers. -/
theorem identifyGuardedJointKernel_failed_iff (G : ObservedGraph S) (query : JointKernelQuery S)
    (failure : IdentificationFail S) :
    identifyGuardedJointKernel G query = .failed failure ↔ identifyJointKernel G query = .failed failure := by
  have same := identifyGuardedJointKernel_decision_eq G query
  constructor
  · intro failed
    rw [failed] at same
    cases original : identifyJointKernel G query with
    | identified _term => simp only [original, IdentificationOutcome.decision] at same; cases same
    | unfinished => simp only [original, IdentificationOutcome.decision] at same; cases same
    | failed other =>
        have equal : failure = other := by
          apply KernelIdentificationDecision.failed.inj
          simpa only [original, IdentificationOutcome.decision] using same
        exact congrArg IdentificationOutcome.failed equal.symm
  · intro failed
    rw [failed] at same
    cases guarded : identifyGuardedJointKernel G query with
    | identified _term => simp only [guarded, IdentificationOutcome.decision] at same; cases same
    | unfinished => simp only [guarded, IdentificationOutcome.decision] at same; cases same
    | failed other =>
        have equal : other = failure := by
          apply KernelIdentificationDecision.failed.inj
          simpa only [guarded, IdentificationOutcome.decision] using same
        exact congrArg IdentificationOutcome.failed equal

end Causality
end Thesis
