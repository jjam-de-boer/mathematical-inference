import Thesis.CausalTransport.ConditionalCompilation

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

/-!
# Original-query transport of recursive IDC failure

An IDC failure does not immediately refute its conditional query.  It says
that, after a sequence of legal observation/action exchanges, corrected joint
ID failed on an irreducible terminal numerator.  This module recovers that
actual terminal query and its original-query exchange trace for every fuel
depth.  The joint failure supplies its hedge through the existing general
extractor, with the exact large and small forest coordinates retained.

The semantic transport is separate from extraction.  In an observationally
positive selected class, each recorded rule-2 exchange equates the two
conditional kernels at every reference assignment.  Thus a terminal
conditional countermodel transports back through the whole trace using the
same two models; no new model, altered query, or choice of a latent unit is
hidden in the recursion.

The difficult terminal implication is deliberately not assumed to follow
from a failed joint numerator.  We prove its general chain-rule case below:
if that numerator's countermodel pair agrees on the denominator, it already
separates the conditional.  A denominator-identifiable class supplies that
agreement, but is not necessary: the positive carrier pair supplies it
directly when the conditioner is outside the large forest and all common
roots are queried outcomes.  General irreducible terminals without such a
matched-denominator construction still require the remaining conditional
countermodel argument.
-/

/-! ## Inspectable exchange traces and their semantic equality -/

/-- The finite sequence of verified single-conditioner exchanges performed
by IDC.  The endpoint query is indexed in the type; it is not supplied later
as an independently chosen query with a superficially matching outcome. -/
inductive ConditionalExchangeTrace (graph : ObservedGraph S) :
    ConditionalKernelQuery S -> ConditionalKernelQuery S -> Type u
  | refl (query) : ConditionalExchangeTrace graph query query
  | exchange {source target} (step : ConditionalExchangeStep graph source)
      (rest : ConditionalExchangeTrace graph
        (source.exchangeCondition step.node step.selected) target) :
      ConditionalExchangeTrace graph source target

/-- Interpret one verified promotion in either model of a positive class.
The rule has the promoted kernel on its left, so symmetry restores the
program's original-to-promoted orientation.  Both endpoints are supported
directly by observational positivity and SCM consistency. -/
noncomputable def ConditionalExchangeStep.equivalentAt
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (step : ConditionalExchangeStep graph query)
    (model : ExactModel S) (compatible : Compatible model graph)
    (positive : ObservationallyPositive model) (assignment : S.Assignment) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm
      (query.exchangeCondition step.node step.selected).sourceTerm assignment :=
  ProbabilityResult.symm
    ((graph.publishedSoundness.pathPrimitive model compatible).doRule assignment
      (step.pathRule graph.dSeparationCorrectness)
      (positive.kernelPositiveSupportedValue
        (query.exchangeCondition step.node step.selected).operationKernel assignment).toSupported
      (positive.kernelPositiveSupportedValue query.operationKernel assignment).toSupported)

/-- Every finite exchange trace preserves its source conditional kernel.
The induction composes actual finite rational equalities, not equality of
functions or an unproved identification interface. -/
noncomputable def ConditionalExchangeTrace.equivalentAt
    {graph : ObservedGraph S} {source target : ConditionalKernelQuery S}
    (trace : ConditionalExchangeTrace graph source target)
    (model : ExactModel S) (compatible : Compatible model graph)
    (positive : ObservationallyPositive model) (assignment : S.Assignment) :
    ProbabilityTerm.EquivalentAt model source.sourceTerm target.sourceTerm assignment := by
  induction trace with
  | refl query => exact ProbabilityResult.refl _
  | exchange step rest inductionHypothesis =>
      exact ProbabilityResult.trans
        (step.equivalentAt model compatible positive assignment) inductionHypothesis

/-- Transport a terminal conditional countermodel through an arbitrary
exchange trace.  Positivity ensures that agreement on the original common
support covers every assignment used by the target's common-support relation.
The observational law and selected-class memberships are unchanged. -/
noncomputable def ConditionalExchangeTrace.transportCounterexample
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {source target : ConditionalKernelQuery S}
    (trace : ConditionalExchangeTrace graph source target)
    (counterexample : ConditionalCounterexampleIn C target) :
    ConditionalCounterexampleIn C source where
  left := counterexample.left
  right := counterexample.right
  left_mem := counterexample.left_mem
  right_mem := counterexample.right_mem
  observationally_equal := counterexample.observationally_equal
  query_separated := by
    intro sourceEquivalent
    apply counterexample.query_separated
    intro assignment _leftSupported _rightSupported
    have leftPositive := obsPositive counterexample.left_mem
    have rightPositive := obsPositive counterexample.right_mem
    rcases sourceEquivalent assignment
        (leftPositive.kernelPositiveSupportedValue source.operationKernel assignment).toSupported
        (rightPositive.kernelPositiveSupportedValue source.operationKernel assignment).toSupported with
      ⟨between⟩
    exact ⟨ProbabilityResult.trans
      (ProbabilityResult.symm (trace.equivalentAt counterexample.left
        (C.mem_compatible _ counterexample.left_mem) leftPositive assignment))
      (ProbabilityResult.trans between (trace.equivalentAt counterexample.right
        (C.mem_compatible _ counterexample.right_mem) rightPositive assignment))⟩

/-! ## Recovering the actual irreducible terminal and its joint hedge -/

/-- Complete failure provenance for one conditional invocation.  `terminal`
is the query reached by the actual program, `exchanges` connects it to the
original source, and `no_exchange` certifies exhaustion of its finite rule-2
search.  The joint hedge is indexed by that terminal's numerator, not falsely
claimed to be a conditional countermodel. -/
structure ConditionalKernelFailure (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (fail : IdentificationFail S) where
  terminal : ConditionalKernelQuery S
  exchanges : ConditionalExchangeTrace graph query terminal
  no_exchange : conditionalExchangeStep? graph terminal = none
  joint_failed : identifyJointKernel graph terminal.jointNumerator = .failed fail
  hedge : CurrentKernelFailureHedge graph NodeSet.full terminal.jointNumerator fail

/-- Extract failure provenance at every recursive depth.  A successful Bayes
branch cannot supply a failure equation; a promotion preserves the nested
terminal and prepends its verified exchange.  There is no bound on the number
of such steps beyond the program's actual finite fuel. -/
noncomputable def identifyConditionalKernelFuelFailed
    {graph : ObservedGraph S} (fuel : Nat) (query : ConditionalKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyConditionalKernelFuel fuel graph query = .failed fail) :
    ConditionalKernelFailure graph query fail := by
  induction fuel generalizing query fail with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      cases found : conditionalExchangeStep? graph query with
      | some step =>
          let nested := inductionHypothesis (query.exchangeCondition step.node step.selected)
            (by simpa only [identifyConditionalKernelFuel, found] using result)
          exact {
            terminal := nested.terminal
            exchanges := .exchange step nested.exchanges
            no_exchange := nested.no_exchange
            joint_failed := nested.joint_failed
            hedge := nested.hedge
          }
      | none =>
          cases joint : identifyJointKernel graph query.jointNumerator with
          | identified numerator =>
              simp only [identifyConditionalKernelFuel, found, joint] at result
              cases result
          | failed terminalFail =>
              have same : terminalFail = fail := by
                simpa only [identifyConditionalKernelFuel, found, joint,
                  IdentificationOutcome.failed.injEq] using result
              subst terminalFail
              exact {
                terminal := query
                exchanges := .refl query
                no_exchange := found
                joint_failed := joint
                hedge := identifyJointKernelFailedHedge query.jointNumerator joint
              }
          | unfinished =>
              simp only [identifyConditionalKernelFuel, found, joint] at result
              cases result

/-- Public conditional failure exposes one irreducible terminal query and a
general joint hedge, connected to the original conditional by a checked trace. -/
noncomputable def identifyConditionalKernelFailed
    {graph : ObservedGraph S} (query : ConditionalKernelQuery S)
    {fail : IdentificationFail S}
    (result : identifyConditionalKernel graph query = .failed fail) :
    ConditionalKernelFailure graph query fail :=
  identifyConditionalKernelFuelFailed _ query result

/-- Every conditioner left at the extracted terminal fails its singleton
exchange test.  Search exhaustion is a uniform statement over the whole
terminal conditioner, not merely the last attempted node. -/
theorem ConditionalKernelFailure.exchangeTest_false
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail)
    (node : Fin S.count) (selected : failure.terminal.condition node = true) :
    conditionalExchangeTest graph failure.terminal node = false :=
  conditionalExchangeStep?_none_excludes_all _ _ failure.no_exchange node selected

/-! ## A matched denominator converts joint separation to conditional separation -/

/-- The semantic chain rule for an arbitrary conditional query in a positive
compatible model.  Its multiplication is supported because the conditional
and denominator kernels both have supported values; no syntactic formula
returned by ID is involved in this identity. -/
noncomputable def ConditionalKernelQuery.chainEquivalentAt
    {graph : ObservedGraph S} (query : ConditionalKernelQuery S)
    (model : ExactModel S) (compatible : Compatible model graph)
    (positive : ObservationallyPositive model) (assignment : S.Assignment) :
    ProbabilityTerm.EquivalentAt model query.jointNumerator.sourceTerm
      (.multiply query.sourceTerm query.jointDenominator.sourceTerm) assignment := by
  have conditionalSupported : query.sourceTerm.SupportedAt model assignment :=
    (positive.kernelPositiveSupportedValue query.operationKernel assignment).toSupported
  have productSupported :
      (ProbabilityTerm.multiply query.sourceTerm query.jointDenominator.sourceTerm).SupportedAt
        model assignment := ProbabilityTerm.multiply_supportedAt conditionalSupported
          (query.jointDenominator.supportedAt model assignment)
  have chain := (graph.publishedSoundness.pathPrimitive model compatible).chain
    query.action query.outcome query.condition NodeSet.empty assignment
    (FourWayDisjoint.of_empty_w _ _ _ query.action_outcome_disjoint
      query.action_condition_disjoint query.outcome_condition_disjoint)
    (query.jointNumerator.supportedAt model assignment)
    (by simpa only [NodeSet.union_empty_right, ConditionalKernelQuery.sourceTerm,
      ConditionalKernelQuery.operationKernel, ConditionalKernelQuery.jointDenominator,
      JointKernelQuery.sourceTerm] using productSupported)
  simpa only [NodeSet.union_empty_right, ConditionalKernelQuery.jointNumerator,
    ConditionalKernelQuery.jointDenominator, ConditionalKernelQuery.sourceTerm,
    JointKernelQuery.sourceTerm] using chain

/-- A joint numerator countermodel that agrees on the denominator must
disagree on the conditional.  This is a pair-level theorem: the denominator
need not be identifiable throughout the selected class, only equal in these
same two countermodels.  Hence it is stronger than the class-level special
case used by the first branch of the conditional completeness argument. -/
noncomputable def ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S)
    (joint : CounterexampleIn C query.jointNumerator)
    (denominator : query.jointDenominator.ValueEquivalent joint.left joint.right) :
    ConditionalCounterexampleIn C query where
  left := joint.left
  right := joint.right
  left_mem := joint.left_mem
  right_mem := joint.right_mem
  observationally_equal := joint.observationally_equal
  query_separated := by
    intro conditional
    apply joint.query_separated
    intro assignment
    have leftPositive := obsPositive joint.left_mem
    have rightPositive := obsPositive joint.right_mem
    rcases conditional assignment
        (leftPositive.kernelPositiveSupportedValue query.operationKernel assignment).toSupported
        (rightPositive.kernelPositiveSupportedValue query.operationKernel assignment).toSupported with
      ⟨conditionalEqual⟩
    rcases denominator assignment with ⟨denominatorEqual⟩
    exact ⟨ProbabilityResult.trans
      (query.chainEquivalentAt joint.left (C.mem_compatible _ joint.left_mem)
        leftPositive assignment)
      (ProbabilityResult.trans (ProbabilityResult.multiply_congr conditionalEqual denominatorEqual)
        (ProbabilityResult.symm (query.chainEquivalentAt joint.right
          (C.mem_compatible _ joint.right_mem) rightPositive assignment)))⟩

/-- Identifiability of the denominator supplies the pair-level equality
needed above.  The numerator's two explicit positive compatible models are
retained as the conditional counterexample. -/
noncomputable def ConditionalCounterexampleIn.ofJointNumeratorOfIdentifiableDenominator
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S)
    (joint : CounterexampleIn C query.jointNumerator)
    (denominator : C.identifiable query.jointDenominator) :
    ConditionalCounterexampleIn C query :=
  ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    obsPositive query joint (denominator joint.left joint.right joint.left_mem
      joint.right_mem joint.observationally_equal)

/-- An empty conditioner needs no positivity hypothesis: its source is
literally the joint numerator, which is supported at every assignment in
every finite SCM.  Thus joint value separation is genuine conditional value
separation on common support even in an unrestricted model class. -/
def ConditionalCounterexampleIn.ofJointNumeratorOfEmptyCondition
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (query : ConditionalKernelQuery S)
    (emptyCondition : NodeSet.isEmpty query.condition = true)
    (joint : CounterexampleIn C query.jointNumerator) :
    ConditionalCounterexampleIn C query := by
  have conditionEmpty := NodeSet.eq_empty_of_isEmpty emptyCondition
  have sourceEqual : query.sourceTerm = query.jointNumerator.sourceTerm := by
    simp only [ConditionalKernelQuery.sourceTerm, ConditionalKernelQuery.jointNumerator,
      JointKernelQuery.sourceTerm, conditionEmpty, NodeSet.union_empty_right]
  exact {
    left := joint.left
    right := joint.right
    left_mem := joint.left_mem
    right_mem := joint.right_mem
    observationally_equal := joint.observationally_equal
    query_separated := by
      intro conditional
      apply joint.query_separated
      intro assignment
      have leftSupported : query.sourceTerm.SupportedAt joint.left assignment := by
        rw [sourceEqual]
        exact query.jointNumerator.supportedAt joint.left assignment
      have rightSupported : query.sourceTerm.SupportedAt joint.right assignment := by
        rw [sourceEqual]
        exact query.jointNumerator.supportedAt joint.right assignment
      simpa only [sourceEqual] using conditional assignment leftSupported rightSupported
  }

/-- A positive conditional countermodel whenever every common root is a
queried outcome and the conditioner lies outside the hedge's large forest.

The root carrier pair separates the numerator by finite marginalization.
Its conditioner coordinates agree pointwise under the intervention because
both constructed mechanisms read the same private backgrounds outside the
large forest.  The matched-denominator chain lemma therefore separates the
conditional in that very pair.  No denominator-identifiability assumption
is made: graphical descendants in the conditioner are allowed, provided
they are outside this forest.  Nor does the construction need a successful
exchange test; it can close an irreducible nonempty-condition terminal.

These explicit geometric hypotheses do not hold for every hedge, so the
general irreducible conditional countermodel leaf remains separate. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootsSubsetOutcomeOfConditionOutsideLarge
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (rootsInOutcome : NodeSet.Subset w.roots query.outcome)
    (conditionOutside : NodeSet.Disjoint query.condition w.large) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let joint := w.positiveCounterexampleOfRootsSubsetOutcome rich
    (rootsInOutcome.trans (NodeSet.subset_union_left query.outcome query.condition))
  ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    (C := GraphModelClass.positive graph) (fun member => member.2) query joint
    (w.carrierDefectParityModels_valueEquivalent_outsideLarge rich
      query.jointDenominator conditionOutside)

/-! ## Restoring the original conditional and isolating the remaining leaf -/

/-- A countermodel for the actual terminal refutes the original conditional
query.  This wrapper retains the extracted trace, so callers cannot replace
the terminal by a merely similar query or discard the remaining given-set. -/
noncomputable def ConditionalKernelFailure.counterexampleOfTerminal
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail)
    (terminal : ConditionalCounterexampleIn C failure.terminal) :
    ConditionalCounterexampleIn C query :=
  failure.exchanges.transportCounterexample obsPositive terminal

/-- Close every exchange depth when the terminal numerator's explicit pair
agrees on its denominator.  The denominator equality is required of those
same models; an unrelated denominator counterexample would not suffice. -/
noncomputable def ConditionalKernelFailure.counterexampleOfDenominatorEquivalent
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail)
    (joint : CounterexampleIn C failure.terminal.jointNumerator)
    (denominator : failure.terminal.jointDenominator.ValueEquivalent joint.left joint.right) :
    ConditionalCounterexampleIn C query :=
  failure.counterexampleOfTerminal obsPositive
    (ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
      obsPositive failure.terminal joint denominator)

/-- The empty-terminal case of arbitrary recursive IDC failure.  Only the
exchange transport uses class positivity; the terminal conversion itself
works for every finite SCM. -/
noncomputable def ConditionalKernelFailure.counterexampleOfEmptyCondition
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail)
    (emptyCondition : NodeSet.isEmpty failure.terminal.condition = true)
    (joint : CounterexampleIn C failure.terminal.jointNumerator) :
    ConditionalCounterexampleIn C query :=
  failure.counterexampleOfTerminal obsPositive
    (ConditionalCounterexampleIn.ofJointNumeratorOfEmptyCondition
      failure.terminal emptyCondition joint)

/-- Reduce semantic failure of the entire recursive conditional program to
its irreducible terminal countermodel argument.  The leaf receives the actual
exhausted exchange search, failed joint invocation, and original-numerator
hedge.  Neither a successful numerator nor an arbitrary root-parity query
can accidentally discharge it. -/
theorem identifyConditionalKernel_failed_not_identifiable_of_terminalCounterexamples
    {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (counterexamples : forall (terminal : ConditionalKernelQuery S)
      (fail : IdentificationFail S),
      conditionalExchangeStep? graph terminal = none ->
      identifyJointKernel graph terminal.jointNumerator = .failed fail ->
      HedgeWitness graph terminal.jointNumerator -> ConditionalCounterexampleIn C terminal)
    (query : ConditionalKernelQuery S) {fail : IdentificationFail S}
    (result : identifyConditionalKernel graph query = .failed fail) :
    Not (C.conditionalIdentifiable query) :=
  let failure := identifyConditionalKernelFailed query result
  (failure.counterexampleOfTerminal obsPositive
    (counterexamples failure.terminal fail failure.no_exchange failure.joint_failed
      failure.hedge.witness)).not_identifiable

/-- Assemble conditional completeness once the general irreducible terminal
countermodel lemma is proved.  Public termination and literal-output success
compilation are already internal theorems; this constructor assumes neither
of them.  Matching the computed result constructs certificate data without
testing the proposition of semantic identifiability or invoking choice. -/
noncomputable def publishedConditionalCertificateOfIdentifiableOfTerminalCounterexamples
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (correct : DSeparationCorrectness graph)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (counterexamples : forall (terminal : ConditionalKernelQuery S)
      (fail : IdentificationFail S),
      conditionalExchangeStep? graph terminal = none ->
      identifyJointKernel graph terminal.jointNumerator = .failed fail ->
      HedgeWitness graph terminal.jointNumerator -> ConditionalCounterexampleIn C terminal)
    (query : ConditionalKernelQuery S) (identifiable : C.conditionalIdentifiable query) :
    PublishedConditionalCertificate C correct query := by
  cases result : identifyConditionalKernel graph query with
  | identified term =>
      exact identifyConditionalKernelPublishedCertificate correct obsPositive query result
  | failed fail =>
      exact False.elim
        (identifyConditionalKernel_failed_not_identifiable_of_terminalCounterexamples
          obsPositive counterexamples query result identifiable)
  | unfinished =>
      exact False.elim (identifyConditionalKernel_ne_unfinished graph query result)

/-- Final mechanical assembly boundary for the full published completeness
record.  The two explicitly supplied arguments are the genuinely open
semantic leaves: positive original-query hedge countermodels and irreducible
conditional terminal countermodels.  This is a reduction of the remaining
work, not a premise-free completeness theorem.  In particular, importing it
does not assert that either countermodel family has been constructed. -/
noncomputable def PublishedCompleteness.ofHedgeAndConditionalTerminalCounterexamples
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (hedgeCounterexamples : forall query, HedgeWitness graph query -> CounterexampleIn C query)
    (terminalCounterexamples : forall (terminal : ConditionalKernelQuery S)
      (fail : IdentificationFail S),
      conditionalExchangeStep? graph terminal = none ->
      identifyJointKernel graph terminal.jointNumerator = .failed fail ->
      HedgeWitness graph terminal.jointNumerator -> ConditionalCounterexampleIn C terminal) :
    PublishedCompleteness C where
  dseparation := graph.dSeparationCorrectness
  joint_complete := publishedJointCertificateOfIdentifiableOfHedgeCounterexamples
    graph.dSeparationCorrectness obsPositive hedgeCounterexamples
  conditional_complete := publishedConditionalCertificateOfIdentifiableOfTerminalCounterexamples
    graph.dSeparationCorrectness obsPositive terminalCounterexamples
  hedge_counterexample := hedgeCounterexamples

end Causality
end Thesis
