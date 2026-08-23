import Thesis.Causality.Model
import Thesis.Causality.Derivation

namespace Thesis
namespace Causality

open Probability

/-!
Denotational semantics for the finite probability-expression language.

The `ProbabilityTerm` syntax used by `DoCalculusDerivation` is
model-independent. This module gives each term a partial finite-rational
meaning in an explicit latent SCM. A missing result records failed support, so
division by a zero-probability condition is represented rather than silently
assigned a value.
-/

namespace ObservedSignature

/-- Replace one component of a dependent observed assignment. -/
def replace (S : ObservedSignature) (assignment : S.Assignment)
    (target : Fin S.count) (value : S.Value target) : S.Assignment :=
  fun i =>
    if h : i = target then h.symm ▸ value else assignment i

end ObservedSignature

namespace ProbabilityResult

/--
The partial result of evaluating a probability expression. `none` means that
the expression has no value at this assignment—for example because a
conditioning denominator is zero. It never means the rational number zero.
-/
abbrev Result := Option QProb

/--
Extensional equality for partial results. A supported result may only agree
with another supported result, and their rational values agree by
cross-multiplication through `QProb.Equiv`.
-/
inductive Equivalent : Result -> Result -> Type
  | unsupported : Equivalent none none
  | value {left right : QProb} :
      QProb.Equiv left right -> Equivalent (some left) (some right)

def refl (result : Result) : Equivalent result result := by
  cases result with
  | none => exact .unsupported
  | some value => exact .value (QProb.equiv_refl value)

def symm {left right : Result} (h : Equivalent left right) :
    Equivalent right left := by
  cases h with
  | unsupported => exact .unsupported
  | value hvalue => exact .value (QProb.equiv_symm hvalue)

def trans {left middle right : Result}
    (hlm : Equivalent left middle) (hmr : Equivalent middle right) :
    Equivalent left right := by
  cases hlm with
  | unsupported =>
      cases hmr
      exact .unsupported
  | value hlmValue =>
      cases hmr with
      | value hmrValue =>
          exact .value (QProb.equiv_trans hlmValue hmrValue)

/-- Addition is defined only when both summands are supported. -/
def add (left right : Result) : Result :=
  match left with
  | none => none
  | some leftValue =>
      match right with
      | none => none
      | some rightValue => some (QProb.add leftValue rightValue)

/-- Multiplication is defined only when both factors are supported. -/
def multiply (left right : Result) : Result :=
  match left with
  | none => none
  | some leftValue =>
      match right with
      | none => none
      | some rightValue => some (QProb.mul leftValue rightValue)

/--
Division propagates failed support and additionally checks that the displayed
denominator has positive numerator. This is the single point at which a
conditional probability can become `none`.
-/
def divide (numerator denominator : Result) : Result :=
  match numerator with
  | none => none
  | some numeratorValue =>
      match denominator with
      | none => none
      | some denominatorValue =>
          if h : 0 < denominatorValue.num then
            some (QProb.div numeratorValue denominatorValue h)
          else
            none

/-- A finite sum is supported exactly when every listed summand is supported. -/
def sum : List Result -> Result
  | [] => some QProb.zero
  | value :: values => add value (sum values)

def add_congr {left left' right right' : Result}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    Equivalent (add left right) (add left' right') := by
  cases hleft with
  | unsupported =>
      cases hright <;> exact .unsupported
  | value hleftValue =>
      cases hright with
      | unsupported => exact .unsupported
      | value hrightValue =>
          exact .value (QProb.add_congr hleftValue hrightValue)

def multiply_congr {left left' right right' : Result}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    Equivalent (multiply left right) (multiply left' right') := by
  cases hleft with
  | unsupported =>
      cases hright <;> exact .unsupported
  | value hleftValue =>
      cases hright with
      | unsupported => exact .unsupported
      | value hrightValue =>
          exact .value (QProb.mul_congr hleftValue hrightValue)

def divide_congr {left left' right right' : Result}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    Equivalent (divide left right) (divide left' right') := by
  cases hleft with
  | unsupported =>
      cases hright <;> exact .unsupported
  | value hleftValue =>
      cases hright with
      | unsupported => exact .unsupported
      | value hrightValue =>
          rename_i numerator numerator' denominator denominator'
          by_cases hpos : 0 < denominator.num
          · have hpos' : 0 < denominator'.num :=
              (QProb.equiv_num_pos_iff hrightValue).mp hpos
            simp only [divide, dif_pos hpos, dif_pos hpos']
            exact .value
              (QProb.div_congr hleftValue hrightValue hpos hpos')
          · have hpos' : Not (0 < denominator'.num) := by
              intro positive
              exact hpos ((QProb.equiv_num_pos_iff hrightValue).mpr positive)
            simp only [divide, dif_neg hpos, dif_neg hpos']
            exact .unsupported

noncomputable def sum_map_congr (values : List X) (left right : X -> Result)
    (h : forall value, Equivalent (left value) (right value)) :
    Equivalent (sum (values.map left)) (sum (values.map right)) := by
  induction values with
  | nil => exact refl _
  | cons value values ih =>
      exact add_congr (h value) ih

noncomputable def sum_map_congr_mem (values : List X)
    (left right : X -> Result)
    (h : forall value, value ∈ values -> Equivalent (left value) (right value)) :
    Equivalent (sum (values.map left)) (sum (values.map right)) := by
  induction values with
  | nil => exact refl _
  | cons value values ih =>
      exact add_congr (h value (by simp))
        (ih (fun member memberIn => h member (by simp [memberIn])))

def add_supported {left right : Result}
    (leftSupported : Sigma fun value => Equivalent left (some value))
    (rightSupported : Sigma fun value => Equivalent right (some value)) :
    Sigma fun value => Equivalent (add left right) (some value) := by
  rcases leftSupported with ⟨leftValue, hleft⟩
  rcases rightSupported with ⟨rightValue, hright⟩
  exact ⟨QProb.add leftValue rightValue,
    add_congr hleft hright⟩

def multiply_supported {left right : Result}
    (leftSupported : Sigma fun value => Equivalent left (some value))
    (rightSupported : Sigma fun value => Equivalent right (some value)) :
    Sigma fun value => Equivalent (multiply left right) (some value) := by
  rcases leftSupported with ⟨leftValue, hleft⟩
  rcases rightSupported with ⟨rightValue, hright⟩
  exact ⟨QProb.mul leftValue rightValue,
    multiply_congr hleft hright⟩

noncomputable def sum_map_supported (values : List X) (term : X -> Result)
    (supported : forall value,
      Sigma fun result => Equivalent (term value) (some result)) :
    Sigma fun result => Equivalent (sum (values.map term)) (some result) := by
  induction values with
  | nil =>
      exact ⟨QProb.zero, refl _⟩
  | cons value values ih =>
      exact add_supported (supported value) ih

end ProbabilityResult

namespace Kernel

/-- Values in the reference assignment supply the hard-intervention targets. -/
def intervention (kernel : Kernel S) (reference : S.Assignment) :
    (i : Fin S.count) -> Option (S.Value i) :=
  fun i => if kernel.action i then some (reference i) else none

/-- A sampled assignment agrees with a reference on the selected nodes. -/
def agreesOn (nodes : NodeSet S) (reference sample : S.Assignment) : Bool :=
  finAll S.count (fun i =>
    if nodes i then decide (sample i = reference i) else true)

theorem agreesOn_iff_project_eq (nodes : NodeSet S)
    (reference sample : S.Assignment) :
    agreesOn nodes reference sample = true <->
      S.project nodes sample = S.project nodes reference := by
  constructor
  · intro agreement
    have component := (finAll_eq_true_iff _).mp agreement
    funext i
    cases selected : nodes i with
    | false => simp [ObservedSignature.project, selected]
    | true =>
        have equalValue : sample i = reference i := by
          have := component i
          simpa [selected] using this
        simp [ObservedSignature.project, selected, equalValue]
  · intro projected
    apply (finAll_eq_true_iff _).mpr
    intro i
    cases selected : nodes i with
    | false => rfl
    | true =>
        have equalValue : sample i = reference i := by
          have := congrFun projected i
          simpa [ObservedSignature.project, selected] using this
        simp [equalValue]

theorem singleton_project_event (nodes : NodeSet S)
    (reference sample : S.Assignment) :
    FiniteProbRecord.singletonEvent (S.project nodes reference)
        (S.project nodes sample) =
      agreesOn nodes reference sample := by
  cases agreement : agreesOn nodes reference sample with
  | false =>
      have different : S.project nodes sample ≠ S.project nodes reference := by
        intro same
        have := (agreesOn_iff_project_eq nodes reference sample).mpr same
        rw [agreement] at this
        contradiction
      simp [FiniteProbRecord.singletonEvent, different]
  | true =>
      have same : S.project nodes sample = S.project nodes reference :=
        (agreesOn_iff_project_eq nodes reference sample).mp agreement
      simp [FiniteProbRecord.singletonEvent, same]

theorem agreesOn_full (reference sample : S.Assignment) :
    agreesOn (NodeSet.full : NodeSet S) reference sample =
      FiniteProbRecord.singletonEvent reference sample := by
  symm
  simpa [ObservedSignature.project, NodeSet.full] using
    (singleton_project_event (S := S) (NodeSet.full : NodeSet S)
      reference sample)

def numeratorEvent (kernel : Kernel S) (reference sample : S.Assignment) : Bool :=
  agreesOn kernel.outcome reference sample &&
    agreesOn kernel.condition reference sample

def conditionEvent (kernel : Kernel S) (reference sample : S.Assignment) : Bool :=
  agreesOn kernel.condition reference sample

def hasAction (kernel : Kernel S) : Bool :=
  finAny S.count kernel.action

def distribution (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) : FiniteProbRecord S.Assignment :=
  if kernel.hasAction then
    model.interventionalDist (kernel.intervention reference)
  else model.observationalDist

/-- Interpret `P(outcome | do(action), condition)` at one full valuation. -/
def denote (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) : ProbabilityResult.Result :=
  let distribution := kernel.distribution model reference
  let denominator := distribution.probVal (kernel.conditionEvent reference)
  let numerator := distribution.probVal (kernel.numeratorEvent reference)
  ProbabilityResult.divide (some numerator) (some denominator)

/-- An unconditional kernel denotes its finite cylinder probability. -/
noncomputable def unconditionalDenote
    (model : FiniteLatentSCM S) (outcome action : NodeSet S)
    (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      ((Kernel.mk outcome action NodeSet.empty).denote model reference)
      (some (((Kernel.mk outcome action NodeSet.empty).distribution
        model reference).probVal (agreesOn outcome reference))) := by
  let kernel : Kernel S := ⟨outcome, action, NodeSet.empty⟩
  let distribution := kernel.distribution model reference
  let cylinder := distribution.probVal (agreesOn outcome reference)
  let numerator := distribution.probVal (kernel.numeratorEvent reference)
  let denominator := distribution.probVal (kernel.conditionEvent reference)
  have normalized : QProb.Equiv denominator QProb.one := by
    exact QProb.equiv_trans
      (FiniteProbRecord.probVal_congr distribution _ Probability.topEvent
        (fun sample => by
          simp [kernel, Kernel.conditionEvent, Kernel.agreesOn,
            NodeSet.empty, finAll_true, Probability.topEvent]))
      distribution.normalization
  have positive : 0 < denominator.num :=
    (QProb.equiv_num_pos_iff normalized).mpr (by decide)
  have numeratorCylinder : QProb.Equiv numerator cylinder := by
    exact FiniteProbRecord.probVal_congr distribution _ _ (fun sample => by
      simp [kernel, Kernel.numeratorEvent,
        Kernel.agreesOn, NodeSet.empty, finAll_true])
  simp only [Kernel.denote, ProbabilityResult.divide]
  rw [dif_pos positive]
  exact .value (QProb.equiv_trans
    (QProb.div_equiv_of_den_equiv_one _ _ positive normalized)
    numeratorCylinder)

end Kernel

namespace ProbabilityTerm

def ObservationalAgreement (left right : FiniteLatentSCM S) : Prop :=
  forall event : S.Assignment -> Bool,
    QProb.Equiv
      (left.observationalValue event) (right.observationalValue event)

/-- Enumerate substitutions for the selected variables among the first `k`. -/
def marginalAssignmentsUpTo (S : ObservedSignature) (nodes : NodeSet S)
    (reference : S.Assignment) :
    (k : Nat) -> k <= S.count -> List S.Assignment
  | 0, _ => [reference]
  | k + 1, hk =>
      let previous :=
        marginalAssignmentsUpTo S nodes reference k
          (Nat.le_trans (Nat.le_succ k) hk)
      let node : Fin S.count := ⟨k, Nat.lt_of_succ_le hk⟩
      if nodes node then
        previous.flatMap (fun assignment =>
          (S.valueEnumeration node).map (fun value =>
            S.replace assignment node value))
      else
        previous

/-- Assignments over which a selected family of variables is marginalized. -/
def marginalAssignments (S : ObservedSignature) (nodes : NodeSet S)
    (reference : S.Assignment) : List S.Assignment :=
  marginalAssignmentsUpTo S nodes reference S.count (Nat.le_refl S.count)

/-- Partial denotation of a probability expression in one finite SCM. -/
noncomputable def denote (model : FiniteLatentSCM S) :
    ProbabilityTerm S -> S.Assignment -> ProbabilityResult.Result
  | .zero, _ => some QProb.zero
  | .kernel K, assignment => K.denote model assignment
  | .marginalize nodes inner, assignment =>
      ProbabilityResult.sum
        ((marginalAssignments S nodes assignment).map
          (fun variant => denote model inner variant))
  | .evaluateAt fixed inner, _ => denote model inner fixed
  | .add left right, assignment =>
      ProbabilityResult.add
        (denote model left assignment) (denote model right assignment)
  | .multiply left right, assignment =>
      ProbabilityResult.multiply
        (denote model left assignment) (denote model right assignment)
  | .divide numerator denominator, assignment =>
      ProbabilityResult.divide
        (denote model numerator assignment) (denote model denominator assignment)

/-- The probability mass of one complete observed assignment. -/
def singletonMassTerm (S : ObservedSignature) (assignment : S.Assignment) :
    ProbabilityTerm S :=
  .evaluateAt assignment
    (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩)

/-- Sum the masses of a finite list of complete observed assignments. -/
def eventTermFrom (S : ObservedSignature) :
    List S.Assignment -> ProbabilityTerm S
  | [] => .zero
  | assignment :: assignments =>
      .add (singletonMassTerm S assignment) (eventTermFrom S assignments)

/-- Compile any decidable event on a finite observed signature to a term. -/
def eventTerm (S : ObservedSignature) (event : S.Assignment -> Bool) :
    ProbabilityTerm S :=
  eventTermFrom S (S.assignmentEnumeration.filter event)

noncomputable def singletonMassTerm_denote
    (model : FiniteLatentSCM S) (reference assignment : S.Assignment) :
    ProbabilityResult.Equivalent
      ((singletonMassTerm S assignment).denote model reference)
      (some (model.observationalDist.probVal
        (FiniteProbRecord.singletonEvent assignment))) := by
  have noAction :
      (Kernel.mk (NodeSet.full : NodeSet S) NodeSet.empty
        NodeSet.empty).hasAction = false := by
    apply (finAny_eq_false_iff _).mpr
    intro i
    rfl
  have cylinder :=
    Kernel.unconditionalDenote model (NodeSet.full : NodeSet S)
      NodeSet.empty assignment
  have cylinder' : ProbabilityResult.Equivalent
      ((singletonMassTerm S assignment).denote model reference)
      (some (model.observationalDist.probVal
        (Kernel.agreesOn NodeSet.full assignment))) := by
    simpa only [singletonMassTerm, denote, Kernel.distribution, noAction,
      Bool.false_eq_true, ↓reduceIte] using cylinder
  exact ProbabilityResult.trans cylinder'
    (.value (FiniteProbRecord.probVal_congr model.observationalDist _ _
      (fun sample => Kernel.agreesOn_full assignment sample)))

noncomputable def eventTermFrom_denote
    (model : FiniteLatentSCM S) (reference : S.Assignment) :
    forall assignments : List S.Assignment,
      ProbabilityResult.Equivalent
        ((eventTermFrom S assignments).denote model reference)
        (some (QProb.listSum (assignments.map (fun assignment =>
          model.observationalDist.probVal
            (FiniteProbRecord.singletonEvent assignment)))))
  | [] => ProbabilityResult.refl _
  | assignment :: assignments => by
      simpa only [eventTermFrom, denote, List.map_cons, QProb.listSum] using
        ProbabilityResult.add_congr
          (singletonMassTerm_denote model reference assignment)
          (eventTermFrom_denote model reference assignments)

/-- The compiled term denotes exactly the probability of its Boolean event. -/
noncomputable def eventTerm_denote
    (model : FiniteLatentSCM S) (reference : S.Assignment)
    (event : S.Assignment -> Bool) :
    ProbabilityResult.Equivalent
      ((eventTerm S event).denote model reference)
      (some (model.observationalDist.probVal event)) := by
  unfold eventTerm
  exact ProbabilityResult.trans
    (eventTermFrom_denote model reference
      (S.assignmentEnumeration.filter event))
    (.value (QProb.equiv_symm
      (FiniteProbRecord.probVal_equiv_listSum_singletons
        model.observationalDist S.assignmentEnumeration
        S.assignmentEnumeration_nodup S.assignmentEnumeration_complete event)))

/--
Support and equality at one finite valuation, used by partial kernels.

The witness lives in `Type`, not merely `Prop`, because later certificate
constructions need the computed rational value as well as the fact that the
expression is defined.
-/
def SupportedAt (model : FiniteLatentSCM S) (term : ProbabilityTerm S)
    (assignment : S.Assignment) : Type :=
  Sigma fun value =>
    ProbabilityResult.Equivalent (term.denote model assignment) (some value)

def EquivalentAt (model : FiniteLatentSCM S)
    (left right : ProbabilityTerm S) (assignment : S.Assignment) : Type :=
  ProbabilityResult.Equivalent
    (left.denote model assignment) (right.denote model assignment)

noncomputable def marginalize_congrAt (model : FiniteLatentSCM S)
    (nodes : NodeSet S) (assignment : S.Assignment) {left right}
    (h : forall variant,
      variant ∈ marginalAssignments S nodes assignment ->
        EquivalentAt model left right variant) :
    EquivalentAt model (.marginalize nodes left) (.marginalize nodes right)
      assignment := by
  simpa only [denote] using
    (ProbabilityResult.sum_map_congr_mem
      (marginalAssignments S nodes assignment)
      (fun variant => left.denote model variant)
      (fun variant => right.denote model variant) h)

theorem actionFree_hasAction_false (kernel : Kernel S)
    (actionFree : (ProbabilityTerm.kernel kernel).ActionFree) :
    kernel.hasAction = false := by
  apply (finAny_eq_false_iff kernel.action).mpr
  exact actionFree

/-- Action-free expressions have the same denotation in observationally equal models. -/
noncomputable def actionFree_invariant
    (left right : FiniteLatentSCM S)
    (observational : ObservationalAgreement left right)
    (term : ProbabilityTerm S) (actionFree : term.ActionFree) :
    forall assignment,
      ProbabilityResult.Equivalent
        (term.denote left assignment) (term.denote right assignment) := by
  intro assignment
  induction term generalizing assignment with
  | zero => exact ProbabilityResult.refl _
  | kernel kernel =>
      have noAction := actionFree_hasAction_false kernel actionFree
      simp only [denote, Kernel.denote, Kernel.distribution, noAction,
        Bool.false_eq_true, ↓reduceIte]
      exact ProbabilityResult.divide_congr
        (.value (observational (kernel.numeratorEvent assignment)))
        (.value (observational (kernel.conditionEvent assignment)))
  | marginalize nodes term ih =>
      simpa only [denote] using
        (ProbabilityResult.sum_map_congr
          (marginalAssignments S nodes assignment)
          (fun variant => term.denote left variant)
          (fun variant => term.denote right variant)
          (fun variant => ih actionFree variant))
  | evaluateAt fixed term ih =>
      exact ih actionFree fixed
  | add first second firstIH secondIH =>
      simpa only [denote] using
        ProbabilityResult.add_congr
          (firstIH actionFree.1 assignment)
          (secondIH actionFree.2 assignment)
  | multiply first second firstIH secondIH =>
      simpa only [denote] using
        ProbabilityResult.multiply_congr
          (firstIH actionFree.1 assignment)
          (secondIH actionFree.2 assignment)
  | divide numerator denominator numeratorIH denominatorIH =>
      simpa only [denote] using
        ProbabilityResult.divide_congr
          (numeratorIH actionFree.1 assignment)
          (denominatorIH actionFree.2 assignment)

end ProbabilityTerm

/-! ## Pointwise support semantics for partial conditional kernels -/

/-- Primitive soundness at one valuation and only under its local support. -/
structure LocalPrimitiveSoundness (G : ObservedGraph S)
    (model : FiniteLatentSCM S) where
  doRule : forall {left right} (assignment : S.Assignment),
    DoRuleApplication G left right ->
      ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
      ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
      ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
        assignment
  marginalization : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
      ProbabilityTerm.SupportedAt model (.kernel ⟨y, x, w⟩) assignment ->
      ProbabilityTerm.SupportedAt model
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment ->
      ProbabilityTerm.EquivalentAt model
        (.kernel ⟨y, x, w⟩)
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment
  conditioning : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
      ProbabilityTerm.SupportedAt model
        (.kernel ⟨y, x, NodeSet.union z w⟩) assignment ->
      ProbabilityTerm.SupportedAt model
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      ProbabilityTerm.EquivalentAt model
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment
  chain : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
      ProbabilityTerm.SupportedAt model
        (.kernel ⟨NodeSet.union y z, x, w⟩) assignment ->
      ProbabilityTerm.SupportedAt model
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      ProbabilityTerm.EquivalentAt model
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment

/--
Recursive support evidence for one valuation of one derivation. The first two
components certify the endpoints. The final component mirrors the syntax tree
and carries precisely the subexpression support needed by each proof rule.
-/
def LocalDerivationSupport (model : FiniteLatentSCM S)
    (assignment : S.Assignment) {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right) : Type :=
  left.SupportedAt model assignment ×
    right.SupportedAt model assignment ×
      match derivation with
      | .refl _ => Unit
      | .symm inner => LocalDerivationSupport model assignment inner
      | .trans first second =>
          LocalDerivationSupport model assignment first ×
            LocalDerivationSupport model assignment second
      | .doRule _ => Unit
      | .marginalization _ _ _ _ _ => Unit
      | .conditioning _ _ _ _ _ => Unit
      | .chain _ _ _ _ _ => Unit
      | .marginalizeCongr nodes inner =>
          forall variant,
            variant ∈ ProbabilityTerm.marginalAssignments S nodes assignment ->
              LocalDerivationSupport model variant inner
      | .evaluateAtCongr fixed inner =>
          LocalDerivationSupport model fixed inner
      | .addCongr first second =>
          LocalDerivationSupport model assignment first ×
            LocalDerivationSupport model assignment second
      | .multiplyCongr first second =>
          LocalDerivationSupport model assignment first ×
            LocalDerivationSupport model assignment second
      | .divideCongr numerator denominator =>
          LocalDerivationSupport model assignment numerator ×
            LocalDerivationSupport model assignment denominator

noncomputable def LocalDerivationSupport.endpoints
    {left right : ProbabilityTerm S}
    {derivation : DoCalculusDerivation G left right}
    (supported : LocalDerivationSupport model assignment derivation) :
    left.SupportedAt model assignment × right.SupportedAt model assignment := by
  cases derivation <;> exact ⟨supported.1, supported.2.1⟩

noncomputable def DoCalculusDerivation.denotational_soundAt
    (semantics : LocalPrimitiveSoundness G model)
    (derivation : DoCalculusDerivation G left right)
    (supported : LocalDerivationSupport model assignment derivation) :
    ProbabilityTerm.EquivalentAt model left right assignment := by
  /-
  The proof follows the certificate syntax exactly: primitive leaves use the
  supplied local laws, while congruence constructors recurse into their
  independently supported subderivations.
  -/
  induction derivation generalizing assignment with
  | refl => exact ProbabilityResult.refl _
  | symm derivation ih =>
      exact ProbabilityResult.symm (ih supported.2.2)
  | trans leftDerivation rightDerivation leftIH rightIH =>
      exact ProbabilityResult.trans
        (leftIH supported.2.2.1) (rightIH supported.2.2.2)
  | doRule rule =>
      exact semantics.doRule assignment rule supported.1 supported.2.1
  | marginalization x y z w disjoint =>
      exact semantics.marginalization x y z w assignment disjoint
        supported.1 supported.2.1
  | conditioning x y z w disjoint =>
      exact semantics.conditioning x y z w assignment disjoint
        supported.1 supported.2.1
  | chain x y z w disjoint =>
      exact semantics.chain x y z w assignment disjoint
        supported.1 supported.2.1
  | marginalizeCongr nodes derivation ih =>
      apply ProbabilityTerm.marginalize_congrAt
      intro variant member
      exact ih (supported.2.2 variant member)
  | evaluateAtCongr fixed derivation ih =>
      exact ih supported.2.2
  | addCongr leftDerivation rightDerivation leftIH rightIH =>
      simpa only [ProbabilityTerm.denote] using
        ProbabilityResult.add_congr
          (leftIH supported.2.2.1) (rightIH supported.2.2.2)
  | multiplyCongr leftDerivation rightDerivation leftIH rightIH =>
      simpa only [ProbabilityTerm.denote] using
        ProbabilityResult.multiply_congr
          (leftIH supported.2.2.1) (rightIH supported.2.2.2)
  | divideCongr numeratorDerivation denominatorDerivation
      numeratorIH denominatorIH =>
      simpa only [ProbabilityTerm.denote] using
        ProbabilityResult.divide_congr
          (numeratorIH supported.2.2.1) (denominatorIH supported.2.2.2)

end Causality
end Thesis
