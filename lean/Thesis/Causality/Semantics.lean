import Thesis.Causality.ProbabilityResult
import Thesis.Causality.SupportAwareSemantics
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

@[simp] theorem replace_at (S : ObservedSignature) (assignment : S.Assignment)
    (target : Fin S.count) (value : S.Value target) :
    S.replace assignment target value target = value := by
  simp [replace]

theorem replace_ne (S : ObservedSignature) (assignment : S.Assignment)
    (target i : Fin S.count) (value : S.Value target) (different : i ≠ target) :
    S.replace assignment target value i = assignment i := by
  simp [replace, different]

end ObservedSignature

namespace NodeSet

/-- Boolean node-set disjointness is symmetric. -/
theorem Disjoint.symm {left right : NodeSet S}
    (disjoint : Disjoint left right) : Disjoint right left := by
  intro i rightSelected
  cases leftSelected : left i with
  | false => rfl
  | true =>
      have impossible := disjoint i leftSelected
      rw [rightSelected] at impossible
      contradiction

end NodeSet


namespace Kernel

/-- Values in the reference assignment supply the hard-intervention targets. -/
def intervention (kernel : Kernel S) (reference : S.Assignment) :
    (i : Fin S.count) -> Option (S.Value i) :=
  fun i => if kernel.action i then some (reference i) else none

/-- A sampled assignment agrees with a reference on the selected nodes. -/
def agreesOn (nodes : NodeSet S) (reference sample : S.Assignment) : Bool :=
  finAll S.count (fun i =>
    if nodes i then decide (sample i = reference i) else true)

/-- Every assignment agrees with itself on any selected node set. -/
theorem agreesOn_refl (nodes : NodeSet S) (reference : S.Assignment) :
    agreesOn nodes reference reference = true := by
  unfold agreesOn
  refine (finAll_eq_true_iff _).mpr ?_
  intro i
  cases nodes i <;> simp

private theorem finAll_and {n : Nat} (left right : Fin n -> Bool) :
    finAll n (fun i => left i && right i) =
      (finAll n left && finAll n right) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [finAll]
      rw [inductionHypothesis]
      cases finAll n (fun i => left i.castSucc) <;>
        cases finAll n (fun i => right i.castSucc) <;>
        cases left (Fin.last n) <;> cases right (Fin.last n) <;> rfl

/-- Agreement on a union is the conjunction of the two cylinder agreements. -/
theorem agreesOn_union (left right : NodeSet S)
    (reference sample : S.Assignment) :
    agreesOn (NodeSet.union left right) reference sample =
      (agreesOn left reference sample &&
        agreesOn right reference sample) := by
  unfold agreesOn
  rw [← finAll_and]
  apply finAll_congr
  intro i
  cases hleft : left i <;> cases hright : right i <;>
    simp [NodeSet.union, hleft, hright]

/-- Changing a reference outside the selected nodes does not change agreement. -/
theorem agreesOn_reference_congr (nodes : NodeSet S)
    (first second sample : S.Assignment)
    (agree : ∀ i, nodes i = true -> first i = second i) :
    agreesOn nodes first sample = agreesOn nodes second sample := by
  unfold agreesOn
  apply finAll_congr
  intro i
  cases selected : nodes i with
  | false => rfl
  | true =>
      simp only [↓reduceIte]
      rw [agree i selected]

/-- A singleton agreement cylinder reads one full observed label.  The
statement retains the signature's actual value type, not a Boolean encoding. -/
theorem agreesOn_singleton {S : ObservedSignature} (node : Fin S.count) (reference sample : S.Assignment) :
    agreesOn (NodeSet.singleton node) reference sample = decide (sample node = reference node) := by
  apply Bool.eq_iff_iff.mpr
  simp only [agreesOn, NodeSet.singleton, finAll_eq_true_iff]
  constructor
  · intro agreed
    simpa only [decide_true, if_true] using agreed node
  · intro agreed index
    by_cases same : index = node
    · subst index
      simpa only [decide_true, if_true] using agreed
    · simp only [same, decide_false, Bool.false_eq_true, if_false]

/-- Changing a sample outside the selected nodes does not change agreement. -/
theorem agreesOn_sample_congr (nodes : NodeSet S)
    (reference left right : S.Assignment)
    (agree : ∀ i, nodes i = true -> left i = right i) :
    agreesOn nodes reference left = agreesOn nodes reference right := by
  unfold agreesOn
  apply finAll_congr
  intro i
  cases selected : nodes i with
  | false => rfl
  | true =>
      simp only [↓reduceIte]
      rw [agree i selected]

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

/-- Every kernel-distribution event is the pullback through the model's
actual intervened evaluation.  When the action is empty its intervention is
literally `noIntervention`, so the observational branch needs no independent
semantic or positivity assumption. -/
theorem distribution_probVal (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : Probability.Event S.Assignment) :
    Probability.QProb.Equiv ((kernel.distribution model reference).probVal event)
      (model.prior.probVal (fun unit => event (model.evalUnder (kernel.intervention reference) unit))) := by
  cases active : kernel.hasAction with
  | true =>
      simpa only [distribution, active, if_true, FiniteLatentSCM.interventionalDist] using
        model.prior.map_probVal (model.evalUnder (kernel.intervention reference)) event
  | false =>
      have empty : kernel.intervention reference = FiniteLatentSCM.noIntervention S := by
        funext node
        have inactive := (finAny_eq_false_iff kernel.action).mp active node
        simp only [intervention, inactive, Bool.false_eq_true, if_false, FiniteLatentSCM.noIntervention]
      simpa only [distribution, active, Bool.false_eq_true, if_false, empty,
        FiniteLatentSCM.observationalDist, FiniteLatentSCM.eval] using
        model.prior.map_probVal (model.evalUnder (FiniteLatentSCM.noIntervention S)) event

/-- Kernel distributions depend on the action field, not outcome or condition. -/
theorem distribution_eq_of_action (model : FiniteLatentSCM S)
    (firstOutcome secondOutcome action firstCondition secondCondition : NodeSet S)
    (reference : S.Assignment) :
    (Kernel.mk firstOutcome action firstCondition).distribution model reference =
    (Kernel.mk secondOutcome action secondCondition).distribution model reference := by
  rfl

/-- Kernel distributions agree when the intervention references agree on actions. -/
theorem distribution_eq_of_action_reference
    (model : FiniteLatentSCM S)
    (firstOutcome secondOutcome action firstCondition secondCondition : NodeSet S)
    (firstReference secondReference : S.Assignment)
    (agree : ∀ i, action i = true -> firstReference i = secondReference i) :
    (Kernel.mk firstOutcome action firstCondition).distribution model firstReference =
      (Kernel.mk secondOutcome action secondCondition).distribution model secondReference := by
  simp only [distribution, hasAction]
  split
  · congr 1
    funext i
    unfold intervention
    cases selected : action i with
    | false => simp [selected]
    | true =>
        simp only [selected, ↓reduceIte]
        rw [agree i selected]
  · rfl

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

def MarginalVariantUpTo (S : ObservedSignature) (nodes : NodeSet S)
    (reference variant : S.Assignment) (k : Nat) : Prop :=
  (∀ i : Fin S.count, i.val < k -> nodes i = false -> variant i = reference i) ∧
    (∀ i : Fin S.count, k ≤ i.val -> variant i = reference i)

theorem mem_marginalAssignmentsUpTo_iff
    (S : ObservedSignature) (nodes : NodeSet S) (reference variant : S.Assignment) :
    ∀ (k : Nat) (hk : k ≤ S.count),
      variant ∈ marginalAssignmentsUpTo S nodes reference k hk ↔
        MarginalVariantUpTo S nodes reference variant k := by
  intro k
  induction k generalizing variant with
  | zero =>
      intro hk
      simp only [marginalAssignmentsUpTo, List.mem_singleton]
      constructor
      · intro same
        subst variant
        exact ⟨fun _ impossible => (Nat.not_lt_zero _ impossible).elim,
          fun _ _ => rfl⟩
      · intro invariant
        funext i
        exact invariant.2 i (Nat.zero_le _)
  | succ k ih =>
      intro hk
      let node : Fin S.count := ⟨k, Nat.lt_of_succ_le hk⟩
      simp only [marginalAssignmentsUpTo]
      split <;> rename_i selected
      · change nodes node = true at selected
        simp only [List.mem_flatMap, List.mem_map]
        constructor
        · intro member
          rcases member with ⟨previous, previousMember, value, valueMember, replaced⟩
          subst variant
          have previousInvariant :=
            (ih previous (Nat.le_trans (Nat.le_succ k) hk)).mp previousMember
          constructor
          · intro i ilt notSelected
            by_cases same : i = node
            · subst i
              simp [selected] at notSelected
            · have valueDifferent : i.val ≠ k := by
                intro equality
                exact same (Fin.ext equality)
              exact (S.replace_ne previous node i value same).trans
                (previousInvariant.1 i (by omega) notSelected)
          · intro i outside
            have different : i ≠ node := by
              intro same
              have sameValue : i.val = node.val := congrArg Fin.val same
              change i.val = k at sameValue
              omega
            exact (S.replace_ne previous node i value different).trans
              (previousInvariant.2 i (by omega))
        · intro invariant
          let previous := S.replace variant node (reference node)
          have previousInvariant :
              MarginalVariantUpTo S nodes reference previous k := by
            constructor
            · intro i ilt notSelected
              have different : i ≠ node := by
                intro same
                have sameValue : i.val = node.val := congrArg Fin.val same
                change i.val = k at sameValue
                omega
              simp only [previous]
              rw [S.replace_ne variant node i (reference node) different]
              exact invariant.1 i (Nat.lt_trans ilt (Nat.lt_succ_self k)) notSelected
            · intro i outside
              by_cases same : i = node
              · subst i
                exact S.replace_at variant node (reference node)
              · simp only [previous]
                rw [S.replace_ne variant node i (reference node) same]
                have valueDifferent : i.val ≠ k := by
                  intro equality
                  exact same (Fin.ext equality)
                exact invariant.2 i (by omega)
          refine ⟨previous, (ih previous (Nat.le_trans (Nat.le_succ k) hk)).mpr previousInvariant,
            variant node, S.value_complete node (variant node), ?_⟩
          change S.replace previous node (variant node) = variant
          funext i
          by_cases same : i = node
          · subst i
            exact S.replace_at previous node (variant node)
          · rw [S.replace_ne previous node i (variant node) same]
            simp only [previous]
            exact S.replace_ne variant node i (reference node) same
      · change ¬ nodes node = true at selected
        have notSelected : nodes node = false := by
          cases value : nodes node <;> simp_all
        rw [ih variant (Nat.le_trans (Nat.le_succ k) hk)]
        constructor
        · intro previousInvariant
          constructor
          · intro i ilt iNotSelected
            by_cases before : i.val < k
            · exact previousInvariant.1 i before iNotSelected
            · have atNode : i = node := by
                apply Fin.ext
                simp only [node]
                omega
              subst i
              exact previousInvariant.2 node (by simp [node])
          · intro i outside
            exact previousInvariant.2 i (Nat.le_trans (Nat.le_succ k) outside)
        · intro invariant
          constructor
          · intro i before iNotSelected
            exact invariant.1 i (Nat.lt_trans before (Nat.lt_succ_self k)) iNotSelected
          · intro i outside
            by_cases equality : i.val = k
            · have atNode : i = node := Fin.ext equality
              subst i
              exact invariant.1 node (by simp [node]) notSelected
            · exact invariant.2 i (by omega)

theorem marginalAssignmentsUpTo_nodup
    (S : ObservedSignature) (nodes : NodeSet S) (reference : S.Assignment) :
    ∀ (k : Nat) (hk : k ≤ S.count),
      (marginalAssignmentsUpTo S nodes reference k hk).Nodup := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [marginalAssignmentsUpTo]
  | succ k ih =>
      intro hk
      let node : Fin S.count := ⟨k, Nat.lt_of_succ_le hk⟩
      simp only [marginalAssignmentsUpTo]
      split <;> rename_i selected
      · change nodes node = true at selected
        apply (List.pairwise_flatMap).mpr
        constructor
        · intro previous previousMember
          apply (List.pairwise_map).mpr
          change List.Pairwise
            (fun first second =>
              S.replace previous node first ≠ S.replace previous node second)
            (S.valueEnumeration node)
          exact (S.value_nodup node).imp (by
            intro first second different equalReplacement
            apply different
            have atNode := congrFun equalReplacement node
            simpa only [S.replace_at] using atNode)
        · apply List.Pairwise.imp_of_mem (p :=
              ih (Nat.le_trans (Nat.le_succ k) hk))
          intro first second firstIn secondIn different
          intro firstReplacement firstMember secondReplacement secondMember
          simp only [List.mem_map] at firstMember secondMember
          rcases firstMember with ⟨firstValue, _, firstEq⟩
          rcases secondMember with ⟨secondValue, _, secondEq⟩
          intro replacementsEqual
          apply different
          have firstInvariant :=
            (mem_marginalAssignmentsUpTo_iff S nodes reference first k
              (Nat.le_trans (Nat.le_succ k) hk)).mp firstIn
          have secondInvariant :=
            (mem_marginalAssignmentsUpTo_iff S nodes reference second k
              (Nat.le_trans (Nat.le_succ k) hk)).mp secondIn
          funext i
          by_cases same : i = node
          · subst i
            exact (firstInvariant.2 node (by simp [node])).trans
              (secondInvariant.2 node (by simp [node])).symm
          · have atI := congrFun replacementsEqual i
            rw [← firstEq, ← secondEq] at atI
            change S.replace first node firstValue i =
              S.replace second node secondValue i at atI
            simpa only [S.replace_ne first node i firstValue same,
              S.replace_ne second node i secondValue same] using atI
      · exact ih (Nat.le_trans (Nat.le_succ k) hk)

theorem mem_marginalAssignments_iff
    (S : ObservedSignature) (nodes : NodeSet S)
    (reference variant : S.Assignment) :
    variant ∈ marginalAssignments S nodes reference ↔
      ∀ i, nodes i = false -> variant i = reference i := by
  rw [marginalAssignments,
    mem_marginalAssignmentsUpTo_iff S nodes reference variant]
  constructor
  · intro invariant i notSelected
    exact invariant.1 i i.isLt notSelected
  · intro outside
    constructor
    · exact fun i _ => outside i
    · intro i impossible
      exact (Nat.not_le_of_lt i.isLt impossible).elim

/-- Complements of an outcome set enumerate the outcome cylinder: a
variant is a `V \ Y` substitution of the reference exactly when it
agrees with the reference on `Y`. -/
theorem mem_marginal_complement_iff_agreesOn
    (outcome : NodeSet S) (reference variant : S.Assignment) :
    variant ∈ marginalAssignments S
      (NodeSet.diff NodeSet.full outcome) reference ↔
      Kernel.agreesOn outcome reference variant = true := by
  rw [mem_marginalAssignments_iff]
  constructor
  · intro h
    unfold Kernel.agreesOn
    apply (finAll_eq_true_iff _).mpr
    intro i
    cases hy : outcome i
    · rfl
    · have hdiff : NodeSet.diff NodeSet.full outcome i = false := by
        simp [NodeSet.diff, NodeSet.full, hy]
      have heq := h i hdiff
      exact decide_eq_true heq
  · intro hagr i hdiff
    have hy : outcome i = true := by
      simp [NodeSet.diff, NodeSet.full] at hdiff
      cases hY : outcome i
      · simp [hY] at hdiff
      · rfl
    have hcomp :=
      (finAll_eq_true_iff _).mp (by simpa [Kernel.agreesOn] using hagr) i
    simpa [hy] using hcomp

theorem marginalAssignments_nodup
    (S : ObservedSignature) (nodes : NodeSet S) (reference : S.Assignment) :
    (marginalAssignments S nodes reference).Nodup :=
  marginalAssignmentsUpTo_nodup S nodes reference S.count (Nat.le_refl _)

def marginalVariant (S : ObservedSignature) (nodes : NodeSet S)
    (reference sample : S.Assignment) : S.Assignment :=
  fun i => if nodes i then sample i else reference i

theorem marginalVariant_mem (S : ObservedSignature) (nodes : NodeSet S)
    (reference sample : S.Assignment) :
    marginalVariant S nodes reference sample ∈
      marginalAssignments S nodes reference := by
  apply (mem_marginalAssignments_iff S nodes reference _).mpr
  intro i notSelected
  simp [marginalVariant, notSelected]

theorem marginal_member_agrees_outside
    {variant : S.Assignment}
    (member : variant ∈ marginalAssignments S nodes reference)
    (outside : nodes i = false) : variant i = reference i :=
  (mem_marginalAssignments_iff S nodes reference variant).mp member i outside

/-- Partial denotation of a probability expression in one finite SCM. -/
def denote (model : FiniteLatentSCM S) :
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
  | .weightedMultiply weight factor, assignment =>
      ProbabilityResult.weightedMultiply
        (denote model weight assignment) (denote model factor assignment)
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

/-- Marginalization preserves an everywhere-positive current expression.

The reference itself occurs in the finite substitution list, even when no
coordinates are summed or the signature is empty.  Thus the sum is nonempty;
the positivity argument does not need a default selected vertex, an ordering
assumption on the host, or a classical nonemptiness principle. -/
noncomputable def marginalizePositiveSupportedValue
    (model : FiniteLatentSCM S) (nodes : NodeSet S)
    (term : ProbabilityTerm S) (reference : S.Assignment)
    (positive : forall variant,
      ProbabilityResult.PositiveSupportedValue (term.denote model variant)) :
    ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.marginalize nodes term).denote model reference) := by
  apply ProbabilityResult.PositiveSupportedValue.sum_map
    (marginalAssignments S nodes reference)
    (fun variant => term.denote model variant)
  · intro empty
    have selfMember : reference ∈ marginalAssignments S nodes reference :=
      (mem_marginalAssignments_iff S nodes reference reference).mpr
        (fun _ _ => rfl)
    rw [empty] at selfMember
    cases selfMember
  · exact fun variant _member => positive variant

/-- Transport support along syntactic equality of terms.  Used by
`DoCalculusDerivation.eqCongr` when a `NodeSet` covering rewrites a
kernel without changing its denotation. -/
def SupportedAt.congr {t1 t2 : ProbabilityTerm S} (h : t1 = t2)
    {model : FiniteLatentSCM S} {assignment : S.Assignment}
    (supported : SupportedAt model t1 assignment) :
    SupportedAt model t2 assignment :=
  h ▸ supported

def EquivalentAt (model : FiniteLatentSCM S)
    (left right : ProbabilityTerm S) (assignment : S.Assignment) : Type :=
  ProbabilityResult.Equivalent
    (left.denote model assignment) (right.denote model assignment)

/-- Transport support along denotational equality at one assignment. -/
def SupportedAt.of_equivalent {t1 t2 : ProbabilityTerm S}
    {model : FiniteLatentSCM S} {assignment : S.Assignment}
    (h : EquivalentAt model t1 t2 assignment)
    (supported : SupportedAt model t1 assignment) :
    SupportedAt model t2 assignment :=
  ⟨supported.1, ProbabilityResult.trans (ProbabilityResult.symm h) supported.2⟩

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

/--
Lift propositionally inhabited pointwise equivalence through a finite
marginal.  Unlike `marginalize_congrAt`, this form does not expose a function
that chooses Type-valued evidence for every assignment; it follows the finite
enumeration and retains only an inhabited result.
-/
theorem marginalize_congrAt_nonempty (model : FiniteLatentSCM S)
    (nodes : NodeSet S) (assignment : S.Assignment) {left right}
    (h : forall variant,
      Nonempty (EquivalentAt model left right variant)) :
    Nonempty
      (EquivalentAt model (.marginalize nodes left) (.marginalize nodes right)
        assignment) := by
  simpa only [denote] using
    ProbabilityResult.sum_map_congr_nonempty
      (marginalAssignments S nodes assignment)
      (fun variant => left.denote model variant)
      (fun variant => right.denote model variant) h

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
  | weightedMultiply weight factor weightIH factorIH =>
      simpa only [denote] using
        ProbabilityResult.weightedMultiply_congr
          (weightIH actionFree.1 assignment)
          (factorIH actionFree.2 assignment)
  | divide numerator denominator numeratorIH denominatorIH =>
      simpa only [denote] using
        ProbabilityResult.divide_congr
          (numeratorIH actionFree.1 assignment)
          (denominatorIH actionFree.2 assignment)

/-- Recover `P(Y,Z | do(X),W)` by weighting `P(Y | do(X),Z,W)` with
`P(Z | do(X),W)`.  Weight order matters: the first operand is the conditioning
cell mass.  The conditional factor itself is not made defined at null cells.

The equality includes the unsupported-base case, so it does not even need
an endpoint-support hypothesis.  Disjoint query sets are required by causal
derivation constructors elsewhere; this probability identity also holds for
overlapping cylinder sets. -/
noncomputable def weightedChain_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (reference : S.Assignment) :
    EquivalentAt model
      (.kernel ⟨NodeSet.union y z, x, w⟩)
      (.weightedMultiply
        (.kernel ⟨z, x, w⟩)
        (.kernel ⟨y, x, NodeSet.union z w⟩)) reference := by
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let conditionalKernel : Kernel S := ⟨y, x, NodeSet.union z w⟩
  let weightKernel : Kernel S := ⟨z, x, w⟩
  let distribution := jointKernel.distribution model reference
  let jointEvent : Event S.Assignment := fun sample =>
    Kernel.agreesOn y reference sample &&
      Kernel.agreesOn z reference sample &&
      Kernel.agreesOn w reference sample
  let middleEvent : Event S.Assignment := fun sample =>
    Kernel.agreesOn z reference sample && Kernel.agreesOn w reference sample
  let baseEvent : Event S.Assignment := Kernel.agreesOn w reference
  let numerator := distribution.probVal jointEvent
  let middle := distribution.probVal middleEvent
  let base := distribution.probVal baseEvent
  have conditionalDistribution :
      conditionalKernel.distribution model reference = distribution :=
    Kernel.distribution_eq_of_action model
      y (NodeSet.union y z) x (NodeSet.union z w) w reference
  have weightDistribution :
      weightKernel.distribution model reference = distribution :=
    Kernel.distribution_eq_of_action model
      z (NodeSet.union y z) x w w reference
  have jointNumerator : QProb.Equiv
      ((jointKernel.distribution model reference).probVal
        (jointKernel.numeratorEvent reference)) numerator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [jointKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have jointBase : QProb.Equiv
      ((jointKernel.distribution model reference).probVal
        (jointKernel.conditionEvent reference)) base :=
    QProb.equiv_refl _
  have conditionalNumerator : QProb.Equiv
      ((conditionalKernel.distribution model reference).probVal
        (conditionalKernel.numeratorEvent reference)) numerator := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have conditionalMiddle : QProb.Equiv
      ((conditionalKernel.distribution model reference).probVal
        (conditionalKernel.conditionEvent reference)) middle := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, middleEvent, Kernel.conditionEvent,
      Kernel.agreesOn_union]
  have weightMiddle : QProb.Equiv
      ((weightKernel.distribution model reference).probVal
        (weightKernel.numeratorEvent reference)) middle := by
    rw [weightDistribution]
    exact QProb.equiv_refl _
  have weightBase : QProb.Equiv
      ((weightKernel.distribution model reference).probVal
        (weightKernel.conditionEvent reference)) base := by
    rw [weightDistribution]
    exact QProb.equiv_refl _
  let jointCanonical : ProbabilityResult.Equivalent
      (jointKernel.denote model reference)
      (ProbabilityResult.divide (some numerator) (some base)) :=
    ProbabilityResult.divide_congr (.value jointNumerator) (.value jointBase)
  let weightedCanonical : ProbabilityResult.Equivalent
      (ProbabilityResult.weightedMultiply
        (weightKernel.denote model reference)
        (conditionalKernel.denote model reference))
      (ProbabilityResult.weightedMultiply
        (ProbabilityResult.divide (some middle) (some base))
        (ProbabilityResult.divide (some numerator) (some middle))) :=
    ProbabilityResult.weightedMultiply_congr
      (ProbabilityResult.divide_congr (.value weightMiddle) (.value weightBase))
      (ProbabilityResult.divide_congr
        (.value conditionalNumerator) (.value conditionalMiddle))
  have dominated : QProb.LE numerator middle :=
    Nat.mul_le_mul_right distribution.den
      (FiniteProbRecord.eventMass_mono distribution.atoms jointEvent middleEvent
        (fun _ selected => by
          exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp selected).1).2,
            (Bool.and_eq_true_iff.mp selected).2⟩))
  exact ProbabilityResult.trans jointCanonical
    (ProbabilityResult.symm (ProbabilityResult.trans weightedCanonical
      (ProbabilityResult.weightedDivide_chain_of_le numerator middle base dominated)))

end ProbabilityTerm

/-- A supported kernel has a strictly positive conditioner cylinder.
Empty-action IDC uses this to justify dividing the two observational
joints that Bayes writes for `P(Y | Z)`. -/
noncomputable def Kernel.conditionPositive_of_supportedAt
    (model : FiniteLatentSCM S) (kernel : Kernel S)
    (assignment : S.Assignment)
    (supported : ProbabilityTerm.SupportedAt model (.kernel kernel) assignment) :
    0 < ((kernel.distribution model assignment).probVal
      (kernel.conditionEvent assignment)).num := by
  have hsup : ProbabilityResult.Supported
      (ProbabilityResult.divide
        (some ((kernel.distribution model assignment).probVal
          (kernel.numeratorEvent assignment)))
        (some ((kernel.distribution model assignment).probVal
          (kernel.conditionEvent assignment)))) := by
    simpa [ProbabilityTerm.SupportedAt, ProbabilityTerm.denote, Kernel.denote] using
      (⟨supported.1, supported.2⟩ : ProbabilityResult.Supported
        ((ProbabilityTerm.kernel kernel).denote model assignment))
  by_cases hpos : 0 < ((kernel.distribution model assignment).probVal
      (kernel.conditionEvent assignment)).num
  · exact hpos
  · have hnone :
        ProbabilityResult.divide
          (some ((kernel.distribution model assignment).probVal
            (kernel.numeratorEvent assignment)))
          (some ((kernel.distribution model assignment).probVal
            (kernel.conditionEvent assignment))) =
          none := by
      simp [ProbabilityResult.divide, dif_neg hpos]
    rw [hnone] at hsup
    rcases hsup with ⟨_, impossible⟩
    cases impossible

/-- Empty-action `P(Y)` is the observational marginal `∑_{V \ Y} P(V)`.
Finite additivity of singleton masses on the `Y`-cylinder identifies the
two denotations, so empty-action IDC can transport Bayes support onto the
ID formula. -/
noncomputable def emptyActionKernel_equiv_fullMarginal
    (model : FiniteLatentSCM S) (outcome : NodeSet S)
    (assignment : S.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨outcome, NodeSet.empty, NodeSet.empty⟩)
      (.marginalize (NodeSet.diff NodeSet.full outcome)
        (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩))
      assignment := by
  let leftKernel : Kernel S := ⟨outcome, NodeSet.empty, NodeSet.empty⟩
  let fullKernel : Kernel S := ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩
  let variants :=
    ProbabilityTerm.marginalAssignments S
      (NodeSet.diff NodeSet.full outcome) assignment
  have leftNoAction : leftKernel.hasAction = false := by
    apply (finAny_eq_false_iff _).mpr
    intro _i
    rfl
  have fullNoAction : fullKernel.hasAction = false := by
    apply (finAny_eq_false_iff _).mpr
    intro _i
    rfl
  have leftDist :
      leftKernel.distribution model assignment = model.observationalDist := by
    simp [Kernel.distribution, leftNoAction]
  have fullDist (variant : S.Assignment) :
      fullKernel.distribution model variant = model.observationalDist := by
    simp [Kernel.distribution, fullNoAction]
  have hleft :=
    Kernel.unconditionalDenote model outcome NodeSet.empty assignment
  have hleftObs : ProbabilityResult.Equivalent
      (leftKernel.denote model assignment)
      (some (model.observationalDist.probVal
        (Kernel.agreesOn outcome assignment))) := by
    simpa [leftKernel, leftDist] using hleft
  have hvar : ∀ variant, variant ∈ variants ->
      ProbabilityResult.Equivalent
        (fullKernel.denote model variant)
        (some (model.observationalDist.probVal
          (FiniteProbRecord.singletonEvent variant))) := by
    intro variant _member
    have hfull :=
      Kernel.unconditionalDenote model NodeSet.full NodeSet.empty variant
    have hsing : QProb.Equiv
        ((fullKernel.distribution model variant).probVal
          (Kernel.agreesOn NodeSet.full variant))
        (model.observationalDist.probVal
          (FiniteProbRecord.singletonEvent variant)) := by
      rw [fullDist]
      exact FiniteProbRecord.probVal_congr model.observationalDist _ _
        (fun sample => Kernel.agreesOn_full variant sample)
    exact ProbabilityResult.trans hfull (.value hsing)
  have hmarg : ProbabilityResult.Equivalent
      ((ProbabilityTerm.marginalize
        (NodeSet.diff NodeSet.full outcome)
        (.kernel fullKernel)).denote model assignment)
      (some (QProb.listSum (variants.map (fun variant =>
        model.observationalDist.probVal
          (FiniteProbRecord.singletonEvent variant))))) := by
    have hsum :=
      ProbabilityResult.sum_map_congr_mem variants
        (fun variant => fullKernel.denote model variant)
        (fun variant =>
          some (model.observationalDist.probVal
            (FiniteProbRecord.singletonEvent variant)))
        hvar
    have hsome :
        ProbabilityResult.sum (variants.map (fun variant =>
          some (model.observationalDist.probVal
            (FiniteProbRecord.singletonEvent variant)))) =
          some (QProb.listSum (variants.map (fun variant =>
            model.observationalDist.probVal
              (FiniteProbRecord.singletonEvent variant)))) :=
      ProbabilityResult.sum_some_map variants _
    simpa [ProbabilityTerm.denote, variants] using
      ProbabilityResult.trans hsum (by
        rw [hsome]
        exact ProbabilityResult.refl _)
  have pairwise :
      (variants.map FiniteProbRecord.singletonEvent).Pairwise
        Probability.disjoint :=
    FiniteProbRecord.map_singletonEvent_pairwise_disjoint
      (ProbabilityTerm.marginalAssignments_nodup S _ assignment)
  have union :
      Probability.unionList (variants.map FiniteProbRecord.singletonEvent) =
        Kernel.agreesOn outcome assignment := by
    rw [FiniteProbRecord.unionList_map_singletonEvent]
    funext sample
    have hmem :
        sample ∈ variants ↔
          Kernel.agreesOn outcome assignment sample = true :=
      ProbabilityTerm.mem_marginal_complement_iff_agreesOn
        outcome assignment sample
    by_cases hocc : sample ∈ variants
    · have htrue := hmem.mp hocc
      simp [FiniteProbRecord.membershipEvent, hocc, htrue]
    · have hfalse : Kernel.agreesOn outcome assignment sample = false := by
        cases hagr : Kernel.agreesOn outcome assignment sample
        · rfl
        · exact False.elim (hocc (hmem.mpr hagr))
      simp [FiniteProbRecord.membershipEvent, hocc, hfalse]
  have hadd : QProb.Equiv
      (model.observationalDist.probVal
        (Kernel.agreesOn outcome assignment))
      (QProb.listSum (variants.map (fun variant =>
        model.observationalDist.probVal
          (FiniteProbRecord.singletonEvent variant)))) := by
    have additive :=
      model.observationalDist.finite_additivity_family
        (variants.map FiniteProbRecord.singletonEvent) pairwise
    rw [union] at additive
    simpa [List.map_map, Function.comp_apply] using additive
  exact ProbabilityResult.trans hleftObs
    (ProbabilityResult.trans (.value hadd) (ProbabilityResult.symm hmarg))

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
For `weightedMultiplyCongr`, the factor subtree is a function of positive
source-weight evidence: a defined zero weight never requires that subtree.
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
      | .weightedChain _ _ _ _ _ => Unit
      | .multiplyComm _ _ => Unit
      | .multiplyAssoc _ _ _ => Unit
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
      | @DoCalculusDerivation.weightedMultiplyCongr _ _ _ weight _ _ _ first second =>
          LocalDerivationSupport model assignment first ×
            (ProbabilityResult.PositiveSupportedValue (weight.denote model assignment) ->
              LocalDerivationSupport model assignment second)
      | .divideCongr numerator denominator =>
          LocalDerivationSupport model assignment numerator ×
            LocalDerivationSupport model assignment denominator
      | .eqCongr _ _ inner =>
          LocalDerivationSupport model assignment inner

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
  | weightedChain x y z w _disjoint =>
      exact ProbabilityTerm.weightedChain_soundAt model x y z w assignment
  | multiplyComm first second =>
      exact ProbabilityResult.multiply_comm _ _
  | multiplyAssoc first second third =>
      exact ProbabilityResult.multiply_assoc _ _ _
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
  | weightedMultiplyCongr weightDerivation factorDerivation weightIH factorIH =>
      simpa only [ProbabilityTerm.denote] using
        ProbabilityResult.weightedMultiply_congr_on_positive
          (weightIH supported.2.2.1)
          (fun positive => factorIH (supported.2.2.2 positive))
  | divideCongr numeratorDerivation denominatorDerivation
      numeratorIH denominatorIH =>
      simpa only [ProbabilityTerm.denote] using
        ProbabilityResult.divide_congr
          (numeratorIH supported.2.2.1) (denominatorIH supported.2.2.2)
  | eqCongr hleft hright inner ih =>
      subst hleft
      subst hright
      exact ih supported.2.2

end Causality
end Thesis
