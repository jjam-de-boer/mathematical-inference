import Thesis.Probability.QualitativeUrn
import Thesis.Causality.HardIntervention

namespace Thesis
namespace Causality

open Probability
open Probability.ClaytonWaddington
open Probability.ClaytonWaddington.UrnRatio

/-!
Qualitative comparison of finite interventional experiments.

This is not a derivation of causality from Clayton–Waddington urn axioms.
Those axioms have no graphs and do not produce `do`.  Two distinct facts
are recorded here:

* Transport (2a).  Finite SCM interventional laws have a count presentation
  (`toUrn`).  Supported Pearl identities already hold as `QProb.Equiv` of
  kernel denotations; the urn representation theorem rewrites them as
  `QualitativeUrnScale.eqv` of the corresponding cell-count ratios.  An
  undefined numerical conditional stays undefined on the qualitative side
  and is not completed to zero.
* Clayton analogue (2b).  `QualitativeInterventionScale` compares
  experimental claims (a hard intervention together with an observed event).
  Its fields are order axioms and effectiveness of a forced coordinate.
  They do not mention mutilated graphs \(G_{\overline{X}}\) or Pearl's three
  rules.  Every `ExactModel` together with a qualitative urn scale induces
  such a structure.  The three do-rules are theorems of that induced
  comparison, proved from SCM d-separation, not axiom fields of the
  abstract scale.

The converse representation — every abstract finite scale on the two-node
Boolean signature is realized by some `ExactModel` — is not proved.  The
type of that missing construction is `TwoNodeBooleanRepresentation`.
-/

namespace QualitativeDoCalculus

/-- The interventional law of `I`, presented as a finite urn. -/
def interventionalUrn (model : ExactModel S)
    (intervention : HardIntervention S) : UrnProb S.Assignment :=
  (model.interventionalDist intervention.value).toUrn

/-- Qualitative plausibility of an observed event after a hard intervention. -/
def eventPlaus (Q : QualitativeUrnScale) (model : ExactModel S)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    Q.Plaus :=
  Q.ratioPlaus (ofUrnEvent (interventionalUrn model intervention) event)

/-- Empty `do` is ordinary evaluation: the idle intervention's pushforward
is the observational record. -/
theorem interventionalDist_empty (model : ExactModel S) :
    model.interventionalDist (HardIntervention.empty S).value =
      model.observationalDist :=
  rfl

/-- Kernel evaluation uses the same pushforward as the hard intervention
read from the reference assignment, including the empty-action branch. -/
theorem Kernel.distribution_eq_interventional
    (model : ExactModel S) (kernel : Kernel S) (reference : S.Assignment) :
    kernel.distribution model reference =
      model.interventionalDist (kernel.intervention reference) := by
  unfold Kernel.distribution
  split
  · rfl
  · next hact =>
      have hempty :
          kernel.intervention reference = FiniteLatentSCM.noIntervention S := by
        funext node
        have inactive :=
          (finAny_eq_false_iff kernel.action).mp (by
            simpa [Kernel.hasAction] using hact) node
        simp [Kernel.intervention, inactive, FiniteLatentSCM.noIntervention]
      rw [hempty]
      rfl

/-- Urn presentation of the law under a kernel's intervention. -/
def kernelUrn (model : ExactModel S) (kernel : Kernel S)
    (assignment : S.Assignment) : UrnProb S.Assignment :=
  (kernel.distribution model assignment).toUrn

theorem Kernel.numeratorEvent_implies_conditionEvent
    (kernel : Kernel S) (reference sample : S.Assignment) :
    kernel.numeratorEvent reference sample = true →
      kernel.conditionEvent reference sample = true := by
  intro selected
  simp only [Kernel.numeratorEvent, Kernel.conditionEvent] at selected ⊢
  exact (Bool.and_eq_true_iff.mp selected).2

/-- Count-ratio of a supported kernel `P(outcome | do(action), condition)`. -/
def kernelRatio (model : ExactModel S) (kernel : Kernel S)
    (assignment : S.Assignment)
    (hpos : 0 < (kernelUrn model kernel assignment).probNum
      (kernel.conditionEvent assignment)) : UrnRatio where
  N := (kernelUrn model kernel assignment).probNum
    (kernel.conditionEvent assignment)
  k := (kernelUrn model kernel assignment).probNum
    (kernel.numeratorEvent assignment)
  pos := hpos
  le :=
    count_mono (Kernel.numeratorEvent_implies_conditionEvent kernel assignment)

/-- A kernel denotation is missing exactly when the displayed conditioner
has numerator zero.  This is the existing `0/0` discipline: the conditional
is undefined, not a rational zero. -/
theorem kernelDenote_eq_none_iff (model : ExactModel S) (kernel : Kernel S)
    (assignment : S.Assignment) :
    kernel.denote model assignment = none ↔
      ¬ (0 < ((kernel.distribution model assignment).probVal
        (kernel.conditionEvent assignment)).num) := by
  simp [Kernel.denote, ProbabilityResult.divide]

theorem kernelUrn_condition_pos_iff (model : ExactModel S)
    (kernel : Kernel S) (assignment : S.Assignment) :
    0 < (kernelUrn model kernel assignment).probNum
        (kernel.conditionEvent assignment) ↔
      0 < ((kernel.distribution model assignment).probVal
        (kernel.conditionEvent assignment)).num := by
  have agrees :=
    (kernel.distribution model assignment).toUrn_agrees
      (kernel.conditionEvent assignment)
  simpa [kernelUrn, UrnProb.probVal] using
    (QProb.equiv_num_pos_iff agrees).symm

/-- The displayed kernel ratio is the cell-count presentation of the
supported numerical conditional. -/
def kernelDenote_equiv_ratio (model : ExactModel S) (kernel : Kernel S)
    (assignment : S.Assignment)
    (hpos : 0 < (kernelUrn model kernel assignment).probNum
      (kernel.conditionEvent assignment)) :
    ProbabilityResult.Equivalent
      (kernel.denote model assignment)
      (some (kernelRatio model kernel assignment hpos).toQProb) := by
  let dist := kernel.distribution model assignment
  let numE := kernel.numeratorEvent assignment
  let condE := kernel.conditionEvent assignment
  let recNum := dist.probVal numE
  let recDen := dist.probVal condE
  have agreesNum := dist.toUrn_agrees numE
  have agreesDen := dist.toUrn_agrees condE
  have hposRec : 0 < recDen.num :=
    (kernelUrn_condition_pos_iff model kernel assignment).mp hpos
  have hdiv :
      ProbabilityResult.divide (some recNum) (some recDen) =
        some (QProb.div recNum recDen hposRec) := by
    simp [ProbabilityResult.divide, hposRec]
  rw [show kernel.denote model assignment =
      ProbabilityResult.divide (some recNum) (some recDen) from rfl, hdiv]
  refine .value (QProb.equiv_trans
    (QProb.div_congr agreesNum agreesDen hposRec hpos) ?_)
  simp [QProb.Equiv, QProb.div, UrnRatio.toQProb, kernelRatio, kernelUrn,
    UrnProb.probVal, dist, numE, condE]
  ac_rfl

/-- Qualitative plausibility of a kernel.  `none` is failed support, never
a completed `0/0`. -/
def kernelPlaus (Q : QualitativeUrnScale) (model : ExactModel S)
    (kernel : Kernel S) (assignment : S.Assignment) : Option Q.Plaus :=
  if hpos : 0 < (kernelUrn model kernel assignment).probNum
      (kernel.conditionEvent assignment) then
    some (Q.ratioPlaus (kernelRatio model kernel assignment hpos))
  else
    none

theorem kernelPlaus_eq_none_iff_denote_eq_none (Q : QualitativeUrnScale)
    (model : ExactModel S) (kernel : Kernel S) (assignment : S.Assignment) :
    kernelPlaus Q model kernel assignment = none ↔
      kernel.denote model assignment = none := by
  simp [kernelPlaus, kernelDenote_eq_none_iff,
    kernelUrn_condition_pos_iff]

/-- Supported numerical evaluation supplies a qualitative ratio. -/
theorem kernelPlaus_isSome_of_supported (Q : QualitativeUrnScale)
    (model : ExactModel S) (kernel : Kernel S) (assignment : S.Assignment)
    (supported : ProbabilityTerm.SupportedAt model (.kernel kernel)
      assignment) :
    ∃ p, kernelPlaus Q model kernel assignment = some p := by
  by_cases hpos : 0 < (kernelUrn model kernel assignment).probNum
      (kernel.conditionEvent assignment)
  · exact ⟨Q.ratioPlaus (kernelRatio model kernel assignment hpos), by
      simp [kernelPlaus, hpos]⟩
  · have hnone : kernelPlaus Q model kernel assignment = none := by
      simp [kernelPlaus, hpos]
    have hdenote : kernel.denote model assignment = none :=
      (kernelPlaus_eq_none_iff_denote_eq_none Q model kernel assignment).mp
        hnone
    rcases supported with ⟨_, heq⟩
    simp [ProbabilityTerm.denote, hdenote] at heq
    cases heq

/-- Comparison of two kernel plausibilities.  Both-undefined is recorded as
unsupported agreement, matching `ProbabilityResult.Equivalent`, and is not
an equivalence to zero. -/
inductive KernelPlausEqv (Q : QualitativeUrnScale) :
    Option Q.Plaus → Option Q.Plaus → Prop
  | unsupported : KernelPlausEqv Q none none
  | defined {a b} : Q.eqv a b → KernelPlausEqv Q (some a) (some b)

theorem KernelPlausEqv.not_none_some {Q : QualitativeUrnScale}
    {p : Q.Plaus} : KernelPlausEqv Q none (some p) → False := by
  intro h
  cases h

theorem KernelPlausEqv.not_some_none {Q : QualitativeUrnScale}
    {p : Q.Plaus} : KernelPlausEqv Q (some p) none → False := by
  intro h
  cases h

/-- An undefined kernel is not silently the zero ratio `0/1`. -/
theorem kernelPlaus_undefined_not_zero_ratio (Q : QualitativeUrnScale)
    (model : ExactModel S) (kernel : Kernel S) (assignment : S.Assignment)
    (hnone : kernelPlaus Q model kernel assignment = none) :
    ¬ KernelPlausEqv Q (kernelPlaus Q model kernel assignment)
        (some (Q.ratioPlaus ⟨1, 0, Nat.succ_pos 0, Nat.zero_le 1⟩)) := by
  intro heqv
  rw [hnone] at heqv
  exact KernelPlausEqv.not_none_some heqv

/-- Transport: supported numerical kernel equality is qualitative equality
of the cell-count ratios.  The three Pearl rules therefore need not mention
rationals once they hold as `QProb.Equiv`. -/
theorem kernelPlausEqv_of_numerical (Q : QualitativeUrnScale)
    (model : ExactModel S) (left right : Kernel S)
    (assignment : S.Assignment)
    (leftSupported : ProbabilityTerm.SupportedAt model (.kernel left)
      assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model (.kernel right)
      assignment)
    (numerical : ProbabilityTerm.EquivalentAt model (.kernel left)
      (.kernel right) assignment) :
    KernelPlausEqv Q
      (kernelPlaus Q model left assignment)
      (kernelPlaus Q model right assignment) := by
  have hposL : 0 < (kernelUrn model left assignment).probNum
      (left.conditionEvent assignment) := by
    by_cases hpos : 0 < (kernelUrn model left assignment).probNum
        (left.conditionEvent assignment)
    · exact hpos
    · have hnone : kernelPlaus Q model left assignment = none := by
        simp [kernelPlaus, hpos]
      have hdenote : left.denote model assignment = none :=
        (kernelPlaus_eq_none_iff_denote_eq_none Q model left assignment).mp
          hnone
      rcases leftSupported with ⟨_, heq⟩
      simp [ProbabilityTerm.denote, hdenote] at heq
      cases heq
  have hposR : 0 < (kernelUrn model right assignment).probNum
      (right.conditionEvent assignment) := by
    by_cases hpos : 0 < (kernelUrn model right assignment).probNum
        (right.conditionEvent assignment)
    · exact hpos
    · have hnone : kernelPlaus Q model right assignment = none := by
        simp [kernelPlaus, hpos]
      have hdenote : right.denote model assignment = none :=
        (kernelPlaus_eq_none_iff_denote_eq_none Q model right assignment).mp
          hnone
      rcases rightSupported with ⟨_, heq⟩
      simp [ProbabilityTerm.denote, hdenote] at heq
      cases heq
  have hl :
      kernelPlaus Q model left assignment =
        some (Q.ratioPlaus (kernelRatio model left assignment hposL)) := by
    simp [kernelPlaus, hposL]
  have hr :
      kernelPlaus Q model right assignment =
        some (Q.ratioPlaus (kernelRatio model right assignment hposR)) := by
    simp [kernelPlaus, hposR]
  have hleft := kernelDenote_equiv_ratio model left assignment hposL
  have hright := kernelDenote_equiv_ratio model right assignment hposR
  have hratios : ProbabilityResult.Equivalent
      (some (kernelRatio model left assignment hposL).toQProb)
      (some (kernelRatio model right assignment hposR).toQProb) :=
    ProbabilityResult.trans (ProbabilityResult.symm hleft)
      (ProbabilityResult.trans numerical hright)
  have hsame : sameRatio
      (kernelRatio model left assignment hposL)
      (kernelRatio model right assignment hposR) := by
    cases hratios with
    | value hv => exact hv
  rw [hl, hr]
  exact .defined (Q.sameRatio_implies_eqv hsame)

/-- Converse transport along the finite urn representation. -/
def numerical_of_kernelPlausEqv (Q : QualitativeUrnScale)
    (model : ExactModel S) (left right : Kernel S)
    (assignment : S.Assignment)
    (heqv : KernelPlausEqv Q
      (kernelPlaus Q model left assignment)
      (kernelPlaus Q model right assignment)) :
    ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
      assignment := by
  by_cases hposL : 0 < (kernelUrn model left assignment).probNum
      (left.conditionEvent assignment)
  · by_cases hposR : 0 < (kernelUrn model right assignment).probNum
        (right.conditionEvent assignment)
    · have hl :
          kernelPlaus Q model left assignment =
            some (Q.ratioPlaus (kernelRatio model left assignment hposL)) := by
        simp [kernelPlaus, hposL]
      have hr :
          kernelPlaus Q model right assignment =
            some (Q.ratioPlaus (kernelRatio model right assignment hposR)) := by
        simp [kernelPlaus, hposR]
      have hQ : Q.eqv
          (Q.ratioPlaus (kernelRatio model left assignment hposL))
          (Q.ratioPlaus (kernelRatio model right assignment hposR)) := by
        have heqv' : KernelPlausEqv Q
            (some (Q.ratioPlaus (kernelRatio model left assignment hposL)))
            (some (Q.ratioPlaus (kernelRatio model right assignment hposR))) := by
          simpa [hl, hr] using heqv
        cases heqv' with
        | defined h => exact h
      have hsame : sameRatio
          (kernelRatio model left assignment hposL)
          (kernelRatio model right assignment hposR) :=
        Q.eqv_implies_sameRatio hQ
      have hleft := kernelDenote_equiv_ratio model left assignment hposL
      have hright := kernelDenote_equiv_ratio model right assignment hposR
      exact ProbabilityResult.trans hleft
        (ProbabilityResult.trans (.value (sameRatio_toQProb hsame))
          (ProbabilityResult.symm hright))
    · have hl :
          kernelPlaus Q model left assignment =
            some (Q.ratioPlaus (kernelRatio model left assignment hposL)) := by
        simp [kernelPlaus, hposL]
      have hr : kernelPlaus Q model right assignment = none := by
        simp [kernelPlaus, hposR]
      exact (KernelPlausEqv.not_some_none (by simpa [hl, hr] using heqv)).elim
  · have hl : kernelPlaus Q model left assignment = none := by
      simp [kernelPlaus, hposL]
    by_cases hposR : 0 < (kernelUrn model right assignment).probNum
        (right.conditionEvent assignment)
    · have hr :
          kernelPlaus Q model right assignment =
            some (Q.ratioPlaus (kernelRatio model right assignment hposR)) := by
        simp [kernelPlaus, hposR]
      exact (KernelPlausEqv.not_none_some (by simpa [hl, hr] using heqv)).elim
    · have hr : kernelPlaus Q model right assignment = none := by
        simp [kernelPlaus, hposR]
      have hLden : left.denote model assignment = none :=
        (kernelPlaus_eq_none_iff_denote_eq_none Q model left assignment).mp hl
      have hRden : right.denote model assignment = none :=
        (kernelPlaus_eq_none_iff_denote_eq_none Q model right assignment).mp hr
      simpa [ProbabilityTerm.EquivalentAt, ProbabilityTerm.denote, hLden,
        hRden] using ProbabilityResult.Equivalent.unsupported

/-- Qualitative conditional independence of node families under a common
intervention, stated without graphs or mutilations.  Failed support on
either side is not treated as independence. -/
def qualitativelyIndependent (Q : QualitativeUrnScale)
    (model : ExactModel S)
    (action y z w : NodeSet S) : Prop :=
  ∀ assignment : S.Assignment,
    ∀ a b : Q.Plaus,
      kernelPlaus Q model ⟨y, action, NodeSet.union z w⟩ assignment =
          some a →
        kernelPlaus Q model ⟨y, action, w⟩ assignment = some b →
          Q.eqv a b

/-! ## Number-free interventional comparison structure (2b) -/

/--
Comparisons of experimental claims.  An experimental claim is a hard
intervention together with an observed event.  Observation is the empty
intervention; it is not a second primitive.

The three Pearl rules and d-separation in mutilated graphs are not fields
of this structure.  They appear later as theorems of the scale induced by
a finite SCM.
-/
structure QualitativeInterventionScale.{u} (S : ObservedSignature) where
  Plaus : Type u
  plaus : HardIntervention S → Event S.Assignment → Plaus
  eqv : Plaus → Plaus → Prop
  lt : Plaus → Plaus → Prop
  eqv_refl : ∀ a, eqv a a
  eqv_symm : ∀ {a b}, eqv a b → eqv b a
  eqv_trans : ∀ {a b c}, eqv a b → eqv b c → eqv a c
  lt_irrefl : ∀ a, lt a a → False
  lt_trans : ∀ {a b c}, lt a b → lt b c → lt a c
  lt_respects_eqv :
    ∀ {a b c d}, eqv a c → eqv b d → lt a b → lt c d
  /-- Forcing a coordinate makes the corresponding cylinder as plausible as
  the certain event.  This is structural effectiveness, not a do-calculus
  rewrite and not a statement about \(G_{\overline{X}}\). -/
  effectiveness :
    ∀ (I : HardIntervention S) (i : Fin S.count) (value : S.Value i),
      I.value i = some value →
      eqv (plaus I (fun a => decide (a i = value)))
        (plaus I topEvent)

namespace QualitativeInterventionScale

/-- Observation is the idle experiment. -/
def observationalPlaus (Q : QualitativeInterventionScale S)
    (event : Event S.Assignment) : Q.Plaus :=
  Q.plaus (HardIntervention.empty S) event

end QualitativeInterventionScale

theorem interventionalValue_effectiveness (model : ExactModel S)
    (I : HardIntervention S) (i : Fin S.count) (value : S.Value i)
    (hI : I.value i = some value) :
    QProb.Equiv
      (model.interventionalValue I.value (fun a => decide (a i = value)))
      QProb.one := by
  have hmap :=
    model.interventionalValue_eq I.value (fun a => decide (a i = value))
  refine QProb.equiv_trans hmap ?_
  have hpoint :
      (fun u => decide (model.evalUnder I.value u i = value)) =
        topEvent := by
    funext u
    simp [topEvent, model.evalUnder_effectiveness I.value u i value hI]
  rw [hpoint]
  exact model.prior.normalization

/-- Every finite SCM, read through a qualitative urn scale, induces an
interventional comparison structure.  Clayton/urn axioms supply the
event-level order; they do not supply `do`. -/
def induced (model : ExactModel S) (Q : QualitativeUrnScale) :
    QualitativeInterventionScale S where
  Plaus := Q.Plaus
  plaus := eventPlaus Q model
  eqv := Q.eqv
  lt := Q.lt
  eqv_refl := Q.eqv_refl
  eqv_symm := Q.eqv_symm
  eqv_trans := Q.eqv_trans
  lt_irrefl := Q.lt_irrefl
  lt_trans := Q.lt_trans
  lt_respects_eqv := Q.lt_respects_eqv
  effectiveness := by
    intro I i value hI
    let μ := interventionalUrn model I
    let forced : Event S.Assignment := fun a => decide (a i = value)
    have agreesForced :=
      (model.interventionalDist I.value).toUrn_agrees forced
    have agreesTop :=
      (model.interventionalDist I.value).toUrn_agrees topEvent
    have hforced : QProb.Equiv (μ.probVal forced) QProb.one :=
      QProb.equiv_trans (QProb.equiv_symm agreesForced)
        (interventionalValue_effectiveness model I i value hI)
    have htop : QProb.Equiv (μ.probVal topEvent) QProb.one :=
      QProb.equiv_trans (QProb.equiv_symm agreesTop)
        (model.interventionalDist I.value).normalization
    have hsame : sameRatio (ofUrnEvent μ forced) (ofUrnEvent μ topEvent) := by
      have hk : μ.probNum forced = μ.n := by
        have : QProb.Equiv (μ.probVal forced) QProb.one := hforced
        simpa [QProb.Equiv, UrnProb.probVal, QProb.one] using this
      have ht : μ.probNum topEvent = μ.n := μ.probNum_top
      simp [sameRatio, ofUrnEvent, hk, ht]
    exact Q.sameRatio_implies_eqv hsame

theorem induced_observational (model : ExactModel S)
    (Q : QualitativeUrnScale) (event : Event S.Assignment) :
    (induced model Q).observationalPlaus event =
      eventPlaus Q model (HardIntervention.empty S) event :=
  rfl

/-- Soundness of the analogue: the inducing model realizes the induced
scale on every experimental claim. -/
theorem induced_realizes (model : ExactModel S) (Q : QualitativeUrnScale)
    (I : HardIntervention S) (event : Event S.Assignment) :
    (induced model Q).eqv
      ((induced model Q).plaus I event)
      (eventPlaus Q model I event) :=
  Q.eqv_refl _

/-! ## Tiny two-node Boolean signature for representation -/

/-- Two Boolean observed nodes, no directed edge.  Used only as the carrier
of the representation question below; it is not an identification engine. -/
def twoBoolSignature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  value_nodup := by
    intro _
    simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by
    intro _ _ h
    simp at h

def twoBoolFirst : Fin twoBoolSignature.count := ⟨0, by decide⟩
def twoBoolSecond : Fin twoBoolSignature.count := ⟨1, by decide⟩

def twoBoolFairBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def twoBoolLatent : LatentExtension twoBoolSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun l i => decide (l.val = i.val)

/-- Independent private fair bits.  Markovian, so the projected graph has
no bidirected edge. -/
def twoBoolIndependentModel : ExactModel twoBoolSignature where
  latent := twoBoolLatent
  factor := fun _ => twoBoolFairBit
  prior := FiniteProduct.record 2 (fun _ => Bool) (fun _ => twoBoolFairBit)
  product_law :=
    FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool)
      (fun _ => twoBoolFairBit)
  mechanism := fun child _ latents =>
    latents ⟨child.val, child.isLt⟩ (by
      simp [twoBoolLatent])

theorem twoBoolIndependentModel_markovian :
    twoBoolIndependentModel.IsMarkovian := by
  intro l i j hi hj
  have hi' : l.val = i.val := of_decide_eq_true hi
  have hj' : l.val = j.val := of_decide_eq_true hj
  exact Fin.ext (hi'.symm.trans hj')

/-- Explicit idle and singleton/joint interventions on the two-node
Boolean signature. -/
inductive ListedTwoNodeIntervention where
  | idle
  | doFirst (value : Bool)
  | doSecond (value : Bool)
  | doBoth (first second : Bool)

def ListedTwoNodeIntervention.toHard :
    ListedTwoNodeIntervention → HardIntervention twoBoolSignature
  | idle => HardIntervention.empty twoBoolSignature
  | doFirst value =>
      (HardIntervention.empty twoBoolSignature).set twoBoolFirst value
  | doSecond value =>
      (HardIntervention.empty twoBoolSignature).set twoBoolSecond value
  | doBoth first second =>
      ((HardIntervention.empty twoBoolSignature).set twoBoolFirst first).set
        twoBoolSecond second

/-- Agreement of listed-experiment comparisons with those induced by a
finite SCM.  The two scales may use different plausibility types; only the
comparison relation on the listed family is matched. -/
def Realizes (scale : QualitativeInterventionScale twoBoolSignature)
    (model : ExactModel twoBoolSignature) (Q : QualitativeUrnScale) :
    Prop :=
  ∀ (I J : ListedTwoNodeIntervention)
    (E F : Event twoBoolSignature.Assignment),
    scale.eqv (scale.plaus I.toHard E) (scale.plaus J.toHard F) ↔
      (induced model Q).eqv
        ((induced model Q).plaus I.toHard E)
        ((induced model Q).plaus J.toHard F)

/-- Soundness of representation on the tiny signature: a scale induced by
an `ExactModel` is realized by that model. -/
theorem induced_realizes_listed (model : ExactModel twoBoolSignature)
    (Q : QualitativeUrnScale) :
    Realizes (induced model Q) model Q := by
  intro _ _ _ _
  rfl

theorem qualitativeInterventionScale_nonempty :
    Nonempty (QualitativeInterventionScale.{0} twoBoolSignature) :=
  ⟨induced twoBoolIndependentModel rationalScale⟩

/--
Converse representation on the two-node Boolean signature.

Every finite SCM induces a qualitative intervention scale.  The converse —
an arbitrary `QualitativeInterventionScale` on this signature, compared on
the listed interventions, is realized by some `ExactModel` — is not proved.
The axioms do not include Pearl's rules or mutilated-graph d-separation, so
they do not force SCM mechanism constraints.  This is the type of the
missing construction, not a theorem.
-/
def TwoNodeBooleanRepresentation : Prop :=
  ∀ scale : QualitativeInterventionScale.{0} twoBoolSignature,
    ∃ model : ExactModel twoBoolSignature,
      ∃ Q : QualitativeUrnScale.{0}, Realizes scale model Q

end QualitativeDoCalculus

end Causality
end Thesis
