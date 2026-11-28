import Thesis.CausalTransport.CatalogueSampling
import Thesis.CausalTransport.CatalogueSymmetry
import Thesis.Causality.ModelSymmetry
import Thesis.Probability.Reindexing

/-!
# Relabelling complete IID cohorts

The observed alphabet is explicitly enumerated. A histogram is read at its
actual assignment labels, and an invertible relabelling pulls each count
back from the unique old cell. Thus relabelling includes the zero cells
and preserves the number of trials, independently of any model's law.
-/

namespace Thesis.Causality.CatalogueInference

open Probability Probability.Distros FiniteSymmetry FiniteProduct

variable {S : ObservedSignature.{0}} {G : Group}

namespace CountSample

private def labels (S : ObservedSignature.{0}) : FiniteWitness S.Assignment :=
  FiniteWitness.ofList S.assignmentEnumeration S.assignmentEnumeration_complete
    S.assignmentEnumeration_nodup

/-- Read the bin of a named assignment. Completeness and uniqueness of
the signature's enumeration justify the lookup. -/
def countAt (sample : CountSample S) (state : S.Assignment) : Nat :=
  sample.bins.get ⟨((labels S).encode state).val,
    sample.dimension.symm ▸ ((labels S).encode state).isLt⟩

def ofCounts (counts : S.Assignment → Nat) : CountSample S where
  bins := List.ofFn (fun index => counts ((labels S).decode index))
  dimension := List.length_ofFn

theorem countAt_ofCounts (counts : S.Assignment → Nat) (state : S.Assignment) :
    (ofCounts counts).countAt state = counts state := by
  unfold countAt ofCounts
  rw [List.get_eq_getElem, List.getElem_ofFn]
  exact congrArg counts ((labels S).decode_encode state)

/-- Named cell equality implies literal equality of complete histograms. -/
theorem ext_of_countAt (left right : CountSample S)
    (same : ∀ state, left.countAt state = right.countAt state) : left = right := by
  cases left with
  | mk l dl =>
    cases right with
    | mk r dr =>
      suffices l = r from by cases this; rfl
      apply List.ext_getElem (dl.trans dr.symm)
      intro index inL inR
      let slot : Fin (labels S).card := ⟨index, by
        change index < S.assignmentEnumeration.length
        exact dl ▸ inL⟩
      have agrees := same ((labels S).decode slot)
      unfold countAt at agrees
      simpa only [(labels S).encode_decode, List.get_eq_getElem] using agrees

private theorem ofCounts_countAt (sample : CountSample S) :
    ofCounts sample.countAt = sample :=
  ext_of_countAt _ _ (countAt_ofCounts _)

def rename (action : Action G S.Assignment) (g : G.Carrier) (sample : CountSample S) :
    CountSample S :=
  ofCounts (fun state => sample.countAt (action.act (G.inv g) state))

theorem countAt_rename (action : Action G S.Assignment) (g : G.Carrier)
    (sample : CountSample S) (state : S.Assignment) :
    (sample.rename action g).countAt state = sample.countAt (action.act (G.inv g) state) :=
  countAt_ofCounts _ _

/-- Histogram relabelling is an actual action, including cells of count zero. -/
def action (outcomes : Action G S.Assignment) : Action G (CountSample S) where
  act g sample := sample.rename outcomes g
  one_act sample := by
    apply ext_of_countAt
    intro state
    rw [countAt_rename]
    exact congrArg sample.countAt (by simpa only [outcomes.one_act] using outcomes.inv_act G.one state)
  mul_act g h sample := by
    apply ext_of_countAt
    intro state
    simp only [countAt_rename]
    apply congrArg sample.countAt
    apply outcomes.injective (g := G.mul g h)
    rw [outcomes.act_inv, outcomes.mul_act, outcomes.act_inv, outcomes.act_inv]

/-- Construct the literal registered histogram of a sequence of draws. -/
def ofWord (word : List S.Assignment) : CountSample S :=
  ⟨labelledHistogram S.assignmentEnumeration word, labelledHistogram_length _ _⟩

theorem countAt_ofWord (word : List S.Assignment) (state : S.Assignment) :
    (ofWord word).countAt state = word.count state := by
  unfold countAt ofWord labelledHistogram
  rw [List.get_eq_getElem, List.getElem_map]
  exact congrArg (fun value => word.count value) ((labels S).decode_encode state)

/-- Counting after a relabelling of the word is literal relabelling of
the count sample. The proof uses both inverse laws at each named cell. -/
theorem ofWord_map (outcomes : Action G S.Assignment) (g : G.Carrier)
    (word : List S.Assignment) :
    ofWord (word.map (outcomes.act g)) = (ofWord word).rename outcomes g := by
  apply ext_of_countAt
  intro state
  simp only [countAt_rename, countAt_ofWord]
  rw [List.count_eq_countP, List.countP_map, List.count_eq_countP]
  apply List.countP_congr
  intro other _
  simp only [Function.comp_apply, beq_iff_eq]
  constructor
  · intro same
    rw [← same, outcomes.inv_act]
  · intro same
    rw [same, outcomes.act_inv]

/-- The sample size is unchanged by indexing its bins in a different order. -/
theorem rename_sum (outcomes : Action G S.Assignment) (g : G.Carrier)
    (sample : CountSample S) : (sample.rename outcomes g).bins.sum = sample.bins.sum := by
  let w := labels S
  let forward := fun i : Fin w.card => w.encode (outcomes.act g (w.decode i))
  let backward := fun i : Fin w.card => w.encode (outcomes.act (G.inv g) (w.decode i))
  have leftInv (i : Fin w.card) : forward (backward i) = i := by
    simp only [forward, backward, w.decode_encode, outcomes.act_inv, w.encode_decode]
  have rightInv (i : Fin w.card) : backward (forward i) = i := by
    simp only [forward, backward, w.decode_encode, outcomes.inv_act, w.encode_decode]
  have perm := (AdditiveCarrier.finRange_map_bijective_perm backward forward leftInv rightInv).map
    (fun i => sample.countAt (w.decode i))
  have sumPerm {left right : List Nat} (permutation : left.Perm right) : left.sum = right.sum := by
    induction permutation with
    | nil => rfl
    | cons _ _ ih => simp only [List.sum_cons, ih]
    | swap _ _ _ => simp only [List.sum_cons]; omega
    | trans _ _ ih ih' => exact ih.trans ih'
  have indexed : (List.ofFn (fun i : Fin w.card =>
      sample.countAt (outcomes.act (G.inv g) (w.decode i)))).sum =
      (List.ofFn (fun i : Fin w.card => sample.countAt (w.decode i))).sum := by
    simpa only [List.map_map, Function.comp_def, backward, w.decode_encode, List.finRange,
      List.map_ofFn] using sumPerm perm
  exact indexed.trans (congrArg (fun s : CountSample S => s.bins.sum) (ofCounts_countAt sample))

theorem eq_of_bins_eq {left right : CountSample S} (same : left.bins = right.bins) :
    left = right := by
  cases left
  cases right
  cases same
  rfl

end CountSample

namespace ExperimentTag

/-- A renaming retains the observation tag and acts on explicit settings. -/
def actionOf (settings : Action G (HardIntervention S)) : Action G (ExperimentTag S) where
  act g tag := match tag with
    | .observational => .observational
    | .intervene a => .intervene (settings.act g a)
  one_act tag := by cases tag <;> simp [settings.one_act]
  mul_act g h tag := by cases tag <;> simp [settings.mul_act]

theorem setting_actionOf (settings : Action G (HardIntervention S))
    (fixed : ∀ g, settings.act g (.empty S) = .empty S)
    (g : G.Carrier) (tag : ExperimentTag S) :
    ((actionOf settings).act g tag).action = settings.act g tag.action := by
  cases tag with
  | observational => exact (fixed g).symm
  | intervene _ => rfl

end ExperimentTag

namespace CountExperiment

def actionOf (outcomes : Action G S.Assignment) (settings : Action G (HardIntervention S)) :
    Action G (CountExperiment S) where
  act g cohort := ⟨(ExperimentTag.actionOf settings).act g cohort.tag,
    (CountSample.action outcomes).act g cohort.sample⟩
  one_act cohort := by
    cases cohort
    simp only [Action.one_act]
  mul_act g h cohort := by
    simp only [Action.mul_act]

end CountExperiment

/-- In a coherent family the empty intervention is fixed. The structural
transport of any actual hypothesis already supplies this fact. -/
theorem family_fixes_observation {H : Type} (family : ModelFamilyAction G H S) (h : H)
    (g : G.Carrier) : family.experiments.act g (.empty S) = .empty S := by
  rw [← family.experiments_agree g h]
  let transport := family.transport g h
  apply HardIntervention.extensional
  intro node
  rw [← transport.nodes.forward_backward node]
  exact transport.forced (.empty S) _

/-- Actual IID histogram likelihoods are equivariant as rational values.
This compares the same count event after a coherent outcome and setting
relabelling. No separate hypothesis of likelihood equivariance is supplied. -/
theorem iidCountLikelihood_equivariant {H : Type} (family : ModelFamilyAction G H S)
    (g : G.Carrier) (h : H) (cohort : CountExperiment S) :
    QProb.Equiv
      (iidModelCountLikelihood (family.models (family.hypotheses.act g h))
        ((CountExperiment.actionOf family.outcomes family.experiments).act g cohort))
      (iidModelCountLikelihood (family.models h) cohort) := by
  let μ : Distro S.Assignment := ⟨predictedTable (family.models h) cohort.tag⟩
  let renamed := (CountExperiment.actionOf family.outcomes family.experiments).act g cohort
  let ν : Distro S.Assignment := ⟨predictedTable
    (family.models (family.hypotheses.act g h)) renamed.tag⟩
  have law : ν.SameLaw (μ.map (family.outcomes.act g)) := by
    intro event
    apply QProb.equiv_trans ?_ (QProb.equiv_symm (μ.map_probVal _ _))
    change QProb.Equiv ((family.models (family.hypotheses.act g h)).interventionalValue
      ((ExperimentTag.actionOf family.experiments).act g cohort.tag).action.value event)
      ((family.models h).interventionalValue cohort.tag.action.value
        (fun state => event (family.outcomes.act g state)))
    rw [ExperimentTag.setting_actionOf family.experiments (family_fixes_observation family h)]
    exact family.interventionalValue g h cohort.tag.action event
  have size : renamed.sample.bins.sum = cohort.sample.bins.sum :=
    CountSample.rename_sum family.outcomes g cohort.sample
  let trials := cohort.sample.bins.sum
  have histogram (word : List S.Assignment) :
      FiniteProbRecord.singletonEvent renamed.sample.bins
        (labelledHistogram S.assignmentEnumeration (word.map (family.outcomes.act g))) =
      FiniteProbRecord.singletonEvent cohort.sample.bins
        (labelledHistogram S.assignmentEnumeration word) := by
    apply Bool.eq_iff_iff.mpr
    unfold FiniteProbRecord.singletonEvent
    simp only [decide_eq_true_eq]
    change (CountSample.ofWord (word.map (family.outcomes.act g))).bins =
        (cohort.sample.rename family.outcomes g).bins ↔
      (CountSample.ofWord word).bins = cohort.sample.bins
    rw [CountSample.ofWord_map]
    constructor
    · intro same
      have samples := CountSample.eq_of_bins_eq same
      have cancelled := (CountSample.action family.outcomes).injective g samples
      exact congrArg CountSample.bins cancelled
    · intro same
      rw [CountSample.eq_of_bins_eq same]
  change QProb.Equiv ((iidCountDistro ν S.assignmentEnumeration renamed.sample.bins.sum).pmf
      renamed.sample.bins) ((iidCountDistro μ S.assignmentEnumeration trials).pmf cohort.sample.bins)
  rw [size]
  refine QProb.equiv_trans (iidCountDistro_sampling _ _ _ _) ?_
  refine QProb.equiv_trans ((iidWordDistro_sameLaw law trials) _) ?_
  refine QProb.equiv_trans (iidWordDistro_map μ _ trials _) ?_
  refine QProb.equiv_trans (Distro.map_probVal _ _ _) ?_
  exact QProb.equiv_trans ((iidWordDistro μ trials).record.probVal_congr _ _ histogram)
    (QProb.equiv_symm (iidCountDistro_sampling _ _ _ _))

theorem iidExperimentLikelihood_equivariant {H : Type} (family : ModelFamilyAction G H S)
    (g : G.Carrier) (h : H) (cohorts : List (CountExperiment S)) :
    QProb.Equiv
      (iidExperimentLikelihood (family.models (family.hypotheses.act g h))
        (cohorts.map ((CountExperiment.actionOf family.outcomes family.experiments).act g)))
      (iidExperimentLikelihood (family.models h) cohorts) := by
  induction cohorts with
  | nil => exact QProb.equiv_refl _
  | cons cohort rest ih =>
    exact QProb.mul_congr (iidCountLikelihood_equivariant family g h cohort) ih

/-- Equality of partial posterior laws respects absence of supported
evidence, and ignores the presentation of a supported rational law. -/
def SamePosterior {A : Type} : Option (Distro A) → Option (Distro A) → Prop
  | none, none => True
  | some left, some right => left.SameLaw right
  | _, _ => False

theorem SamePosterior.trans {A : Type} {left middle right : Option (Distro A)}
    (first : SamePosterior left middle) (second : SamePosterior middle right) :
    SamePosterior left right := by
  cases left <;> cases middle <;> cases right <;>
    simp only [SamePosterior] at first second ⊢ <;>
    first | trivial | contradiction | exact fun event => QProb.equiv_trans (first event) (second event)

private theorem integral_scale_eq (prior : Distro (Fin n)) (left right : Fin n → Nat)
    (a b : Nat) (same : ∀ i, left i * a = right i * b) :
    natIntegral prior.record.atoms left * a = natIntegral prior.record.atoms right * b := by
  rw [← natIntegral_mul, ← natIntegral_mul]
  exact natIntegral_congr _ _ _ same

/-- Natural likelihood vectors with globally equivalent rational scales
give the same partial posterior. Different catalogues can use unrelated
common denominators, so raw equality of natural weights is too strong. -/
theorem posterior_scaled_sameLaw (prior : Distro (Fin n)) (left right : Fin n → Nat)
    {a b : Nat} (aPositive : 0 < a) (bPositive : 0 < b)
    (same : ∀ i, left i * a = right i * b) :
    SamePosterior (posterior? prior left) (posterior? prior right) := by
  have total := integral_scale_eq prior left right a b same
  have support : 0 < natIntegral prior.record.atoms left ↔ 0 < natIntegral prior.record.atoms right := by
    constructor
    · intro positive
      have cross := Nat.mul_pos positive aPositive
      rw [total] at cross
      exact Nat.pos_of_mul_pos_right cross
    · intro positive
      have cross := Nat.mul_pos positive bPositive
      rw [← total] at cross
      exact Nat.pos_of_mul_pos_right cross
  by_cases positive : 0 < natIntegral prior.record.atoms left
  · let targetPositive := support.mp positive
    simp only [posterior?, dif_pos positive, dif_pos targetPositive, SamePosterior]
    intro event
    let leftMass := natIntegral prior.record.atoms (fun i => if event i then left i else 0)
    let rightMass := natIntegral prior.record.atoms (fun i => if event i then right i else 0)
    have eventScale : leftMass * a = rightMass * b := by
      apply integral_scale_eq
      intro i
      cases selected : event i <;> simp [selected, same]
    change FiniteProbRecord.eventMass
        (prior.record.atoms.map (fun atom => (atom.1, atom.2 * left atom.1))) event *
        (prior.reweightNat right targetPositive).record.den =
      FiniteProbRecord.eventMass
        (prior.record.atoms.map (fun atom => (atom.1, atom.2 * right atom.1))) event *
        (prior.reweightNat left positive).record.den
    rw [eventMass_reweight, eventMass_reweight, Distro.reweightNat_den, Distro.reweightNat_den]
    change leftMass * natIntegral prior.record.atoms right =
      rightMass * natIntegral prior.record.atoms left
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos aPositive bPositive)
    calc
      _ = (leftMass * a) * (natIntegral prior.record.atoms right * b) := by ac_rfl
      _ = (rightMass * b) * (natIntegral prior.record.atoms left * a) := by rw [eventScale, total]
      _ = _ := by ac_rfl
  · have absent := fun p => positive (support.mpr p)
    simp only [posterior?, dif_neg positive, dif_neg absent, SamePosterior]

theorem posterior_prior_sameLaw {left right : Distro (Fin n)} (same : left.SameLaw right)
    (weight : Fin n → Nat) : SamePosterior (posterior? left weight) (posterior? right weight) := by
  have support := QProb.equiv_num_pos_iff (same.expectNat weight)
  by_cases positive : 0 < natIntegral left.record.atoms weight
  · have targetPositive : 0 < natIntegral right.record.atoms weight := support.mp positive
    simp only [posterior?, dif_pos positive, dif_pos targetPositive, SamePosterior]
    exact same.reweightNat weight positive targetPositive
  · have absent : ¬ 0 < natIntegral right.record.atoms weight := fun p => positive (support.mpr p)
    simp only [posterior?, dif_neg positive, dif_neg absent, SamePosterior]

/-- The sampled-SCM posterior itself commutes with a coherent relabelling.
Presentations can differ after clearing rational denominators. Exhausted
evidence is included in the same statement. -/
theorem iidModelPosterior_transport (family : ModelFamilyAction G (Fin n) S)
    (prior : Distro (Fin n)) (g : G.Carrier) (cohorts : List (CountExperiment S)) :
    SamePosterior
      (iidModelPosterior? ⟨family.models, prior.map (family.hypotheses.act g)⟩
        (cohorts.map ((CountExperiment.actionOf family.outcomes family.experiments).act g)))
      ((iidModelPosterior? ⟨family.models, prior⟩ cohorts).map
        (fun posterior => posterior.map (family.hypotheses.act g))) := by
  let before := fun i => iidExperimentLikelihood (family.models i) cohorts
  let after := fun i => iidExperimentLikelihood (family.models i)
    (cohorts.map ((CountExperiment.actionOf family.outcomes family.experiments).act g))
  let renamedPrior := prior.map (family.hypotheses.act g)
  change SamePosterior (posterior? renamedPrior (qprobWeights n after))
    ((posterior? prior (qprobWeights n before)).map (fun posterior =>
      posterior.map (family.hypotheses.act g)))
  rw [← posterior_transport family.hypotheses g prior (qprobWeights n before)]
  apply posterior_scaled_sameLaw renamedPrior _ _
    (natProduct_pos n (fun i => (before i).den) (fun i => (before i).den_pos))
    (natProduct_pos n (fun i => (after i).den) (fun i => (after i).den_pos))
  intro i
  let old := family.hypotheses.act (G.inv g) i
  have transported : QProb.Equiv (after i) (before old) := by
    have same := iidExperimentLikelihood_equivariant family g old cohorts
    simpa only [old, family.hypotheses.act_inv] using same
  exact QProb.equiv_trans (qprobWeights_represents n after i)
    (QProb.equiv_trans transported (QProb.equiv_symm (qprobWeights_represents n before old)))

/-- An invariant prior can be reused after the data have been transformed. -/
theorem iidModelPosterior_transport_invariant (family : ModelFamilyAction G (Fin n) S)
    (prior : Distro (Fin n)) (invariant : PriorInvariant family.hypotheses prior)
    (g : G.Carrier) (cohorts : List (CountExperiment S)) :
    SamePosterior (iidModelPosterior? ⟨family.models, prior⟩
      (cohorts.map ((CountExperiment.actionOf family.outcomes family.experiments).act g)))
      ((iidModelPosterior? ⟨family.models, prior⟩ cohorts).map
        (fun posterior => posterior.map (family.hypotheses.act g))) :=
  (posterior_prior_sameLaw (fun event => QProb.equiv_symm (invariant g event)) _).trans
    (iidModelPosterior_transport family prior g cohorts)

end Thesis.Causality.CatalogueInference
