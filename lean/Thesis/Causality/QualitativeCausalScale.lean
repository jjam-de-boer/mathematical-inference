import Thesis.Causality.QualitativeDoCalculus
import Thesis.Causality.ReachabilityCorrectness

namespace Thesis
namespace Causality

open Probability
open Probability.ClaytonWaddington
open Probability.ClaytonWaddington.UrnRatio
open QualitativeDoCalculus

/-!
Qualitative comparisons of experiments, with a short list of causal sentences.

This is not causality from Clayton–Waddington urn axioms.  Those axioms have
no graphs and no `do`.  Each fixed hard intervention is reused as a finite
qualitative probability of events (a weighted urn).  Extra fields mention
which knobs are set and which nodes are direct causes along `S.directed`.
They do not mention Pearl's three rules, path d-separation, or the mutilated
graph \(G_{\overline{X}}\) as structure fields.

Investigation of the load-bearing step.  Local screening-off by direct
causes (idle experiment) together with non-descendant invariance and
parent-modularity does not yield a proof, in this library, that an abstract
`do(X)` slice is Markov on the *defined* mutilation `mutilatedDirected S X`.
Moving screening-off from the idle graph to that mutilation is the usual
truncated-factorization / global-Markov argument.  Local Markov does not
give global d-separation without positivity (intersection), and putting
“Markov on \(G_{\overline{X}}\)” or Rules 1–3 into the structure would
collapse the crown into 2a.  Those identities therefore remain theorems of
induced SCM scales, not of an arbitrary model of the sentences below.
That gap is Unresolved, not a refutation of the sentences themselves.
The thin 2b converse (no Clayton slice) is the Refuted fact.

Representation of every finite model of this structure by an `ExactModel`
is not proved.
-/

namespace QualitativeCausalScale

/-- Two assignments agree on the selected coordinates. -/
def assignmentsAgreeOn (nodes : NodeSet S) (x y : S.Assignment) : Prop :=
  ∀ i, nodes i = true → x i = y i

/-- An event mentions only the selected coordinates. -/
def dependsOnlyOn (nodes : NodeSet S) (event : Event S.Assignment) : Prop :=
  ∀ x y, assignmentsAgreeOn nodes x y → event x = event y

/-- Directed reachability along `S.directed`, including the zero-length walk. -/
def directedReachable (S : ObservedSignature) (source target : Fin S.count) :
    Bool :=
  FiniteReachability.within finBeq (NodeSet.enumerated S) S.directed S.count
    source target

/-- Nodes lying on a directed path from some member of `Z`, including `Z`. -/
def descendantsOf (S : ObservedSignature) (Z : NodeSet S) : NodeSet S :=
  fun i =>
    (NodeSet.enumerated S).any (fun z => Z z && directedReachable S z i)

/-- Nodes that are not effects of `Z` along `S.directed`. -/
def nonDescendantsOf (S : ObservedSignature) (Z : NodeSet S) : NodeSet S :=
  fun i => !(descendantsOf S Z i)

/-- Direct causes of a node, read from `S.directed`. -/
def parentsOf (S : ObservedSignature) (child : Fin S.count) : NodeSet S :=
  fun parent => S.directed parent child

theorem directedReachable_self (S : ObservedSignature) (i : Fin S.count) :
    directedReachable S i i = true :=
  (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
      (NodeSet.mem_enumerated S) S.count i i).mpr
    (FiniteReachability.BoundedWalk.refl S.directed S.count i)

theorem ExactWalk.nonempty_snoc {α : Type _} {edge : α → α → Bool}
    {length : Nat} {source middle target : α}
    (walk : FiniteReachability.ExactWalk edge length source middle)
    (last : edge middle target = true) :
    Nonempty (FiniteReachability.ExactWalk edge (length + 1) source target) := by
  induction walk with
  | refl _node =>
      exact ⟨.step last (.refl target)⟩
  | @step _length _source _mid _middle first _rest ih =>
      rcases ih last with ⟨extended⟩
      exact ⟨.step first extended⟩

theorem directedReachable_of_parent (S : ObservedSignature)
    {z parent child : Fin S.count}
    (hreach : directedReachable S z parent = true)
    (hedge : S.directed parent child = true) :
    directedReachable S z child = true := by
  have bounded :
      FiniteReachability.BoundedWalk S.directed S.count z parent :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
        (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
        (NodeSet.mem_enumerated S) S.count z parent).mp hreach
  rcases bounded with ⟨_length, _bound, ⟨walk⟩⟩
  have reachable : FiniteReachability.Reachable S.directed z child :=
    ⟨_length + 1, ExactWalk.nonempty_snoc walk hedge⟩
  have rebound :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
      (NodeSet.mem_enumerated S) reachable
  have boundedChild :
      FiniteReachability.BoundedWalk S.directed S.count z child := by
    simpa [NodeSet.length_enumerated] using rebound
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) S.directed finBeq_eq_true_iff
      (NodeSet.mem_enumerated S) S.count z child).mpr boundedChild

theorem descendantsOf_of_mem (S : ObservedSignature) (Z : NodeSet S)
    {i : Fin S.count} (hi : Z i = true) :
    descendantsOf S Z i = true := by
  refine List.any_eq_true.mpr ⟨i, NodeSet.mem_enumerated S i, ?_⟩
  exact Bool.and_eq_true_iff.mpr ⟨hi, directedReachable_self S i⟩

theorem descendantsOf_parent (S : ObservedSignature) (Z : NodeSet S)
    {parent child : Fin S.count}
    (hedge : S.directed parent child = true)
    (hparent : descendantsOf S Z parent = true) :
    descendantsOf S Z child = true := by
  rcases List.any_eq_true.mp hparent with ⟨z, zMem, hz⟩
  have hzZ : Z z = true := (Bool.and_eq_true_iff.mp hz).1
  have hzR : directedReachable S z parent = true :=
    (Bool.and_eq_true_iff.mp hz).2
  refine List.any_eq_true.mpr ⟨z, zMem, ?_⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hzZ, directedReachable_of_parent S hzR hedge⟩

theorem not_descendant_parent (S : ObservedSignature) (Z : NodeSet S)
    {parent child : Fin S.count}
    (hedge : S.directed parent child = true)
    (hchild : descendantsOf S Z child = false) :
    descendantsOf S Z parent = false := by
  cases hparent : descendantsOf S Z parent with
  | false => rfl
  | true =>
      have hcontra := descendantsOf_parent S Z hedge hparent
      exact (Bool.false_ne_true (hchild.symm.trans hcontra)).elim

theorem not_mem_of_not_descendant (S : ObservedSignature) (Z : NodeSet S)
    {i : Fin S.count} (h : descendantsOf S Z i = false) :
    Z i = false := by
  cases hi : Z i with
  | false => rfl
  | true =>
      have hdesc := descendantsOf_of_mem S Z hi
      exact (Bool.false_ne_true (h.symm.trans hdesc)).elim

theorem target_eq_none_of_not_descendant
    (target : (i : Fin S.count) → Option (S.Value i)) {child : Fin S.count}
    (hnd : descendantsOf S (fun i => (target i).isSome) child = false) :
    target child = none := by
  have hcut :
      (target child).isSome = false :=
    not_mem_of_not_descendant S (fun i => (target i).isSome) hnd
  cases htarget : target child with
  | none => rfl
  | some _ =>
      simp [htarget] at hcut

/-- Evaluation off the effects of an intervention ignores that intervention. -/
theorem evalNodeUnder_eq_of_not_descendant (M : ExactModel S)
    (target : (i : Fin S.count) → Option (S.Value i))
    (u : M.latent.Assignment) (child : Fin S.count)
    (hnd : descendantsOf S (fun i => (target i).isSome) child = false) :
    M.evalNodeUnder target u child =
      M.evalNodeUnder (FiniteLatentSCM.noIntervention S) u child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  have hnone := target_eq_none_of_not_descendant target hnd
  simp only [FiniteLatentSCM.equationUnder, hnone,
    FiniteLatentSCM.noIntervention]
  congr 1
  funext parent edge
  exact evalNodeUnder_eq_of_not_descendant M target u parent
    (not_descendant_parent S (fun i => (target i).isSome) edge hnd)
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

theorem evalUnder_eq_on_nonDescendants (M : ExactModel S)
    (target : (i : Fin S.count) → Option (S.Value i))
    (u : M.latent.Assignment) {i : Fin S.count}
    (hnd : descendantsOf S (fun i => (target i).isSome) i = false) :
    M.evalUnder target u i =
      M.evalUnder (FiniteLatentSCM.noIntervention S) u i :=
  evalNodeUnder_eq_of_not_descendant M target u i hnd

theorem sameRatio_of_probVal_equiv {X : Type _} (μ ν : UrnProb X)
    (E F : Event X) (h : QProb.Equiv (μ.probVal E) (ν.probVal F)) :
    sameRatio (ofUrnEvent μ E) (ofUrnEvent ν F) := by
  simpa [sameRatio, ofUrnEvent, UrnProb.probVal, QProb.Equiv] using h

end QualitativeCausalScale

/--
Experimental comparisons with Clayton reused at each `do`, plus causal
coherence along direct causes.

Each axiom is one plain sentence a reader who does not already know
do-calculus could accept about experiments and direct causes.
-/
structure QualitativeCausalScale.{u} (S : ObservedSignature) where
  urn : QualitativeUrnScale.{u}
  /-- Each fixed experiment is a finite pile of weighted cells. -/
  slice : HardIntervention S → UrnProb S.Assignment
  /-- After setting a coordinate to a value, that value is as plausible as
  every-outcome. -/
  effectiveness :
    ∀ (I : HardIntervention S) (i : Fin S.count) (value : S.Value i),
      I.value i = some value →
      sameRatio
        (ofUrnEvent (slice I) (fun a => decide (a i = value)))
        (ofUrnEvent (slice I) topEvent)
  /-- Setting knobs does not change claims that mention only nodes that are
  not effects of those knobs. -/
  nonDescendantInvariance :
    ∀ (I : HardIntervention S) (E : Event S.Assignment),
      QualitativeCausalScale.dependsOnlyOn
        (QualitativeCausalScale.nonDescendantsOf S I.targets) E →
      sameRatio
        (ofUrnEvent (slice I) E)
        (ofUrnEvent (slice (HardIntervention.empty S)) E)
  /-- Once every direct cause of a node has been set, two experiments that
  set those causes to the same values and do not set the node itself make
  the same claims about that node. -/
  parentModularity :
    ∀ (child : Fin S.count) (I J : HardIntervention S)
      (E : Event S.Assignment),
      (∀ parent, S.directed parent child = true →
        I.value parent = J.value parent) →
      (∀ parent, S.directed parent child = true →
        (I.value parent).isSome = true) →
      I.value child = none →
      J.value child = none →
      QualitativeCausalScale.dependsOnlyOn (NodeSet.singleton child) E →
      sameRatio (ofUrnEvent (slice I) E) (ofUrnEvent (slice J) E)

namespace QualitativeCausalScale

/-- Plausibility of an event after a hard intervention, from the slice urn. -/
def plaus (C : QualitativeCausalScale S) (I : HardIntervention S)
    (E : Event S.Assignment) : C.urn.Plaus :=
  C.urn.ratioPlaus (ofUrnEvent (C.slice I) E)

/-- The idle experiment is ordinary observation. -/
def observationalPlaus (C : QualitativeCausalScale S)
    (E : Event S.Assignment) : C.urn.Plaus :=
  C.plaus (HardIntervention.empty S) E

/-- Hard intervention read from a kernel's action and a reference assignment. -/
def interventionOf (kernel : Kernel S) (reference : S.Assignment) :
    HardIntervention S where
  value := kernel.intervention reference

/-- Urn of the experiment a kernel denotes at a reference assignment. -/
def kernelUrnOf (C : QualitativeCausalScale S) (kernel : Kernel S)
    (reference : S.Assignment) : UrnProb S.Assignment :=
  C.slice (interventionOf kernel reference)

/-- Count-ratio of a supported qualitative kernel. -/
def kernelRatioOf (C : QualitativeCausalScale S) (kernel : Kernel S)
    (reference : S.Assignment)
    (hpos : 0 < (C.kernelUrnOf kernel reference).probNum
      (kernel.conditionEvent reference)) : UrnRatio where
  N := (C.kernelUrnOf kernel reference).probNum
    (kernel.conditionEvent reference)
  k := (C.kernelUrnOf kernel reference).probNum
    (kernel.numeratorEvent reference)
  pos := hpos
  le :=
    count_mono (Kernel.numeratorEvent_implies_conditionEvent kernel reference)

/-- Support-aware qualitative conditional.  `none` is failed support, never
a completed `0/0`. -/
def kernelPlausOf (C : QualitativeCausalScale S) (kernel : Kernel S)
    (reference : S.Assignment) : Option C.urn.Plaus :=
  if hpos : 0 < (C.kernelUrnOf kernel reference).probNum
      (kernel.conditionEvent reference) then
    some (C.urn.ratioPlaus (C.kernelRatioOf kernel reference hpos))
  else
    none

theorem kernelPlausOf_eq_none_iff (C : QualitativeCausalScale S)
    (kernel : Kernel S) (reference : S.Assignment) :
    C.kernelPlausOf kernel reference = none ↔
      ¬ (0 < (C.kernelUrnOf kernel reference).probNum
        (kernel.conditionEvent reference)) := by
  by_cases hpos : 0 < (C.kernelUrnOf kernel reference).probNum
      (kernel.conditionEvent reference)
  · simp [kernelPlausOf, hpos]
  · simp [kernelPlausOf, hpos]

/-- Idle screening-off by direct causes: given a node's parents, claims
about that node do not change when we also see its other non-effects.
Failed support is not treated as independence.  This is a property of a
scale, not an expert graph-surgery field. -/
def IdleScreeningOff (C : QualitativeCausalScale S) : Prop :=
  ∀ (child : Fin S.count) (reference : S.Assignment),
    let pa := parentsOf S child
    let extra :=
      NodeSet.diff (nonDescendantsOf S (NodeSet.singleton child)) pa
    let left : Kernel S :=
      ⟨NodeSet.singleton child, NodeSet.empty, NodeSet.union extra pa⟩
    let right : Kernel S :=
      ⟨NodeSet.singleton child, NodeSet.empty, pa⟩
    ∀ a b,
      C.kernelPlausOf left reference = some a →
        C.kernelPlausOf right reference = some b →
          C.urn.eqv a b

/-- The comparison structure induced by the slice urns. -/
def toInterventionScale (C : QualitativeCausalScale S) :
    QualitativeInterventionScale S where
  Plaus := C.urn.Plaus
  plaus := C.plaus
  eqv := C.urn.eqv
  lt := C.urn.lt
  eqv_refl := C.urn.eqv_refl
  eqv_symm := C.urn.eqv_symm
  eqv_trans := C.urn.eqv_trans
  lt_irrefl := C.urn.lt_irrefl
  lt_trans := C.urn.lt_trans
  lt_respects_eqv := C.urn.lt_respects_eqv
  effectiveness := by
    intro I i value hI
    exact C.urn.sameRatio_implies_eqv (C.effectiveness I i value hI)

/-- Local Markov of a `do(I)` slice relative to the defined mutilation of
`S.directed` (incoming arrows to `I.targets` dropped).  This is a theorem
target, not an axiom field. -/
def MutilatedIdleScreeningOff (C : QualitativeCausalScale S)
    (I : HardIntervention S) : Prop :=
  ∀ (child : Fin S.count) (reference : S.Assignment),
    let pa : NodeSet S := fun parent =>
      mutilatedDirected S I.targets parent child
    let extra :=
      NodeSet.diff (nonDescendantsOf S (NodeSet.singleton child)) pa
    let left : Kernel S :=
      ⟨NodeSet.singleton child, I.targets, NodeSet.union extra pa⟩
    let right : Kernel S :=
      ⟨NodeSet.singleton child, I.targets, pa⟩
    ∀ a b,
      C.kernelPlausOf left reference = some a →
        C.kernelPlausOf right reference = some b →
          C.urn.eqv a b

/-- The load-bearing implication, as a named proposition.  Unresolved. -/
def MutilatedMarkovFromAxioms : Prop :=
  ∀ {S : ObservedSignature.{0}} (C : QualitativeCausalScale.{0} S),
    IdleScreeningOff C →
      ∀ I : HardIntervention S, MutilatedIdleScreeningOff C I

/-- Slice comparisons match those of a finite SCM's interventional urns. -/
def RealizedBy (C : QualitativeCausalScale S) (model : ExactModel S) : Prop :=
  ∀ (I : HardIntervention S) (E F : Event S.Assignment),
    sameRatio (ofUrnEvent (C.slice I) E) (ofUrnEvent (C.slice I) F) ↔
      sameRatio (ofUrnEvent (interventionalUrn model I) E)
        (ofUrnEvent (interventionalUrn model I) F)

/-- Completeness: every finite model of the scale on a stated signature is
realized by some `ExactModel`.  Not proved. -/
def ExactModelRepresentation (S : ObservedSignature) : Prop :=
  ∀ C : QualitativeCausalScale.{0} S,
    ∃ model : ExactModel S, RealizedBy C model

/-- Every finite SCM, read through a qualitative urn scale, induces a
qualitative causal scale.  Direct-cause sentences are proved from evaluation,
not from Pearl's rules. -/
def inducedCausal (model : ExactModel S) (Q : QualitativeUrnScale) :
    QualitativeCausalScale S where
  urn := Q
  slice := interventionalUrn model
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
    have hk : μ.probNum forced = μ.n := by
      simpa [QProb.Equiv, UrnProb.probVal, QProb.one] using hforced
    have ht : μ.probNum topEvent = μ.n := μ.probNum_top
    show sameRatio (ofUrnEvent μ forced) (ofUrnEvent μ topEvent)
    simp [sameRatio, ofUrnEvent]
    rw [hk, ht]
  nonDescendantInvariance := by
    intro I E hE
    have hpoint :
        (fun u => E (model.evalUnder I.value u)) =
          (fun u => E (model.evalUnder (FiniteLatentSCM.noIntervention S) u)) := by
      funext u
      apply hE
      intro i hi
      have hnd :
          descendantsOf S (fun j => (I.value j).isSome) i = false := by
        simpa [nonDescendantsOf, HardIntervention.targets] using hi
      exact evalUnder_eq_on_nonDescendants model I.value u hnd
    have hI :=
      model.interventionalValue_eq I.value E
    have hIdle :=
      model.interventionalValue_eq (HardIntervention.empty S).value E
    have hprior :
        QProb.Equiv
          (model.interventionalValue I.value E)
          (model.interventionalValue (HardIntervention.empty S).value E) := by
      refine QProb.equiv_trans hI (QProb.equiv_trans ?_ (QProb.equiv_symm hIdle))
      simpa [hpoint] using QProb.equiv_refl
        (model.prior.probVal (fun u => E (model.evalUnder I.value u)))
    have agreesI :=
      (model.interventionalDist I.value).toUrn_agrees E
    have agreesIdle :=
      (model.interventionalDist (HardIntervention.empty S).value).toUrn_agrees E
    have hμ :
        QProb.Equiv
          ((interventionalUrn model I).probVal E)
          ((interventionalUrn model (HardIntervention.empty S)).probVal E) :=
      QProb.equiv_trans (QProb.equiv_symm agreesI)
        (QProb.equiv_trans hprior agreesIdle)
    exact sameRatio_of_probVal_equiv _ _ E E hμ
  parentModularity := by
    intro child I J E agreeParents parentsSet hInone hJnone hE
    have hpoint :
        (fun u => E (model.evalUnder I.value u)) =
          (fun u => E (model.evalUnder J.value u)) := by
      funext u
      apply hE
      intro i hi
      have hi' : i = child := (NodeSet.singleton_eq_true_iff child i).mp hi
      subst i
      have hIeval :
          model.evalUnder I.value u child =
            model.evalNodeUnder I.value u child :=
        rfl
      have hJeval :
          model.evalUnder J.value u child =
            model.evalNodeUnder J.value u child :=
        rfl
      rw [hIeval, hJeval, FiniteLatentSCM.evalNodeUnder,
        FiniteLatentSCM.evalNodeUnder]
      simp only [FiniteLatentSCM.equationUnder, hInone, hJnone]
      congr 1
      funext parent edge
      cases hIv : I.value parent with
      | none =>
          have hsome : (I.value parent).isSome = true :=
            parentsSet parent edge
          simp [hIv] at hsome
      | some value =>
          have hJv : J.value parent = some value := by
            have hagree := agreeParents parent edge
            simpa [hIv] using hagree.symm
          have hIval :=
            model.evalUnder_effectiveness I.value u parent value hIv
          have hJval :=
            model.evalUnder_effectiveness J.value u parent value hJv
          change model.evalUnder I.value u parent =
            model.evalUnder J.value u parent
          exact hIval.trans hJval.symm
    have hI := model.interventionalValue_eq I.value E
    have hJ := model.interventionalValue_eq J.value E
    have hprior :
        QProb.Equiv
          (model.interventionalValue I.value E)
          (model.interventionalValue J.value E) := by
      refine QProb.equiv_trans hI (QProb.equiv_trans ?_ (QProb.equiv_symm hJ))
      simpa [hpoint] using QProb.equiv_refl
        (model.prior.probVal (fun u => E (model.evalUnder I.value u)))
    have agreesI := (model.interventionalDist I.value).toUrn_agrees E
    have agreesJ := (model.interventionalDist J.value).toUrn_agrees E
    have hμ :
        QProb.Equiv
          ((interventionalUrn model I).probVal E)
          ((interventionalUrn model J).probVal E) :=
      QProb.equiv_trans (QProb.equiv_symm agreesI)
        (QProb.equiv_trans hprior agreesJ)
    exact sameRatio_of_probVal_equiv _ _ E E hμ

theorem inducedCausal_slice (model : ExactModel S) (Q : QualitativeUrnScale)
    (I : HardIntervention S) :
    (inducedCausal model Q).slice I = interventionalUrn model I :=
  rfl

theorem inducedCausal_realized (model : ExactModel S) (Q : QualitativeUrnScale) :
    RealizedBy (inducedCausal model Q) model := by
  intro _I _E _F
  rfl

theorem inducedCausal_toInterventionScale_effectiveness
    (model : ExactModel S) (Q : QualitativeUrnScale)
    (I : HardIntervention S) (i : Fin S.count) (value : S.Value i)
    (hI : I.value i = some value) :
    (inducedCausal model Q).toInterventionScale.eqv
      ((inducedCausal model Q).toInterventionScale.plaus I
        (fun a => decide (a i = value)))
      ((inducedCausal model Q).toInterventionScale.plaus I topEvent) :=
  (inducedCausal model Q).toInterventionScale.effectiveness I i value hI

/-- Slice comparisons match the 2b induced intervention scale. -/
theorem inducedCausal_plaus_eq_eventPlaus (model : ExactModel S)
    (Q : QualitativeUrnScale) (I : HardIntervention S)
    (E : Event S.Assignment) :
    (inducedCausal model Q).plaus I E = eventPlaus Q model I E :=
  rfl

end QualitativeCausalScale

end Causality
end Thesis
