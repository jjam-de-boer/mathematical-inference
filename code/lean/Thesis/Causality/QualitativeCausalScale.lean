import Thesis.Causality.WorldTicket

namespace Thesis
namespace Causality

open Probability
open Probability.ClaytonWaddington
open Probability.ClaytonWaddington.UrnRatio
open QualitativeDoCalculus
open WorldTicket

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

Listing-bag sentences are corollaries of ticketwise world-ticket readings
(`Thesis.Causality.WorldTicket`), not a basis for Pearl.

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

/-- Direct causes of a node, read from `S.directed`. -/
def parentsOf (S : ObservedSignature) (child : Fin S.count) : NodeSet S :=
  fun parent => S.directed parent child

export WorldTicket (directedReachable descendantsOf nonDescendantsOf
  evalUnder_eq_on_nonDescendants reading_parent_modularity
  listing_effectiveness listing_non_effect listing_parent_modularity)

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
        (nonDescendantsOf S I.targets) E →
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
qualitative causal scale.  Bag-level sentences are corollaries of the
ticketwise world-ticket readings, not Pearl's rules. -/
def inducedCausal (model : ExactModel S) (Q : QualitativeUrnScale) :
    QualitativeCausalScale S where
  urn := Q
  slice := interventionalUrn model
  effectiveness := by
    intro I i value hI
    exact listing_effectiveness model I i value hI
  nonDescendantInvariance := by
    intro I E hE
    exact listing_non_effect model I E hE
  parentModularity := by
    intro child I J E agreeParents parentsSet hInone hJnone hE
    refine listing_parent_modularity model child I J E
      agreeParents parentsSet hInone hJnone ?_
    intro x y hxy
    exact hE x y (fun i hi => by
      have hi' : i = child := (NodeSet.singleton_eq_true_iff child i).mp hi
      subst i
      exact hxy)

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
