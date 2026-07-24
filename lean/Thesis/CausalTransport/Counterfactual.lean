import Thesis.CausalTransport.FiniteSource
import Thesis.Causality.Counterfactual

namespace Thesis
namespace Causality

open Probability

/-!
Finite source-to-target transport for counterfactual identification.

Counterfactual events may mention arbitrarily many hard-intervention worlds,
but all atoms are evaluated at one shared latent assignment.  The independent
finite-table evaluator and the intrinsic evaluator are connected pointwise.
The external completeness boundary returns a source-native multiworld
reduction and a do-calculus derivation to an action-free observational term;
the semantic composition and target transport are checked here.
-/

namespace CounterfactualAtom

def finiteSourceHolds {T : FiniteTableSignature}
    (atom : CounterfactualAtom T.toObserved) (M : FiniteTableSCM T)
    (u : M.latent.Assignment) : Bool :=
  decide (M.evalUnder atom.action u atom.node = atom.value)

theorem finiteSourceHolds_preserved {T : FiniteTableSignature}
    (atom : CounterfactualAtom T.toObserved) (M : FiniteTableSCM T)
    (u : M.latent.Assignment) :
    atom.finiteSourceHolds M u = atom.holds M.interpret u := by
  unfold finiteSourceHolds holds
  rw [M.evalUnder_preserved atom.action u atom.node]
  rfl

end CounterfactualAtom

namespace CounterfactualEvent

def finiteSourceHolds {T : FiniteTableSignature}
    (event : CounterfactualEvent T.toObserved) (M : FiniteTableSCM T)
    (u : M.latent.Assignment) : Bool :=
  match event with
  | CounterfactualEvent.truth => true
  | CounterfactualEvent.falsity => false
  | CounterfactualEvent.atom counterfactualAtom =>
      counterfactualAtom.finiteSourceHolds M u
  | CounterfactualEvent.conj left right =>
      left.finiteSourceHolds M u && right.finiteSourceHolds M u
  | CounterfactualEvent.disj left right =>
      left.finiteSourceHolds M u || right.finiteSourceHolds M u
  | CounterfactualEvent.neg inner => !(inner.finiteSourceHolds M u)

theorem finiteSourceHolds_preserved {T : FiniteTableSignature}
    (event : CounterfactualEvent T.toObserved) (M : FiniteTableSCM T)
    (u : M.latent.Assignment) :
    event.finiteSourceHolds M u = event.holds M.interpret u := by
  induction event with
  | truth => simp [finiteSourceHolds, holds]
  | falsity => simp [finiteSourceHolds, holds]
  | atom counterfactualAtom =>
      simpa [finiteSourceHolds, holds] using
        counterfactualAtom.finiteSourceHolds_preserved M u
  | conj left right leftIH rightIH =>
      simp [finiteSourceHolds, holds, leftIH, rightIH]
  | disj left right leftIH rightIH =>
      simp [finiteSourceHolds, holds, leftIH, rightIH]
  | neg inner ih =>
      simp [finiteSourceHolds, holds, ih]

end CounterfactualEvent

namespace CounterfactualQuery

def finiteSourceDenominator {T : FiniteTableSignature}
    (query : CounterfactualQuery T.toObserved) (M : FiniteTableSCM T) :
    QProb :=
  M.prior.probVal (query.condition.finiteSourceHolds M)

def finiteSourceNumerator {T : FiniteTableSignature}
    (query : CounterfactualQuery T.toObserved) (M : FiniteTableSCM T) :
    QProb :=
  M.prior.probVal (fun u =>
    query.condition.finiteSourceHolds M u &&
      query.outcome.finiteSourceHolds M u)

def finiteSourceDenote {T : FiniteTableSignature}
    (query : CounterfactualQuery T.toObserved) (M : FiniteTableSCM T) :
    ProbabilityResult.Result :=
  ProbabilityResult.divide (some (query.finiteSourceNumerator M))
    (some (query.finiteSourceDenominator M))

theorem finiteSourceDenominator_preserved {T : FiniteTableSignature}
    (query : CounterfactualQuery T.toObserved) (M : FiniteTableSCM T) :
    QProb.Equiv (query.finiteSourceDenominator M)
      (query.denominator M.interpret) :=
  FiniteProbRecord.probVal_congr M.prior _ _
    (fun u => query.condition.finiteSourceHolds_preserved M u)

theorem finiteSourceNumerator_preserved {T : FiniteTableSignature}
    (query : CounterfactualQuery T.toObserved) (M : FiniteTableSCM T) :
    QProb.Equiv (query.finiteSourceNumerator M)
      (query.numerator M.interpret) :=
  FiniteProbRecord.probVal_congr M.prior _ _ (fun u => by
    rw [query.condition.finiteSourceHolds_preserved M u,
      query.outcome.finiteSourceHolds_preserved M u])

noncomputable def finiteSourceDenote_preserved {T : FiniteTableSignature}
    (query : CounterfactualQuery T.toObserved) (M : FiniteTableSCM T) :
    ProbabilityResult.Equivalent (query.finiteSourceDenote M)
      (query.denote M.interpret) :=
  ProbabilityResult.divide_congr
    (.value (query.finiteSourceNumerator_preserved M))
    (.value (query.finiteSourceDenominator_preserved M))

def FiniteSourceSupportedAt {T : FiniteTableSignature}
    (query : CounterfactualQuery T.toObserved) (M : FiniteTableSCM T) :
    Type :=
  Sigma fun value =>
    ProbabilityResult.Equivalent (query.finiteSourceDenote M) (some value)

def SupportedAt (query : CounterfactualQuery S) (M : ExactModel S) : Type :=
  Sigma fun value => ProbabilityResult.Equivalent (query.denote M) (some value)

noncomputable def finiteSourceSupportedAt_to_target
    {T : FiniteTableSignature} (query : CounterfactualQuery T.toObserved)
    (M : FiniteTableSCM T) (supported : query.FiniteSourceSupportedAt M) :
    query.SupportedAt M.interpret := by
  rcases supported with ⟨value, equivalent⟩
  exact ⟨value, ProbabilityResult.trans
    (ProbabilityResult.symm (query.finiteSourceDenote_preserved M))
    equivalent⟩

noncomputable def finiteSourceSupportedAt_of_target
    {T : FiniteTableSignature} (query : CounterfactualQuery T.toObserved)
    (M : FiniteTableSCM T) (supported : query.SupportedAt M.interpret) :
    query.FiniteSourceSupportedAt M := by
  rcases supported with ⟨value, equivalent⟩
  exact ⟨value, ProbabilityResult.trans
    (query.finiteSourceDenote_preserved M) equivalent⟩

end CounterfactualQuery

def FiniteSourceCounterfactualIdentifiable {T : FiniteTableSignature}
    (G : FiniteTableGraph T) (query : CounterfactualQuery T.toObserved) : Prop :=
  forall (left right : FiniteTableSCM T),
    FiniteSourceCompatible left G ->
    FiniteSourceCompatible right G ->
    FiniteSourceObservationallyEquivalent left right ->
    Nonempty (ProbabilityResult.Equivalent
      (query.finiteSourceDenote left) (query.finiteSourceDenote right))

def FiniteSourceCounterfactualSupported {T : FiniteTableSignature}
    (G : FiniteTableGraph T) (query : CounterfactualQuery T.toObserved) : Prop :=
  forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G ->
      Nonempty (query.FiniteSourceSupportedAt model)

def CounterfactualIdentifiable (G : ObservedGraph S)
    (query : CounterfactualQuery S) : Prop :=
  forall (left right : ExactModel S),
    Compatible left G -> Compatible right G ->
    ObservationallyEquivalent left right ->
    Nonempty (ProbabilityResult.Equivalent
      (query.denote left) (query.denote right))

def CounterfactualSupported (G : ObservedGraph S)
    (query : CounterfactualQuery S) : Prop :=
  forall model : ExactModel S,
    Compatible model G -> Nonempty (query.SupportedAt model)

theorem finiteSource_counterfactualIdentifiable_iff
    {T : FiniteTableSignature} (G : FiniteTableGraph T)
    (query : CounterfactualQuery T.toObserved) :
    FiniteSourceCounterfactualIdentifiable G query <->
      CounterfactualIdentifiable G.interpret query := by
  constructor
  · intro identifiable left right leftCompatible rightCompatible observational
    let sourceLeft := FiniteTableSCM.ofExact left
    let sourceRight := FiniteTableSCM.ofExact right
    rcases identifiable sourceLeft sourceRight
      ((finiteSourceCompatible_iff sourceLeft G).mpr leftCompatible)
      ((finiteSourceCompatible_iff sourceRight G).mpr rightCompatible)
      ((finiteSource_observational_iff sourceLeft sourceRight).mpr observational)
      with ⟨sourceEquivalent⟩
    exact ⟨ProbabilityResult.trans
      (ProbabilityResult.symm
        (query.finiteSourceDenote_preserved sourceLeft))
      (ProbabilityResult.trans sourceEquivalent
        (query.finiteSourceDenote_preserved sourceRight))⟩
  · intro identifiable left right leftCompatible rightCompatible observational
    rcases identifiable left.interpret right.interpret
      ((finiteSourceCompatible_iff left G).mp leftCompatible)
      ((finiteSourceCompatible_iff right G).mp rightCompatible)
      ((finiteSource_observational_iff left right).mp observational)
      with ⟨targetEquivalent⟩
    exact ⟨ProbabilityResult.trans
      (query.finiteSourceDenote_preserved left)
      (ProbabilityResult.trans targetEquivalent
        (ProbabilityResult.symm
          (query.finiteSourceDenote_preserved right)))⟩

theorem finiteSource_counterfactualSupported_iff
    {T : FiniteTableSignature} (G : FiniteTableGraph T)
    (query : CounterfactualQuery T.toObserved) :
    FiniteSourceCounterfactualSupported G query <->
      CounterfactualSupported G.interpret query := by
  constructor
  · intro supported model compatible
    rcases supported (FiniteTableSCM.ofExact model)
      ((finiteSourceCompatible_iff (FiniteTableSCM.ofExact model) G).mpr
        compatible) with ⟨sourceSupported⟩
    let source := FiniteTableSCM.ofExact model
    exact ⟨query.finiteSourceSupportedAt_to_target source sourceSupported⟩
  · intro supported model compatible
    rcases supported model.interpret
      ((finiteSourceCompatible_iff model G).mp compatible) with
      ⟨targetSupported⟩
    exact ⟨query.finiteSourceSupportedAt_of_target model targetSupported⟩

/-! ## Inspectable observational reduction and transport -/

/--
The source-native output of the multiworld (`ID*`/`IDC*`) reduction.  Its
formula may still contain ordinary interventional kernels; observational
identification subsequently removes those actions with the existing
do-calculus language.
-/
structure FiniteSourceCounterfactualReduction {T : FiniteTableSignature}
    (G : FiniteTableGraph T) (query : CounterfactualQuery T.toObserved) where
  reference : T.Assignment
  formula : ProbabilityTerm T.toObserved
  reduction : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G ->
      ProbabilityResult.Equivalent (query.finiteSourceDenote model)
        (model.termDenote formula reference)

/--
An explicit do-calculus continuation from the multiworld reduction to an
action-free observational formula, including support for every subderivation.
-/
structure FiniteSourceCounterfactualObservationalization
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (sound : PublishedFiniteSourceSoundness T G)
    {query : CounterfactualQuery T.toObserved}
    (reduction : FiniteSourceCounterfactualReduction G query) where
  formula : ProbabilityTerm T.toObserved
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G.interpret
    reduction.formula formula
  supported : forall model : FiniteTableSCM T,
    (compatible : FiniteSourceCompatible model G) ->
      FiniteSourceLocalDerivationSupport model reduction.reference
        (derivation.compile sound.dseparation)

/-- A complete source certificate ending in an observable expression. -/
structure FiniteSourceCounterfactualCertificate {T : FiniteTableSignature}
    (G : FiniteTableGraph T) (query : CounterfactualQuery T.toObserved) where
  reference : T.Assignment
  formula : ProbabilityTerm T.toObserved
  actionFree : formula.ActionFree
  supported : FiniteSourceCounterfactualSupported G query
  reduction : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G ->
      ProbabilityResult.Equivalent (query.finiteSourceDenote model)
        (model.termDenote formula reference)

noncomputable def FiniteSourceCounterfactualObservationalization.toCertificate
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {sound : PublishedFiniteSourceSoundness T G}
    {query : CounterfactualQuery T.toObserved}
    {reduction : FiniteSourceCounterfactualReduction G query}
    (observationalization :
      FiniteSourceCounterfactualObservationalization sound reduction) :
    FiniteSourceCounterfactualCertificate G query where
  reference := reduction.reference
  formula := observationalization.formula
  actionFree := observationalization.actionFree
  supported := by
    intro model compatible
    let supportTree := observationalization.supported model compatible
    unfold FiniteSourceLocalDerivationSupport at supportTree
    rcases supportTree.1 with ⟨value, formulaSupported⟩
    exact ⟨⟨value, ProbabilityResult.trans
      (reduction.reduction model compatible) formulaSupported⟩⟩
  reduction := by
    intro model compatible
    let compiled := observationalization.derivation.compile sound.dseparation
    let semanticEquality := compiled.finiteSource_denotational_soundAt
      ((sound.pathPrimitive model compatible).compile sound.dseparation)
      (observationalization.supported model compatible)
    exact ProbabilityResult.trans
      (reduction.reduction model compatible) semanticEquality

theorem FiniteSourceCounterfactualCertificate.identifiable
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {query : CounterfactualQuery T.toObserved}
    (certificate : FiniteSourceCounterfactualCertificate G query) :
    FiniteSourceCounterfactualIdentifiable G query := by
  intro left right leftCompatible rightCompatible observational
  exact ⟨ProbabilityResult.trans
    (certificate.reduction left leftCompatible)
    (ProbabilityResult.trans
      (finiteSource_actionFree_invariant left right observational
        certificate.formula certificate.actionFree certificate.reference)
      (ProbabilityResult.symm
        (certificate.reduction right rightCompatible)))⟩

/-- The interpreted certificate speaks only about intrinsic target semantics. -/
structure CounterfactualIdentificationCertificate (G : ObservedGraph S)
    (query : CounterfactualQuery S) where
  reference : S.Assignment
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  supported : CounterfactualSupported G query
  reduction : forall model : ExactModel S,
    Compatible model G ->
      ProbabilityResult.Equivalent (query.denote model)
        (formula.denote model reference)

noncomputable def FiniteSourceCounterfactualCertificate.toTarget
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {query : CounterfactualQuery T.toObserved}
    (certificate : FiniteSourceCounterfactualCertificate G query) :
    CounterfactualIdentificationCertificate G.interpret query where
  reference := certificate.reference
  formula := certificate.formula
  actionFree := certificate.actionFree
  supported :=
    (finiteSource_counterfactualSupported_iff G query).mp certificate.supported
  reduction := by
    intro model compatible
    let source := FiniteTableSCM.ofExact model
    have sourceCompatible : FiniteSourceCompatible source G :=
      (finiteSourceCompatible_iff source G).mpr compatible
    simpa [source] using
      ProbabilityResult.trans
        (ProbabilityResult.symm (query.finiteSourceDenote_preserved source))
        (ProbabilityResult.trans
          (certificate.reduction source sourceCompatible)
          (source.termDenote_preserved certificate.formula
            certificate.reference))

theorem CounterfactualIdentificationCertificate.identifiable
    (certificate : CounterfactualIdentificationCertificate G query) :
    CounterfactualIdentifiable G query := by
  intro left right leftCompatible rightCompatible observational
  exact ⟨ProbabilityResult.trans
    (certificate.reduction left leftCompatible)
    (ProbabilityResult.trans
      (ProbabilityTerm.actionFree_invariant left right observational
        certificate.formula certificate.actionFree certificate.reference)
      (ProbabilityResult.symm
        (certificate.reduction right rightCompatible)))⟩

/-!
This is the exact external theorem boundary for observational counterfactual
identification.  It does not mention intrinsic models.  For each supported
source-identifiable query it must supply both the finite multiworld reduction
and its ordinary do-calculus observationalization.
-/
structure PublishedFiniteCounterfactualCompleteness
    (T : FiniteTableSignature) (G : FiniteTableGraph T)
    (sound : PublishedFiniteSourceSoundness T G) where
  complete : forall query : CounterfactualQuery T.toObserved,
    FiniteSourceCounterfactualIdentifiable G query ->
    FiniteSourceCounterfactualSupported G query ->
      Sigma fun reduction : FiniteSourceCounterfactualReduction G query =>
        FiniteSourceCounterfactualObservationalization sound reduction

/-- The transported object retains both source derivation layers. -/
structure EncodedCounterfactualDerivation
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (sound : PublishedFiniteSourceSoundness T G)
    (query : CounterfactualQuery T.toObserved) where
  reduction : FiniteSourceCounterfactualReduction G query
  observationalization :
    FiniteSourceCounterfactualObservationalization sound reduction

noncomputable def EncodedCounterfactualDerivation.toTarget
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {sound : PublishedFiniteSourceSoundness T G}
    {query : CounterfactualQuery T.toObserved}
    (encoded : EncodedCounterfactualDerivation sound query) :
    CounterfactualIdentificationCertificate G.interpret query :=
  encoded.observationalization.toCertificate.toTarget

noncomputable def transport_counterfactual_completeness
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {sound : PublishedFiniteSourceSoundness T G}
    (published : PublishedFiniteCounterfactualCompleteness T G sound)
    (query : CounterfactualQuery T.toObserved)
    (identifiable : CounterfactualIdentifiable G.interpret query)
    (supported : CounterfactualSupported G.interpret query) :
    EncodedCounterfactualDerivation sound query := by
  let sourceIdentifiable :=
    (finiteSource_counterfactualIdentifiable_iff G query).mpr identifiable
  let sourceSupported :=
    (finiteSource_counterfactualSupported_iff G query).mpr supported
  rcases published.complete query sourceIdentifiable sourceSupported with
    ⟨reduction, observationalization⟩
  exact ⟨reduction, observationalization⟩

/--
Given the exact published finite specialization, supported observational
counterfactual identifiability is equivalent to an inspectable transported
certificate.
-/
theorem finiteSource_transported_counterfactual_iff
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {sound : PublishedFiniteSourceSoundness T G}
    (published : PublishedFiniteCounterfactualCompleteness T G sound)
    (query : CounterfactualQuery T.toObserved) :
    (CounterfactualIdentifiable G.interpret query /\
      CounterfactualSupported G.interpret query) <->
      Nonempty (EncodedCounterfactualDerivation sound query) := by
  constructor
  · intro properties
    exact ⟨transport_counterfactual_completeness published query
      properties.1 properties.2⟩
  · intro encoded
    rcases encoded with ⟨encoded⟩
    let certificate := encoded.toTarget
    exact ⟨certificate.identifiable, certificate.supported⟩

end Causality
end Thesis
