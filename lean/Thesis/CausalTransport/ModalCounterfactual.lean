import Thesis.Causality.ModalCounterfactual
import Thesis.CausalTransport.Modal
import Thesis.CausalTransport.Counterfactual

namespace Thesis
namespace Causality

open Probability

universe u

/-!
Mode-indexed transport for finite counterfactual semantics.

This is the final bridge from an external finite-source completeness package to
the executable modal counterfactual endpoint.  It first isolates the concrete
support condition for one-action queries.  It then bundles four independent
ingredients at a current causal mode: graph compatibility, a transported
source derivation, a modal trace, and an executed multiworld construction.  No
new external theorem is assumed here; the final equivalence merely packages
the certificate supplied by `PublishedFiniteCounterfactualCompleteness`.
-/

/-! ## Support is exactly factual-evidence positivity for one-action queries -/

theorem CounterfactualQuery.singleAction_supportedAt_iff
    (M : ExactModel S) (evidence : S.Assignment -> Bool)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (outcome : S.Assignment -> Bool) :
    Nonempty ((CounterfactualQuery.singleAction evidence action outcome).SupportedAt M)
      <-> M.CounterfactualSupported evidence := by
  constructor
  · rintro ⟨⟨value, supported⟩⟩
    let query := CounterfactualQuery.singleAction evidence action outcome
    have denominatorPositive : 0 < (query.denominator M).num := by
      by_cases positive : 0 < (query.denominator M).num
      · exact positive
      · have unsupported : query.denote M = none := by
          simp [CounterfactualQuery.denote, ProbabilityResult.divide, positive]
        rw [unsupported] at supported
        cases supported
    have denominatorEquivalent : QProb.Equiv (query.denominator M)
        (M.prior.probVal (fun u => evidence (M.eval u))) :=
      FiniteProbRecord.probVal_congr M.prior _ _ (fun u =>
        CounterfactualQuery.singleAction_condition_holds
          evidence action outcome M u)
    have latentPositive :
        0 < (M.prior.probVal (fun u => evidence (M.eval u))).num :=
      (QProb.equiv_num_pos_iff denominatorEquivalent).mp denominatorPositive
    simpa [FiniteLatentSCM.CounterfactualSupported,
      FiniteLatentSCM.observationalDist, FiniteProbRecord.EventPositive,
      FiniteProbRecord.probVal, FiniteProbRecord.map,
      FiniteProbRecord.eventMass_map_labels] using latentPositive
  · intro positive
    exact ⟨⟨M.counterfactualValue evidence positive action outcome,
      CounterfactualQuery.singleAction_denote_eq_counterfactualValue
        M evidence positive action outcome⟩⟩

/-! ## Counterfactual transport indexed by a causal mode and its modal worlds -/

/-!
The theorem above concerns support of the direct query language.  The rest of
the file retains the stronger operational information required by the thesis:
the same query is represented both by a source derivation and by an actually
executed modal multiworld endpoint.
-/

/--
A counterfactual certificate anchored at a concrete epistemic mode.  `encoded`
is the finite-source proof object; `modalTrace` explains its locked query
contexts; `combinedConstruction` is the executable realization whose endpoint
is compared to the derived observational formula below.
-/
structure ModeIndexedCounterfactualDerivation
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (mode : CausalMode T.toObserved)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : CounterfactualQuery T.toObserved) where
  compatible : mode.CompatibleWith G.interpret
  encoded : EncodedCounterfactualDerivation sound query
  modalTrace : ModalCounterfactualQueryTrace mode query
  combinedConstruction :
    ModalCombinedCounterfactualConstruction mode query

/--
The published reduction is applied to the result computed by the atomically
executed endpoint record, not merely to the parallel query syntax.
-/
noncomputable def ModeIndexedCounterfactualDerivation.endpointReduction
    (derivation : ModeIndexedCounterfactualDerivation mode sound query) :
    ProbabilityResult.Equivalent
      derivation.combinedConstruction.endpointDenote
      (derivation.encoded.toTarget.formula.denote mode.record.model
        derivation.encoded.toTarget.reference) :=
  ProbabilityResult.trans
    derivation.combinedConstruction.semanticAgreement
    (derivation.encoded.toTarget.reduction mode.record.model
      derivation.compatible)

/-- Support witness read at the actual combined-construction endpoint. -/
def CombinedCounterfactualSupportedAt
    (construction : ModalCombinedCounterfactualConstruction mode query) : Type :=
  Sigma fun value =>
    ProbabilityResult.Equivalent construction.endpointDenote (some value)

/-- Published support is transported through the executed multiworld semantics. -/
theorem ModeIndexedCounterfactualDerivation.endpointSupportedAt
    (derivation : ModeIndexedCounterfactualDerivation mode sound query) :
    Nonempty
      (CombinedCounterfactualSupportedAt derivation.combinedConstruction) := by
  rcases derivation.encoded.toTarget.supported mode.record.model
      derivation.compatible with ⟨supported⟩
  exact ⟨⟨supported.1, ProbabilityResult.trans
    derivation.combinedConstruction.semanticAgreement supported.2⟩⟩

/--
Counterfactual completeness transport retaining every modal action world.
The forward direction obtains the external source certificate and equips it
with compatibility and canonical executable/modal data.  The reverse direction
recovers compatibility together with the underlying finite-source properties.
-/
theorem finiteSource_modeIndexed_transported_counterfactual_iff
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (mode : CausalMode T.toObserved)
    (sound : PublishedFiniteSourceSoundness T G)
    (published : PublishedFiniteCounterfactualCompleteness T G sound)
    (query : CounterfactualQuery T.toObserved) :
    (mode.CompatibleWith G.interpret /\
      CounterfactualIdentifiable G.interpret query /\
      CounterfactualSupported G.interpret query) <->
      Nonempty (ModeIndexedCounterfactualDerivation mode sound query) := by
  constructor
  · rintro ⟨currentCompatible, properties⟩
    rcases (finiteSource_transported_counterfactual_iff published query).mp
      properties with ⟨encoded⟩
    exact ⟨⟨currentCompatible, encoded,
      ModalCounterfactualQueryTrace.canonical mode query,
      ModalCombinedCounterfactualConstruction.canonical mode query⟩⟩
  · rintro ⟨indexed⟩
    exact ⟨indexed.compatible,
      (finiteSource_transported_counterfactual_iff published query).mpr
        ⟨indexed.encoded⟩⟩

/-- Compatibility-specialized form of the mode-indexed counterfactual equivalence. -/
theorem finiteSource_modeIndexed_transported_counterfactual_iff_of_compatible
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (mode : CausalMode T.toObserved)
    (currentCompatible : mode.CompatibleWith G.interpret)
    (sound : PublishedFiniteSourceSoundness T G)
    (published : PublishedFiniteCounterfactualCompleteness T G sound)
    (query : CounterfactualQuery T.toObserved) :
    (CounterfactualIdentifiable G.interpret query /\
      CounterfactualSupported G.interpret query) <->
      Nonempty (ModeIndexedCounterfactualDerivation mode sound query) := by
  constructor
  · intro properties
    exact (finiteSource_modeIndexed_transported_counterfactual_iff
      mode sound published query).mp ⟨currentCompatible, properties⟩
  · intro certificate
    exact ((finiteSource_modeIndexed_transported_counterfactual_iff
      mode sound published query).mpr certificate).2

end Causality
end Thesis
