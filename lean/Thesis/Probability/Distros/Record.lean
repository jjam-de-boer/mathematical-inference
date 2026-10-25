import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace Distros

/-!
# General finite distribution records

A `Distro` wraps a finite rational probability record on an arbitrary outcome
type. Its event probabilities, singleton masses and relabelling laws need no
numeric embedding of outcomes, moments or combinatorial machinery.

Natural-valued moments, convolution and generating functions belong to
`Distros.Basic`, which reexports this interface. Law/support and elementary
entropy clients can import the present layer without those developments.
No positivity of individual atom weights or finite enumeration of the whole
outcome type is required here.
-/

/-- A finite probability distro on an arbitrary outcome type. -/
structure Distro (Ω : Type u) where
  record : FiniteProbRecord Ω

namespace Distro

/-- The probability mass of a singleton outcome. -/
def pmf [DecidableEq Ω] (μ : Distro Ω) (value : Ω) : QProb :=
  μ.record.probVal (FiniteProbRecord.singletonEvent value)

/-- The unit-cell urn presentation of a distro. -/
def toUrn (μ : Distro Ω) : UrnProb Ω :=
  μ.record.toUrn

/-- Record and urn presentations agree on every Boolean event. -/
theorem toUrn_agrees (μ : Distro Ω) :
    FiniteProbRecord.AgreesWith μ.record μ.toUrn :=
  μ.record.toUrn_agrees

/-- Every event probability of a distro is a probability in `[0, 1]`. -/
theorem probVal_bounds (μ : Distro Ω) (event : Event Ω) :
    QProb.LE QProb.zero (μ.record.probVal event) ∧
      QProb.LE (μ.record.probVal event) QProb.one :=
  μ.record.probVal_bounds event

/-- The whole space has probability one. -/
theorem normalization (μ : Distro Ω) :
    QProb.Equiv (μ.record.probVal topEvent) QProb.one :=
  μ.record.normalization

/-- Relabel outcomes, keeping the atom weights and the common denominator. -/
def map (μ : Distro Ω) (f : Ω → X) : Distro X where
  record := μ.record.map f

/-- Event probabilities are preserved under relabelling, evaluated on the
preimage. -/
theorem map_probVal (μ : Distro Ω) (f : Ω → X) (event : Event X) :
    QProb.Equiv ((μ.map f).record.probVal event)
      (μ.record.probVal (fun omega => event (f omega))) :=
  FiniteProbRecord.map_probVal μ.record f event

/-- Singleton masses after relabelling are the source masses of the
preimage. -/
theorem map_pmf [DecidableEq X] (μ : Distro Ω) (f : Ω → X) (value : X) :
    QProb.Equiv
      ((μ.map f).pmf value)
      (μ.record.probVal (fun omega =>
        FiniteProbRecord.singletonEvent value (f omega))) := by
  simpa [Distro.pmf] using
    map_probVal μ f (FiniteProbRecord.singletonEvent value)

/-- Relabelling composes: decode after encode is encode-then-decode. -/
theorem map_comp (μ : Distro Ω) (f : Ω → X) (g : X → Y) :
    (μ.map f).map g = μ.map (fun omega => g (f omega)) := by
  simp [map, FiniteProbRecord.map_comp]

/-- Composed relabelling is preimage under the composite encoding. -/
theorem map_comp_probVal (μ : Distro Ω) (f : Ω → X) (g : X → Y)
    (event : Event Y) :
    QProb.Equiv (((μ.map f).map g).record.probVal event)
      (μ.record.probVal (fun omega => event (g (f omega)))) := by
  rw [map_comp]
  exact map_probVal μ (fun omega => g (f omega)) event

/-- A section of the encoding recovers event probabilities after
round-trip relabelling. -/
theorem map_section_probVal (μ : Distro Ω) (encode : Ω → X) (decode : X → Ω)
    (hsec : forall omega, decode (encode omega) = omega)
    (event : Event Ω) :
    QProb.Equiv
      (((μ.map encode).map decode).record.probVal event)
      (μ.record.probVal event) := by
  refine QProb.equiv_trans (map_comp_probVal μ encode decode event) ?_
  simp [FiniteProbRecord.probVal, QProb.Equiv]
  refine congrArg (fun mass => mass * μ.record.den) ?_
  apply FiniteProbRecord.eventMass_congr
  intro omega
  simp [hsec]

/-- A section of the encoding recovers singleton masses after round-trip
relabelling. -/
theorem map_section_pmf [DecidableEq Ω] (μ : Distro Ω)
    (encode : Ω → X) (decode : X → Ω)
    (hsec : forall omega, decode (encode omega) = omega)
    (value : Ω) :
    QProb.Equiv
      (((μ.map encode).map decode).pmf value)
      (μ.pmf value) := by
  refine QProb.equiv_trans
    (map_pmf (μ.map encode) decode value) ?_
  refine QProb.equiv_trans
    (map_probVal μ encode (fun x =>
      FiniteProbRecord.singletonEvent value (decode x))) ?_
  simp [Distro.pmf, FiniteProbRecord.probVal, QProb.Equiv]
  refine congrArg (fun mass => mass * μ.record.den) ?_
  apply FiniteProbRecord.eventMass_congr
  intro omega
  simp [FiniteProbRecord.singletonEvent, hsec]

/-- Relabelling along the identity leaves the distro unchanged. -/
theorem map_id (μ : Distro Ω) : μ.map id = μ := by
  simp [map, FiniteProbRecord.map_id]

/-- The identity section recovers every event. -/
theorem map_id_probVal (μ : Distro Ω) (event : Event Ω) :
    QProb.Equiv ((μ.map id).record.probVal event)
      (μ.record.probVal event) := by
  rw [map_id]
  exact QProb.equiv_refl _

/-- The identity section recovers every singleton. -/
theorem map_id_pmf [DecidableEq Ω] (μ : Distro Ω) (value : Ω) :
    QProb.Equiv ((μ.map id).pmf value) (μ.pmf value) := by
  rw [map_id]
  exact QProb.equiv_refl _

end Distro

end Distros
end Probability
end Thesis
