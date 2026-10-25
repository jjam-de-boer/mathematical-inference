import Thesis.Probability.Distros.Record
import Thesis.Probability.FiniteRecordPresentation

namespace Thesis.Probability.Distros

/-!
# Finite sampling and declared-domain adapters for named distributions

Named laws may use ambient labels such as natural-number lists even though
their records contain only finitely many atoms. `finitePresentation` supplies
a finite weighted sampling type for any such law, without a unit-cell urn
expansion. Its decoder preserves every event and every supported conditional
by the generic record-presentation theorems.

For an observed variable, `finiteDomainPresentation` instead encodes distinct
values in an explicitly declared finite domain. That domain can retain null
values that are meaningful intervention targets. The two interfaces do not
claim a bijection between an infinite ambient type and a finite type, or turn
repeated atom occurrences into distinguishable observable values.
-/

/-- Finite private-noise sampling codes, one per weighted atom occurrence. -/
def Distro.finitePresentation (distro : Distro Ω) :
    FiniteProbRecord.FinitePresentation distro.record :=
  distro.record.atomPresentation

theorem Distro.finitePresentation_card (distro : Distro Ω) :
    distro.finitePresentation.card = distro.record.atoms.length := rfl

/-- Decoding is literal record recovery, so all event-based probability
interfaces remain available on the original labels. -/
theorem Distro.finitePresentation_recovered (distro : Distro Ω) :
    distro.finitePresentation.record.map distro.finitePresentation.decode = distro.record :=
  distro.finitePresentation.recovered

/-- A finite observed-value presentation requests its domain explicitly,
including every listed zero-weight atom rather than just positive support. -/
def Distro.finiteDomainPresentation [DecidableEq Ω] (distro : Distro Ω) (domain : List Ω)
    (covered : forall atom, atom ∈ distro.record.atoms → atom.1 ∈ domain) :
    FiniteProbRecord.FinitePresentation distro.record :=
  distro.record.domainPresentation domain covered

/-- Every declared value has a code, regardless of its probability. This
constructs the code by finite enumeration; no representative is chosen. -/
theorem Distro.finiteDomainPresentation_covers [DecidableEq Ω] (distro : Distro Ω)
    (domain : List Ω) (covered : forall atom, atom ∈ distro.record.atoms → atom.1 ∈ domain)
    (value : Ω) (member : value ∈ domain) :
    ∃ code, (distro.finiteDomainPresentation domain covered).decode code = value := by
  refine ⟨(FiniteProbRecord.domainWitness domain).encode ⟨value, member⟩, ?_⟩
  exact congrArg Subtype.val ((FiniteProbRecord.domainWitness domain).decode_encode ⟨value, member⟩)

theorem Distro.finiteDomainPresentation_decode_injective [DecidableEq Ω] (distro : Distro Ω)
    (domain : List Ω) (covered : forall atom, atom ∈ distro.record.atoms → atom.1 ∈ domain)
    (left right : Fin (FiniteProbRecord.domainWitness domain).card)
    (same : (distro.finiteDomainPresentation domain covered).decode left =
      (distro.finiteDomainPresentation domain covered).decode right) : left = right :=
  distro.record.domainPresentation_decode_injective domain covered left right same

end Thesis.Probability.Distros
