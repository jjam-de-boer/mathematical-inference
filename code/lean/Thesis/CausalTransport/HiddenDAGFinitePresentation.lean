import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.FiniteRecordPresentation

namespace Thesis.Causality

/-!
# Finite value presentations at the native hidden-DAG boundary

The native model's observed-value adapter requires an actual bijection.
A `FiniteWitness` supplies both directions constructively, whereas a finite
record's occurrence decoder need not be injective. Keep this distinction
explicit: occurrence codes are suitable private-noise samples, but are not
in general a replacement for observed values.

For an explicitly declared finite domain, `FiniteProbRecord.domainWitness`
enumerates its entire subtype, including permitted zero-probability values.
The adapter below therefore retains null intervention targets rather than
silently restricting the observed signature to positive support.
-/

/-- Use an explicit finite enumeration as the native observed-value
conversion. No representative selection or finiteness of an ambient label
type is assumed. -/
def ValueEquivalence.ofFiniteWitness (witness : Probability.FiniteWitness Ω) :
    ValueEquivalence Ω (Fin witness.card) where
  forward := witness.encode
  backward := witness.decode
  forward_backward := witness.encode_decode
  backward_forward := witness.decode_encode

end Thesis.Causality
