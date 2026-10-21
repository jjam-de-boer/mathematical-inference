import Thesis.Probability.Distros.Basic

namespace Thesis.Probability.Distros

/-!
# Equality and support of finite probability laws

These interfaces depend only on finite probability records, not on moments,
covariance or concentration. They are shared by ordinary distribution clients
and exact entropy. The existing `LawEquivalence` and `SignedConcentration`
modules re-export the same public declarations for import compatibility.

Law equality compares every Boolean event rather than record syntax: repeated
labels, denominator rescaling and atom order may change the presentation
without changing the law. Almost-sure support deliberately ignores zero-weight
occurrences, but retains every occurrence of positive weight. Neither interface
requires a finite enumeration of the outcome type or global decidable equality.

The declarations below are moved unchanged from those two older modules.
Transport through moments remains in `LawEquivalence`; signed concentration
theorems remain in `SignedConcentration`. Keeping that direction one-way lets
support-only clients avoid importing those specialized proofs.
-/

/-- Agreement of all Boolean event probabilities, independent of the
ordering, splitting, or denominator of the atom presentation. -/
def Distro.SameLaw (μ ν : Distro Ω) : Prop :=
  ∀ event : Event Ω, QProb.Equiv (μ.record.probVal event) (ν.record.probVal event)

namespace Distro.SameLaw

theorem refl (μ : Distro Ω) : μ.SameLaw μ := fun _ => QProb.equiv_refl _

theorem symm {μ ν : Distro Ω} (h : μ.SameLaw ν) : ν.SameLaw μ :=
  fun event => QProb.equiv_symm (h event)

theorem trans {μ ν ξ : Distro Ω} (h : μ.SameLaw ν) (h' : ν.SameLaw ξ) : μ.SameLaw ξ :=
  fun event => QProb.equiv_trans (h event) (h' event)

theorem map {μ ν : Distro Ω} (h : μ.SameLaw ν) (f : Ω → X) :
    (μ.map f).SameLaw (ν.map f) := fun event =>
  QProb.equiv_trans (μ.map_probVal f event)
    (QProb.equiv_trans (h (fun x => event (f x))) (QProb.equiv_symm (ν.map_probVal f event)))

end Distro.SameLaw

/-- Almost-sure statements ignore zero-weight occurrences but retain all
positive occurrences, including repeated outcome labels. -/
def Distro.AlmostSurely (μ : Distro Ω) (predicate : Ω → Prop) : Prop :=
  ∀ atom ∈ μ.record.atoms, 0 < atom.2 → predicate atom.1

end Thesis.Probability.Distros
