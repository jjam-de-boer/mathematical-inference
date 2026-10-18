import Thesis.Probability.Distros.PositiveSupport
import Thesis.Probability.Distros.PGFUniqueness

namespace Thesis.Probability.Distros

/-- Positional decoding is required only on positive-weight atoms. The
finite event-law argument retains every original zero-weight occurrence. -/
theorem Distro.sameLaw_of_encodedCounts_positiveSupport (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : μ.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (hν : ν.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (numeric : (⟨μ, encodeCounts base⟩ : NatDistro (List Nat)).SameLaw ⟨ν, encodeCounts base⟩) :
    μ.SameLaw ν := by
  let numericμ : NatDistro (List Nat) := ⟨μ, encodeCounts base⟩
  let numericν : NatDistro (List Nat) := ⟨ν, encodeCounts base⟩
  intro event
  have encoded := (NatDistro.sameLaw_iff_events numericμ numericν).mp numeric
    (fun value => event (decodeCounts length base value))
  have left : QProb.Equiv (μ.record.probVal (fun counts => event (decodeCounts length base (encodeCounts base counts))))
      (μ.record.probVal event) := by
    apply μ.probVal_congr_positive
    intro atom member weight
    change event (decodeCounts length base (encodeCounts base atom.1)) = event atom.1
    have dimension := (hμ atom member weight).1
    rw [← dimension, decodeCounts_encode atom.1 base positive (hμ atom member weight).2]
  have right : QProb.Equiv (ν.record.probVal (fun counts => event (decodeCounts length base (encodeCounts base counts))))
      (ν.record.probVal event) := by
    apply ν.probVal_congr_positive
    intro atom member weight
    change event (decodeCounts length base (encodeCounts base atom.1)) = event atom.1
    have dimension := (hν atom member weight).1
    rw [← dimension, decodeCounts_encode atom.1 base positive (hν atom member weight).2]
  exact QProb.equiv_trans (QProb.equiv_symm left) (QProb.equiv_trans encoded right)

/-- Positive natural PGF arguments determine a count law under almost-sure
shape and coordinate bounds, independently of zero-weight outliers. -/
theorem Distro.sameLaw_of_multivariatePGF_positive_nat_positiveSupport (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : μ.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (hν : ν.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (same : ∀ args : List Nat, args.length = length → (∀ arg ∈ args, 0 < arg) →
      QProb.Equiv (multivariatePGF μ (args.map QProb.ofNat)) (multivariatePGF ν (args.map QProb.ofNat))) :
    μ.SameLaw ν := by
  let numericμ : NatDistro (List Nat) := ⟨μ, encodeCounts base⟩
  let numericν : NatDistro (List Nat) := ⟨ν, encodeCounts base⟩
  let value := μ.record.den * ν.record.den + 1
  let args := encodedNatArguments base value length
  have left : QProb.Equiv (multivariatePGF μ (args.map QProb.ofNat)) (pgf numericμ (QProb.ofNat value)) := by
    refine QProb.equiv_trans (μ.expectation_congr _ _ (fun counts => multivariateMonomial_ofNat args counts)) ?_
    refine QProb.equiv_trans (μ.expectation_nat _) ?_
    refine QProb.equiv_trans ?_ (QProb.equiv_symm (pgf_ofNat_expectNat numericμ value))
    have equality : μ.expectNat (natMonomial args) = μ.expectNat (fun counts => value ^ encodeCounts base counts) := by
      apply μ.expectNat_congr_positive
      intro atom member weight
      have dimension := (hμ atom member weight).1
      change natMonomial (encodedNatArguments base value length) atom.1 = value ^ encodeCounts base atom.1
      rw [← dimension, natMonomial_encoded]
    rw [equality]
    exact QProb.equiv_refl _
  have right : QProb.Equiv (multivariatePGF ν (args.map QProb.ofNat)) (pgf numericν (QProb.ofNat value)) := by
    refine QProb.equiv_trans (ν.expectation_congr _ _ (fun counts => multivariateMonomial_ofNat args counts)) ?_
    refine QProb.equiv_trans (ν.expectation_nat _) ?_
    refine QProb.equiv_trans ?_ (QProb.equiv_symm (pgf_ofNat_expectNat numericν value))
    have equality : ν.expectNat (natMonomial args) = ν.expectNat (fun counts => value ^ encodeCounts base counts) := by
      apply ν.expectNat_congr_positive
      intro atom member weight
      have dimension := (hν atom member weight).1
      change natMonomial (encodedNatArguments base value length) atom.1 = value ^ encodeCounts base atom.1
      rw [← dimension, natMonomial_encoded]
    rw [equality]
    exact QProb.equiv_refl _
  apply Distro.sameLaw_of_encodedCounts_positiveSupport μ ν length base positive hμ hν
  apply NatDistro.sameLaw_of_pgf_largeNat numericμ numericν
  exact QProb.equiv_trans (QProb.equiv_symm left)
    (QProb.equiv_trans (same args (encodedNatArguments_length base value length)
      (encodedNatArguments_positive base value length (Nat.succ_pos _))) right)

/-- All natural PGF arguments also suffice under positive-support bounds. -/
theorem Distro.sameLaw_of_multivariatePGF_nat_positiveSupport (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : μ.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (hν : ν.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (same : ∀ args : List Nat, args.length = length →
      QProb.Equiv (multivariatePGF μ (args.map QProb.ofNat)) (multivariatePGF ν (args.map QProb.ofNat))) :
    μ.SameLaw ν :=
  Distro.sameLaw_of_multivariatePGF_positive_nat_positiveSupport μ ν length base positive hμ hν
    (fun args dimension _ => same args dimension)

/-- Rational PGFs determine a count law with almost-sure shape and bounds. -/
theorem Distro.sameLaw_of_multivariatePGF_positiveSupport (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : μ.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (hν : ν.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count < base))
    (same : ∀ args : List QProb, args.length = length →
      QProb.Equiv (multivariatePGF μ args) (multivariatePGF ν args)) : μ.SameLaw ν :=
  Distro.sameLaw_of_multivariatePGF_nat_positiveSupport μ ν length base positive hμ hν
    (fun args dimension => same (args.map QProb.ofNat) (by simpa only [List.length_map] using dimension))

end Thesis.Probability.Distros
