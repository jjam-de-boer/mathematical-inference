import Thesis.Probability.FiniteRationalMoment

namespace Thesis.Probability.FiniteProbRecord

/-!
# Conditional agreement as a finite integer contrast

For a proposed rational value `q = N / D`, the response
`D * 1_(evidence && event) - N * 1_evidence` has mean zero exactly when
the supported conditional probability of `event` given `evidence` equals
`q`. Its coefficients are integers; the actual record still has natural
weights and its original positive denominator.

The distinction at null evidence is essential. Such a record also has zero
contrast, for every proposed value, but supplies no conditional probability.
The null-evidence lemmas never call `conditionOn`. Conversely, a nonzero
contrast certifies positive evidence and can later supply a supported
countermodel to conditional agreement.

All identities use the supplied atom occurrences, including repeated labels
and zero weights. Neither the record nor the proposed fraction is reduced.
No enumeration or decidable equality of the ambient outcome type is needed.
These are probability lemmas, not yet a causal classification procedure.
-/

/-- Clear the proposed value's denominator in a conditional comparison.
Only the response is signed; no probability weight is subtracted. -/
def conditionalContrast (evidence event : Event Ω) (value : QProb) (outcome : Ω) : Int :=
  (value.den : Int) * (if evidence outcome && event outcome then 1 else 0) -
    (value.num : Int) * (if evidence outcome then 1 else 0)

private theorem signedAtomMass_conditionalContrast (atoms : List (Ω × Nat))
    (evidence event : Event Ω) (value : QProb) :
    signedAtomMass atoms (conditionalContrast evidence event value) =
      (value.den : Int) * (eventMass atoms (fun outcome => evidence outcome && event outcome) : Int) -
        (value.num : Int) * (eventMass atoms evidence : Int) := by
  induction atoms with
  | nil =>
      simp only [signedAtomMass, List.map_nil, List.sum_nil, eventMass,
        Int.natCast_zero, Int.mul_zero, Int.sub_self]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨outcome, weight⟩
      change (weight : Int) * conditionalContrast evidence event value outcome +
        signedAtomMass rest (conditionalContrast evidence event value) = _
      rw [inductionHypothesis]
      cases selectedEvidence : evidence outcome <;> cases selectedEvent : event outcome <;>
        simp only [conditionalContrast, eventMass, selectedEvidence, selectedEvent,
          Bool.false_and, Bool.true_and, Bool.false_eq_true, if_false, if_true,
          Int.natCast_add, Int.natCast_zero, Int.mul_zero, Int.mul_one, Int.zero_sub, Int.sub_zero,
          Int.zero_add, Int.add_zero,
          Int.mul_add, Int.mul_sub, Int.sub_eq_add_neg, Int.mul_neg, Int.neg_add] <;>
        ac_rfl

/-- The unnormalized contrast is exactly the conditional cross-product.
The equality holds even when the evidence mass is zero. -/
theorem signedMass_conditionalContrast (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb) :
    record.signedMass (conditionalContrast evidence event value) =
      (value.den : Int) * (eventMass record.atoms (fun outcome => evidence outcome && event outcome) : Int) -
        (value.num : Int) * (eventMass record.atoms evidence : Int) :=
  signedAtomMass_conditionalContrast record.atoms evidence event value

/-- Positive evidence is required only to form the actual conditional.
Agreement uses `QProb.Equiv`, so unreduced proposed values are retained. -/
theorem signedMass_conditionalContrast_zero_iff (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb) (positive : record.EventPositive evidence) :
    record.signedMass (conditionalContrast evidence event value) = 0 ↔
      QProb.Equiv ((record.conditionOn evidence positive).probVal event) value := by
  rw [record.signedMass_conditionalContrast, Int.sub_eq_zero]
  change _ ↔ eventMass (record.atoms.filter (fun atom => evidence atom.1)) event * value.den =
    value.num * eventMass record.atoms evidence
  rw [eventMass_filter_event, Int.mul_comm (value.den : Int)]
  constructor
  · intro same
    have cast : ((eventMass record.atoms (fun outcome => evidence outcome && event outcome) * value.den : Nat) : Int) =
        ((value.num * eventMass record.atoms evidence : Nat) : Int) := by
      simpa only [Int.natCast_mul] using same
    exact Int.ofNat.inj cast
  · intro same
    have cast := congrArg (fun n : Nat => (n : Int)) same
    simpa only [Int.natCast_mul] using cast

/-- Null evidence forces the joint subevent to have zero mass as well.
A zero-weight occurrence may still have nonzero pointwise contrast; only
its integral vanishes. No conditional value is assigned to this record. -/
theorem signedMass_conditionalContrast_zero_of_not_positive (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb) (unsupported : ¬ record.EventPositive evidence) :
    record.signedMass (conditionalContrast evidence event value) = 0 := by
  have evidenceZero : eventMass record.atoms evidence = 0 := Nat.eq_zero_of_not_pos unsupported
  have included := eventMass_mono record.atoms (fun outcome => evidence outcome && event outcome) evidence
    (fun _ selected => (Bool.and_eq_true_iff.mp selected).1)
  have jointZero : eventMass record.atoms (fun outcome => evidence outcome && event outcome) = 0 := by
    omega
  rw [record.signedMass_conditionalContrast, evidenceZero, jointZero]
  simp only [Int.natCast_zero, Int.mul_zero, Int.sub_self]

/-- Normalize the same integer response by the record's actual total mass.
This is the form consumed by integer-response moment optimizers; it uses
only the foundational rational-mean interface, with no solver import. -/
theorem rationalMean_conditionalContrast (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb) :
    SignedRatio.Equiv
      (record.rationalMean (fun outcome => ⟨conditionalContrast evidence event value outcome, 1, Nat.zero_lt_one⟩))
      ⟨record.signedMass (conditionalContrast evidence event value), record.den, record.den_pos⟩ := by
  simpa only [SignedRatio.divideNat, Nat.mul_one] using
    record.rationalMean_cleared
      (fun outcome => ⟨conditionalContrast evidence event value outcome, 1, Nat.zero_lt_one⟩)
      (conditionalContrast evidence event value) 1 Nat.zero_lt_one
      (fun _ => SignedRatio.equiv_refl _)

/-- On positive evidence, zero normalized contrast characterizes the actual
conditional value. The condition is both necessary and sufficient. -/
theorem rationalMean_conditionalContrast_zero_iff (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb) (positive : record.EventPositive evidence) :
    SignedRatio.Equiv
      (record.rationalMean (fun outcome => ⟨conditionalContrast evidence event value outcome, 1, Nat.zero_lt_one⟩))
      SignedRatio.zero ↔
      QProb.Equiv ((record.conditionOn evidence positive).probVal event) value := by
  have mean := record.rationalMean_conditionalContrast evidence event value
  have zero_iff : SignedRatio.Equiv
      (record.rationalMean (fun outcome => ⟨conditionalContrast evidence event value outcome, 1, Nat.zero_lt_one⟩))
      SignedRatio.zero ↔ record.signedMass (conditionalContrast evidence event value) = 0 := by
    constructor
    · intro zero
      exact (SignedRatio.equiv_zero_iff _).mp
        (SignedRatio.equiv_trans (SignedRatio.equiv_symm mean) zero)
    · intro zero
      exact SignedRatio.equiv_trans mean ((SignedRatio.equiv_zero_iff _).mpr zero)
  exact zero_iff.trans (record.signedMass_conditionalContrast_zero_iff evidence event value positive)

/-- The normalized contrast also vanishes at null evidence. This conclusion
does not weaken the support premise of the preceding conditional theorem. -/
theorem rationalMean_conditionalContrast_zero_of_not_positive (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb) (unsupported : ¬ record.EventPositive evidence) :
    SignedRatio.Equiv
      (record.rationalMean (fun outcome => ⟨conditionalContrast evidence event value outcome, 1, Nat.zero_lt_one⟩))
      SignedRatio.zero :=
  SignedRatio.equiv_trans (record.rationalMean_conditionalContrast evidence event value)
    ((SignedRatio.equiv_zero_iff _).mpr
      (record.signedMass_conditionalContrast_zero_of_not_positive evidence event value unsupported))

/-- A nonzero mean therefore supplies the support needed to compare actual
conditional values. The case split is the constructive natural-mass
dichotomy, not excluded middle for an arbitrary proposition. -/
theorem eventPositive_of_conditionalContrast_mean_ne_zero (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb)
    (nonzero : ¬ SignedRatio.Equiv
      (record.rationalMean (fun outcome => ⟨conditionalContrast evidence event value outcome, 1, Nat.zero_lt_one⟩))
      SignedRatio.zero) : record.EventPositive evidence := by
  rcases Nat.eq_zero_or_pos (eventMass record.atoms evidence) with null | positive
  · exact False.elim (nonzero (record.rationalMean_conditionalContrast_zero_of_not_positive evidence event value
      (fun supported => Nat.ne_of_gt supported null)))
  · exact positive

end Thesis.Probability.FiniteProbRecord
