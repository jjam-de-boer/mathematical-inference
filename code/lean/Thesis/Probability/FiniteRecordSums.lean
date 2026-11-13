import Thesis.Probability.FiniteRecord

namespace Thesis.Probability.FiniteProbRecord

/-!
# Selected weighted sums on arbitrary finite records

These are list-level identities, before normalization and without positive
support. Repeated labels, zero-weight occurrences and a zero multiplier all
remain valid. In particular, factoring a future-event mass does not require
importing any reinforced or depleting urn mechanism.

The original distro spelling is retained in `Distros.ReinforcedConditioning`
as a compatibility wrapper. This owner contains the unchanged inductive proof.
-/

/-- Pull a constant natural multiplier out of the selected atom-weight sum. -/
theorem eventMass_factor_sum (atoms : List (Ω × Nat)) (evidence : Event Ω) (factor : Nat) :
    (atoms.map (fun atom => if evidence atom.1 then atom.2 * factor else 0)).sum =
      FiniteProbRecord.eventMass atoms evidence * factor := by
  induction atoms with
  | nil => simp only [List.map_nil, List.sum_nil, FiniteProbRecord.eventMass, Nat.zero_mul]
  | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons, FiniteProbRecord.eventMass, ih]
      cases evidence atom.1 <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.add_mul]

end Thesis.Probability.FiniteProbRecord
