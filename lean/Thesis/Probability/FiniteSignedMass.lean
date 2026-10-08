import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability

/-!
# Finite integer-valued integrands over actual nonnegative records

Hidden-channel cancellation is an equality of finite sums of characters.
Its intermediate integrands can be negative even though every probability
record still has natural weights and a positive denominator.  This module
uses ordinary constructive integers for those integrands only.  It introduces
neither signed probability records nor rational representatives.

`signedMass` retains the record's actual atom multiplicities and weights.
Its product theorem integrates the genuine independent product record.
The Boolean character theorem identifies an integral with the difference
of the two ordinary natural event masses, so a vanishing character has an
exact connection to the existing probability semantics.

These identities are finite algebra.  They do not assert observational
equivalence or the existence of a graph-specific countermodel family.
-/

namespace FiniteProbRecord

/-- A Boolean parity character: even has sign one and odd has sign minus
one.  Only this integrand, never a record atom weight, can be negative. -/
def characterSign (bit : Bool) : Int := if bit then -1 else 1

theorem characterSign_xor (left right : Bool) :
    characterSign (Bool.xor left right) = characterSign left * characterSign right := by
  cases left <;> cases right <;> rfl

/-- Integrate an integer-valued function against an explicit atom list.
The natural weights are embedded exactly, without division or rounding. -/
def signedAtomMass (atoms : List (Ω × Nat)) (integrand : Ω -> Int) : Int :=
  (atoms.map fun atom => (atom.2 : Int) * integrand atom.1).sum

/-- Unnormalized signed integral against the actual record atoms.  The
normalizing denominator stays in the ordinary finite probability record. -/
def signedMass (record : FiniteProbRecord Ω) (integrand : Ω -> Int) : Int :=
  signedAtomMass record.atoms integrand

theorem signedAtomMass_congr (atoms : List (Ω × Nat)) (left right : Ω -> Int)
    (same : forall value, left value = right value) :
    signedAtomMass atoms left = signedAtomMass atoms right := by
  unfold signedAtomMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom _member
  rw [same atom.1]

theorem signedAtomMass_append (left right : List (Ω × Nat)) (integrand : Ω -> Int) :
    signedAtomMass (left ++ right) integrand = signedAtomMass left integrand + signedAtomMass right integrand := by
  simp only [signedAtomMass, List.map_append, List.sum_append]

/-- Mapping an actual finite record changes the integrand, not its weights. -/
theorem signedAtomMass_map (atoms : List (Ω × Nat)) (map : Ω -> X) (integrand : X -> Int) :
    signedAtomMass (atoms.map fun atom => (map atom.1, atom.2)) integrand =
      signedAtomMass atoms (fun value => integrand (map value)) := by
  simp only [signedAtomMass, List.map_map, Function.comp_def]

theorem signedMass_map (record : FiniteProbRecord Ω) (map : Ω -> X) (integrand : X -> Int) :
    (record.map map).signedMass integrand = record.signedMass (fun value => integrand (map value)) := by
  simp only [signedMass, signedAtomMass, FiniteProbRecord.map, List.map_map, Function.comp_def]

/-- A constant integrand retains the actual total natural mass. -/
theorem signedAtomMass_const (atoms : List (Ω × Nat)) (value : Int) :
    signedAtomMass atoms (fun _ => value) = (totalMass atoms : Int) * value := by
  induction atoms with
  | nil => simp [signedAtomMass, totalMass]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨label, weight⟩
      simp only [signedAtomMass, List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
      simp only [totalMass, Int.natCast_add, Int.add_mul]

theorem signedMass_const (record : FiniteProbRecord Ω) (value : Int) :
    record.signedMass (fun _ => value) = (record.den : Int) * value := by
  rw [signedMass, signedAtomMass_const, record.total_mass]

/-- Integration distributes over an addition of integrands on the same
actual atom list.  Repeated labels and zero weights are retained exactly. -/
theorem signedAtomMass_add (atoms : List (Ω × Nat)) (left right : Ω -> Int) :
    signedAtomMass atoms (fun value => left value + right value) =
      signedAtomMass atoms left + signedAtomMass atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp only [signedAtomMass, List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis, Int.mul_add]
      ac_rfl

/-- A complete finite sum can be integrated term by term against one
record.  This is a finite interchange of sums, not an infinite convergence
result; no cancellation or positivity of the integrands is required. -/
theorem signedAtomMass_listSum (atoms : List (Ω × Nat)) (values : List X) (term : X -> Ω -> Int) :
    signedAtomMass atoms (fun value => (values.map fun index => term index value).sum) =
      (values.map fun index => signedAtomMass atoms (term index)).sum := by
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, signedAtomMass_const, Int.mul_zero]
  | cons index rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact (signedAtomMass_add atoms (term index) _).trans (congrArg (_ + ·) inductionHypothesis)

theorem signedMass_listSum (record : FiniteProbRecord Ω) (values : List X) (term : X -> Ω -> Int) :
    record.signedMass (fun value => (values.map fun index => term index value).sum) =
      (values.map fun index => record.signedMass (term index)).sum :=
  signedAtomMass_listSum record.atoms values term

private theorem signedAtomMass_map_left (atoms : List (Ω × Nat))
    (map : Ω -> X) (factor : Nat) (integrand : X -> Int) :
    signedAtomMass (atoms.map fun atom => (map atom.1, factor * atom.2)) integrand =
      (factor : Int) * signedAtomMass atoms (fun value => integrand (map value)) := by
  induction atoms with
  | nil => simp [signedAtomMass]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      simp only [signedAtomMass, List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
      simp only [Int.natCast_mul, Int.mul_add, Int.mul_assoc]

private theorem signedAtomMass_mul_right (atoms : List (Ω × Nat)) (integrand : Ω -> Int) (factor : Int) :
    signedAtomMass atoms (fun value => integrand value * factor) = signedAtomMass atoms integrand * factor := by
  induction atoms with
  | nil => simp [signedAtomMass]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      simp only [signedAtomMass, List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
      simp only [Int.add_mul, Int.mul_assoc]

/-- A fixed integer coefficient can be pulled outside the actual weighted
integral.  The coefficient need not be nonzero, and no weight is divided out. -/
theorem signedAtomMass_mul_left (atoms : List (Ω × Nat)) (factor : Int) (integrand : Ω -> Int) :
    signedAtomMass atoms (fun value => factor * integrand value) = factor * signedAtomMass atoms integrand := by
  exact (signedAtomMass_congr atoms _ _ (fun value => Int.mul_comm factor (integrand value))).trans
    ((signedAtomMass_mul_right atoms integrand factor).trans (Int.mul_comm _ _))

theorem signedMass_mul_left (record : FiniteProbRecord Ω) (factor : Int) (integrand : Ω -> Int) :
    record.signedMass (fun value => factor * integrand value) = factor * record.signedMass integrand :=
  signedAtomMass_mul_left record.atoms factor integrand

/-- Exact rectangular signed integration on a weighted Cartesian product.
This is the independence calculation at the real natural atom weights. -/
theorem signedAtomMass_weightedCartesian (left : List (Ω × Nat)) (right : List (X × Nat))
    (leftValue : Ω -> Int) (rightValue : X -> Int) :
    signedAtomMass (weightedCartesian left right) (fun pair => leftValue pair.1 * rightValue pair.2) =
      signedAtomMass left leftValue * signedAtomMass right rightValue := by
  induction left with
  | nil => simp [weightedCartesian, signedAtomMass]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      change signedAtomMass
        ((right.map fun atom => ((value, atom.1), weight * atom.2)) ++ weightedCartesian rest right)
        (fun pair => leftValue pair.1 * rightValue pair.2) = _
      rw [signedAtomMass_append, inductionHypothesis]
      have scaled : signedAtomMass (right.map fun atom => ((value, atom.1), weight * atom.2))
          (fun pair => leftValue pair.1 * rightValue pair.2) =
            (weight : Int) * signedAtomMass right (fun other => leftValue value * rightValue other) :=
        signedAtomMass_map_left right (fun other => (value, other)) weight _
      rw [scaled]
      have extracted : signedAtomMass right (fun other => leftValue value * rightValue other) =
          leftValue value * signedAtomMass right rightValue := by
        rw [signedAtomMass_congr right _ _ (fun other => Int.mul_comm _ _), signedAtomMass_mul_right]
        exact Int.mul_comm _ _
      rw [extracted]
      simp only [signedAtomMass, List.map_cons, List.sum_cons, Int.add_mul, Int.mul_assoc]

/-- A factorized integrand integrates through the actual independent
finite-record product, including zero weights and repeated atom labels. -/
theorem signedMass_product (left : FiniteProbRecord Ω) (right : FiniteProbRecord X)
    (leftValue : Ω -> Int) (rightValue : X -> Int) :
    (left.product right).signedMass (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.signedMass leftValue * right.signedMass rightValue :=
  signedAtomMass_weightedCartesian left.atoms right.atoms leftValue rightValue

/-- Boolean characters are the difference of the ordinary even and odd
natural masses.  This equality is about the same atom list, not a surrogate
distribution or an assumed uniform hidden parity. -/
theorem signedAtomMass_character (atoms : List (Ω × Nat)) (event : Event Ω) :
    signedAtomMass atoms (fun value => characterSign (event value)) =
      (eventMass atoms (fun value => !(event value)) : Int) - (eventMass atoms event : Int) := by
  induction atoms with
  | nil => simp [signedAtomMass, eventMass]
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      cases selected : event value <;>
        simp only [signedAtomMass, List.map_cons, List.sum_cons, eventMass, selected,
          Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
          characterSign, Int.natCast_add, Int.mul_one, Int.mul_neg, Int.sub_eq_add_neg,
          Int.neg_add, Int.add_assoc] at inductionHypothesis ⊢ <;>
        rw [inductionHypothesis] <;> ac_rfl

theorem signedMass_character (record : FiniteProbRecord Ω) (event : Event Ω) :
    record.signedMass (fun value => characterSign (event value)) =
      (eventMass record.atoms (fun value => !(event value)) : Int) - (eventMass record.atoms event : Int) :=
  signedAtomMass_character record.atoms event

/-- Equal ordinary character fibres give a zero signed integral.  This is
the exact cancellation input for independent hidden-channel products. -/
theorem signedMass_character_zero (record : FiniteProbRecord Ω) (event : Event Ω)
    (balanced : eventMass record.atoms (fun value => !(event value)) = eventMass record.atoms event) :
    record.signedMass (fun value => characterSign (event value)) = 0 := by
  rw [record.signedMass_character event, balanced, Int.sub_self]

end FiniteProbRecord
end Probability
end Thesis
