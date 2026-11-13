import Thesis.Probability.Distros.LawEquivalence
import Thesis.Probability.Distros.MultivariatePGF

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Generating functions determine finite laws.  At a base larger than the
cross-cleared mass coefficients, their natural polynomial expansion has
unique digits.  Bounded count vectors are encoded and constructively decoded
by positional notation, so equality of multivariate PGFs gives every-event
law equality.  Whole-number arguments suffice for that conclusion, and the
resulting law equality transports arbitrary nonnegative rational PGFs.
-/

theorem natSum_mul_right (n factor : Nat) (f : Nat → Nat) :
    natSum n (fun k => f k * factor) = natSum n f * factor := by
  induction n with
  | zero => simp only [natSum, Nat.zero_mul]
  | succ n ih => simp only [natSum, ih, Nat.add_mul]

def natPolyEval (degree base : Nat) (coeff : Nat → Nat) : Nat :=
  natSum (degree + 1) (fun k => coeff k * base ^ k)

theorem natPolyEval_head (degree base : Nat) (coeff : Nat → Nat) :
    natPolyEval (degree + 1) base coeff = coeff 0 + base * natPolyEval degree base (fun k => coeff (k + 1)) := by
  unfold natPolyEval
  rw [natSum_head]
  simp only [Nat.pow_zero, Nat.mul_one]
  congr 1
  rw [← natSum_mul_left]
  apply natSum_congr
  intro k _
  rw [Nat.pow_succ]
  ac_rfl

theorem natPolyEval_scale (degree base factor : Nat) (coeff : Nat → Nat) :
    natPolyEval degree base (fun k => coeff k * factor) = natPolyEval degree base coeff * factor := by
  unfold natPolyEval
  rw [← natSum_mul_right]
  apply natSum_congr
  intro k _
  dsimp only
  ac_rfl

/-- Coefficients below the base cannot carry into one another. -/
theorem natPolyEval_unique (degree base : Nat) (positive : 0 < base) (left right : Nat → Nat)
    (hleft : ∀ k, k ≤ degree → left k < base)
    (hright : ∀ k, k ≤ degree → right k < base)
    (same : natPolyEval degree base left = natPolyEval degree base right) :
    ∀ k, k ≤ degree → left k = right k := by
  induction degree generalizing left right with
  | zero =>
      intro k bound
      have eq : k = 0 := by omega
      subst k
      simpa only [natPolyEval, natSum, Nat.pow_zero, Nat.mul_one, Nat.zero_add] using same
  | succ degree ih =>
      rw [natPolyEval_head, natPolyEval_head] at same
      have head : left 0 = right 0 := by
        have h := congrArg (fun value => value % base) same
        simpa only [Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (hleft 0 (Nat.zero_le _)),
          Nat.mod_eq_of_lt (hright 0 (Nat.zero_le _))] using h
      have tail : natPolyEval degree base (fun k => left (k + 1)) =
          natPolyEval degree base (fun k => right (k + 1)) := by
        rw [head] at same
        exact Nat.eq_of_mul_eq_mul_left positive (Nat.add_left_cancel same)
      intro k bound
      cases k with
      | zero => exact head
      | succ k =>
          exact ih (fun k => left (k + 1)) (fun k => right (k + 1))
            (fun k hk => hleft (k + 1) (by omega))
            (fun k hk => hright (k + 1) (by omega)) tail k (by omega)

theorem natIntegral_group (atoms : List (Ω × Nat)) (embed : Ω → Nat) (f : Nat → Nat) (bound : Nat)
    (support : ∀ atom ∈ atoms, embed atom.1 ≤ bound) :
    natIntegral atoms (fun x => f (embed x)) =
      natSum (bound + 1) (fun k =>
        FiniteProbRecord.eventMass atoms (fun x => decide (embed x = k)) * f k) := by
  induction atoms with
  | nil =>
      simp only [natIntegral, FiniteProbRecord.eventMass, Nat.zero_mul]
      exact (natSum_zero_fun _).symm
  | cons atom rest ih =>
      have terms : natSum (bound + 1) (fun k =>
          FiniteProbRecord.eventMass (atom :: rest) (fun x => decide (embed x = k)) * f k) =
        natSum (bound + 1) (fun k => (if k = embed atom.1 then atom.2 else 0) * f k +
          FiniteProbRecord.eventMass rest (fun x => decide (embed x = k)) * f k) := by
        apply natSum_congr
        intro k _
        by_cases eq : embed atom.1 = k
        · simp only [FiniteProbRecord.eventMass, eq, decide_true, if_true, Nat.add_mul]
        · have ne : k ≠ embed atom.1 := Ne.symm eq
          simp only [FiniteProbRecord.eventMass, eq, ne, decide_false, Bool.false_eq_true,
            if_false, Nat.zero_mul, Nat.zero_add]
      rw [terms, natSum_add, natSum_spike, if_pos (Nat.lt_succ_of_le (support atom (List.mem_cons_self ..))),
        ← ih (fun other member => support other (List.mem_cons_of_mem _ member))]
      rfl

theorem pgf_ofNat_expectNat (μ : NatDistro Ω) (base : Nat) :
    QProb.Equiv (pgf μ (QProb.ofNat base)) (μ.distro.expectNat (fun x => base ^ μ.embed x)) :=
  QProb.equiv_trans (μ.distro.expectation_congr _ _ (fun x => qpow_ofNat base (μ.embed x)))
    (μ.distro.expectation_nat _)

def numericMass (μ : NatDistro Ω) (k : Nat) : Nat :=
  FiniteProbRecord.eventMass μ.distro.record.atoms (fun x => decide (μ.embed x = k))

theorem NatDistro.sameLaw_of_cleared_masses (μ : NatDistro Ω) (ν : NatDistro X) (bound : Nat)
    (hμ : ∀ atom ∈ μ.distro.record.atoms, μ.embed atom.1 ≤ bound)
    (hν : ∀ atom ∈ ν.distro.record.atoms, ν.embed atom.1 ≤ bound)
    (same : ∀ k, k ≤ bound → numericMass μ k * ν.distro.record.den = numericMass ν k * μ.distro.record.den) :
    μ.SameLaw ν := by
  apply (NatDistro.sameLaw_iff_events μ ν).mpr
  intro event
  change FiniteProbRecord.eventMass μ.distro.record.atoms (fun x => event (μ.embed x)) * ν.distro.record.den =
    FiniteProbRecord.eventMass ν.distro.record.atoms (fun x => event (ν.embed x)) * μ.distro.record.den
  rw [← natIntegral_indicator, ← natIntegral_indicator,
    natIntegral_group μ.distro.record.atoms μ.embed (fun k => if event k then 1 else 0) bound hμ,
    natIntegral_group ν.distro.record.atoms ν.embed (fun k => if event k then 1 else 0) bound hν,
    ← natSum_mul_right, ← natSum_mul_right]
  apply natSum_congr
  intro k hk
  calc
    _ = (numericMass μ k * ν.distro.record.den) * (if event k then 1 else 0) := by ac_rfl
    _ = (numericMass ν k * μ.distro.record.den) * (if event k then 1 else 0) := by rw [same k (Nat.le_of_lt_succ hk)]
    _ = _ := by ac_rfl

/-- One sufficiently large natural argument determines a finite numeric
law: cross-cleared probability coefficients are digits below this base. -/
theorem NatDistro.sameLaw_of_pgf_largeNat (μ : NatDistro Ω) (ν : NatDistro X)
    (same : QProb.Equiv
      (pgf μ (QProb.ofNat (μ.distro.record.den * ν.distro.record.den + 1)))
      (pgf ν (QProb.ofNat (μ.distro.record.den * ν.distro.record.den + 1)))) : μ.SameLaw ν := by
  let bound := max (observableBound μ.distro.record.atoms μ.embed) (observableBound ν.distro.record.atoms ν.embed)
  let base := μ.distro.record.den * ν.distro.record.den + 1
  have hμ : ∀ atom ∈ μ.distro.record.atoms, μ.embed atom.1 ≤ bound :=
    fun atom member => Nat.le_trans (observableBound_mem _ _ atom member) (Nat.le_max_left _ _)
  have hν : ∀ atom ∈ ν.distro.record.atoms, ν.embed atom.1 ≤ bound :=
    fun atom member => Nat.le_trans (observableBound_mem _ _ atom member) (Nat.le_max_right _ _)
  have cleared := QProb.equiv_trans (QProb.equiv_symm (pgf_ofNat_expectNat μ base))
    (QProb.equiv_trans same (pgf_ofNat_expectNat ν base))
  change natIntegral μ.distro.record.atoms (fun x => base ^ μ.embed x) * ν.distro.record.den =
    natIntegral ν.distro.record.atoms (fun x => base ^ ν.embed x) * μ.distro.record.den at cleared
  rw [natIntegral_group _ μ.embed _ bound hμ, natIntegral_group _ ν.embed _ bound hν] at cleared
  have polynomial : natPolyEval bound base (fun k => numericMass μ k * ν.distro.record.den) =
      natPolyEval bound base (fun k => numericMass ν k * μ.distro.record.den) := by
    rw [natPolyEval_scale, natPolyEval_scale]
    exact cleared
  apply NatDistro.sameLaw_of_cleared_masses μ ν bound hμ hν
  apply natPolyEval_unique bound base (Nat.succ_pos _) _ _ _ _ polynomial
  · intro k _
    have bounded := FiniteProbRecord.eventMass_le_totalMass μ.distro.record.atoms (fun x => decide (μ.embed x = k))
    rw [μ.distro.record.total_mass] at bounded
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_right ν.distro.record.den bounded)
  · intro k _
    have bounded := FiniteProbRecord.eventMass_le_totalMass ν.distro.record.atoms (fun x => decide (ν.embed x = k))
    rw [ν.distro.record.total_mass] at bounded
    have bound' := Nat.mul_le_mul_right μ.distro.record.den bounded
    rw [Nat.mul_comm ν.distro.record.den μ.distro.record.den] at bound'
    exact Nat.lt_succ_of_le bound'

theorem NatDistro.sameLaw_iff_pgf (μ : NatDistro Ω) (ν : NatDistro X) :
    μ.SameLaw ν ↔ ∀ s : QProb, QProb.Equiv (pgf μ s) (pgf ν s) := by
  constructor
  · exact fun h s => h.pgf s
  · intro h
    exact NatDistro.sameLaw_of_pgf_largeNat μ ν (h _)

def encodeCounts (base : Nat) : List Nat → Nat
  | [] => 0
  | count :: counts => count + base * encodeCounts base counts

def decodeCounts : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | length + 1, base, value => value % base :: decodeCounts length base (value / base)

theorem decodeCounts_encode (counts : List Nat) (base : Nat) (positive : 0 < base)
    (bounded : ∀ count ∈ counts, count < base) :
    decodeCounts counts.length base (encodeCounts base counts) = counts := by
  induction counts with
  | nil => rfl
  | cons count counts ih =>
      have head := bounded count (List.mem_cons_self ..)
      simp only [encodeCounts, decodeCounts,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt head,
        Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt head, Nat.zero_add]
      rw [ih (fun other member => bounded other (List.mem_cons_of_mem _ member))]

def encodedArguments (base : Nat) (s : QProb) : Nat → List QProb
  | 0 => []
  | length + 1 => s :: encodedArguments base (qpow s base) length

theorem encodedArguments_length (base : Nat) (s : QProb) (length : Nat) :
    (encodedArguments base s length).length = length := by
  induction length generalizing s with
  | zero => rfl
  | succ length ih => simp only [encodedArguments, List.length_cons, ih]

theorem qpow_mul (s : QProb) (first second : Nat) :
    QProb.Equiv (qpow (qpow s first) second) (qpow s (first * second)) := by
  simp only [QProb.Equiv, qpow_num, qpow_den, ← Nat.pow_mul]

theorem multivariateMonomial_encoded (counts : List Nat) (base : Nat) (s : QProb) :
    QProb.Equiv (multivariateMonomial (encodedArguments base s counts.length) counts)
      (qpow s (encodeCounts base counts)) := by
  induction counts generalizing s with
  | nil => exact QProb.equiv_refl _
  | cons count counts ih =>
      simp only [encodedArguments, multivariateMonomial, encodeCounts]
      exact QProb.equiv_trans
        (QProb.mul_congr (QProb.equiv_refl _)
          (QProb.equiv_trans (ih (qpow s base)) (qpow_mul s base (encodeCounts base counts))))
        (QProb.equiv_symm (qpow_add s count (base * encodeCounts base counts)))

theorem Distro.sameLaw_of_encodedCounts (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : ∀ atom ∈ μ.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
    (hν : ∀ atom ∈ ν.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
    (numeric : (⟨μ, encodeCounts base⟩ : NatDistro (List Nat)).SameLaw ⟨ν, encodeCounts base⟩) :
    μ.SameLaw ν := by
  let numericμ : NatDistro (List Nat) := ⟨μ, encodeCounts base⟩
  let numericν : NatDistro (List Nat) := ⟨ν, encodeCounts base⟩
  intro event
  have encoded := (NatDistro.sameLaw_iff_events numericμ numericν).mp numeric
    (fun value => event (decodeCounts length base value))
  have left : QProb.Equiv (μ.record.probVal (fun counts => event (decodeCounts length base (encodeCounts base counts))))
      (μ.record.probVal event) := by
    apply μ.probVal_congr_on_support
    intro atom member
    have dimension := (hμ atom member).1
    rw [← dimension, decodeCounts_encode atom.1 base positive (hμ atom member).2]
  have right : QProb.Equiv (ν.record.probVal (fun counts => event (decodeCounts length base (encodeCounts base counts))))
      (ν.record.probVal event) := by
    apply ν.probVal_congr_on_support
    intro atom member
    have dimension := (hν atom member).1
    rw [← dimension, decodeCounts_encode atom.1 base positive (hν atom member).2]
  exact QProb.equiv_trans (QProb.equiv_symm left) (QProb.equiv_trans encoded right)


/-- Multivariate PGFs determine a law whose finite count vectors have a
fixed dimension and bounded coordinates.  Positional encoding reduces the
proof to the numeric PGF theorem, with a constructive decoding section. -/
theorem Distro.sameLaw_of_multivariatePGF (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : ∀ atom ∈ μ.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
    (hν : ∀ atom ∈ ν.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
    (same : ∀ args : List QProb, args.length = length →
      QProb.Equiv (multivariatePGF μ args) (multivariatePGF ν args)) : μ.SameLaw ν := by
  let numericμ : NatDistro (List Nat) := ⟨μ, encodeCounts base⟩
  let numericν : NatDistro (List Nat) := ⟨ν, encodeCounts base⟩
  have numeric : numericμ.SameLaw numericν := by
    apply (NatDistro.sameLaw_iff_pgf numericμ numericν).mpr
    intro s
    have left : QProb.Equiv (multivariatePGF μ (encodedArguments base s length)) (pgf numericμ s) := by
      change QProb.Equiv (μ.expectation (multivariateMonomial (encodedArguments base s length)))
        (μ.expectation (fun counts => qpow s (encodeCounts base counts)))
      apply μ.expectation_congr_on_support
      intro atom member
      have dimension := (hμ atom member).1
      rw [← dimension]
      exact multivariateMonomial_encoded atom.1 base s
    have right : QProb.Equiv (multivariatePGF ν (encodedArguments base s length)) (pgf numericν s) := by
      change QProb.Equiv (ν.expectation (multivariateMonomial (encodedArguments base s length)))
        (ν.expectation (fun counts => qpow s (encodeCounts base counts)))
      apply ν.expectation_congr_on_support
      intro atom member
      have dimension := (hν atom member).1
      rw [← dimension]
      exact multivariateMonomial_encoded atom.1 base s
    exact QProb.equiv_trans (QProb.equiv_symm left)
      (QProb.equiv_trans (same _ (encodedArguments_length base s length)) right)
  exact Distro.sameLaw_of_encodedCounts μ ν length base positive hμ hν numeric

def encodedNatArguments (base value : Nat) : Nat → List Nat
  | 0 => []
  | length + 1 => value :: encodedNatArguments base (value ^ base) length

theorem encodedNatArguments_length (base value length : Nat) :
    (encodedNatArguments base value length).length = length := by
  induction length generalizing value with
  | zero => rfl
  | succ length ih => simp only [encodedNatArguments, List.length_cons, ih]

/-- Positional PGF encodings use only positive arguments when their
initial value is positive. Zero arguments are unnecessary for uniqueness. -/
theorem encodedNatArguments_positive (base value length : Nat) (positive : 0 < value) :
    ∀ arg ∈ encodedNatArguments base value length, 0 < arg := by
  induction length generalizing value with
  | zero => intro arg member; cases member
  | succ length ih =>
      intro arg member
      change arg ∈ value :: encodedNatArguments base (value ^ base) length at member
      rcases List.mem_cons.mp member with same | member
      · subst arg; exact positive
      · exact ih (value ^ base) (Nat.pow_pos positive) arg member

theorem natMonomial_encoded (counts : List Nat) (base value : Nat) :
    natMonomial (encodedNatArguments base value counts.length) counts = value ^ encodeCounts base counts := by
  induction counts generalizing value with
  | nil => rfl
  | cons count counts ih =>
      simp only [encodedNatArguments, natMonomial, encodeCounts]
      rw [ih, ← Nat.pow_mul, Nat.pow_add]

/-- Positive whole-number multivariate arguments already determine the
complete finite count law, including all events and rational PGFs. -/
theorem Distro.sameLaw_of_multivariatePGF_positive_nat (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : ∀ atom ∈ μ.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
    (hν : ∀ atom ∈ ν.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
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
      apply μ.expectNat_congr_on_support
      intro atom member
      have dimension := (hμ atom member).1
      change natMonomial (encodedNatArguments base value length) atom.1 = value ^ encodeCounts base atom.1
      rw [← dimension, natMonomial_encoded]
    rw [equality]
    exact QProb.equiv_refl _
  have right : QProb.Equiv (multivariatePGF ν (args.map QProb.ofNat)) (pgf numericν (QProb.ofNat value)) := by
    refine QProb.equiv_trans (ν.expectation_congr _ _ (fun counts => multivariateMonomial_ofNat args counts)) ?_
    refine QProb.equiv_trans (ν.expectation_nat _) ?_
    refine QProb.equiv_trans ?_ (QProb.equiv_symm (pgf_ofNat_expectNat numericν value))
    have equality : ν.expectNat (natMonomial args) = ν.expectNat (fun counts => value ^ encodeCounts base counts) := by
      apply ν.expectNat_congr_on_support
      intro atom member
      have dimension := (hν atom member).1
      change natMonomial (encodedNatArguments base value length) atom.1 = value ^ encodeCounts base atom.1
      rw [← dimension, natMonomial_encoded]
    rw [equality]
    exact QProb.equiv_refl _
  apply Distro.sameLaw_of_encodedCounts μ ν length base positive hμ hν
  apply NatDistro.sameLaw_of_pgf_largeNat numericμ numericν
  exact QProb.equiv_trans (QProb.equiv_symm left)
    (QProb.equiv_trans (same args (encodedNatArguments_length base value length)
      (encodedNatArguments_positive base value length (Nat.succ_pos _))) right)

/-- Whole-number multivariate arguments determine the complete finite count
law. This interface also allows zero arguments. -/
theorem Distro.sameLaw_of_multivariatePGF_nat (μ ν : Distro (List Nat)) (length base : Nat)
    (positive : 0 < base)
    (hμ : ∀ atom ∈ μ.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
    (hν : ∀ atom ∈ ν.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count < base)
    (same : ∀ args : List Nat, args.length = length →
      QProb.Equiv (multivariatePGF μ (args.map QProb.ofNat)) (multivariatePGF ν (args.map QProb.ofNat))) :
    μ.SameLaw ν :=
  Distro.sameLaw_of_multivariatePGF_positive_nat μ ν length base positive hμ hν
    (fun args dimension _ => same args dimension)

end Thesis.Probability.Distros
