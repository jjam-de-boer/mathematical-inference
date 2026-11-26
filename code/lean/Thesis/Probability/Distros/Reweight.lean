import Thesis.Probability.Distros.LawEquivalence
namespace Thesis.Probability.Distros

/-!
# Natural likelihood updates and transport

Reweighting multiplies each existing atom mass by a supplied natural weight
and normalizes by the resulting total. It keeps repeated and zero-weight
occurrences; a positive total is required before a normalized record exists.
The caller supplies the likelihood and its sampling interpretation.

The normalization and event-mass identities make the update usable without
depending on atom-list syntax. Law-equivalent priors produce law-equivalent
updates, and a likelihood depending only on a mapped label can be applied
before or after that map with exactly the same resulting record.
-/

/-- Normalize an explicit weighted list by its actual total mass. Empty or
all-zero lists cannot inhabit the positive-mass input of this constructor. -/
def ofWeightedAtoms (atoms : List (Ω × Nat)) (positive : 0 < FiniteProbRecord.totalMass atoms) : Distro Ω :=
  ⟨⟨atoms, FiniteProbRecord.totalMass atoms, positive, rfl⟩⟩

/-- Atom and denominator equality determine the record; normalization and
positivity witnesses add no further computational data to compare. -/
theorem Distro.eq_of_atoms_den {μ ν : Distro Ω} (atoms : μ.record.atoms = ν.record.atoms)
    (den : μ.record.den = ν.record.den) : μ = ν := by
  cases μ with
  | mk μ =>
    cases ν with
    | mk ν =>
      cases μ
      cases ν
      cases atoms
      cases den
      rfl

/-- Multiply each atom by a natural likelihood and normalize by its actual mass. -/
def Distro.reweightNat (μ : Distro Ω) (weight : Ω → Nat)
    (positive : 0 < natIntegral μ.record.atoms weight) : Distro Ω :=
  ofWeightedAtoms (μ.record.atoms.map (fun atom => (atom.1, atom.2 * weight atom.1))) (by
    have total : FiniteProbRecord.totalMass (μ.record.atoms.map (fun atom => (atom.1, atom.2 * weight atom.1))) =
        natIntegral μ.record.atoms weight := by
      induction μ.record.atoms with
      | nil => rfl
      | cons atom rest ih => simp only [List.map_cons, FiniteProbRecord.totalMass, natIntegral, ih]
    rw [total]; exact positive)

theorem totalMass_reweight (atoms : List (Ω × Nat)) (weight : Ω → Nat) :
    FiniteProbRecord.totalMass (atoms.map (fun atom => (atom.1, atom.2 * weight atom.1))) =
      natIntegral atoms weight := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp only [List.map_cons, FiniteProbRecord.totalMass, natIntegral, ih]

/-- Event mass after updating is the original weighted integral restricted
to that event. This numerator identity includes structural likelihood zeros. -/
theorem eventMass_reweight (atoms : List (Ω × Nat)) (weight : Ω → Nat) (event : Event Ω) :
    FiniteProbRecord.eventMass (atoms.map (fun atom => (atom.1, atom.2 * weight atom.1))) event =
      natIntegral atoms (fun x => if event x then weight x else 0) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      cases selected : event atom.1 <;>
        simp only [List.map_cons, FiniteProbRecord.eventMass, natIntegral, selected, Bool.false_eq_true,
          if_true, if_false, Nat.mul_zero, Nat.zero_add, ih]

theorem Distro.reweightNat_den (μ : Distro Ω) (weight : Ω → Nat)
    (positive : 0 < natIntegral μ.record.atoms weight) :
    (μ.reweightNat weight positive).record.den = natIntegral μ.record.atoms weight :=
  totalMass_reweight _ _

/-- Reweighting depends on the law rather than its atom presentation. -/
theorem Distro.SameLaw.reweightNat {μ ν : Distro Ω} (same : μ.SameLaw ν) (weight : Ω → Nat)
    (hμ : 0 < natIntegral μ.record.atoms weight) (hν : 0 < natIntegral ν.record.atoms weight) :
    (μ.reweightNat weight hμ).SameLaw (ν.reweightNat weight hν) := by
  intro event
  change FiniteProbRecord.eventMass (μ.record.atoms.map (fun atom => (atom.1, atom.2 * weight atom.1))) event *
      FiniteProbRecord.totalMass (ν.record.atoms.map (fun atom => (atom.1, atom.2 * weight atom.1))) =
    FiniteProbRecord.eventMass (ν.record.atoms.map (fun atom => (atom.1, atom.2 * weight atom.1))) event *
      FiniteProbRecord.totalMass (μ.record.atoms.map (fun atom => (atom.1, atom.2 * weight atom.1)))
  rw [eventMass_reweight, eventMass_reweight, totalMass_reweight, totalMass_reweight]
  have total := same.expectNat weight
  have mass := same.expectNat (fun x => if event x then weight x else 0)
  change natIntegral μ.record.atoms weight * ν.record.den = natIntegral ν.record.atoms weight * μ.record.den at total
  change natIntegral μ.record.atoms _ * ν.record.den = natIntegral ν.record.atoms _ * μ.record.den at mass
  -- Compare numerator and normalizer after clearing the original positive
  -- denominator. Reduced fractions or a common atom presentation are unneeded.
  apply Nat.eq_of_mul_eq_mul_right μ.record.den_pos
  calc
    _ = natIntegral μ.record.atoms (fun x => if event x then weight x else 0) *
        (natIntegral ν.record.atoms weight * μ.record.den) := by ac_rfl
    _ = natIntegral ν.record.atoms (fun x => if event x then weight x else 0) *
        natIntegral μ.record.atoms weight * μ.record.den := by
          rw [← total]
          calc
            _ = (natIntegral μ.record.atoms (fun x => if event x then weight x else 0) * ν.record.den) *
                natIntegral μ.record.atoms weight := by ac_rfl
            _ = _ := by rw [mass]; ac_rfl

/-- A label-level likelihood can be applied on either side of pushforward.
The map may merge outcomes; all masses in each fibre are still retained. -/
theorem Distro.reweightNat_map (μ : Distro Ω) (f : Ω → X) (weight : X → Nat)
    (positive : 0 < natIntegral (μ.map f).record.atoms weight) :
    ((μ.reweightNat (fun x => weight (f x)) (by simpa only [map, FiniteProbRecord.map, natIntegral_map] using positive)).map f) =
      ((μ.map f).reweightNat weight positive) := by
  apply Distro.eq_of_atoms_den
  · simp only [reweightNat, map, FiniteProbRecord.map, ofWeightedAtoms, List.map_map, Function.comp_def]
  · simp only [reweightNat_den, map, FiniteProbRecord.map, natIntegral_map]

end Thesis.Probability.Distros
