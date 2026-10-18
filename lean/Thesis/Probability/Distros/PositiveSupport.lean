import Thesis.Probability.Distros.RationalConcentration
import Thesis.Probability.Construction

namespace Thesis.Probability.Distros

/-- Zero-weight occurrences impose no comparison obligation. This changes
integration lemmas, without removing atoms or changing any declared domain. -/
theorem natIntegral_congr_positive (atoms : List (Ω × Nat)) (f g : Ω → Nat)
    (same : ∀ atom ∈ atoms, 0 < atom.2 → f atom.1 = g atom.1) :
    natIntegral atoms f = natIntegral atoms g := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      change atom.2 * f atom.1 + natIntegral atoms f = atom.2 * g atom.1 + natIntegral atoms g
      rw [ih (fun other member => same other (List.mem_cons_of_mem _ member))]
      by_cases zero : atom.2 = 0
      · simp only [zero, Nat.zero_mul]
      · rw [same atom (List.mem_cons_self ..) (Nat.pos_of_ne_zero zero)]

theorem Distro.expectNat_congr_positive (μ : Distro Ω) (f g : Ω → Nat)
    (same : μ.AlmostSurely (fun x => f x = g x)) : μ.expectNat f = μ.expectNat g := by
  simp only [expectNat, natIntegral_congr_positive _ _ _ same]

theorem rationalIntegral_congr_positive (atoms : List (Ω × Nat)) (f g : Ω → QProb)
    (same : ∀ atom ∈ atoms, 0 < atom.2 → QProb.Equiv (f atom.1) (g atom.1)) :
    QProb.Equiv (rationalIntegral atoms f) (rationalIntegral atoms g) := by
  induction atoms with
  | nil => exact QProb.equiv_refl _
  | cons atom atoms ih =>
      apply QProb.add_congr
      · by_cases zero : atom.2 = 0
        · simp only [QProb.Equiv, QProb.scale, zero, Nat.zero_mul]
        · exact QProb.scale_congr _ (same atom (List.mem_cons_self ..) (Nat.pos_of_ne_zero zero))
      · exact ih (fun other member => same other (List.mem_cons_of_mem _ member))

theorem Distro.expectation_congr_positive (μ : Distro Ω) (f g : Ω → QProb)
    (same : μ.AlmostSurely (fun x => QProb.Equiv (f x) (g x))) :
    QProb.Equiv (μ.expectation f) (μ.expectation g) :=
  QProb.div_congr (rationalIntegral_congr_positive _ _ _ same) (QProb.equiv_refl _) _ _

theorem Distro.probVal_congr_positive (μ : Distro Ω) (left right : Event Ω)
    (same : μ.AlmostSurely (fun x => left x = right x)) :
    QProb.Equiv (μ.record.probVal left) (μ.record.probVal right) := by
  have mass : FiniteProbRecord.eventMass μ.record.atoms left = FiniteProbRecord.eventMass μ.record.atoms right := by
    rw [← natIntegral_indicator, ← natIntegral_indicator]
    apply natIntegral_congr_positive
    intro atom member weight
    rw [same atom member weight]
  change FiniteProbRecord.eventMass μ.record.atoms left * μ.record.den =
    FiniteProbRecord.eventMass μ.record.atoms right * μ.record.den
  rw [mass]

theorem Distro.pmf_zero_of_almostSure_ne [DecidableEq Ω] (μ : Distro Ω) (value : Ω)
    (avoids : μ.AlmostSurely (fun x => x ≠ value)) : QProb.Equiv (μ.pmf value) QProb.zero :=
  QProb.equiv_trans (μ.probVal_congr_positive (FiniteProbRecord.singletonEvent value) (fun _ => false)
    (fun atom member weight => by
      have different := avoids atom member weight
      simp only [FiniteProbRecord.singletonEvent, different, decide_false])) μ.record.probVal_false

/-- Singleton probabilities determine a finite record's law even when the
ambient type is infinite. The finite carrier is built from both original
atom lists, retaining coverage of all zero-weight labels. -/
theorem Distro.sameLaw_of_pmf [DecidableEq Ω] (μ ν : Distro Ω)
    (same : ∀ value, QProb.Equiv (μ.pmf value) (ν.pmf value)) : μ.SameLaw ν := by
  let values := deduplicate (μ.record.atoms.map Prod.fst ++ ν.record.atoms.map Prod.fst)
  have first : ∀ atom ∈ μ.record.atoms, atom.1 ∈ values := fun atom member =>
    (mem_deduplicate _ _).mpr (List.mem_append_left _ (List.mem_map.mpr ⟨atom, member, rfl⟩))
  have second : ∀ atom ∈ ν.record.atoms, atom.1 ∈ values := fun atom member =>
    (mem_deduplicate _ _).mpr (List.mem_append_right _ (List.mem_map.mpr ⟨atom, member, rfl⟩))
  intro event
  have expand (ρ : Distro Ω) (covered : ∀ atom ∈ ρ.record.atoms, atom.1 ∈ values) :
      QProb.Equiv (ρ.record.probVal event)
        (QProb.listSum ((values.filter event).map (fun value => ρ.pmf value))) := by
    refine QProb.equiv_trans (ρ.probVal_congr_on_support event (FiniteProbRecord.membershipEvent (values.filter event)) ?_)
      (ρ.record.probVal_membership_equiv_listSum (values.filter event)
        (List.Sublist.nodup List.filter_sublist (deduplicate_nodup _)))
    intro atom member
    cases selected : event atom.1 <;>
      simp [FiniteProbRecord.membershipEvent, List.mem_filter, covered atom member, selected]
  exact QProb.equiv_trans (expand μ first)
    (QProb.equiv_trans (QProb.listSum_map_congr (values.filter event) _ _ same) (QProb.equiv_symm (expand ν second)))

end Thesis.Probability.Distros
