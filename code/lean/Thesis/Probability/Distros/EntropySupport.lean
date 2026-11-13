import Thesis.Probability.Distros.EntropyUniform
import Thesis.Probability.FiniteRecordSupport

namespace Thesis.Probability.Distros

/-- Keep a decidable subset for an internal proof. This does not change a
caller's declared grid or any atom record. -/
def EntropyGrid.restrict (grid : EntropyGrid A) (selected : A → Bool) : EntropyGrid A :=
  ⟨grid.cells.filter selected, List.Sublist.nodup List.filter_sublist grid.distinct⟩

private theorem logSum_filter (values : List A) (selected : A → Bool) (f : A → ExactLog)
    (vanishes : ∀ value ∈ values, selected value = false → ExactLog.Equiv (f value) ExactLog.zero) :
    ExactLog.Equiv (ExactLog.listSum ((values.filter selected).map f)) (ExactLog.listSum (values.map f)) := by
  induction values with
  | nil => exact ExactLog.equiv_refl _
  | cons head rest ih =>
      have tail := ih (fun value member => vanishes value (List.mem_cons_of_mem _ member))
      cases chosen : selected head with
      | true => simpa only [List.filter_cons, chosen, List.map_cons, ExactLog.listSum] using
          ExactLog.add_congr (ExactLog.equiv_refl (f head)) tail
      | false =>
          simp only [List.filter_cons, chosen, List.map_cons, ExactLog.listSum]
          have zero := vanishes head (List.mem_cons_self ..) chosen
          have erased := ExactLog.add_congr zero (ExactLog.equiv_refl (ExactLog.listSum (rest.map f)))
          rw [ExactLog.zero_add] at erased
          exact ExactLog.equiv_trans tail (ExactLog.equiv_symm erased)

/-- Removing only zero-mass cells for a proof leaves entropy unchanged. -/
theorem Distro.entropy_restrict [DecidableEq A] (μ : Distro A) (grid : EntropyGrid A) (selected : A → Bool)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (restricted : μ.AlmostSurely (fun value => value ∈ (grid.restrict selected).cells))
    (vanishes : ∀ value ∈ grid.cells, selected value = false → (μ.pmf value).num = 0) :
    ExactLog.Equiv (μ.entropy (grid.restrict selected) restricted) (μ.entropy grid support) :=
  logSum_filter grid.cells selected (fun value => entropyTerm (μ.pmf value))
    (fun value member absent => by
      change ExactLog.Equiv (entropyTerm (μ.pmf value)) ExactLog.zero
      rw [entropyTerm_zero_num _ (vanishes value member absent)]
      exact ExactLog.equiv_refl _)

theorem Distro.pmf_pos_of_atom [DecidableEq A] (μ : Distro A) (atom : A × Nat)
    (listed : atom ∈ μ.record.atoms) (positive : 0 < atom.2) : 0 < (μ.pmf atom.1).num :=
  (FiniteProbRecord.eventMass_pos_iff_exists_atom μ.record.atoms _).mpr
    ⟨atom, listed, positive, by simp [FiniteProbRecord.singletonEvent]⟩

end Thesis.Probability.Distros
