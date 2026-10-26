import Thesis.Probability.Distros.ConditionalInformation
import Thesis.Probability.Distros.EntropyContinuity
import Thesis.Probability.ConstructivePermutation

namespace Thesis.Probability.Distros

open FiniteProbRecord

/-!
# Data-processing for exact finite Shannon entropy

A deterministic map cannot increase Shannon entropy on a complete finite
grid.  The inequality is the grouping of fibres; it does not interpret the
map as a causal mechanism and does not require positivity of fibre masses.
-/

variable {A : Type u} {B : Type v}

def EntropyGrid.fiber [DecidableEq B] (source : EntropyGrid A) (f : A → B) (value : B) : List A :=
  source.cells.filter (fun cell => decide (f cell = value))

theorem EntropyGrid.fiber_nodup [DecidableEq B] (source : EntropyGrid A) (f : A → B) (value : B) :
    (source.fiber f value).Nodup :=
  List.Sublist.nodup List.filter_sublist source.distinct

private theorem fiber_mem_iff [DecidableEq B] (source : EntropyGrid A) (f : A → B)
    (value : B) (cell : A) :
    cell ∈ source.fiber f value ↔ cell ∈ source.cells ∧ f cell = value := by
  simp only [EntropyGrid.fiber, List.mem_filter, decide_eq_true_eq]

private theorem covers_flatMap_mem [DecidableEq B] (source : EntropyGrid A)
    (target : EntropyGrid B) (f : A → B)
    (covers : ∀ cell ∈ source.cells, f cell ∈ target.cells) (cell : A) :
    cell ∈ source.cells ↔
      cell ∈ target.cells.flatMap (fun value => source.fiber f value) := by
  constructor
  · intro listed
    exact List.mem_flatMap.mpr ⟨f cell, covers cell listed,
      (fiber_mem_iff source f (f cell) cell).mpr ⟨listed, rfl⟩⟩
  · intro listed
    rcases List.mem_flatMap.mp listed with ⟨_, _, member⟩
    exact ((fiber_mem_iff source f _ cell).mp member).1

private theorem fiber_flatMap_nodup_list [DecidableEq B] (source : List A)
    (sourceNodup : source.Nodup) (target : List B) (targetNodup : target.Nodup)
    (f : A → B) :
    (target.flatMap (fun value => source.filter (fun cell => decide (f cell = value)))).Nodup := by
  induction target with
  | nil => simp
  | cons head rest ih =>
      have parts := List.nodup_cons.mp targetNodup
      simp only [List.flatMap_cons]
      refine (List.nodup_append).mpr ⟨List.Sublist.nodup List.filter_sublist sourceNodup, ih parts.2, ?_⟩
      intro cell listed otherCell later
      intro sameCell
      subst sameCell
      rcases List.mem_flatMap.mp later with ⟨other, otherListed, otherFiber⟩
      have sameHead : f cell = head := of_decide_eq_true (List.mem_filter.mp listed).2
      have sameOther : f cell = other := of_decide_eq_true (List.mem_filter.mp otherFiber).2
      exact parts.1 (sameHead.symm.trans sameOther ▸ otherListed)

private theorem fiber_flatMap_nodup [DecidableEq B] (source : EntropyGrid A)
    (target : EntropyGrid B) (f : A → B) :
    (target.cells.flatMap (fun value => source.fiber f value)).Nodup :=
  fiber_flatMap_nodup_list source.cells source.distinct target.cells target.distinct f

theorem Distro.map_pmf_fiber [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (complete : ∀ value, value ∈ source.cells)
    (value : B) :
    QProb.Equiv ((μ.map f).pmf value)
      (QProb.listSum ((source.fiber f value).map μ.pmf)) := by
  refine QProb.equiv_trans (μ.map_pmf f value) ?_
  simpa only [EntropyGrid.fiber, Distro.pmf, singletonEvent] using
    μ.record.probVal_equiv_listSum_singletons source.cells source.distinct complete
      (fun cell => decide (f cell = value))

/-- Grouping identity: source entropy is the sum of fibre entropy-sums. -/
theorem Distro.entropy_fiber_regroup [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (target : EntropyGrid B)
    (sourceSupport : μ.AlmostSurely (fun value => value ∈ source.cells))
    (targetComplete : ∀ value, value ∈ target.cells) :
    ExactLog.Equiv (μ.entropy source sourceSupport)
      (ExactLog.listSum (target.cells.map (fun value =>
        entropySum ((source.fiber f value).map μ.pmf)))) := by
  have covers : ∀ cell ∈ source.cells, f cell ∈ target.cells :=
    fun cell _ => targetComplete (f cell)
  have permutation : source.cells.Perm (target.cells.flatMap (fun value => source.fiber f value)) :=
    ConstructivePermutation.perm_of_nodup_mem_iff source.cells
      (target.cells.flatMap (fun value => source.fiber f value))
      source.distinct (fiber_flatMap_nodup source target f)
      (fun cell => covers_flatMap_mem source target f covers cell)
  have permuted := entropySum_perm (permutation.map μ.pmf)
  have sourceEq : μ.entropy source sourceSupport = entropySum (source.cells.map μ.pmf) := by
    simp only [Distro.entropy, entropySum, List.map_map, Function.comp_def]
  have flattened :
      entropySum ((target.cells.flatMap (fun value => source.fiber f value)).map μ.pmf) =
        ExactLog.listSum (target.cells.map (fun value => entropySum ((source.fiber f value).map μ.pmf))) := by
    rw [List.map_flatMap]
    exact entropySum_flatMap target.cells (fun value => (source.fiber f value).map μ.pmf)
  rw [sourceEq]
  exact ExactLog.equiv_trans permuted (by rw [flattened]; exact ExactLog.equiv_refl _)

theorem Distro.entropy_map_fiber_terms [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (target : EntropyGrid B)
    (targetSupport : (μ.map f).AlmostSurely (fun value => value ∈ target.cells))
    (sourceComplete : ∀ value, value ∈ source.cells) :
    ExactLog.Equiv ((μ.map f).entropy target targetSupport)
      (ExactLog.listSum (target.cells.map (fun value =>
        entropyTerm (QProb.listSum ((source.fiber f value).map μ.pmf))))) := by
  unfold Distro.entropy
  apply ExactLog.listSum_map_congr
  intro value _
  exact entropyTerm_congr (μ.map_pmf_fiber f source sourceComplete value)

/-- Extra entropy inside the fibres of a deterministic map.  This is the
conditional entropy `H(source | f(source))` as a grouping remainder. -/
def Distro.conditionalEntropyMap [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (target : EntropyGrid B) : ExactLog :=
  ExactLog.listSum (target.cells.map fun value =>
    ExactLog.sub
      (entropySum ((source.fiber f value).map μ.pmf))
      (entropyTerm (QProb.listSum ((source.fiber f value).map μ.pmf))))

theorem Distro.conditionalEntropyMap_nonneg [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (target : EntropyGrid B) :
    ExactLog.LE ExactLog.zero (μ.conditionalEntropyMap f source target) := by
  apply ExactLog.listSum_map_nonnegative
  intro _ _
  exact (ExactLog.zero_le_sub_iff _ _).mpr (entropySum_ge_term _)

/-- Finite chain rule for a deterministic map: `H(source) = H(f(source)) + H(source|f)`. -/
theorem Distro.entropy_map_chain [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (target : EntropyGrid B)
    (sourceSupport : μ.AlmostSurely (fun value => value ∈ source.cells))
    (targetSupport : (μ.map f).AlmostSurely (fun value => value ∈ target.cells))
    (sourceComplete : ∀ value, value ∈ source.cells)
    (targetComplete : ∀ value, value ∈ target.cells) :
    ExactLog.Equiv (μ.entropy source sourceSupport)
      (ExactLog.add ((μ.map f).entropy target targetSupport)
        (μ.conditionalEntropyMap f source target)) := by
  have fibers := μ.entropy_fiber_regroup f source target sourceSupport targetComplete
  have mapped := μ.entropy_map_fiber_terms f source target targetSupport sourceComplete
  have remainder :
      ExactLog.Equiv (μ.conditionalEntropyMap f source target)
        (ExactLog.sub
          (ExactLog.listSum (target.cells.map (fun value =>
            entropySum ((source.fiber f value).map μ.pmf))))
          (ExactLog.listSum (target.cells.map (fun value =>
            entropyTerm (QProb.listSum ((source.fiber f value).map μ.pmf)))))) :=
    ExactLog.listSum_map_sub target.cells
      (fun value => entropySum ((source.fiber f value).map μ.pmf))
      (fun value => entropyTerm (QProb.listSum ((source.fiber f value).map μ.pmf)))
  have split :
      ExactLog.Equiv
        (ExactLog.add ((μ.map f).entropy target targetSupport)
          (μ.conditionalEntropyMap f source target))
        (ExactLog.add
          (ExactLog.listSum (target.cells.map (fun value =>
            entropyTerm (QProb.listSum ((source.fiber f value).map μ.pmf)))))
          (ExactLog.sub
            (ExactLog.listSum (target.cells.map (fun value =>
              entropySum ((source.fiber f value).map μ.pmf))))
            (ExactLog.listSum (target.cells.map (fun value =>
              entropyTerm (QProb.listSum ((source.fiber f value).map μ.pmf))))))) :=
    ExactLog.add_congr mapped remainder
  have cancelled := ExactLog.add_sub_cancel
    (ExactLog.listSum (target.cells.map (fun value =>
      entropySum ((source.fiber f value).map μ.pmf))))
    (ExactLog.listSum (target.cells.map (fun value =>
      entropyTerm (QProb.listSum ((source.fiber f value).map μ.pmf)))))
  exact ExactLog.equiv_trans fibers (ExactLog.equiv_symm (ExactLog.equiv_trans split cancelled))

/-- Information loss of a deterministic map is the fibre remainder
`H(source) - H(f(source))`. -/
theorem Distro.entropy_map_information_loss [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (target : EntropyGrid B)
    (sourceSupport : μ.AlmostSurely (fun value => value ∈ source.cells))
    (targetSupport : (μ.map f).AlmostSurely (fun value => value ∈ target.cells))
    (sourceComplete : ∀ value, value ∈ source.cells)
    (targetComplete : ∀ value, value ∈ target.cells) :
    ExactLog.Equiv (μ.conditionalEntropyMap f source target)
      (ExactLog.sub (μ.entropy source sourceSupport)
        ((μ.map f).entropy target targetSupport)) :=
  ExactLog.equiv_symm (ExactLog.sub_eq_of_add
    (μ.entropy_map_chain f source target sourceSupport targetSupport
      sourceComplete targetComplete))

/-- Shannon entropy of a pushforward cannot exceed the source entropy. -/
theorem Distro.entropy_map_le [DecidableEq A] [DecidableEq B]
    (μ : Distro A) (f : A → B) (source : EntropyGrid A) (target : EntropyGrid B)
    (sourceSupport : μ.AlmostSurely (fun value => value ∈ source.cells))
    (targetSupport : (μ.map f).AlmostSurely (fun value => value ∈ target.cells))
    (sourceComplete : ∀ value, value ∈ source.cells)
    (targetComplete : ∀ value, value ∈ target.cells) :
    ExactLog.LE ((μ.map f).entropy target targetSupport) (μ.entropy source sourceSupport) :=
  (ExactLog.le_congr (ExactLog.equiv_refl _)
    (ExactLog.equiv_symm (μ.entropy_map_chain f source target sourceSupport targetSupport
      sourceComplete targetComplete))).mp
    (ExactLog.le_add_of_nonneg_right _ _ (μ.conditionalEntropyMap_nonneg f source target))

end Thesis.Probability.Distros
