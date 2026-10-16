import Thesis.Probability.Distros.ConditionalMoments
import Thesis.Probability.Distros.RationalClearing

namespace Thesis.Probability.Distros
open Combinatorics

/-- Regrouping by a finite list of distinct labels preserves every weighted
atom occurrence, including repeated outcomes and zero-weight atoms. -/
theorem fibreCells_perm [DecidableEq A] (labels : List A) (key : Ω → A) (atoms : List (Ω × Nat))
    (distinct : labels.Nodup) (covered : ∀ atom ∈ atoms, key atom.1 ∈ labels) :
    (labels.map (fun label => atoms.filter (fun atom => decide (key atom.1 = label)))).flatten.Perm atoms := by
  induction labels generalizing atoms with
  | nil =>
      cases atoms with
      | nil => exact List.Perm.refl _
      | cons atom atoms => exact False.elim (List.not_mem_nil (covered atom (List.mem_cons_self ..)))
  | cons label labels ih =>
      let rest := atoms.filter (fun atom => !decide (key atom.1 = label))
      have unchanged : labels.map (fun other => atoms.filter (fun atom => decide (key atom.1 = other))) =
          labels.map (fun other => rest.filter (fun atom => decide (key atom.1 = other))) := by
        apply List.map_congr_left
        intro other member
        have different : other ≠ label := by
          intro same
          subst other
          exact (List.nodup_cons.mp distinct).1 member
        change atoms.filter (fun atom => decide (key atom.1 = other)) =
          (atoms.filter (fun atom => !decide (key atom.1 = label))).filter (fun atom => decide (key atom.1 = other))
        rw [List.filter_filter]
        apply List.filter_congr
        intro atom _
        by_cases selected : key atom.1 = other
        · simp only [selected, different, decide_true, decide_false, Bool.not_false, Bool.true_and]
        · simp only [selected, decide_false, Bool.false_and]
      have tail := ih rest (List.nodup_cons.mp distinct).2 (by
        intro atom member
        have source := (List.mem_filter.mp member).1
        have rejected := (List.mem_filter.mp member).2
        have absent : key atom.1 ≠ label := by
          intro same
          simp only [same, decide_true, Bool.not_true, Bool.false_eq_true] at rejected
        exact (List.mem_cons.mp (covered atom source)).resolve_left absent)
      simp only [List.map_cons, List.flatten_cons, unchanged]
      exact (tail.append_left _).trans (List.filter_append_perm (fun atom => decide (key atom.1 = label)) atoms)

/-- The actual partition into fibres of a finite-valued observable. -/
def AtomPartition.ofObservable (μ : Distro Ω) (key : Ω → Fin colours) : AtomPartition μ :=
  ⟨(List.finRange colours).map (fun label => μ.record.atoms.filter (fun atom => decide (key atom.1 = label))),
    fibreCells_perm _ key μ.record.atoms (finRange_nodup _) (fun _ _ => List.mem_finRange _)⟩

/-- Conditional expectation as an observable on the original outcome type.
Unsupported fibres have the same explicit zero convention as block means. -/
def Distro.conditionalExpectation (μ : Distro Ω) (key : Ω → Fin colours) (f : Ω → SignedRatio) : Ω → SignedRatio :=
  fun x => conditionalBlockMean (μ.record.atoms.filter (fun atom => decide (key atom.1 = key x))) f

theorem Distro.conditionalExpectation_conditionOn (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (x : Ω)
    (positive : μ.record.EventPositive (fun y => decide (key y = key x))) :
    μ.conditionalExpectation key f x =
      (μ.record.conditionOn (fun y => decide (key y = key x)) positive).rationalMean f :=
  conditionalBlockMean_conditionOn μ _ positive f

theorem rationalAtomSum_constant (atoms : List (Ω × Nat)) (c : SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms (fun _ => c))
      (SignedRatio.scaleNat (FiniteProbRecord.totalMass atoms) c) := by
  have result := FiniteProbRecord.rationalAtomSum_cleared atoms (fun _ => c) (fun _ => c.num)
    c.den c.den_pos (fun _ => SignedRatio.equiv_refl _)
  rw [FiniteProbRecord.signedAtomMass_const] at result
  exact result

theorem rationalAtomSum_byObservable (atoms : List (Ω × Nat)) (key : Ω → Fin colours) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms f)
      (SignedRatio.listSum ((List.finRange colours).map (fun label =>
        FiniteProbRecord.rationalAtomSum (atoms.filter (fun atom => decide (key atom.1 = label))) f))) := by
  have perm := fibreCells_perm (List.finRange colours) key atoms (finRange_nodup _) (fun _ _ => List.mem_finRange _)
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (rationalAtomSum_perm perm f))
    (by simpa only [List.map_map, Function.comp_def] using
      rationalAtomSum_flatten ((List.finRange colours).map (fun label => atoms.filter (fun atom => decide (key atom.1 = label)))) f)

/-- The conditional-mean integral in each fibre equals the original integral. -/
theorem Distro.conditionalExpectation_fibre_integral (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (label : Fin colours) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum
      (μ.record.atoms.filter (fun atom => decide (key atom.1 = label))) (μ.conditionalExpectation key f))
      (FiniteProbRecord.rationalAtomSum (μ.record.atoms.filter (fun atom => decide (key atom.1 = label))) f) := by
  let cell := μ.record.atoms.filter (fun atom => decide (key atom.1 = label))
  have constant : ∀ atom ∈ cell, SignedRatio.Equiv (μ.conditionalExpectation key f atom.1) (conditionalBlockMean cell f) := by
    intro atom member
    have same := of_decide_eq_true (List.mem_filter.mp member).2
    change SignedRatio.Equiv (conditionalBlockMean (μ.record.atoms.filter (fun other => decide (key other.1 = key atom.1))) f) _
    rw [same]
    exact SignedRatio.equiv_refl _
  exact SignedRatio.equiv_trans (rationalAtomSum_congr_on_support cell _ _ constant)
    (SignedRatio.equiv_trans (rationalAtomSum_constant cell (conditionalBlockMean cell f))
      (conditionalBlockMean_weighted cell f))

/-- Conditional expectation preserves integration against every observable
of the conditioning label. This includes unsupported fibres without division. -/
theorem Distro.conditionalExpectation_weighted (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (h : Fin colours → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.mul (h (key x)) (f x)))
      (μ.rationalExpectation (fun x => SignedRatio.mul (h (key x)) (μ.conditionalExpectation key f x))) := by
  apply SignedRatio.divideNat_congr (denominator := μ.record.den) (positive := μ.record.den_pos)
  refine SignedRatio.equiv_trans (rationalAtomSum_byObservable μ.record.atoms key _) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.finRange colours) _ _ (fun label => ?_))
    (SignedRatio.equiv_symm (rationalAtomSum_byObservable μ.record.atoms key _))
  let cell := μ.record.atoms.filter (fun atom => decide (key atom.1 = label))
  have factor (u : Ω → SignedRatio) :
      SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum cell (fun x => SignedRatio.mul (h (key x)) (u x)))
        (SignedRatio.mul (h label) (FiniteProbRecord.rationalAtomSum cell u)) := by
    refine SignedRatio.equiv_trans (rationalAtomSum_congr_on_support cell _ _ ?_) (rationalAtomSum_mul_left cell (h label) u)
    intro atom member
    have same := of_decide_eq_true (List.mem_filter.mp member).2
    rw [same]
    exact SignedRatio.equiv_refl _
  exact SignedRatio.equiv_trans (factor f) (SignedRatio.equiv_trans
    (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (μ.conditionalExpectation_fibre_integral key f label)))
    (SignedRatio.equiv_symm (factor (μ.conditionalExpectation key f))))

/-- The tower law down to the unconditional expectation. -/
theorem Distro.conditionalExpectation_total (μ : Distro Ω) (key : Ω → Fin colours) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (μ.conditionalExpectation key f)) (μ.rationalExpectation f) := by
  have weighted := μ.conditionalExpectation_weighted key f (fun _ => SignedRatio.one)
  have first := SignedRatio.equiv_trans (μ.rationalExpectation_mul_left SignedRatio.one f) (SignedRatio.one_mul _)
  have second := SignedRatio.equiv_trans
    (μ.rationalExpectation_mul_left SignedRatio.one (μ.conditionalExpectation key f)) (SignedRatio.one_mul _)
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm second)
    (SignedRatio.equiv_trans (SignedRatio.equiv_symm weighted) first)

private theorem ratio_mul_sub (a b c : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.mul a (SignedRatio.sub b c))
      (SignedRatio.sub (SignedRatio.mul a b) (SignedRatio.mul a c)) := by
  simp only [SignedRatio.Equiv, SignedRatio.mul, SignedRatio.sub, SignedRatio.add, SignedRatio.neg,
    Int.natCast_mul, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg]
  congr 1 <;> ac_rfl

/-- The conditional residual is orthogonal to every signed rational
function of the conditioning label, including the constant function one. -/
theorem Distro.conditionalExpectation_orthogonal (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (h : Fin colours → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.mul (h (key x))
      (SignedRatio.sub (f x) (μ.conditionalExpectation key f x)))) SignedRatio.zero :=
  SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _
    (fun x => ratio_mul_sub (h (key x)) (f x) (μ.conditionalExpectation key f x)))
    (SignedRatio.equiv_trans (μ.rationalExpectation_sub _ _)
      ((SignedRatio.sub_equiv_zero_iff _ _).mpr (μ.conditionalExpectation_weighted key f h)))

end Thesis.Probability.Distros
