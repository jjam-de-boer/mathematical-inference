import Thesis.Probability.Distros.RationalSimplex

/-!
Convert rational simplex assignments to finite weighted probability laws.

A signed rational assignment satisfying nonnegativity and normalization is
encoded as natural weights on a nonempty listed grid. Nonnegativity is
essential: the total helper `massProbability` truncates negative integer
numerators, and its representation theorem assumes they are nonnegative.
The construction retains zero-weight occurrences and permits repeated cell
labels. Its expectation formula sums over occurrences. The converse PMF
vector is a simplex only when the listed labels are distinct and support
the original law, preventing duplicate labels from counting mass twice.
-/

namespace Thesis.Probability.Distros

/-- A signed presentation is converted only under a nonnegativity proof
when used by the grid constructor. Negative auxiliary coefficients are never
installed as probability weights. -/
def massProbability (value : SignedRatio) : QProb := ⟨value.num.toNat, value.den, value.den_pos⟩

theorem massProbability_spec (value : SignedRatio) (positive : SignedRatio.Nonnegative value) :
    SignedRatio.Equiv (massProbability value).toSignedRatio value := by
  change (value.num.toNat : Int) * value.den = value.num * value.den
  rw [Int.toNat_of_nonneg positive]

/-- Read a finite simplex coordinate at a natural index, defaulting to
zero outside the vector. Correct recovery in range uses the simplex's
nonnegativity assumption through massProbability_spec. -/
def indexedMassProbability (values : Fin variables → SignedRatio) (i : Nat) : QProb :=
  if within : i < variables then massProbability (values ⟨i, within⟩) else QProb.zero

private theorem mass_sum_embedding (values : List QProb) :
    (QProb.listSum values).toSignedRatio = SignedRatio.listSum (values.map QProb.toSignedRatio) := by
  induction values with
  | nil => rfl
  | cons value values ih => rw [QProb.listSum, QProb.toSignedRatio_add, List.map_cons, SignedRatio.listSum, ih]

theorem simplex_sum (values : Fin variables → SignedRatio) (simplex : RationalLinear.Simplex values) :
    SignedRatio.Equiv (SignedRatio.listSum ((List.finRange variables).map values)) SignedRatio.one := by
  have expanded := SignedRatio.equiv_trans (RationalLinear.dot_sum variables (fun _ => 1) values)
    (SignedRatio.listSum_map_congr (List.finRange variables) _ values (fun i => SignedRatio.one_scaleInt (values i)))
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm expanded) simplex.2

/-- The simplex constraints make the converted nonnegative coordinates
sum to one as rational probabilities. No rounding or clipping error remains
under those constraints. -/
theorem indexedMassProbability_normalized (values : Fin variables → SignedRatio) (simplex : RationalLinear.Simplex values) :
    QProb.Equiv (QProb.listSum ((List.range variables).map (indexedMassProbability values))) QProb.one := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  rw [mass_sum_embedding, List.map_map]
  simp only [Function.comp_def]
  rw [← finRange_val_map variables (fun i => (indexedMassProbability values i).toSignedRatio)]
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.finRange variables) _ values ?_) (simplex_sum values simplex)
  intro i
  simp only [indexedMassProbability, dif_pos i.isLt]
  exact massProbability_spec (values i) (simplex.1 i)

private theorem massGrid_normalized (values : Fin variables → SignedRatio) (simplex : RationalLinear.Simplex values)
    (nonempty : 0 < variables) :
    QProb.Equiv (QProb.listSum ((List.range (variables - 1 + 1)).map (indexedMassProbability values))) QProb.one := by
  rw [Nat.sub_add_cancel (by omega)]
  exact indexedMassProbability_normalized values simplex

/-- Turn a computed simplex assignment into a genuine finite weighted law.
Each grid occurrence is retained, including zero weights. -/
def simplexGrid (cells : List A) (default : A) (values : Fin cells.length → SignedRatio)
    (simplex : RationalLinear.Simplex values) (nonempty : 0 < cells.length) : Distro A :=
  (probabilityGrid (cells.length - 1) (indexedMassProbability values) (massGrid_normalized values simplex nonempty)).map
    (fun i => cells.getD i default)

theorem simplexGrid_supported (cells : List A) (default : A) (values : Fin cells.length → SignedRatio)
    (simplex : RationalLinear.Simplex values) (nonempty : 0 < cells.length) :
    (simplexGrid cells default values simplex nonempty).AlmostSurely (fun cell => cell ∈ cells) := by
  intro atom member weight
  rcases List.mem_map.mp member with ⟨source, listed, same⟩
  cases same
  have bounded := probabilityGrid_bounded (cells.length - 1) (indexedMassProbability values)
    (massGrid_normalized values simplex nonempty) source listed weight
  have within : source.1 < cells.length := by omega
  change cells.getD source.1 default ∈ cells
  rw [← List.getElem_eq_getD (h := within) default]
  exact List.getElem_mem within

/-- Every listed cell has a record occurrence even when its weight is
zero. This retention assertion does not claim positive support for that cell. -/
theorem simplexGrid_retains (cells : List A) (default : A) (values : Fin cells.length → SignedRatio)
    (simplex : RationalLinear.Simplex values) (nonempty : 0 < cells.length) (cell : A) (member : cell ∈ cells) :
    ∃ weight, (cell, weight) ∈ (simplexGrid cells default values simplex nonempty).record.atoms := by
  obtain ⟨i, within, same⟩ := List.getElem_of_mem member
  obtain ⟨weight, listed⟩ := probabilityGrid_retains (cells.length - 1) (indexedMassProbability values)
    (massGrid_normalized values simplex nonempty) i (by omega)
  refine ⟨weight, List.mem_map.mpr ⟨(i, weight), listed, ?_⟩⟩
  change (cells.getD i default, weight) = (cell, weight)
  rw [← List.getElem_eq_getD (h := within) default, same]

/-- Expectations are exactly the finite coordinate sum, including repeated
labels and zero weights. The default cell cannot affect an in-range coordinate. -/
theorem simplexGrid_expectation (cells : List A) (default : A) (values : Fin cells.length → SignedRatio)
    (simplex : RationalLinear.Simplex values) (nonempty : 0 < cells.length) (f : A → SignedRatio) :
    SignedRatio.Equiv ((simplexGrid cells default values simplex nonempty).rationalExpectation f)
      (SignedRatio.listSum ((List.finRange cells.length).map (fun i => SignedRatio.mul (values i) (f (cells.getD i.val default))))) := by
  unfold simplexGrid
  rw [Distro.rationalExpectation_map]
  refine SignedRatio.equiv_trans (Distro.rationalExpectation_bounded_pmf _ (cells.length - 1)
    (probabilityGrid_bounded (cells.length - 1) (indexedMassProbability values) (massGrid_normalized values simplex nonempty))
    (fun i => f (cells.getD i default))) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem (List.range (cells.length - 1 + 1)) _
    (fun i => SignedRatio.mul (indexedMassProbability values i).toSignedRatio (f (cells.getD i default))) ?_) ?_
  · intro i member
    exact SignedRatio.mul_congr (QProb.toSignedRatio_congr (probabilityGrid_pmf (cells.length - 1)
      (indexedMassProbability values) (massGrid_normalized values simplex nonempty) i (by have upper := List.mem_range.mp member; omega)))
      (SignedRatio.equiv_refl _)
  · rw [Nat.sub_add_cancel (by omega), ← finRange_val_map cells.length
      (fun i => SignedRatio.mul (indexedMassProbability values i).toSignedRatio (f (cells.getD i default)))]
    apply SignedRatio.listSum_map_congr
    intro i
    simp only [indexedMassProbability, dif_pos i.isLt]
    exact SignedRatio.mul_congr (massProbability_spec (values i) (simplex.1 i)) (SignedRatio.equiv_refl _)

theorem simplexGrid_integer_expectation (cells : List A) (default : A) (values : Fin cells.length → SignedRatio)
    (simplex : RationalLinear.Simplex values) (nonempty : 0 < cells.length) (response : A → Int) :
    SignedRatio.Equiv ((simplexGrid cells default values simplex nonempty).rationalExpectation (fun x => ⟨response x, 1, Nat.zero_lt_one⟩))
      (RationalLinear.dot cells.length (fun i => response (cells.getD i.val default)) values) :=
  SignedRatio.equiv_trans (simplexGrid_expectation cells default values simplex nonempty _)
    (SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.finRange cells.length) _ _
      (fun _ => SignedRatio.mul_comm _ _)) (SignedRatio.equiv_symm (RationalLinear.dot_sum _ _ _)))

/-- Read an arbitrary grid-supported law as its vector of rational PMFs. -/
def gridMasses [DecidableEq A] (μ : Distro A) (cells : List A) (default : A) : Fin cells.length → SignedRatio :=
  fun i => (μ.pmf (cells.getD i.val default)).toSignedRatio

theorem gridMasses_integer_expectation [DecidableEq A] (μ : Distro A) (cells : List A) (default : A)
    (distinct : cells.Nodup) (support : μ.AlmostSurely (fun cell => cell ∈ cells)) (response : A → Int) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => ⟨response x, 1, Nat.zero_lt_one⟩))
      (RationalLinear.dot cells.length (fun i => response (cells.getD i.val default)) (gridMasses μ cells default)) := by
  refine SignedRatio.equiv_trans (μ.rationalExpectation_grid_pmf cells distinct support _) ?_
  rw [← finRange_getD_map cells default (fun cell => SignedRatio.mul (μ.pmf cell).toSignedRatio ⟨response cell, 1, Nat.zero_lt_one⟩)]
  exact SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ (fun _ => SignedRatio.mul_comm _ _))
    (SignedRatio.equiv_symm (RationalLinear.dot_sum _ _ _))

/-- Recover a normalized simplex from singleton probabilities on a distinct
supporting grid. Distinctness prevents repeated PMF entries from double-counting mass. -/
theorem gridMasses_simplex [DecidableEq A] (μ : Distro A) (cells : List A) (default : A)
    (distinct : cells.Nodup) (support : μ.AlmostSurely (fun cell => cell ∈ cells)) :
    RationalLinear.Simplex (gridMasses μ cells default) :=
  ⟨fun _ => QProb.toSignedRatio_nonnegative _,
    SignedRatio.equiv_trans (SignedRatio.equiv_symm (gridMasses_integer_expectation μ cells default distinct support (fun _ => 1)))
      (μ.rationalExpectation_constant SignedRatio.one)⟩

end Thesis.Probability.Distros
