import Thesis.Probability.Distros.ProbabilityGrid
import Thesis.Probability.Distros.FinitePmfExpectation

namespace Thesis.Probability.Distros

/-- Enumerating a list by bounded indices visits every occurrence once.
The default is never used within the index range. -/
theorem range_getD_map (cells : List A) (default : A) (f : A → B) :
    (List.range cells.length).map (fun i => f (cells.getD i default)) = cells.map f := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i left right
    have within : i < cells.length := by simpa only [List.length_map] using right
    simp only [List.getElem_map, List.getElem_range]
    exact congrArg f (List.getElem_eq_getD (h := within) default).symm

private theorem probabilityList_normalized (cells : List A) (default : A) (probabilities : A → QProb)
    (nonempty : 0 < cells.length) (normalized : QProb.Equiv (QProb.listSum (cells.map probabilities)) QProb.one) :
    QProb.Equiv (QProb.listSum ((List.range (cells.length - 1 + 1)).map
      (fun i => probabilities (cells.getD i default)))) QProb.one := by
  rw [Nat.sub_add_cancel (by omega), range_getD_map]
  exact normalized

/-- Normalized rational masses on an arbitrary nonempty finite list.
Every occurrence is retained, including repetitions and zero-weight cells. -/
def probabilityList (cells : List A) (default : A) (probabilities : A → QProb)
    (nonempty : 0 < cells.length) (normalized : QProb.Equiv (QProb.listSum (cells.map probabilities)) QProb.one) : Distro A :=
  (probabilityGrid (cells.length - 1) (fun i => probabilities (cells.getD i default))
    (probabilityList_normalized cells default probabilities nonempty normalized)).map (fun i => cells.getD i default)

theorem probabilityList_supported (cells : List A) (default : A) (probabilities : A → QProb)
    (nonempty : 0 < cells.length) (normalized : QProb.Equiv (QProb.listSum (cells.map probabilities)) QProb.one) :
    (probabilityList cells default probabilities nonempty normalized).AlmostSurely (fun cell => cell ∈ cells) := by
  intro atom member weight
  rcases List.mem_map.mp member with ⟨source, listed, same⟩
  cases same
  have bounded := probabilityGrid_bounded (cells.length - 1) (fun i => probabilities (cells.getD i default))
    (probabilityList_normalized cells default probabilities nonempty normalized) source listed weight
  have within : source.1 < cells.length := by omega
  change cells.getD source.1 default ∈ cells
  rw [← List.getElem_eq_getD (h := within) default]
  exact List.getElem_mem within

theorem probabilityList_retains (cells : List A) (default : A) (probabilities : A → QProb)
    (nonempty : 0 < cells.length) (normalized : QProb.Equiv (QProb.listSum (cells.map probabilities)) QProb.one)
    (cell : A) (member : cell ∈ cells) :
    ∃ weight, (cell, weight) ∈ (probabilityList cells default probabilities nonempty normalized).record.atoms := by
  obtain ⟨i, within, same⟩ := List.getElem_of_mem member
  obtain ⟨weight, listed⟩ := probabilityGrid_retains (cells.length - 1) (fun i => probabilities (cells.getD i default))
    (probabilityList_normalized cells default probabilities nonempty normalized) i (by omega)
  refine ⟨weight, List.mem_map.mpr ⟨(i, weight), listed, ?_⟩⟩
  change (cells.getD i default, weight) = (cell, weight)
  rw [← List.getElem_eq_getD (h := within) default, same]

theorem probabilityList_expectation (cells : List A) (default : A) (probabilities : A → QProb)
    (nonempty : 0 < cells.length) (normalized : QProb.Equiv (QProb.listSum (cells.map probabilities)) QProb.one)
    (f : A → SignedRatio) :
    SignedRatio.Equiv ((probabilityList cells default probabilities nonempty normalized).rationalExpectation f)
      (SignedRatio.listSum (cells.map (fun cell => SignedRatio.mul (probabilities cell).toSignedRatio (f cell)))) := by
  unfold probabilityList
  rw [Distro.rationalExpectation_map]
  refine SignedRatio.equiv_trans (Distro.rationalExpectation_bounded_pmf _ (cells.length - 1)
    (probabilityGrid_bounded (cells.length - 1) (fun i => probabilities (cells.getD i default))
      (probabilityList_normalized cells default probabilities nonempty normalized)) (fun i => f (cells.getD i default))) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem (List.range (cells.length - 1 + 1)) _
    (fun i => SignedRatio.mul (probabilities (cells.getD i default)).toSignedRatio (f (cells.getD i default))) ?_) ?_
  · intro i member
    exact SignedRatio.mul_congr (QProb.toSignedRatio_congr (probabilityGrid_pmf (cells.length - 1)
      (fun i => probabilities (cells.getD i default)) (probabilityList_normalized cells default probabilities nonempty normalized)
      i (by have upper := List.mem_range.mp member; omega))) (SignedRatio.equiv_refl _)
  · rw [Nat.sub_add_cancel (by omega),
      range_getD_map cells default (fun cell => SignedRatio.mul (probabilities cell).toSignedRatio (f cell))]
    exact SignedRatio.equiv_refl _

end Thesis.Probability.Distros
