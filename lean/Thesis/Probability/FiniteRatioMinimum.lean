import Thesis.Probability.Core

namespace Thesis
namespace Probability
namespace FiniteRatioMinimum

/-!
# A constructive minimum among explicitly supplied rational ratios

Support reduction must choose the largest feasible perturbation step, which
amounts to minimizing a weight divided by a positive direction coefficient.
The ratios may exceed one; only their stored denominators must be positive.
`QProb` supplies exactly this nonnegative fraction arithmetic, without a
normalization or probability-one premise.

An explicit initial candidate makes the finite list nonempty.  The program
compares natural cross-products and retains an actual candidate; it never
selects an argmin from an existential proposition.  Bounds range over precisely
the supplied list plus that initial candidate.  A caller claiming a minimum
over an entire finite domain must also prove its enumeration complete.
-/

def select (value : α → QProb) (initial : α) : List α → α
  | [] => initial
  | candidate :: candidates =>
      if (value candidate).num * (value initial).den ≤ (value initial).num * (value candidate).den then
        select value candidate candidates
      else select value initial candidates

/-- The selected value is no larger than the initial value or any listed
value.  Reverse comparisons use decidable natural arithmetic, not a global
decision principle for propositions about the candidate type. -/
theorem select_bounds (value : α → QProb) (initial : α) (candidates : List α) :
    QProb.LE (value (select value initial candidates)) (value initial) ∧
      forall candidate, candidate ∈ candidates → QProb.LE (value (select value initial candidates)) (value candidate) := by
  induction candidates generalizing initial with
  | nil =>
      refine ⟨QProb.le_refl _, ?_⟩
      intro candidate impossible
      cases impossible
  | cons head tail inductionHypothesis =>
      by_cases better : (value head).num * (value initial).den ≤ (value initial).num * (value head).den
      · rw [select, if_pos better]
        have bounds := inductionHypothesis head
        refine ⟨QProb.le_trans bounds.1 better, ?_⟩
        intro candidate listed
        rcases List.mem_cons.mp listed with same | later
        · subst candidate; exact bounds.1
        · exact bounds.2 candidate later
      · rw [select, if_neg better]
        have bounds := inductionHypothesis initial
        have reversed : QProb.LE (value initial) (value head) := by
          change (value initial).num * (value head).den ≤ (value head).num * (value initial).den
          omega
        refine ⟨bounds.1, ?_⟩
        intro candidate listed
        rcases List.mem_cons.mp listed with same | later
        · subst candidate; exact QProb.le_trans bounds.1 reversed
        · exact bounds.2 candidate later

theorem select_mem (value : α → QProb) (initial : α) (candidates : List α) :
    select value initial candidates ∈ initial :: candidates := by
  induction candidates generalizing initial with
  | nil => exact List.mem_cons_self
  | cons head tail inductionHypothesis =>
      by_cases better : (value head).num * (value initial).den ≤ (value initial).num * (value head).den
      · rw [select, if_pos better]
        exact List.mem_cons_of_mem initial (inductionHypothesis head)
      · rw [select, if_neg better]
        rcases List.mem_cons.mp (inductionHypothesis initial) with same | later
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem initial (List.mem_cons_of_mem head later)

end FiniteRatioMinimum
end Probability
end Thesis
