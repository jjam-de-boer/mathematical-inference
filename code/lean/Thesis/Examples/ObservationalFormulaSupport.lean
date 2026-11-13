import Thesis.CausalTransport.FormulaSupportCatalogue

namespace Thesis.Causality.Examples.ObservationalFormulaSupport

open Probability

/-!
# Support-only expression checks and bounded catalogue comparison

One observed Boolean variable keeps the complete support cube tiny. Two
records have identical positive support but different nonzero probabilities.
Their status computations agree while their numerical event values do not.
The additional tests retain strict/weighted zero behaviour, actionful-leaf
rejection, and exact finite-catalogue coverage comparisons. These arbitrary
syntax plans are not presented as certified causal-identification formulas.
-/

def signature : ObservedSignature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def node : Fin signature.count := ⟨0, by decide⟩
def requested : signature.Assignment := fun _ => true

def fair : FiniteProbRecord signature.Assignment where
  atoms := [(fun _ => false, 1), (fun _ => true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def biased : FiniteProbRecord signature.Assignment where
  atoms := [(fun _ => false, 3), (fun _ => true, 1)]
  den := 4
  den_pos := by decide
  total_mass := rfl

theorem same_support : fair.support = biased.support := by
  funext value
  have constant : value = fun _ => value node := by
    funext index
    have same : index = node := Fin.ext (by
      change index.val = 0
      have bound := index.isLt
      change index.val < 1 at bound
      omega)
    rw [same]
  cases selected : value node with
  | false =>
      have same : value = fun _ => false := constant.trans (funext (fun _ => selected))
      rw [same]
      decide +kernel
  | true =>
      have same : value = fun _ => true := constant.trans (funext (fun _ => selected))
      rw [same]
      decide +kernel

def marginal : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩

theorem marginal_positive :
    marginal.supportStatus fair.support requested = .positive := by decide +kernel

theorem status_preserved :
    ProbabilityResult.status (marginal.observationalDenote fair requested) =
      ProbabilityResult.status (marginal.observationalDenote biased requested) :=
  marginal.status_eq_of_support_eq same_support requested

theorem values_not_preserved :
    ¬QProb.Equiv (fair.probVal (Kernel.agreesOn NodeSet.full requested))
      (biased.probVal (Kernel.agreesOn NodeSet.full requested)) := by decide +kernel

def unavailable : ProbabilityTerm signature := .divide .zero .zero

theorem strict_zero_is_not_completion :
    (ProbabilityTerm.multiply .zero unavailable).supportStatus fair.support requested = .undefined := rfl

theorem weighted_zero_skips :
    (ProbabilityTerm.weightedMultiply .zero unavailable).supportStatus fair.support requested = .zero := rfl

theorem actionful_leaf_rejected :
    (ProbabilityTerm.kernel (S := signature) ⟨NodeSet.empty, NodeSet.full, NodeSet.empty⟩).supportStatus
      fair.support requested = .undefined := rfl

def readyPlan : ObservationalFormulaPlan signature := ⟨.zero, .always⟩
def unavailablePlan : ObservationalFormulaPlan signature := ⟨unavailable, .always⟩
def guardedPlan : ObservationalFormulaPlan signature := ⟨.zero, .actionOne NodeSet.full⟩

theorem full_support_rejects_probability_one_guard :
    guardedPlan.availableOnSupport fair.support requested = false := by decide +kernel

/-- Exhausting the four raw patterns is intentionally confined to this
one-variable fixture; normalized records retain only three nonempty ones. -/
theorem three_nonempty_patterns : (ObservationalSupportPattern.nonempty signature).length = 3 := by
  decide +kernel

theorem undefined_candidate_is_redundant :
    ObservationalFormulaPlan.sameCoverage [readyPlan, unavailablePlan] [readyPlan] = true := by
  decide +kernel

theorem guard_can_shrink_coverage :
    ObservationalFormulaPlan.coverageIncluded [readyPlan] [guardedPlan] = false := by
  decide +kernel

theorem rejected_record_is_reported :
    fair.support ∈ ObservationalFormulaPlan.uncoveredPatterns [guardedPlan] requested :=
  (ObservationalFormulaPlan.mem_uncoveredPatterns_iff _ _ _).mpr
    ⟨ObservationalSupportPattern.support_mem_nonempty fair, by decide +kernel⟩

end Thesis.Causality.Examples.ObservationalFormulaSupport
