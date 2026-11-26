import Thesis.Probability.Distros.EntropyOptimize

/-!
# Executing certified rational entropy optimization

The binary box fixture checks actual enumeration and removal of an
incompatible box only after rational infeasibility is certified. A large
unreduced fraction tests location without a denominator grid. The public
solver rejects an impossible expectation, gives a zero-entropy singleton
certificate, and retains a forced-zero cell with repeated signed rows.

A supplied exactly feasible fair law takes the faster certification path
at error `1/1000`, retaining its original denominator. Every certificate's
upper bound applies to all admissible rational laws, not just the search's
finite candidates. Tolerance positivity and exact moment feasibility remain
explicit; the algorithm certifies an error interval rather than promising
an exactly attained rational maximizer in every problem.
-/

namespace Thesis.Examples.EntropyOptimize
open Probability Probability.Distros

private def binary : PartialMomentProblem Nat := ⟨[0, 1], 0, by decide, by decide, []⟩
private def singleton : PartialMomentProblem Nat := ⟨[7], 7, by decide, by decide, []⟩
private def impossible : PartialMomentProblem Nat :=
  ⟨[0, 1], 0, by decide, by decide, [MomentInterval.exact (fun _ => 0) SignedRatio.one]⟩

example : (ProbabilityBoxes.enumerate 2 1).length = 4 := by decide +kernel
example : (ProbabilityBoxes.locate (⟨1000000001, 2000000001, by decide⟩ : QProb) (by decide) 2).val = 1 := by decide +kernel

/-- Three boxes have actual feasible witnesses; the incompatible box is
removed only after the complete rational solver certifies infeasibility. -/
example : (binary.boxCandidates 1 (by decide)).length = 3 := by decide +kernel

private def isInfeasible {problem : PartialMomentProblem Nat} {tolerance : QProb}
    (result : problem.EntropyResult tolerance) : Bool :=
  match result with | .infeasible _ => true | .feasible _ => false

private def hasZeroLower {problem : PartialMomentProblem Nat} {tolerance : QProb}
    (result : problem.EntropyResult tolerance) : Bool :=
  match result with | .feasible certificate => decide (certificate.lower.num = 0) | .infeasible _ => false

/-- A complete infeasibility result is retained at the entropy interface. -/
example : isInfeasible (impossible.solveEntropy ⟨1, 100, by decide⟩ (by decide)) = true := by decide +kernel

/-- This executes the full public solver and the rational enclosure layer.
The singleton optimum has zero entropy and a clipped nonnegative lower bound. -/
example : hasZeroLower (singleton.solveEntropy ⟨1, 8, by decide⟩ (by decide)) = true := by decide +kernel

private def forcedZero : PartialMomentProblem Nat :=
  ⟨[0, 1], 0, by decide, by decide,
    [MomentInterval.exact (fun value => if value = 1 then 1 else 0) SignedRatio.zero,
      MomentInterval.exact (fun _ => -2) ⟨-2, 1, by decide⟩,
      MomentInterval.exact (fun _ => -2) ⟨-2, 1, by decide⟩]⟩
private def retainsNullOne {problem : PartialMomentProblem Nat} {tolerance : QProb}
    (result : problem.EntropyResult tolerance) : Bool :=
  match result with
  | .feasible certificate => decide ((1, 0) ∈ certificate.law.distro.record.atoms)
  | .infeasible _ => false

/-- The executed solver retains the original forced-zero cell and repeated
signed rows rather than deleting them from the declared problem. -/
example : retainsNullOne (forcedZero.solveEntropy ⟨2, 1, by decide⟩ (by decide)) = true := by decide +kernel

private def fair : Distro Nat := ⟨⟨[(0, 1), (1, 1)], 2, by decide, by decide⟩⟩
private def fairLaw : binary.CompatibleLaw :=
  ⟨fair, (by
    change ∀ atom ∈ fair.record.atoms, 0 < atom.2 → atom.1 ∈ binary.cells
    decide +kernel),
    (by intro constraint member; cases member),
    (by
      intro cell member
      change cell ∈ [0, 1] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨1, by decide⟩)⟩

/-- A supplied exact feasible uniform law is certified to a small tolerance
without exhaustive box enumeration. All moment constraints remain exact. -/
example : (binary.certifyEntropy fairLaw ⟨1, 1000, by decide⟩ (by decide)).law.distro.record.den = 2 := by decide +kernel

/-- The certificate contract bounds every feasible rational law, rather
than merely the finite candidate list used internally by the search. -/
example (epsilon : QProb) (certificate : binary.EntropyCertificate epsilon)
    (μ : Distro Nat) (valid : binary.Admissible μ) :
    ExactLog.LE (ExactLog.ofQProb certificate.lower)
      (certificate.law.distro.entropy binary.entropyGrid certificate.law.support) ∧
    ExactLog.LE (μ.entropy binary.entropyGrid valid.1) (ExactLog.ofQProb certificate.upper) ∧
    QProb.LE certificate.lower certificate.upper ∧
    QProb.LE certificate.upper (QProb.add certificate.lower epsilon) :=
  ⟨certificate.lower_bound, certificate.global_bound μ valid, certificate.lower_le_upper, certificate.gap⟩

end Thesis.Examples.EntropyOptimize
