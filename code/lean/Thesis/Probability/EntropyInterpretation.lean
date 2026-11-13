import Thesis.Probability.ExactLogInterpretation
import Thesis.Probability.EntropyGrouping

namespace Thesis.Probability.ConstructiveReal

/-- Base-two logarithm of a positive rational argument, with certified real
value. Extension to general positive real arguments is a separate analytic step. -/
def rationalLog2 (value : PositiveRatio) : ConstructiveReal := (ExactLog.log value).interpret

theorem rationalLog2_mul (a b : PositiveRatio) :
    Equiv (rationalLog2 (a.mul b)) (add (rationalLog2 a) (rationalLog2 b)) := by
  rw [rationalLog2, ← ExactLog.log_mul]
  exact ExactLog.interpret_add _ _

theorem rationalLog2_inv (value : PositiveRatio) :
    Equiv (rationalLog2 value.inv) (neg (rationalLog2 value)) := ExactLog.interpret_neg _

theorem rationalLog2_divide (a b : PositiveRatio) :
    Equiv (rationalLog2 (a.mul b.inv)) (sub (rationalLog2 a) (rationalLog2 b)) :=
  equiv_trans (rationalLog2_mul _ _) (add_congr (equiv_refl _) (rationalLog2_inv b))

/-- The usual analytic entropy summand on rational masses, with zero
contribution at a zero coordinate. The zero case never evaluates a logarithm. -/
def entropyTerm (mass : QProb) : ConstructiveReal :=
  if positive : 0 < mass.num then
    neg (scaleRatio mass (rationalLog2 ⟨mass.num, mass.den, positive, mass.den_pos⟩))
  else zero

theorem entropyTerm_zero (mass : QProb) (vanished : mass.num = 0) : entropyTerm mass = zero := by
  simp only [entropyTerm, vanished, Nat.lt_irrefl, ↓reduceDIte]

def entropySum (masses : List QProb) : ConstructiveReal := listSum (masses.map entropyTerm)

/-- Analytic KL summands are `p (log₂ p − log₂ r)`, with strictly positive
reference mass and the same zero-observation convention as the rational core. -/
def relativeEntropyTerm (observed reference : QProb) (referencePositive : 0 < reference.num) : ConstructiveReal :=
  if positive : 0 < observed.num then
    scaleRatio observed (sub (rationalLog2 ⟨observed.num, observed.den, positive, observed.den_pos⟩)
      (rationalLog2 ⟨reference.num, reference.den, referencePositive, reference.den_pos⟩))
  else zero

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability

/-- The implemented rational entropy term has exactly its analytic value. -/
theorem entropyTerm_interpret (mass : QProb) :
    ConstructiveReal.Equiv (entropyTerm mass).interpret (ConstructiveReal.entropyTerm mass) := by
  by_cases positive : 0 < mass.num
  · simp only [entropyTerm, ConstructiveReal.entropyTerm, positive, ↓reduceDIte]
    change ConstructiveReal.Equiv
      (ExactLog.scaleRatio mass (ExactLog.neg (ExactLog.log ⟨mass.num, mass.den, positive, mass.den_pos⟩))).interpret _
    rw [ExactLog.scaleRatio_neg]
    exact ConstructiveReal.equiv_trans (ExactLog.interpret_neg _)
      (ConstructiveReal.neg_congr (ExactLog.interpret_scaleRatio _ _))
  · simp only [entropyTerm, ConstructiveReal.entropyTerm, positive, ↓reduceDIte]
    exact ExactLog.interpret_ofSignedRatio SignedRatio.zero

/-- Finite rational entropy agrees with the analytic Shannon sum, including
all declared zero coordinates. No new atom-weight type is introduced. -/
theorem entropySum_interpret (masses : List QProb) :
    ConstructiveReal.Equiv (entropySum masses).interpret (ConstructiveReal.entropySum masses) := by
  have distributed := ExactLog.interpret_listSum (masses.map entropyTerm)
  simp only [List.map_map] at distributed
  exact ConstructiveReal.equiv_trans distributed
    (ConstructiveReal.listSum_map_congr masses _ _ (fun mass _ => entropyTerm_interpret mass))

theorem relativeEntropyTerm_interpret (observed reference : QProb) (referencePositive : 0 < reference.num) :
    ConstructiveReal.Equiv (relativeEntropyTerm observed reference referencePositive).interpret
      (ConstructiveReal.relativeEntropyTerm observed reference referencePositive) := by
  by_cases positive : 0 < observed.num
  · simp only [relativeEntropyTerm, ConstructiveReal.relativeEntropyTerm, positive, ↓reduceDIte]
    exact ConstructiveReal.equiv_trans (ExactLog.interpret_scaleRatio _ _)
      (ConstructiveReal.scaleRatio_congr (ConstructiveReal.rationalLog2_divide _ _) observed)
  · simp only [relativeEntropyTerm, ConstructiveReal.relativeEntropyTerm, positive, ↓reduceDIte]
    exact ExactLog.interpret_ofSignedRatio SignedRatio.zero

end Thesis.Probability
