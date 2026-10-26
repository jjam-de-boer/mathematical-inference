import Thesis.Probability.Distros.UncertaintyMeasure
import Thesis.Probability.ExactLogLinear

namespace Thesis.Probability
open QProb

/-!
# Conditional entropy and Shannon monotonicity of grouping

`ProbabilityVector.Compound.entropy_grouping` is the finite chain rule:
the joint entropy of a two-stage choice is the outer entropy plus the
weighted inner entropies.  Conditional entropy is that remainder.

Mutual information of two coordinates is `H(X)+H(Y)-H(X,Y)`, once those
three values are in hand.  It is not defined from a `Compound` alone,
because distinct branches need not share an inner alphabet.

These identities live on normalized mass vectors.  They do not assume a
causal parent factorization, a hidden-variable model, or positivity of
branch weights.  Zero outer weight contributes nothing, independently of
the unused inner vector.
-/

namespace QProb

/-- A nonnegative summand cannot decrease a presentation. -/
theorem le_add_left (p q : QProb) : LE p (add p q) := by
  change p.num * (p.den * q.den) ≤ (p.num * q.den + q.num * p.den) * p.den
  calc
    p.num * (p.den * q.den)
        = p.num * p.den * q.den := (Nat.mul_assoc _ _ _).symm
    _ = p.num * q.den * p.den := by ac_rfl
    _ ≤ p.num * q.den * p.den + q.num * p.den * p.den := Nat.le_add_right _ _
    _ = (p.num * q.den + q.num * p.den) * p.den := (Nat.add_mul _ _ _).symm

theorem le_add_right (p q : QProb) : LE p (add q p) :=
  le_congr (equiv_refl p) (add_comm p q) (le_add_left p q)

theorem le_listSum_of_mem (masses : List QProb) {q : QProb} (member : q ∈ masses) :
    LE q (listSum masses) := by
  induction masses with
  | nil => cases member
  | cons head rest ih =>
      cases List.mem_cons.mp member with
      | inl same =>
          subst same
          exact le_add_left q (listSum rest)
      | inr later =>
          exact le_trans (ih later) (le_add_right (listSum rest) head)

end QProb

namespace ExactLog

/-- Adding a nonnegative remainder cannot decrease an exact logarithm. -/
theorem le_add_of_nonneg_right (x y : ExactLog) (nonnegative : LE zero y) :
    LE x (add x y) := by
  have lifted : LE (add zero x) (add y x) :=
    (add_le_add_right_iff zero y x).mpr nonnegative
  rw [zero_add] at lifted
  exact (le_congr (equiv_refl x) (add_comm y x)).mp lifted

end ExactLog

namespace ProbabilityVector

/-- Every coordinate of a normalized vector is a probability, so it cannot
exceed one.  The comparison uses the existing cross-multiplication order. -/
theorem mass_le_one (vector : ProbabilityVector) {mass : QProb}
    (listed : mass ∈ vector.masses) : QProb.LE mass QProb.one :=
  QProb.le_congr (QProb.equiv_refl mass) vector.normalized
    (QProb.le_listSum_of_mem vector.masses listed)

theorem entropy_nonnegative (vector : ProbabilityVector) :
    ExactLog.LE ExactLog.zero vector.entropy := by
  apply ExactLog.listSum_map_nonnegative
  intro mass listed
  exact entropyTerm_nonnegative mass (vector.mass_le_one listed)

/-- Conditional entropy of the second stage given the first.  A zero-weight
branch contributes zero regardless of its inner entropy. -/
def Compound.conditionalEntropy (choice : Compound) : ExactLog :=
  ExactLog.listSum (choice.branches.map fun branch =>
    ExactLog.scaleRatio branch.1 branch.2.entropy)

theorem Compound.conditionalEntropy_nonnegative (choice : Compound) :
    ExactLog.LE ExactLog.zero choice.conditionalEntropy := by
  apply ExactLog.listSum_map_nonnegative
  intro branch listed
  exact ExactLog.scaleRatio_nonnegative branch.1 (branch.2.entropy_nonnegative)

/-- The finite chain rule, with the remainder named as conditional entropy. -/
theorem Compound.entropy_chain (choice : Compound) :
    ExactLog.Equiv choice.refined.entropy
      (ExactLog.add choice.outer.entropy choice.conditionalEntropy) :=
  choice.entropy_grouping

/-- Shannon monotonicity for a two-stage refinement: adding a second stage
cannot decrease entropy.  This is the projection form of the data-processing
inequality; it does not require a causal interpretation of the stages. -/
theorem Compound.outer_entropy_le_refined (choice : Compound) :
    ExactLog.LE choice.outer.entropy choice.refined.entropy :=
  (ExactLog.le_congr (ExactLog.equiv_refl _) choice.entropy_chain).mpr
    (ExactLog.le_add_of_nonneg_right _ _ choice.conditionalEntropy_nonnegative)

end ProbabilityVector

/-- Shannon mutual information from the three joint/marginal entropies.
The value is `H(X)+H(Y)-H(X,Y)` as an exact logarithm. -/
def mutualInformation (entropyX entropyY entropyXY : ExactLog) : ExactLog :=
  ExactLog.sub (ExactLog.add entropyX entropyY) entropyXY

/-- Chain-rule form `I(X;Y) = H(Y) - H(Y|X)`. -/
theorem mutualInformation_eq_inner_minus_conditional
    (entropyX entropyY entropyXY conditional : ExactLog)
    (chain : ExactLog.Equiv entropyXY (ExactLog.add entropyX conditional)) :
    ExactLog.Equiv (mutualInformation entropyX entropyY entropyXY)
      (ExactLog.sub entropyY conditional) := by
  unfold mutualInformation ExactLog.sub
  have replaceXY :
      ExactLog.Equiv
        (ExactLog.add (ExactLog.add entropyX entropyY) (ExactLog.neg entropyXY))
        (ExactLog.add (ExactLog.add entropyX entropyY)
          (ExactLog.neg (ExactLog.add entropyX conditional))) :=
    ExactLog.add_congr (ExactLog.equiv_refl _) (ExactLog.neg_congr chain)
  have regrouped := ExactLog.add_four entropyX entropyY
    (ExactLog.neg entropyX) (ExactLog.neg conditional)
  have cancelled := ExactLog.add_congr (ExactLog.add_neg entropyX)
    (ExactLog.equiv_refl (ExactLog.add entropyY (ExactLog.neg conditional)))
  refine ExactLog.equiv_trans replaceXY ?_
  rw [ExactLog.neg_add]
  exact ExactLog.equiv_trans regrouped
    (ExactLog.equiv_trans cancelled (by rw [ExactLog.zero_add]; exact ExactLog.equiv_refl _))

end Thesis.Probability
