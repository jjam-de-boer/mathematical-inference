import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

variable {S : ObservedSignature}

/-!
# Constructive equality of finite probability-expression syntax

Probability terms contain function-valued Boolean node sets and dependent
observed assignments.  Those fields are finite: `NodeSet.equal` explicitly
enumerates observed indices, and `ObservedSignature.assignmentDecidableEq`
uses the signature's supplied value-equality procedures.  Consequently
syntactic equality of complete terms is decidable without classical equality
on arbitrary functions, choice, or propositional excluded middle.

This small syntax utility supports exact regression checks against the
engine's generated formula.  It decides term equality only; it does not
decide denotational equivalence or make algebraically equal formulas literal
equals.  In particular, product regrouping still needs its derivation tree.
-/

/-- Compare Boolean selections by their explicit finite equality test. -/
instance NodeSet.decidableEq (S : ObservedSignature) : DecidableEq (NodeSet S) :=
  fun left right =>
    if same : NodeSet.equal left right = true then
      .isTrue ((NodeSet.equal_eq_true_iff left right).mp same)
    else
      .isFalse (fun equality => same ((NodeSet.equal_eq_true_iff left right).mpr equality))

namespace Kernel

/-- Compare all three selections before constructing an equality proof. -/
def equal (left right : Kernel S) : Bool :=
  NodeSet.equal left.outcome right.outcome && NodeSet.equal left.action right.action &&
    NodeSet.equal left.condition right.condition

theorem equal_eq_true_iff (left right : Kernel S) : equal left right = true ↔ left = right := by
  cases left with
  | mk firstOutcome firstAction firstCondition =>
      cases right with
      | mk secondOutcome secondAction secondCondition =>
          simp only [equal, Bool.and_eq_true_iff, NodeSet.equal_eq_true_iff]
          constructor
          · rintro ⟨⟨rfl, rfl⟩, rfl⟩; rfl
          · intro same; cases same; exact ⟨⟨rfl, rfl⟩, rfl⟩

instance decidableEq (S : ObservedSignature) : DecidableEq (Kernel S) :=
  fun left right =>
    if same : equal left right = true then .isTrue ((equal_eq_true_iff left right).mp same)
    else .isFalse (fun equality => same ((equal_eq_true_iff left right).mpr equality))

end Kernel

namespace ProbabilityTerm

/-- Pointwise finite comparison avoids transporting later field tests along
function-extensionality proofs produced by earlier field comparisons. -/
private def assignmentEqual (left right : S.Assignment) : Bool :=
  finAll S.count (fun node => decide (left node = right node))

private theorem assignmentEqual_eq_true_iff (left right : S.Assignment) :
    assignmentEqual left right = true ↔ left = right := by
  constructor
  · intro same
    funext node
    exact of_decide_eq_true ((finAll_eq_true_iff _).mp same node)
  · intro same
    subst right
    exact (finAll_eq_true_iff _).mpr (fun _node => decide_eq_true rfl)

/-- Compare expression syntax by a recursive Boolean procedure.  Algebraic
equivalence is deliberately not part of this test. -/
def equal : ProbabilityTerm S -> ProbabilityTerm S -> Bool
  | .zero, .zero => true
  | .kernel left, .kernel right => Kernel.equal left right
  | .marginalize leftNodes left, .marginalize rightNodes right =>
      NodeSet.equal leftNodes rightNodes && equal left right
  | .evaluateAt leftAssignment left, .evaluateAt rightAssignment right =>
      assignmentEqual leftAssignment rightAssignment && equal left right
  | .add first second, .add first' second' => equal first first' && equal second second'
  | .multiply first second, .multiply first' second' => equal first first' && equal second second'
  | .divide first second, .divide first' second' => equal first first' && equal second second'
  | _, _ => false

/-- A successful syntax test proves literal term equality.  All constructor
proofs recurse on the displayed finite syntax; no representative is chosen. -/
theorem equal_eq_true_iff (left right : ProbabilityTerm S) : equal left right = true ↔ left = right := by
  induction left generalizing right with
  | zero => cases right <;> simp [equal]
  | kernel kernel => cases right <;> simp [equal, Kernel.equal_eq_true_iff]
  | marginalize nodes inner inductionHypothesis =>
      cases right <;> simp [equal, NodeSet.equal_eq_true_iff, inductionHypothesis]
  | evaluateAt assignment inner inductionHypothesis =>
      cases right <;> simp [equal, assignmentEqual_eq_true_iff, inductionHypothesis]
  | add first second firstIH secondIH => cases right <;> simp [equal, firstIH, secondIH]
  | multiply first second firstIH secondIH => cases right <;> simp [equal, firstIH, secondIH]
  | divide first second firstIH secondIH => cases right <;> simp [equal, firstIH, secondIH]

/-- The entire Boolean comparison runs before its equality proof is built.
This avoids stuck `Eq.rec` transports through function-extensionality proofs
that a generic derived equality procedure can introduce between fields. -/
instance decidableEq (S : ObservedSignature) : DecidableEq (ProbabilityTerm S) :=
  fun left right =>
    if same : equal left right = true then .isTrue ((equal_eq_true_iff left right).mp same)
    else .isFalse (fun equality => same ((equal_eq_true_iff left right).mpr equality))

end ProbabilityTerm

end Causality
end Thesis
