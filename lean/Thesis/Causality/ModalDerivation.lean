import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

/-!
Operation-sensitive modal annotations for finite do-calculus derivations.

The modalities here do not execute an intervention or observation.  They lock
the symbolic query context.  Ordinary SCM operations provide the executable
record transformations, while a modal rule cell certifies that Pearl's side
condition relates two locked query modes.  This keeps the operational and modal
roles separate while making their connection inspectable in Lean.
-/

/-- Generating locks for observations and hard interventions. -/
inductive CausalQueryModality (S : ObservedSignature) where
  | observe (nodes : NodeSet S)
  | intervene (nodes : NodeSet S)

/-- A probability kernel viewed as an outcome in an action/observation mode. -/
structure CausalQueryMode (S : ObservedSignature) where
  outcome : NodeSet S
  action : NodeSet S
  condition : NodeSet S

namespace CausalQueryMode

def empty (outcome : NodeSet S) : CausalQueryMode S where
  outcome := outcome
  action := NodeSet.empty
  condition := NodeSet.empty

/-- Lock a query mode; the context-native operation is represented elsewhere. -/
def lock (mode : CausalQueryMode S) :
    CausalQueryModality S -> CausalQueryMode S
  | .observe nodes =>
      { mode with condition := NodeSet.union mode.condition nodes }
  | .intervene nodes =>
      { mode with action := NodeSet.union mode.action nodes }

def ofKernel (kernel : Kernel S) : CausalQueryMode S where
  outcome := kernel.outcome
  action := kernel.action
  condition := kernel.condition

def toKernel (mode : CausalQueryMode S) : Kernel S where
  outcome := mode.outcome
  action := mode.action
  condition := mode.condition

/-- Intensional-friendly equality of query modes, stated componentwise. -/
structure PointwiseEquivalent (left right : CausalQueryMode S) : Prop where
  outcome : forall i, left.outcome i = right.outcome i
  action : forall i, left.action i = right.action i
  condition : forall i, left.condition i = right.condition i

/-- The action and observation fields of a kernel are precisely its two locks. -/
theorem kernel_built_from_locks (kernel : Kernel S) :
    PointwiseEquivalent
      (((empty kernel.outcome).lock (.intervene kernel.action)).lock
        (.observe kernel.condition))
      (ofKernel kernel) := by
  constructor <;> intro i <;> rfl

end CausalQueryMode

/-- The three operation-sensitive kinds of Pearl rule cell. -/
inductive ModalRuleKind where
  | observation
  | actionObservationExchange
  | action
  deriving DecidableEq, Repr

/--
A proof-carrying two-cell between locked query modes.  Rule 1 changes an
observation lock, rule 2 exchanges action and observation locks, and rule 3
changes an action lock.  Each constructor retains the exact graph condition.
-/
inductive ModalRuleCell (G : ObservedGraph S) :
    CausalQueryMode S -> CausalQueryMode S -> Type
  | observation (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (separated :
        G.dSeparated (.bar x) y z (NodeSet.union x w) = true) :
      ModalRuleCell G
        (CausalQueryMode.ofKernel (rule1Left x y z w))
        (CausalQueryMode.ofKernel (rule1Right x y z w))
  | actionObservationExchange (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (separated :
        G.dSeparated (.barUnderline x z) y z (NodeSet.union x w) = true) :
      ModalRuleCell G
        (CausalQueryMode.ofKernel (rule2Left x y z w))
        (CausalQueryMode.ofKernel (rule2Right x y z w))
  | action (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w)
      (separated :
        let base := GraphMutilation.bar x
        let removable := G.nonAncestorsOf base z w
        G.dSeparated
          { removeIncoming := NodeSet.union x removable
            removeOutgoing := NodeSet.empty }
          y z (NodeSet.union x w) = true) :
      ModalRuleCell G
        (CausalQueryMode.ofKernel (rule3Left x y z w))
        (CausalQueryMode.ofKernel (rule3Right x y z w))

namespace ModalRuleCell

def kind : ModalRuleCell G source target -> ModalRuleKind
  | .observation .. => .observation
  | .actionObservationExchange .. => .actionObservationExchange
  | .action .. => .action

def toDoRule : ModalRuleCell G source target ->
    DoRuleApplication G source.toKernel target.toKernel
  | .observation x y z w disjoint separated =>
      .rule1 x y z w disjoint separated
  | .actionObservationExchange x y z w disjoint separated =>
      .rule2 x y z w disjoint separated
  | .action x y z w disjoint separated =>
      .rule3 x y z w disjoint separated

end ModalRuleCell

def DoRuleApplication.toModalCell
    (application : DoRuleApplication G left right) :
    ModalRuleCell G (CausalQueryMode.ofKernel left)
      (CausalQueryMode.ofKernel right) := by
  cases application with
  | rule1 x y z w disjoint separated =>
      exact .observation x y z w disjoint separated
  | rule2 x y z w disjoint separated =>
      exact .actionObservationExchange x y z w disjoint separated
  | rule3 x y z w disjoint separated =>
      exact .action x y z w disjoint separated

/-!
The annotation is indexed by the ordinary derivation that it explains. Its
`doRule` constructor carries a modal rule cell; the remaining constructors
record composition and probability-algebra structure. The rule cell is a
thesis-specific indexed annotation, not a formal 2-cell in an instantiated
Gratzer mode theory.
-/
inductive ModalDerivationTrace (G : ObservedGraph S) :
    {left right : ProbabilityTerm S} ->
      DoCalculusDerivation G left right -> Type
  | refl (term) : ModalDerivationTrace G (.refl term)
  | symm {left right} {derivation : DoCalculusDerivation G left right} :
      ModalDerivationTrace G derivation ->
        ModalDerivationTrace G (.symm derivation)
  | trans {left middle right}
      {first : DoCalculusDerivation G left middle}
      {second : DoCalculusDerivation G middle right} :
      ModalDerivationTrace G first -> ModalDerivationTrace G second ->
        ModalDerivationTrace G (.trans first second)
  | doRule {left right} (application : DoRuleApplication G left right) :
      ModalRuleCell G (CausalQueryMode.ofKernel left)
        (CausalQueryMode.ofKernel right) ->
      ModalDerivationTrace G (.doRule application)
  | marginalization (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      ModalDerivationTrace G (.marginalization x y z w disjoint)
  | conditioning (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      ModalDerivationTrace G (.conditioning x y z w disjoint)
  | chain (x y z w : NodeSet S)
      (disjoint : FourWayDisjoint x y z w) :
      ModalDerivationTrace G (.chain x y z w disjoint)
  | marginalizeCongr (nodes : NodeSet S) {left right}
      {derivation : DoCalculusDerivation G left right} :
      ModalDerivationTrace G derivation ->
        ModalDerivationTrace G (.marginalizeCongr nodes derivation)
  | evaluateAtCongr (assignment : S.Assignment) {left right}
      {derivation : DoCalculusDerivation G left right} :
      ModalDerivationTrace G derivation ->
        ModalDerivationTrace G (.evaluateAtCongr assignment derivation)
  | addCongr {left left' right right'}
      {first : DoCalculusDerivation G left left'}
      {second : DoCalculusDerivation G right right'} :
      ModalDerivationTrace G first -> ModalDerivationTrace G second ->
        ModalDerivationTrace G (.addCongr first second)
  | multiplyCongr {left left' right right'}
      {first : DoCalculusDerivation G left left'}
      {second : DoCalculusDerivation G right right'} :
      ModalDerivationTrace G first -> ModalDerivationTrace G second ->
        ModalDerivationTrace G (.multiplyCongr first second)
  | divideCongr {left left' right right'}
      {numerator : DoCalculusDerivation G left left'}
      {denominator : DoCalculusDerivation G right right'} :
      ModalDerivationTrace G numerator -> ModalDerivationTrace G denominator ->
        ModalDerivationTrace G (.divideCongr numerator denominator)

def DoCalculusDerivation.toModalTrace :
    (derivation : DoCalculusDerivation G left right) ->
      ModalDerivationTrace G derivation
  | .refl term => .refl term
  | .symm derivation => .symm derivation.toModalTrace
  | .trans first second =>
      .trans first.toModalTrace second.toModalTrace
  | .doRule application =>
      .doRule application application.toModalCell
  | .marginalization x y z w disjoint =>
      .marginalization x y z w disjoint
  | .conditioning x y z w disjoint =>
      .conditioning x y z w disjoint
  | .chain x y z w disjoint => .chain x y z w disjoint
  | .marginalizeCongr nodes derivation =>
      .marginalizeCongr nodes derivation.toModalTrace
  | .evaluateAtCongr assignment derivation =>
      .evaluateAtCongr assignment derivation.toModalTrace
  | .addCongr first second =>
      .addCongr first.toModalTrace second.toModalTrace
  | .multiplyCongr first second =>
      .multiplyCongr first.toModalTrace second.toModalTrace
  | .divideCongr numerator denominator =>
      .divideCongr numerator.toModalTrace denominator.toModalTrace

namespace ModalDerivationTrace

/-- The operation-sensitive Pearl cells encountered by a derivation. -/
def ruleKinds : {derivation : DoCalculusDerivation G left right} ->
    ModalDerivationTrace G derivation -> List ModalRuleKind
  | _, .refl _ => []
  | _, .symm trace => trace.ruleKinds
  | _, .trans first second => first.ruleKinds ++ second.ruleKinds
  | _, .doRule _ cell => [cell.kind]
  | _, .marginalization .. => []
  | _, .conditioning .. => []
  | _, .chain .. => []
  | _, .marginalizeCongr _ trace => trace.ruleKinds
  | _, .evaluateAtCongr _ trace => trace.ruleKinds
  | _, .addCongr first second => first.ruleKinds ++ second.ruleKinds
  | _, .multiplyCongr first second => first.ruleKinds ++ second.ruleKinds
  | _, .divideCongr numerator denominator =>
      numerator.ruleKinds ++ denominator.ruleKinds

end ModalDerivationTrace

/-- An ordinary derivation together with its checked modal annotation. -/
structure ModalDoCalculusDerivation (G : ObservedGraph S)
    (left right : ProbabilityTerm S) where
  derivation : DoCalculusDerivation G left right
  trace : ModalDerivationTrace G derivation

def DoCalculusDerivation.toModal
    (derivation : DoCalculusDerivation G left right) :
    ModalDoCalculusDerivation G left right where
  derivation := derivation
  trace := derivation.toModalTrace

namespace ModalDoCalculusDerivation

def erase (derivation : ModalDoCalculusDerivation G left right) :
    DoCalculusDerivation G left right :=
  derivation.derivation

theorem erase_toModal (derivation : DoCalculusDerivation G left right) :
    derivation.toModal.erase = derivation :=
  rfl

/-- Modal annotation preserves the already checked partial denotation proof. -/
noncomputable def denotational_soundAt
    (semantics : LocalPrimitiveSoundness G model)
    (derivation : ModalDoCalculusDerivation G left right)
    (supported : LocalDerivationSupport
      model assignment derivation.derivation) :
    ProbabilityTerm.EquivalentAt model left right assignment :=
  derivation.derivation.denotational_soundAt semantics supported

end ModalDoCalculusDerivation

end Causality
end Thesis
