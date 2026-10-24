import Thesis.Causality.HardIntervention
import Thesis.Probability.FiniteFunctionTables

namespace Thesis.Causality.SharedResponse

open Probability

/-!
# Finite response tables for a single shared hidden cause

A response atom records one deterministic local equation at every observed
node, at every declared parent input. The carrier depends only on the public
signature, not on a particular model's source alphabets or rational weights.
Null parent configurations remain rows: hard interventions may reach them.

The catalogue is genuinely exhaustive. Proof-indexed absent-parent slots have
one vacuous input; equality of tables is decided by finite row comparisons,
not by classical equality of arbitrary functions. No catalogue is expanded by
the proofs below, and finiteness is not a practical-size guarantee.

Every finite latent-root model pushes its actual joint noise law onto these
tables, preserving all hard-intervention event probabilities simultaneously.
This operation may introduce additional shared confounding. It is therefore
not an arbitrary-graph reduction: the converse model construction belongs to
the class permitting one root incident at every observed node. Graph-class
membership and the rational linear solver are separate downstream bridges.
-/

variable (S : ObservedSignature.{0})

/-- Exact finite codes for all typed parent inputs, including absent edges. -/
def parentWitness (child : Fin S.count) : FiniteWitness (S.ParentValues child) :=
  FiniteProduct.finiteWitness S.count
    (fun parent => S.directed parent child = true → S.Value parent)
    (fun parent => ProofFunction.enumeration (S.directed parent child = true) (S.valueEnumeration parent))
    (fun parent => ProofFunction.enumeration_complete _ _ (S.value_complete parent))
    (fun parent => ProofFunction.decidableEq (S.directed parent child = true))

abbrev LocalTable (child : Fin S.count) :=
  FiniteFunctionTable.Table (parentWitness S child) (S.Value child)

abbrev Table := (child : Fin S.count) → LocalTable S child

def localDecidableEq (child : Fin S.count) : DecidableEq (LocalTable S child) :=
  FiniteProduct.assignmentDecidableEq (parentWitness S child).card
    (fun _ => S.Value child) (fun _ => S.valueDecidableEq child)

instance tableDecidableEq : DecidableEq (Table S) :=
  FiniteProduct.assignmentDecidableEq S.count (LocalTable S) (localDecidableEq S)

def localTables (child : Fin S.count) : List (LocalTable S child) :=
  FiniteFunctionTable.enumeration (parentWitness S child) (S.valueEnumeration child)

theorem localTables_complete (child : Fin S.count) (table : LocalTable S child) :
    table ∈ localTables S child :=
  FiniteFunctionTable.enumeration_complete _ _ (S.value_complete child) table

/-- A repetition-free complete grid for later rational mass constraints. -/
def enumeration : List (Table S) :=
  deduplicate (FiniteProduct.enumeration S.count (LocalTable S) (localTables S))

theorem enumeration_complete (table : Table S) : table ∈ enumeration S :=
  (mem_deduplicate _ _).mpr
    (FiniteProduct.enumeration_complete _ _ _ (localTables_complete S) table)

theorem enumeration_nodup : (enumeration S).Nodup := deduplicate_nodup _

def defaultTable : Table S := fun child _ => S.defaultValue child

theorem enumeration_nonempty : 0 < (enumeration S).length :=
  List.length_pos_of_mem (enumeration_complete S (defaultTable S))

/-- Read only a node's declared observed parents. The current intervened
parent values, not their factual equations, are passed to this lookup. -/
def lookup (table : Table S) (child : Fin S.count) (parents : S.ParentValues child) : S.Value child :=
  FiniteFunctionTable.lookup (parentWitness S child) (table child) parents

def evalNode (target : (child : Fin S.count) → Option (S.Value child))
    (table : Table S) (child : Fin S.count) : S.Value child :=
  match target child with
  | some value => value
  | none => lookup S table child (fun parent _edge => evalNode target table parent)
termination_by child.val
decreasing_by exact S.directed_earlier _edge

def eval (target : (child : Fin S.count) → Option (S.Value child))
    (table : Table S) : S.Assignment := fun child => evalNode S target table child

/-- Fixing one actual noise assignment determines every local response row,
including rows never visited in the factual or any selected query law. -/
def responseOf (model : ExactModel S) (unit : model.latent.Assignment) : Table S :=
  fun child => FiniteFunctionTable.tabulate (parentWitness S child)
    (fun parents => model.mechanism child parents (fun root _ => unit root))

theorem lookup_responseOf (model : ExactModel S) (unit : model.latent.Assignment)
    (child : Fin S.count) (parents : S.ParentValues child) :
    lookup S (responseOf S model unit) child parents =
      model.mechanism child parents (fun root _ => unit root) :=
  congrArg (fun inputs => model.mechanism child inputs (fun root _ => unit root))
    ((parentWitness S child).decode_encode parents)

/-- Pointwise execution is preserved for every intervention, without any
source, action or observed-support premise. -/
theorem evalNode_responseOf (model : ExactModel S) (unit : model.latent.Assignment)
    (target : (child : Fin S.count) → Option (S.Value child)) (child : Fin S.count) :
    evalNode S target (responseOf S model unit) child = model.evalNodeUnder target unit child := by
  rw [evalNode, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : target child with
  | some value => rfl
  | none =>
      change lookup S (responseOf S model unit) child _ =
        model.mechanism child _ (fun root _ => unit root)
      rw [lookup_responseOf]
      apply congrArg (fun parents => model.mechanism child parents (fun root _ => unit root))
      funext parent edge
      exact evalNode_responseOf model unit target parent
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem eval_responseOf (model : ExactModel S) (unit : model.latent.Assignment)
    (target : (child : Fin S.count) → Option (S.Value child)) :
    eval S target (responseOf S model unit) = model.evalUnder target unit := by
  funext child
  exact evalNode_responseOf S model unit target child

/-- Push forward the actual rational joint record; weights, their denominator
and repeated/null occurrences are not replaced by a real relaxation. -/
def lawOf (model : ExactModel S) : FiniteProbRecord (Table S) :=
  model.prior.map (responseOf S model)

theorem lawOf_interventionalValue (model : ExactModel S)
    (target : (child : Fin S.count) → Option (S.Value child)) (event : Event S.Assignment) :
    QProb.Equiv ((lawOf S model).probVal (fun table => event (eval S target table)))
      (model.interventionalValue target event) :=
  QProb.equiv_trans (model.prior.map_probVal _ _)
    (QProb.equiv_trans (model.prior.probVal_congr _ _ (fun unit =>
      congrArg event (eval_responseOf S model unit target)))
      (QProb.equiv_symm (model.interventionalValue_eq target event)))

end Thesis.Causality.SharedResponse
