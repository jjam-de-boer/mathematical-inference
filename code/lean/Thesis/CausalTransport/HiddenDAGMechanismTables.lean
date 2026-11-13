import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.FiniteFunctionTables

namespace Thesis.Causality

open Probability

/-!
# All compatible finite mechanism tables for a declared alphabet shape

The catalogue below depends only on the full hidden graph and its node/source
cardinality vectors. It does not inspect an input model's equations, observed
law, rational source weights, or list of examples. Every local table reads
exactly the graph's typed parent inputs and that node's own private noise.
In particular, this does not accidentally enumerate functions with access to
nonparents or all private sources.

Proof-indexed parent slots use the explicit Boolean edge decisions. An absent
parent contributes one vacuous function rather than its node's value choices.
This handles roots and irrelevant empty alphabets without a default input or
a classical function-equality principle. Actual table rows have finite codes;
all output vectors and then all node-wise table families are enumerated by
the existing dependent-product construction.

The completeness and inverse-tabulation proofs concern every table row, not
only trajectories having positive probability. Interpreting a table into a
native model is a separate adapter; a finite table catalogue does not itself
enumerate infinitely many rational source-weight assignments.
-/

namespace FiniteHiddenDAG

variable {S : ObservedSignature.{0}}

abbrev CodeValues (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat) :=
  fun node => Fin (nodeCard node)

/-- Equality of typed parent inputs is decided coordinate by coordinate,
and at an absent edge no value comparison is made. -/
def codeParentDecidableEq (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat) (child : Fin H.count) :
    DecidableEq (H.ParentValues (H.CodeValues nodeCard) child) :=
  FiniteProduct.assignmentDecidableEq H.count
    (fun parent => H.edge parent child = true → Fin (nodeCard parent))
    (fun parent => ProofFunction.decidableEq (H.edge parent child = true))

def codeParentChoices (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat)
    (child parent : Fin H.count) : List (H.edge parent child = true → Fin (nodeCard parent)) :=
  ProofFunction.enumeration (H.edge parent child = true) (List.finRange (nodeCard parent))

theorem codeParentChoices_complete (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat)
    (child parent : Fin H.count) (input : H.edge parent child = true → Fin (nodeCard parent)) :
    input ∈ H.codeParentChoices nodeCard child parent :=
  ProofFunction.enumeration_complete _ _ (fun value => List.mem_finRange value) input

def codeParentWitness (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat) (child : Fin H.count) :
    FiniteWitness (H.ParentValues (H.CodeValues nodeCard) child) :=
  FiniteProduct.finiteWitness H.count
    (fun parent => H.edge parent child = true → Fin (nodeCard parent))
    (H.codeParentChoices nodeCard child) (H.codeParentChoices_complete nodeCard child)
    (fun parent => ProofFunction.decidableEq (H.edge parent child = true))

/-- The finite noise witness is literal `Fin`; it does not assume source
positivity or collapse zero-weight rows out of the mechanism's domain. -/
def codeNoiseWitness (card : Nat) : FiniteWitness (Fin card) :=
  ⟨card, id, id, fun _ => rfl, fun _ => rfl⟩

def codeInputWitness (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat) (child : Fin H.count) :
    FiniteWitness (H.ParentValues (H.CodeValues nodeCard) child × Fin (sourceCard child)) :=
  (H.codeParentWitness nodeCard child).product (codeNoiseWitness (sourceCard child))

abbrev CodeLocalTable (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat) (child : Fin H.count) :=
  FiniteFunctionTable.Table (H.codeInputWitness nodeCard sourceCard child) (Fin (nodeCard child))

abbrev CodeMechanismTables (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat) :=
  (child : Fin H.count) → H.CodeLocalTable nodeCard sourceCard child

abbrev CodeMechanisms (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat) :=
  (child : Fin H.count) → H.ParentValues (H.CodeValues nodeCard) child → Fin (sourceCard child) → Fin (nodeCard child)

def codeLocalTables (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat) (child : Fin H.count) :
    List (H.CodeLocalTable nodeCard sourceCard child) :=
  FiniteFunctionTable.enumeration (H.codeInputWitness nodeCard sourceCard child) (List.finRange (nodeCard child))

theorem codeLocalTables_complete (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat)
    (child : Fin H.count) (table : H.CodeLocalTable nodeCard sourceCard child) :
    table ∈ H.codeLocalTables nodeCard sourceCard child :=
  FiniteFunctionTable.enumeration_complete _ _ (fun value => List.mem_finRange value) table

/-- The full finite catalogue is independent of the equations and source
weights of the model later presented on this cardinality shape. -/
def codeMechanismCatalogue (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat) :
    List (H.CodeMechanismTables nodeCard sourceCard) :=
  FiniteProduct.enumeration H.count (H.CodeLocalTable nodeCard sourceCard) (H.codeLocalTables nodeCard sourceCard)

theorem codeMechanismCatalogue_complete (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat)
    (tables : H.CodeMechanismTables nodeCard sourceCard) : tables ∈ H.codeMechanismCatalogue nodeCard sourceCard :=
  FiniteProduct.enumeration_complete _ _ _ (H.codeLocalTables_complete nodeCard sourceCard) tables

def tabulateCodeMechanisms (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat)
    (equations : H.CodeMechanisms nodeCard sourceCard) : H.CodeMechanismTables nodeCard sourceCard :=
  fun child => FiniteFunctionTable.tabulate (H.codeInputWitness nodeCard sourceCard child)
    (fun input => equations child input.1 input.2)

def lookupCodeMechanisms (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat)
    (tables : H.CodeMechanismTables nodeCard sourceCard) : H.CodeMechanisms nodeCard sourceCard :=
  fun child parents noise => FiniteFunctionTable.lookup (H.codeInputWitness nodeCard sourceCard child) (tables child) (parents, noise)

/-- Every compatible equation is reconstructed exactly at every declared
parent/noise input. No observed-positivity or retained-action premise occurs. -/
theorem lookupCodeMechanisms_tabulate (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat)
    (equations : H.CodeMechanisms nodeCard sourceCard) :
    H.lookupCodeMechanisms nodeCard sourceCard (H.tabulateCodeMechanisms nodeCard sourceCard equations) = equations := by
  funext child parents noise
  exact congrArg (fun input => equations child input.1 input.2)
    ((H.codeInputWitness nodeCard sourceCard child).decode_encode (parents, noise))

theorem tabulateCodeMechanisms_lookup (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat)
    (tables : H.CodeMechanismTables nodeCard sourceCard) :
    H.tabulateCodeMechanisms nodeCard sourceCard (H.lookupCodeMechanisms nodeCard sourceCard tables) = tables := by
  funext child row
  exact congrArg (tables child) ((H.codeInputWitness nodeCard sourceCard child).encode_decode row)

theorem tabulatedCodeMechanisms_mem (H : FiniteHiddenDAG S) (nodeCard sourceCard : Fin H.count → Nat)
    (equations : H.CodeMechanisms nodeCard sourceCard) :
    H.tabulateCodeMechanisms nodeCard sourceCard equations ∈ H.codeMechanismCatalogue nodeCard sourceCard :=
  H.codeMechanismCatalogue_complete nodeCard sourceCard _

end FiniteHiddenDAG
end Thesis.Causality
