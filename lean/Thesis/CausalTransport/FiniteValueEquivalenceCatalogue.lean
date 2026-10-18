import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.FiniteFunctionTables

namespace Thesis.Causality

open Probability

/-!
# Finite observed-value conversions, checked in both directions

Enumerate forward/backward function pairs between `Fin card` and an explicitly
finite public domain, then retain exactly the pairs whose two composites are
the identity. The check visits every declared value, not merely positive
observations. Thus observationally null intervention targets cannot vanish.

Each accepted pair is turned into an actual `ValueEquivalence` by the proved
checker theorem. Every supplied two-sided conversion is included. There is
no choice of a bijection from a mere cardinality equality and no request for
decidable equality of arbitrary function types. All function candidates are
enumerated through their finite input witnesses.
-/

namespace ValueEquivalenceCatalogue

structure Raw (card : Nat) (Value : Type u) where
  forward : Fin card → Value
  backward : Value → Fin card

def valueWitness [DecidableEq Value] (values : List Value) (complete : ∀ value, value ∈ values) : FiniteWitness Value :=
  FiniteWitness.ofList (deduplicate values) (fun value => (mem_deduplicate value values).mpr (complete value))
    (deduplicate_nodup values)

def candidates [DecidableEq Value] (card : Nat) (values : List Value) (complete : ∀ value, value ∈ values) : List (Raw card Value) :=
  (FiniteFunctionTable.functionEnumeration (FiniteWitness.fin card) values).flatMap (fun forward =>
    (FiniteFunctionTable.functionEnumeration (valueWitness values complete) (List.finRange card)).map
      (fun backward => ⟨forward, backward⟩))

theorem candidates_complete [DecidableEq Value] (card : Nat) (values : List Value) (complete : ∀ value, value ∈ values)
    (raw : Raw card Value) : raw ∈ candidates card values complete := by
  cases raw with
  | mk forward backward =>
      exact List.mem_flatMap_of_mem (FiniteFunctionTable.functionEnumeration_complete _ values complete forward)
        (List.mem_map_of_mem (f := fun backward => (⟨forward, backward⟩ : Raw card Value))
          (FiniteFunctionTable.functionEnumeration_complete _ _ (fun value => List.mem_finRange value) backward))

def check [DecidableEq Value] (values : List Value) (raw : Raw card Value) : Bool :=
  (List.finRange card).all (fun code => decide (raw.backward (raw.forward code) = code)) &&
    values.all (fun value => decide (raw.forward (raw.backward value) = value))

/-- Proofs are obtained from the finite Boolean checks at every input;
neither inverse law is accepted as an external semantic interface. -/
def checkedEquivalence [DecidableEq Value] (values : List Value) (complete : ∀ value, value ∈ values)
    (raw : Raw card Value) (accepted : check values raw = true) : ValueEquivalence (Fin card) Value where
  forward := raw.forward
  backward := raw.backward
  forward_backward := fun value => of_decide_eq_true
    ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).2) value (complete value))
  backward_forward := fun code => of_decide_eq_true
    ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).1) code (List.mem_finRange code))

theorem check_complete [DecidableEq Value] (values : List Value) (conversion : ValueEquivalence (Fin card) Value) :
    check values ⟨conversion.forward, conversion.backward⟩ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact List.all_eq_true.mpr (fun code _ => decide_eq_true (conversion.backward_forward code))
  · exact List.all_eq_true.mpr (fun value _ => decide_eq_true (conversion.forward_backward value))

def catalogue [DecidableEq Value] (card : Nat) (values : List Value) (complete : ∀ value, value ∈ values) :
    List (ValueEquivalence (Fin card) Value) :=
  ((candidates card values complete).filter (check values)).attach.map (fun admitted =>
    checkedEquivalence values complete admitted.val (List.mem_filter.mp admitted.property).2)

/-- Completeness covers all two-sided observed conversions, including
different permutations of the same declared values and the empty domain. -/
theorem catalogue_complete [DecidableEq Value] (card : Nat) (values : List Value) (complete : ∀ value, value ∈ values)
    (conversion : ValueEquivalence (Fin card) Value) : conversion ∈ catalogue card values complete := by
  let raw : Raw card Value := ⟨conversion.forward, conversion.backward⟩
  have member : raw ∈ (candidates card values complete).filter (check values) :=
    List.mem_filter.mpr ⟨candidates_complete card values complete raw, check_complete values conversion⟩
  unfold catalogue
  refine List.mem_map.mpr ⟨⟨raw, member⟩, List.mem_attach _ _, ?_⟩
  cases conversion
  rfl

end ValueEquivalenceCatalogue
end Thesis.Causality
