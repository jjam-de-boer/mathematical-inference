import Thesis.CausalTransport.HedgeChannelTable
import Thesis.Examples.HedgeChannelConstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelTable

open Probability

/-!
# Actual positive channel-table checks on a two-node bow

The table centres read both a declared directed parent and the appropriate
channel coordinate of an incident pair-root source.  Positivity and exact
graph compatibility are obtained from the general actual-CPT construction,
not by evaluating its much larger private response-function prior.

The local numerical regression checks a hard intervention at the action
node.  It evaluates only the two already integrated private row factors at
one explicit shared assignment.  The complete expansion theorem is used to
retain the actual factors; neither observational equality nor a countermodel
gap for this illustrative table family is asserted.
-/

private def graph := HedgeChannelConstruction.graph
private def signature := HedgeChannelConstruction.signature

private def table : BooleanChannelTable (Fin 2) :=
  BooleanChannelTable.ofCapacity (List.finRange 2) (fun channel => channel.val + 1) 5 (by decide +kernel)

private def tables (_child : Fin signature.count) : BooleanChannelTable (Fin 2) := table

private def signals : Causality.HedgeChannelTable.Signals graph 2 :=
  fun child parents inputs channel => Bool.xor
    (PairRootChannels.inputIncidence graph.binary 2 NodeSet.full child inputs channel)
    (if edge : signature.directed HedgeChannelConstruction.actionNode child = true then
      parents HedgeChannelConstruction.actionNode edge else false)

/-- The genuine functionalized model is canonically semi-Markovian and
projects to exactly the bow graph; channel vectors add no global source. -/
theorem actual_model_compatible :
    Compatible (Causality.HedgeChannelTable.model graph 2 tables signals) graph.binary :=
  Causality.HedgeChannelTable.model_compatible graph 2 tables signals

/-- Full observed support is a theorem of the actual model semantics,
including the parent-responsive row, without invoking soundness. -/
theorem actual_model_positive : ObservationallyPositive (Causality.HedgeChannelTable.model graph 2 tables signals) :=
  Causality.HedgeChannelTable.model_positive graph 2 tables signals

private def shared : (PairRootChannels.extension graph.binary 2).Assignment := fun _ _ => false
private def sample : signature.binary.Assignment := fun node => decide (node.val = 0)
private def target : Fin signature.count -> Option Bool := fun node => if node.val = 0 then some true else none

/-- The matching forced action contributes exactly one.  The actual free
child reads the forced true parent and has numerator two at the false sample.
Only these row cells, not any SCM private response enumeration, are reduced. -/
theorem forced_private_product :
    ((FiniteProduct.qProduct signature.count (fun child => (Causality.HedgeChannelTable.cpt graph 2 tables signals).sliceFactors
      target shared sample ((Causality.HedgeChannelTable.cpt graph 2 tables signals).privateRoot child))).num : Int) = 2 := by
  have expanded := Causality.HedgeChannelTable.privateProduct_num_expansion graph 2 tables signals target shared sample
  exact expanded.trans (by decide +kernel)

/-- Proper selection of one connected channel cancels the full character
against the actual pair-root prior.  The second selection remains arbitrary. -/
theorem actual_prior_cancels (secondSelection : NodeSet signature) (phases : Fin 2 -> Bool) :
    (PairRootChannels.prior graph 2).signedMass (fun assignment => FiniteProduct.iProduct 2
      (fun channel => FiniteProbRecord.characterSign (Bool.xor (phases channel)
        (hedgeChannelIncidenceParity graph NodeSet.full
          (if channel.val = 0 then NodeSet.singleton HedgeChannelConstruction.actionNode else secondSelection)
          (fun root => assignment root channel))))) = 0 :=
  PairRootChannels.prior_character_signedMass_zero graph 2 (fun _ => NodeSet.full)
    (fun channel => if channel.val = 0 then NodeSet.singleton HedgeChannelConstruction.actionNode else secondSelection)
    phases 0 HedgeChannelConstruction.witness.large_forest.component (by intro node _selected; rfl)
    HedgeChannelConstruction.outcomeNode (by decide +kernel)
    (by change NodeSet.singleton HedgeChannelConstruction.actionNode HedgeChannelConstruction.outcomeNode = false; decide +kernel)
    HedgeChannelConstruction.actionNode
    (by change NodeSet.singleton HedgeChannelConstruction.actionNode HedgeChannelConstruction.actionNode = true; decide +kernel)

end HedgeChannelTable
end Examples
end Causality
end Thesis
