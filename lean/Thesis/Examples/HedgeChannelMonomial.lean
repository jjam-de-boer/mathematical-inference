import Thesis.CausalTransport.HedgeChannelMonomial
import Thesis.Examples.HedgeChannelConstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelMonomial

open Probability

/-!
# Actual monomial and survivor checks on a small bow

Two independent channels are installed at the bow's original pair root.
Both read the same directed-parent signal at the child, but each reads its
own independent channel bit.  Selecting a different channel at each row
therefore gives a nonzero pointwise coefficient and a zero actual integral.
The cancellation below uses the general monomial theorem, not an evaluation
of the private response-function prior.

The complete factual numerator is recovered from the channel expansion.
An intervention removes one row's channel choices, so only background terms
survive; the action-cut theorem checks an actual selected remaining term.
Zero channels and repeated local labels test two boundaries of the complete
expansion.  Repeated labels must retain multiplicity even though their chosen
channel index is the same.

These are regressions of universal algebra and action-cut lemmas.  They do
not constitute the graph-specific coefficient-matched countermodel family
or a replacement for its original-query causal-gap proof.
-/

private def signature := HedgeChannelConstruction.signature
private def graph := HedgeChannelConstruction.graph

private def table : BooleanChannelTable (Fin 2) :=
  BooleanChannelTable.ofCapacity (List.finRange 2) (fun channel => channel.val + 1) 5 (by decide +kernel)
private def tables (_child : Fin signature.count) := table
private def nodes (_channel : Fin 2) : NodeSet signature := NodeSet.full
private def parentSignal (child : Fin signature.count) (parents : signature.binary.ParentValues child) (_channel : Fin 2) : Bool :=
  if edge : signature.directed HedgeChannelConstruction.actionNode child = true then
    parents HedgeChannelConstruction.actionNode edge else false
private def signals := Causality.HedgeChannelTable.incidenceSignals graph 2 nodes parentSignal
private def sample : signature.binary.Assignment := fun _ => false
private def noTarget (_child : Fin signature.count) : Option Bool := none
private def mixedChoice (child : Fin signature.count) : Option (Fin 2) :=
  if child.val = 0 then some 0 else some 1

/-- The mixed-channel monomial really has coefficient two; it does not
vanish merely because a local amplitude has been set to zero. -/
theorem mixed_coefficient : Causality.HedgeChannelTable.choiceCoefficient tables noTarget sample mixedChoice = 2 := by
  decide +kernel

/-- Proper selection of the first connected channel cancels the actual
mixed row term, including its positive coefficient and second-channel term. -/
theorem mixed_actual_integral_zero :
    (PairRootChannels.prior graph.binary 2).signedMass
      (Causality.HedgeChannelTable.choiceMonomial graph 2 tables signals noTarget sample mixedChoice) = 0 :=
  Causality.HedgeChannelTable.choiceMonomial_signedMass_zero graph 2 tables nodes parentSignal noTarget sample
    mixedChoice 0 HedgeChannelConstruction.witness.large_forest.component (by intro _child _selected; rfl)
    HedgeChannelConstruction.outcomeNode (by rfl) (by decide +kernel)
    HedgeChannelConstruction.actionNode (by decide +kernel)

/-- Full expansion integrates to numerator 120.  Unlike row-wise averaging,
this retains the two full-channel interactions that survive the actual prior. -/
theorem factual_channel_expansion :
    (Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals noTarget sample : Int) = 120 :=
  (Causality.HedgeChannelTable.integratedNumerator_channelExpansion graph 2 tables nodes parentSignal noTarget sample).trans
    (by decide +kernel)

private def target (child : Fin signature.count) : Option Bool := if child.val = 0 then some false else none
private def remainingChoice (child : Fin signature.count) : Option (Fin 2) := if child.val = 0 then none else some 0

/-- The remaining selected term belongs to the intervention's actual
choice list.  The forced action row has no channel choices at all. -/
theorem remaining_choice_listed :
    remainingChoice ∈ FiniteProduct.enumeration signature.count (fun _ => Option (Fin 2))
      (fun child => (tables child).expansionChoicesUnder (target child)) := by
  decide +kernel

/-- Cutting a support vertex cancels the remaining channel term even
though its receiving child still has a nonzero local channel amplitude. -/
theorem cut_actual_integral_zero :
    (PairRootChannels.prior graph.binary 2).signedMass
      (Causality.HedgeChannelTable.choiceMonomial graph 2 tables signals target sample remainingChoice) = 0 :=
  Causality.HedgeChannelTable.choiceMonomial_signedMass_zero_of_forced graph 2 tables nodes parentSignal
    (fun _child _channel _member => rfl) target sample remainingChoice remaining_choice_listed 0
    HedgeChannelConstruction.witness.large_forest.component HedgeChannelConstruction.actionNode (by rfl)
    false (by rfl) HedgeChannelConstruction.outcomeNode (by rfl)

/-- The truncated whole likelihood retains numerator twenty.  Both
properly selected channel terms cancel; the background term remains. -/
theorem cut_channel_expansion :
    (Causality.HedgeChannelTable.integratedNumerator graph 2 tables signals target sample : Int) = 20 :=
  (Causality.HedgeChannelTable.integratedNumerator_channelExpansion graph 2 tables nodes parentSignal target sample).trans
    (by decide +kernel)

private def repeatedTable : BooleanChannelTable (Fin 2) :=
  BooleanChannelTable.ofCapacity [0, 0, 1] (fun channel => channel.val + 1) 6 (by decide +kernel)
private def repeatedTables (_child : Fin signature.count) := repeatedTable

/-- Repeating the first local channel label retains every repeated row
choice and full-channel interaction.  Deduplicating the choices would change
this actual numerator, so the general expansion must not do so. -/
theorem repeated_labels_channel_expansion :
    (Causality.HedgeChannelTable.integratedNumerator graph 2 repeatedTables signals noTarget sample : Int) = 176 :=
  (Causality.HedgeChannelTable.integratedNumerator_channelExpansion graph 2 repeatedTables nodes parentSignal noTarget sample).trans
    (by decide +kernel)

private def emptyTable : BooleanChannelTable (Fin 0) :=
  BooleanChannelTable.ofCapacity [] Fin.elim0 3 (by decide)
private def emptyTables (_child : Fin signature.count) := emptyTable
private def emptyNodes (channel : Fin 0) : NodeSet signature := Fin.elim0 channel
private def emptyParents (child : Fin signature.count) (_parents : signature.binary.ParentValues child) (channel : Fin 0) : Bool :=
  Fin.elim0 channel
private def emptySignals := Causality.HedgeChannelTable.incidenceSignals graph 0 emptyNodes emptyParents

/-- With zero channels there is one background-only row choice and the
empty channel product is one.  No fictitious root bit or selected channel
is introduced to make the grouping theorem apply at this boundary. -/
theorem zero_channels_expansion :
    (Causality.HedgeChannelTable.integratedNumerator graph 0 emptyTables emptySignals noTarget sample : Int) = 9 :=
  (Causality.HedgeChannelTable.integratedNumerator_channelExpansion graph 0 emptyTables emptyNodes emptyParents noTarget sample).trans
    (by decide +kernel)

end HedgeChannelMonomial
end Examples
end Causality
end Thesis
