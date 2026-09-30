import Thesis.CausalTransport.KernelHedgeTransport

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

/-!
# Structural failure extraction for current-kernel ID

The success compiler follows the corrected program by induction on fuel.
This module supplies its complementary graph-only argument: every actual
failure constructs a hedge for the invocation's query, including its external
actions.  The same two selected forests survive every recursive transport.
Their node sets agree with the failure record, and their large side remains
inside the current host.

The product collector is important.  Its first failing factor is recovered
from the computed outcomes by the existing `FirstFailureAt` data type, not
chosen from a propositional existence statement.  Induction then extracts
that factor's hedge and reconnects it to the parent query.

There is no fixed recursion-depth bound in this proof and no list of selected
branch-name stacks.  The current expression is arbitrary: failure extraction
uses only graph closure and well-formed query coordinates, not positivity,
semantic soundness, or an assumed completeness theorem.  A general positive
original-query countermodel is still needed for semantic completeness.
-/

/-! ## Failure coordinates retained throughout recursive transport -/

/-- A failure's forests, indexed by the query of the current invocation.

Keeping exact node-set alignment is stronger than merely producing some
hedge.  The host inclusion lets pruning and product transport use the actual
nested forest without imposing a new invariant on the caller. -/
structure CurrentKernelFailureHedge (G : ObservedGraph S)
    (remaining : NodeSet S) (query : JointKernelQuery S)
    (fail : IdentificationFail S) where
  witness : HedgeWitness G query
  large_eq : witness.large = fail.remaining
  small_eq : witness.small = fail.free
  remaining_subset : NodeSet.Subset fail.remaining remaining

/-- The extracted large forest lies in its invocation's host.  This follows
from the retained failure coordinates rather than a new graph assumption. -/
theorem CurrentKernelFailureHedge.large_subset
    {G : ObservedGraph S} {remaining : NodeSet S} {query : JointKernelQuery S}
    {fail : IdentificationFail S}
    (extracted : CurrentKernelFailureHedge G remaining query fail) :
    NodeSet.Subset extracted.witness.large remaining := by
  intro node selected
  apply extracted.remaining_subset node
  exact (congrArg (fun nodes => nodes node) extracted.large_eq).symm.trans selected

/-! ## Every failing recursive invocation yields its query's hedge -/

/-- Extract a hedge from every failed corrected-engine invocation.

Parent closure is propagated internally through uncut ancestral pruning and
containing-component restriction.  Each branch uses the action/outcome subset
and disjointness invariants of its own query.  Terminal success and unfinished
branches cannot supply the required failure equation; fuel exhaustion likewise
needs no separate assumption. -/
noncomputable def identifyKernelFuelFailedHedge
    {G : ObservedGraph S} (fuel : Nat) {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) (current : ProbabilityTerm S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    {fail : IdentificationFail S}
    (result : identifyKernelFuel fuel G remaining outcome action current = .failed fail) :
    CurrentKernelFailureHedge G remaining
      (currentKernelJointQuery closed action outcome outcomeSubset disjoint) fail := by
  induction fuel generalizing remaining externalAction action outcome current fail with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      have localAction : NodeSet.inter action remaining = action := by
        rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset actionSubset]
      have localOutcome : NodeSet.inter outcome remaining = outcome := by
        rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset outcomeSubset]
      simp only [identifyKernelFuel, localAction, localOutcome] at result
      split at result
      · cases result
      · rename_i actionNotEmpty
        split at result
        · rename_i ancestral
          split at result
          · rename_i noAdditional
            split at result
            · cases result
            · rename_i component oneComponent
              have componentEqual := cComponents_eq_of_singleton G
                (NodeSet.diff remaining action) oneComponent
              have outcomeInComponent : NodeSet.Subset outcome component := by
                rw [componentEqual]
                intro node selected
                exact Bool.and_eq_true_iff.mpr
                  ⟨outcomeSubset node selected, by rw [disjoint.symm node selected]; rfl⟩
              split at result
              · rename_i single
                -- Immediate failure uses both distinct ancestry guards:
                -- ordinary ancestry for the forest children, incoming-cut
                -- free ancestry for common-root reachability.
                have actionNonempty : NodeSet.isEmpty action = false := by
                  cases empty : NodeSet.isEmpty action with
                  | false => rfl
                  | true => exact False.elim (actionNotEmpty empty)
                cases result
                exact {
                  witness := currentKernelImmediateHedge closed action outcome actionSubset
                    outcomeSubset disjoint actionNonempty ancestral noAdditional oneComponent single
                  large_eq := rfl
                  small_eq := rfl
                  remaining_subset := fun _node selected => selected
                }
              · split at result
                · cases result
                · split at result
                  · rename_i larger containing
                    -- Restriction moves discarded actions into the external
                    -- block.  It neither resets the current expression nor
                    -- changes the intervention witnessed by the two forests.
                    have specification := containingCComponent_spec G remaining component containing
                    have largerSubset := cComponents_subset G remaining specification.1
                    have outcomeInLarger := outcomeInComponent.trans specification.2
                    let nested := inductionHypothesis (closed.restrict larger largerSubset)
                      (NodeSet.inter action larger) outcome (chainProductFrom remaining current larger)
                      (NodeSet.inter_subset_right _ _) outcomeInLarger
                      (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _)) result
                    have discarded : NodeSet.Subset (NodeSet.diff remaining larger) action := by
                      have obtained := currentKernelRestrictionDiscardedAction_of_containing G
                        remaining action (by simpa only [localAction] using oneComponent) containing
                      simpa only [localAction] using obtained
                    exact {
                      witness := currentKernelRestrictionHedge closed action outcome larger actionSubset
                        outcomeSubset disjoint largerSubset outcomeInLarger discarded nested.witness
                      large_eq := nested.large_eq
                      small_eq := nested.small_eq
                      remaining_subset := nested.remaining_subset.trans largerSubset
                    }
                  · cases result
            · let inputs := (G.cComponents (NodeSet.diff remaining action)).map
                (fun component => (ULift.up component : ULift.{u} (NodeSet S)))
              let run := fun (component : ULift.{u} (NodeSet S)) =>
                identifyKernelFuel fuel G remaining component.down
                  (NodeSet.diff remaining component.down) current
              -- Read the collector's first failed factor as data.  Its
              -- membership and exact failure equation justify the recursive
              -- invocation; no arbitrary witness or formula is selected.
              -- The legacy collector interface shares its input universe
              -- with the term universe.  Lifting finite Boolean node sets
              -- preserves arbitrary value universes without changing the
              -- engine's list, order, or selected component.
              let chosen := IdentificationOutcome.firstFailureAt_of_combine_map_eq_failed
                run inputs _ (by simpa only [inputs, run, List.map_map] using result)
              have listed : chosen.1.down ∈ G.cComponents (NodeSet.diff remaining action) := by
                rcases List.mem_map.mp chosen.2.mem with ⟨component, member, equal⟩
                exact (congrArg ULift.down equal) ▸ member
              let nested := inductionHypothesis closed (NodeSet.diff remaining chosen.1.down) chosen.1.down current
                (NodeSet.diff_subset_left _ _)
                ((cComponents_subset G _ listed).trans (NodeSet.diff_subset_left _ _))
                (NodeSet.disjoint_diff_right _ _) chosen.2.selected_eq_failed
              exact {
                witness := currentKernelProductHedge closed action outcome actionSubset outcomeSubset
                  disjoint noAdditional listed nested.witness nested.large_subset
                large_eq := nested.large_eq
                small_eq := nested.small_eq
                remaining_subset := nested.remaining_subset
              }
          · let additional := identificationAdditionalAction G remaining outcome action
            -- The added block contains no outcome.  The transport theorem
            -- rules out a hedge meeting only non-ancestors in that block.
            have additionalSubset := identificationAdditionalAction_subset_remaining G remaining outcome action
            have additionalDisjoint : NodeSet.Disjoint additional outcome := by
              simpa only [localOutcome] using identificationAdditionalAction_disjoint_outcome G remaining outcome action
            let nested := inductionHypothesis closed (NodeSet.union action additional) outcome current
              (NodeSet.union_subset actionSubset additionalSubset) outcomeSubset
              (NodeSet.disjoint_union_left_of disjoint additionalDisjoint) result
            exact {
              witness := currentKernelAdditionalActionHedge closed action outcome actionSubset
                outcomeSubset disjoint nested.witness
              large_eq := nested.large_eq
              small_eq := nested.small_eq
              remaining_subset := nested.remaining_subset
            }
        · let kept := G.ancestralSet remaining (GraphMutilation.none S) outcome
          -- Uncut ancestry keeps every outcome and preserves parent closure
          -- with the same external actions.  Incoming-cut routes stay inside
          -- this host, so actions pruned outside it can safely be restored.
          have outcomeInKept : NodeSet.Subset outcome kept := fun node selected =>
            ancestralSet_contains_targets G remaining (GraphMutilation.none S) outcome
              (outcomeSubset node selected) selected
          have keptSubset := ancestralSet_subset G remaining (GraphMutilation.none S) outcome
          let nested := inductionHypothesis (closed.ancestral outcome) (NodeSet.inter action kept) outcome
            (.marginalize (NodeSet.diff remaining kept) current) (NodeSet.inter_subset_right _ _) outcomeInKept
            (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _)) result
          exact {
            witness := currentKernelPruneHedge closed action outcome kept outcomeSubset disjoint
              (closed.ancestral outcome) outcomeInKept nested.witness nested.large_subset
            large_eq := nested.large_eq
            small_eq := nested.small_eq
            remaining_subset := nested.remaining_subset.trans keptSubset
          }

/-! ## Public failure witnesses the original joint query -/

/-- A failed public replacement-engine run has a hedge for the original
query, not merely for its final local component.  Full-host closure and query
well-formedness construct every recursion invariant internally.  No model
class, value-richness hypothesis, or countermodel theorem is assumed. -/
noncomputable def identifyJointKernelFailedHedge
    {G : ObservedGraph S} (query : JointKernelQuery S) {fail : IdentificationFail S}
    (result : identifyJointKernel G query = .failed fail) :
    CurrentKernelFailureHedge G NodeSet.full query fail := by
  let closed := ObservedGraph.KernelHostClosed.full G
  let extracted := identifyKernelFuelFailedHedge (kernelIdentificationFuel S) closed
    query.action query.outcome (observationalJointTerm S)
    (fun _node _selected => rfl) (fun _node _selected => rfl)
    query.action_outcome_disjoint result
  have queryEqual : currentKernelJointQuery closed query.action query.outcome
      (fun _node _selected => rfl) query.action_outcome_disjoint = query := by
    cases query
    simp only [currentKernelJointQuery, NodeSet.union_empty_left]
  exact queryEqual ▸ extracted

end Causality
end Thesis
