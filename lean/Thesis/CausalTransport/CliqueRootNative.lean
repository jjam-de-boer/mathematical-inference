import Thesis.CausalTransport.LatentRootNativeEvaluation
import Thesis.CausalTransport.HiddenDAGCollapse
import Thesis.Causality.LatentRootGrouping

namespace Thesis.Causality

open Probability

/-!
# Native realization on the fixed clique-root DAG

Combine arbitrary-topology hidden elimination, independent grouping by exact
child masks, and the proved native realization of a root model. The result is
an actual `FiniteHiddenDAGSCM` on the same graph-fixed `cliqueRootProjection`
for every original full DAG with the required observed projection.

The grouped extension's root projection and the graph's clique projection
have literally equal graph data. Transporting a native record along that
proved equality is not a semantic interface: the probability preservation
lemma for transport is equality elimination, and each preceding probability
comparison is an independently proved construction. Multi-child roots,
observational zeros and every declared intervention value are retained.
-/

universe u
variable {S : ObservedSignature.{u}} {P Q : FiniteLatentProjection S}

namespace FiniteHiddenDAGSCM

/-- Change only the proof-indexed projection presentation along a proved
equality. Source alphabets, equations and probability data are not replaced. -/
def reindexProjection (original : FiniteHiddenDAGSCM S P) (same : P = Q) : FiniteHiddenDAGSCM S Q := same ▸ original

theorem reindexProjection_interventionalValue (original : FiniteHiddenDAGSCM S P) (same : P = Q)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    (original.reindexProjection same).interventionalValue intervention event = original.interventionalValue intervention event := by
  cases same
  rfl

theorem reindexProjection_observationalValue (original : FiniteHiddenDAGSCM S P) (same : P = Q) (event : Event S.Assignment) :
    (original.reindexProjection same).observationalValue event = original.observationalValue event := by
  cases same
  rfl

end FiniteHiddenDAGSCM

namespace FiniteLatentSCM

variable (original : ExactModel S) (graph : ObservedGraph S)
variable (projected : ∀ left right, original.latent.projectedBidirected left right = graph.bidirected left right)

theorem cliqueGroupedLatent_rootProjection :
    (original.cliqueGroupedLatent graph projected).rootProjection = graph.cliqueRootProjection := by
  apply FiniteLatentProjection.eq_of_graph_data
    (left := (original.cliqueGroupedLatent graph projected).rootProjection)
    (right := graph.cliqueRootProjection) rfl
  funext left right
  exact graph.cliqueRootIncident_projected left right

/-- The target projection is fixed by `graph`, not by the input root count
or hidden topology. No canonical-root compatibility proof is requested. -/
def toCliqueRootNative : FiniteHiddenDAGSCM S graph.cliqueRootProjection :=
  (LatentRootNative.model (original.cliqueGroupedModel graph projected)).reindexProjection
    (original.cliqueGroupedLatent_rootProjection graph projected)

theorem toCliqueRootNative_interventionalValue (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((original.toCliqueRootNative graph projected).interventionalValue intervention event)
      (original.interventionalValue intervention.value event) := by
  unfold toCliqueRootNative
  rw [FiniteHiddenDAGSCM.reindexProjection_interventionalValue]
  exact QProb.equiv_trans (LatentRootNative.interventionalValue (original.cliqueGroupedModel graph projected) intervention event)
    (original.cliqueGroupedModel_interventionalValue graph projected intervention.value event)

theorem toCliqueRootNative_observationalValue (event : Event S.Assignment) :
    QProb.Equiv ((original.toCliqueRootNative graph projected).observationalValue event) (original.observationalValue event) :=
  original.toCliqueRootNative_interventionalValue graph projected (HardIntervention.empty S) event

end FiniteLatentSCM

namespace FiniteHiddenDAGSCM

variable (original : FiniteHiddenDAGSCM S P) (graph : ObservedGraph S)
variable (projected : ∀ left right, P.observedGraph.bidirected left right = graph.bidirected left right)

/-- Actual projection-wide native reduction. The original graph is allowed
arbitrary finite hidden topology and alphabets. The output graph is fixed. -/
def toCliqueRootSCM : FiniteHiddenDAGSCM S graph.cliqueRootProjection :=
  original.toLatentRootSCM.toCliqueRootNative graph
    (fun left right => (original.toLatentRootSCM_projectedGraph left right).trans (projected left right))

theorem toCliqueRootSCM_interventionalValue (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((original.toCliqueRootSCM graph projected).interventionalValue intervention event)
      (original.interventionalValue intervention event) := by
  have preserved := original.toLatentRootSCM.toCliqueRootNative_interventionalValue graph
    (fun left right => (original.toLatentRootSCM_projectedGraph left right).trans (projected left right)) intervention event
  rw [original.toLatentRootSCM_interventionalValue] at preserved
  exact preserved

theorem toCliqueRootSCM_observationalValue (event : Event S.Assignment) :
    QProb.Equiv ((original.toCliqueRootSCM graph projected).observationalValue event) (original.observationalValue event) :=
  original.toCliqueRootSCM_interventionalValue graph projected (HardIntervention.empty S) event

theorem toCliqueRootSCM_eventPositive_iff (intervention : HardIntervention S) (evidence : Event S.Assignment) :
    ((original.toCliqueRootSCM graph projected).interventionalDist intervention).EventPositive evidence ↔
      (original.interventionalDist intervention).EventPositive evidence :=
  QProb.equiv_num_pos_iff (original.toCliqueRootSCM_interventionalValue graph projected intervention evidence)

end FiniteHiddenDAGSCM
end Thesis.Causality
