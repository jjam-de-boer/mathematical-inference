import Thesis.CausalTransport.ModalRealization
import Thesis.CausalTransport.HedgeChannelCompleteness
import Thesis.CausalTransport.Soundness

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}}

/-!
# Modal completeness using the implemented positive-class theorems

The older modal transport equivalences accept a completeness record as an
argument.  That is useful for an abstract interface, but does not itself
instantiate the record.  Here the forward constructors use the *proved*
`ObservedGraph.publishedCompleteness`, and the reverse direction uses the
independently proved `ObservedGraph.publishedSoundness`.

Both joint ID and recursive conditional IDC retain the positive model class.
Neither a modal trace nor its executable realization enlarges that class to
all zero-containing models.  A mode-indexed application additionally carries
compatibility and observational positivity of the stored model.  The general
support-aware native connection is separate: it must retain local demands,
not manufacture positive membership for a model containing observed zeros.
-/

namespace ObservedGraph

/-- Completeness produces the actual joint certificate and its modal trace;
no external completeness or soundness interface is an input. -/
noncomputable def positiveJointModalCompleteness
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S)
    (identified : (GraphModelClass.positive graph).identifiable query) :
    ModalEncodedJointDerivation graph query (GraphModelClass.positive graph) :=
  (transport_joint_completeness (graph.publishedCompleteness rich) query identified).toModal

/-- The conditional constructor uses the completed recursive IDC theorem,
not an independent joint numerator assumption or a Bayes-only substitute. -/
noncomputable def positiveConditionalModalCompleteness
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S)
    (identified : (GraphModelClass.positive graph).conditionalIdentifiable query) :
    ModalEncodedConditionalDerivation graph query (GraphModelClass.positive graph) :=
  (transport_conditional_completeness (graph.publishedCompleteness rich) query identified).toModal

/-- The modal proof objects characterize exactly the same positive-class
identification predicate as the implemented joint theorem. -/
theorem positive_joint_modal_iff
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) :
    (GraphModelClass.positive graph).identifiable query ↔
      Nonempty (ModalEncodedJointDerivation graph query (GraphModelClass.positive graph)) := by
  constructor
  · intro identified
    exact ⟨graph.positiveJointModalCompleteness rich query identified⟩
  · rintro ⟨encoded⟩
    exact encoded.identifiable graph.publishedSoundness

theorem positive_conditional_modal_iff
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) :
    (GraphModelClass.positive graph).conditionalIdentifiable query ↔
      Nonempty (ModalEncodedConditionalDerivation graph query (GraphModelClass.positive graph)) := by
  constructor
  · intro identified
    exact ⟨graph.positiveConditionalModalCompleteness rich query identified⟩
  · rintro ⟨encoded⟩
    exact encoded.identifiable graph.publishedSoundness

end ObservedGraph

namespace CausalMode

/-- Anchor a computed positive-class joint proof at an actually positive
mode model.  Membership is stored for later executable interpretation. -/
noncomputable def positiveJointModalCompleteness
    (mode : CausalMode S) (graph : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (member : (GraphModelClass.positive graph).Mem mode.record.model)
    (query : JointKernelQuery S)
    (identified : (GraphModelClass.positive graph).identifiable query) :
    ModeIndexedJointDerivationIn mode (GraphModelClass.positive graph) query where
  member := member
  encoded := graph.positiveJointModalCompleteness rich query identified

noncomputable def positiveConditionalModalCompleteness
    (mode : CausalMode S) (graph : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (member : (GraphModelClass.positive graph).Mem mode.record.model)
    (query : ConditionalKernelQuery S)
    (identified : (GraphModelClass.positive graph).conditionalIdentifiable query) :
    ModeIndexedConditionalDerivationIn mode (GraphModelClass.positive graph) query where
  member := member
  encoded := graph.positiveConditionalModalCompleteness rich query identified

/-- The concrete mode-indexed endpoint, with both mathematical packages
inhabited internally rather than left as extra theorem inputs. -/
theorem positive_joint_modal_iff
    (mode : CausalMode S) (graph : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (query : JointKernelQuery S) :
    ((GraphModelClass.positive graph).Mem mode.record.model ∧
      (GraphModelClass.positive graph).identifiable query) ↔
      Nonempty (ModeIndexedJointDerivationIn mode (GraphModelClass.positive graph) query) :=
  mode.transported_joint_iff_in (GraphModelClass.positive graph)
    (graph.publishedCompleteness rich) graph.publishedSoundness query

theorem positive_conditional_modal_iff
    (mode : CausalMode S) (graph : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (query : ConditionalKernelQuery S) :
    ((GraphModelClass.positive graph).Mem mode.record.model ∧
      (GraphModelClass.positive graph).conditionalIdentifiable query) ↔
      Nonempty (ModeIndexedConditionalDerivationIn mode (GraphModelClass.positive graph) query) :=
  mode.transported_conditional_iff_in (GraphModelClass.positive graph)
    (graph.publishedCompleteness rich) graph.publishedSoundness query

end CausalMode
end Causality
end Thesis
