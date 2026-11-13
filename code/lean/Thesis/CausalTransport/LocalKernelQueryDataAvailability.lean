import Thesis.CausalTransport.LocalKernelDataAvailability
import Thesis.CausalTransport.LocalKernelQueryCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {correct : DSeparationCorrectness G}

/-!
# Query transformations preserve printed-data availability

The query wrappers do not introduce a new observed conditional or quotient.
Their probability expression and primitive data are inherited unchanged;
only the source query and its graph-rule/equality nodes change.  Thus the
constructor availability invariant passes through the same actual wrappers
without a new observational-overlap or causal-support premise.

These are the wrappers used by the fuel-recursive guarded compiler: deletion
and addition of actions, uncut ancestral pruning, incoming-cut action
augmentation and containing-component restriction.  They retain their
proved graph geometry and literal target syntax.  This module does not
replace those rules by semantic equalities or assume availability of the
entire successful engine output.
-/

namespace PublishedLocalKernelCompilation.PrintedAvailable

/-- Action deletion only prepends a rule and retains the nested data. -/
noncomputable def prependDeleteActions (x y z : NodeSet S)
    (application : PathDoRuleApplication G (rule3Left x y z NodeSet.empty) (rule3Right x y z NodeSet.empty))
    {nested : PublishedLocalKernelCompilation G correct y x} (available : nested.PrintedAvailable) :
    (PublishedLocalKernelCompilation.prependDeleteActions x y z application nested).PrintedAvailable :=
  fun model projected reference supported => available model projected reference supported

/-- Reversed action addition likewise creates no new printed demand. -/
noncomputable def prependAddActions (x y z : NodeSet S)
    (application : PathDoRuleApplication G (rule3Left x y z NodeSet.empty) (rule3Right x y z NodeSet.empty))
    {nested : PublishedLocalKernelCompilation G correct y (NodeSet.union x z)} (available : nested.PrintedAvailable) :
    (PublishedLocalKernelCompilation.prependAddActions x y z application nested).PrintedAvailable :=
  fun model projected reference supported => available model projected reference supported

end PublishedLocalKernelCompilation.PrintedAvailable

/-- Pruning uses uncut ancestry and the same source-aligned rule-3 wrapper.
The kept kernel's availability supplies the unchanged printed expression. -/
noncomputable def localKernelPruneCompilation_printedAvailable
    {remaining externalAction : NodeSet S} (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining) (disjoint : NodeSet.Disjoint action outcome)
    {nested : PublishedLocalKernelCompilation G correct outcome
      (NodeSet.union externalAction (NodeSet.inter action (G.ancestralSet remaining (.none S) outcome)))}
    (available : nested.PrintedAvailable) :
    (localKernelPruneCompilation closed action outcome actionSubset outcomeSubset disjoint nested).PrintedAvailable :=
  fun model projected reference supported => available model projected reference supported

/-- The incoming-cut additional-action step changes no printed factor.
Its separate graph proof is retained by the actual compiler constructor. -/
noncomputable def localKernelAdditionalActionCompilation_printedAvailable
    {remaining externalAction : NodeSet S} (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S)
    (disjoint : NodeSet.Disjoint (NodeSet.inter action remaining) (NodeSet.inter outcome remaining))
    {nested : PublishedLocalKernelCompilation G correct (NodeSet.inter outcome remaining)
      (NodeSet.union externalAction (NodeSet.union (NodeSet.inter action remaining)
        (identificationAdditionalAction G remaining outcome action)))}
    (available : nested.PrintedAvailable) :
    (localKernelAdditionalActionCompilation closed action outcome disjoint nested).PrintedAvailable :=
  fun model projected reference supported => available model projected reference supported

/-- Containing-component recursion only reindexes the already fixed actions.
The discarded-action subset remains a structural premise, not a new local
probability-support assumption. -/
noncomputable def localKernelRestrictionCompilation_printedAvailable
    (remaining kept externalAction action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining) (discarded : NodeSet.Subset (NodeSet.diff remaining kept) action)
    {nested : PublishedLocalKernelCompilation G correct outcome
      (NodeSet.union (NodeSet.union externalAction (NodeSet.diff remaining kept)) (NodeSet.inter action kept))}
    (available : nested.PrintedAvailable) :
    (localKernelRestrictionCompilation remaining kept externalAction action outcome actionSubset discarded nested).PrintedAvailable :=
  fun model projected reference supported => available model projected reference supported

end Causality
end Thesis
