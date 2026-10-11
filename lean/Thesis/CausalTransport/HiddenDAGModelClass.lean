import Thesis.CausalTransport.HiddenDAGSemantics

namespace Thesis
namespace Causality

/-!
# Model classes within the full finite hidden-DAG semantics

Like `GraphModelClass`, this class selects actual executable SCM records by
a membership predicate.  The ambient domain is every finite model over the
given original hidden DAG: hidden and private-noise alphabets are not fixed
by the class.  Observed alphabets remain the supplied signature's alphabets.

This is different from an arbitrary indexed `HiddenDAGModelFamily`, whose
selection may identify more than the graph alone does.  `all` selects every
original-DAG record and permits observational zeros; `positive` selects every
such record with a strictly positive observed distribution.  Neither class
asserts that the forward collapse has canonical pairwise roots.

Joint identifiability compares full partial kernel results.  Conditional
identifiability compares values on common support, without requiring equality
of support domains or manufacturing a value at a null conditioner.  The
explicit native countermodel records below use those same relations.

The established ID/IDC and certificate APIs use carrier universe zero.  As
in the adjacent realization modules, this places no bound on finite hidden
or private-noise cardinalities.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- A predicate on the complete collection of actual finite SCM records on
one original graph.  Graph compatibility is built into each record's type. -/
structure HiddenDAGModelClass (projection : FiniteLatentProjection S) where
  Mem : FiniteHiddenDAGSCM S projection → Prop

namespace FiniteHiddenDAGSCM

/-- Native full partial-result agreement for one kernel. -/
def KernelResultEquivalent (left right : FiniteHiddenDAGSCM S P) (kernel : Kernel S) : Prop :=
  forall assignment, Nonempty (ProbabilityResult.Equivalent
    (left.kernelDenote kernel assignment) (right.kernelDenote kernel assignment))

/-- Native conditional agreement only where both models actually supply a
supported result.  The support witnesses remain constructive value data. -/
def KernelAgreesOnCommonSupport (left right : FiniteHiddenDAGSCM S P) (kernel : Kernel S) : Prop :=
  forall assignment,
    left.TermSupportedAt (.kernel kernel) assignment →
    right.TermSupportedAt (.kernel kernel) assignment →
    Nonempty (ProbabilityResult.Equivalent
      (left.kernelDenote kernel assignment) (right.kernelDenote kernel assignment))

end FiniteHiddenDAGSCM

namespace HiddenDAGModelClass

/-- Every finite original-DAG model, including observed distributions with
zeros and arbitrary finite hidden/private-noise presentations. -/
def all (projection : FiniteLatentProjection S) : HiddenDAGModelClass projection where
  Mem := fun _ => True

/-- Every finite original-DAG model with positive observed atoms.  The class
does not fix hidden alphabets, noise alphabets or a particular mechanism. -/
def positive (projection : FiniteLatentProjection S) : HiddenDAGModelClass projection where
  Mem := fun model => model.ObservationallyPositive

def Subset (left right : HiddenDAGModelClass P) : Prop :=
  forall model, left.Mem model → right.Mem model

theorem positive_subset_all : (positive P).Subset (all P) := fun _ _ => trivial

/-- Joint identifiability in this actual original-DAG model class. -/
def identifiable (C : HiddenDAGModelClass P) (query : JointKernelQuery S) : Prop :=
  forall left right, C.Mem left → C.Mem right →
    left.ObservationalAgreement right →
    left.KernelResultEquivalent right query.operationKernel

/-- Conditional identifiability in the same class, on common support. -/
def conditionalIdentifiable (C : HiddenDAGModelClass P) (query : ConditionalKernelQuery S) : Prop :=
  forall left right, C.Mem left → C.Mem right →
    left.ObservationalAgreement right →
    left.KernelAgreesOnCommonSupport right query.operationKernel

/-- A larger class's agreement restricts to every subclass.  This is not a
claim of graph-identification equivalence for arbitrary selected families. -/
theorem identifiable_of_subset {left right : HiddenDAGModelClass P}
    (subset : left.Subset right) (query : JointKernelQuery S)
    (identified : right.identifiable query) : left.identifiable query := by
  intro first second firstMem secondMem observational
  exact identified first second (subset first firstMem) (subset second secondMem) observational

/-- Common-support conditional agreement likewise restricts to a subclass,
retaining the same two actual models and their support witnesses. -/
theorem conditionalIdentifiable_of_subset {left right : HiddenDAGModelClass P}
    (subset : left.Subset right) (query : ConditionalKernelQuery S)
    (identified : right.conditionalIdentifiable query) : left.conditionalIdentifiable query := by
  intro first second firstMem secondMem observational
  exact identified first second (subset first firstMem) (subset second secondMem) observational

end HiddenDAGModelClass

/-- Actual original-DAG records witnessing joint non-identifiability in a
stated class, not an assumed projection or countermodel-readiness interface. -/
structure HiddenDAGCounterexampleIn (C : HiddenDAGModelClass P) (query : JointKernelQuery S) where
  left : FiniteHiddenDAGSCM S P
  right : FiniteHiddenDAGSCM S P
  left_mem : C.Mem left
  right_mem : C.Mem right
  observationally_equal : left.ObservationalAgreement right
  query_separated : Not (left.KernelResultEquivalent right query.operationKernel)

/-- A conditional countermodel must separate actual values on common
support.  A mismatch consisting only of missing support would not suffice. -/
structure HiddenDAGConditionalCounterexampleIn (C : HiddenDAGModelClass P)
    (query : ConditionalKernelQuery S) where
  left : FiniteHiddenDAGSCM S P
  right : FiniteHiddenDAGSCM S P
  left_mem : C.Mem left
  right_mem : C.Mem right
  observationally_equal : left.ObservationalAgreement right
  query_separated : Not (left.KernelAgreesOnCommonSupport right query.operationKernel)

/-- The exhibited native pair directly refutes joint class identifiability. -/
theorem HiddenDAGCounterexampleIn.not_identifiable {C : HiddenDAGModelClass P}
    {query : JointKernelQuery S} (counterexample : HiddenDAGCounterexampleIn C query) :
    Not (C.identifiable query) := by
  intro identified
  exact counterexample.query_separated (identified counterexample.left counterexample.right
    counterexample.left_mem counterexample.right_mem counterexample.observationally_equal)

/-- A native common-support value disagreement directly refutes conditional
class identifiability, without deciding that semantic property by LEM. -/
theorem HiddenDAGConditionalCounterexampleIn.not_identifiable {C : HiddenDAGModelClass P}
    {query : ConditionalKernelQuery S} (counterexample : HiddenDAGConditionalCounterexampleIn C query) :
    Not (C.conditionalIdentifiable query) := by
  intro identified
  exact counterexample.query_separated (identified counterexample.left counterexample.right
    counterexample.left_mem counterexample.right_mem counterexample.observationally_equal)

end Causality
end Thesis
