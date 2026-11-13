import Thesis.Causality.LatentTableResponse
import Thesis.Probability.FiniteRecordPerturbation

namespace Thesis
namespace Causality

open Probability

/-!
# Positive original-query countermodels from finite table responses

`LatentTableResponse` computes the full observed and intervened probabilities
of a one-node table replacement.  This module turns finite response checks
into actual positive countermodels for joint and conditional kernels.  The
models retain the supplied signature, all shared incidences, the directed
graph, every other local row, and the original query.

The common positive-row data and the observational cancellation are kept
separate.  A construction may reuse one supported shared assignment, verify
a balanced perturbation's factual cancellation, and then verify its causal
response gap.  A conditional gap compares the actual numerator/denominator
cross-products of these same models; unequal numerators alone do not suffice.

These constructors have no routing or alphabet restrictions, but they do
not prove that every hedge admits the supplied profile pair.  That existence
argument remains the universal completeness obligation.  This intrinsic
module imports neither soundness nor the external completeness interface.
-/

namespace FiniteLatentRationalCPT

variable {S : ObservedSignature.{0}}

/-- Two actual row profiles with a common explicit positivity witness.
Unused local configurations and other shared assignments may have zeros.
The graph is matched exactly, not merely bounded by a supergraph. -/
structure PositiveRowProfiles (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (graph : ObservedGraph S) where
  left : C.RowProfile pivot
  right : C.RowProfile pivot
  canonical : C.shared.CanonicalSemiMarkovian
  projected : forall first second,
    C.shared.projectedBidirected first second = graph.bidirected first second
  supportedShared : C.shared.Assignment
  sharedPositive : forall root,
    (C.sharedFactor root).EventPositive (FiniteProbRecord.singletonEvent (supportedShared root))
  awayPositive : forall (sample : S.Assignment) child, child ≠ pivot →
    (C.row child (C.rowConfiguration child supportedShared sample)).EventPositive
      (FiniteProbRecord.singletonEvent (sample child))
  leftPositive : forall sample : S.Assignment,
    (left (C.rowConfiguration pivot supportedShared sample)).EventPositive
      (FiniteProbRecord.singletonEvent (sample pivot))
  rightPositive : forall sample : S.Assignment,
    (right (C.rowConfiguration pivot supportedShared sample)).EventPositive
      (FiniteProbRecord.singletonEvent (sample pivot))

/-- Raw natural perturbations may be supplied separately at each local
configuration.  Each constructs its two normalized, strictly positive rows;
there is no bound on a direction weight and no chosen response function. -/
abbrev RowPerturbations (C : FiniteLatentRationalCPT S) (pivot : Fin S.count) :=
  Fin (C.configCount pivot) → FiniteRecordPerturbation (S.Value pivot)

def perturbationDecreaseCells (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (perturbations : C.RowPerturbations pivot) : C.CellProfile pivot :=
  fun configuration value => (perturbations configuration).decreaseCell value

def perturbationIncreaseCells (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (perturbations : C.RowPerturbations pivot) : C.CellProfile pivot :=
  fun configuration value => (perturbations configuration).increaseCell value

/-- Pointwise balance is an internal theorem of the generated rows. -/
theorem rowPerturbations_balanced (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (perturbations : C.RowPerturbations pivot) :
    C.CellsBalanced pivot
      (C.profileCells pivot (fun configuration => (perturbations configuration).leftRecord))
      (C.profileCells pivot (fun configuration => (perturbations configuration).rightRecord))
      (C.perturbationDecreaseCells pivot perturbations) (C.perturbationIncreaseCells pivot perturbations) :=
  fun configuration value => (perturbations configuration).cells_balanced value

/-- Construct, rather than assume, the replacement profiles' full support
and normalization.  The unchanged rows still need their ordinary supported-
shared positivity witness; graph compatibility remains exact. -/
def PositiveRowProfiles.ofPerturbations (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (graph : ObservedGraph S) (perturbations : C.RowPerturbations pivot)
    (canonical : C.shared.CanonicalSemiMarkovian)
    (projected : forall first second, C.shared.projectedBidirected first second = graph.bidirected first second)
    (supportedShared : C.shared.Assignment)
    (sharedPositive : forall root,
      (C.sharedFactor root).EventPositive (FiniteProbRecord.singletonEvent (supportedShared root)))
    (awayPositive : forall (sample : S.Assignment) child, child ≠ pivot →
      (C.row child (C.rowConfiguration child supportedShared sample)).EventPositive
        (FiniteProbRecord.singletonEvent (sample child))) :
    PositiveRowProfiles C pivot graph where
  left := fun configuration => (perturbations configuration).leftRecord
  right := fun configuration => (perturbations configuration).rightRecord
  canonical := canonical
  projected := projected
  supportedShared := supportedShared
  sharedPositive := sharedPositive
  awayPositive := awayPositive
  leftPositive := fun sample => (perturbations _).left_positive (sample pivot)
  rightPositive := fun sample => (perturbations _).right_positive (sample pivot)

/-- Observational equality is a finite response condition on the two
profiles, not a premise about unspecified SCMs.  Singleton response equality
will be proved to determine the full observed laws of the constructed pair. -/
structure PositiveRowPair (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (graph : ObservedGraph S) extends PositiveRowProfiles C pivot graph where
  observationalResponses : forall sample,
    QProb.Equiv (C.rowResponseWith pivot left C.sharedEnumeration (FiniteLatentSCM.noIntervention S) sample)
      (C.rowResponseWith pivot right C.sharedEnumeration (FiniteLatentSCM.noIntervention S) sample)

/-- Build the observationally invisible pair by checking the two
nonnegative parts of a balanced perturbation against the factual response.
The record stores actual normalized profiles; the perturbation parts need
not be probability records. -/
def PositiveRowProfiles.ofBalanced
    {C : FiniteLatentRationalCPT S} {pivot : Fin S.count} {graph : ObservedGraph S}
    (profiles : PositiveRowProfiles C pivot graph) (decrease increase : C.CellProfile pivot)
    (balanced : C.CellsBalanced pivot (C.profileCells pivot profiles.left)
      (C.profileCells pivot profiles.right) decrease increase)
    (cancelled : forall sample,
      QProb.Equiv (C.cellResponseWith pivot decrease C.sharedEnumeration (FiniteLatentSCM.noIntervention S) sample)
        (C.cellResponseWith pivot increase C.sharedEnumeration (FiniteLatentSCM.noIntervention S) sample)) :
    PositiveRowPair C pivot graph where
  toPositiveRowProfiles := profiles
  observationalResponses := fun sample =>
    (C.cellResponse_equiv_iff_of_balance pivot _ _ decrease increase balanced
      C.sharedEnumeration (FiniteLatentSCM.noIntervention S) sample).mpr (cancelled sample)

namespace PositiveRowPair

variable {C : FiniteLatentRationalCPT S} {pivot : Fin S.count} {graph : ObservedGraph S}

def leftModel (pair : PositiveRowPair C pivot graph) : ExactModel S :=
  (C.withRow pivot pair.left).toSCM

def rightModel (pair : PositiveRowPair C pivot graph) : ExactModel S :=
  (C.withRow pivot pair.right).toSCM

theorem left_mem (pair : PositiveRowPair C pivot graph) :
    (GraphModelClass.positive graph).Mem pair.leftModel :=
  ⟨C.withRow_toSCM_compatible pivot pair.left graph pair.canonical pair.projected,
    C.withRow_toSCM_positive pivot pair.left pair.supportedShared
      pair.sharedPositive pair.awayPositive pair.leftPositive⟩

theorem right_mem (pair : PositiveRowPair C pivot graph) :
    (GraphModelClass.positive graph).Mem pair.rightModel :=
  ⟨C.withRow_toSCM_compatible pivot pair.right graph pair.canonical pair.projected,
    C.withRow_toSCM_positive pivot pair.right pair.supportedShared
      pair.sharedPositive pair.awayPositive pair.rightPositive⟩

theorem observationally_equal (pair : PositiveRowPair C pivot graph) :
    ObservationallyEquivalent pair.leftModel pair.rightModel :=
  C.withRow_observationally_equivalent pivot pair.left pair.right C.sharedEnumeration
    C.sharedEnumeration_nodup C.sharedEnumeration_complete pair.observationalResponses

/-- Canonical finite event responses are convenient for checking query
gaps.  The observed enumeration contains every full original assignment. -/
def response (_pair : PositiveRowPair C pivot graph) (profile : C.RowProfile pivot)
    (kernel : Kernel S) (reference : S.Assignment) (event : Event S.Assignment) : QProb :=
  C.rowEventResponseWith pivot profile C.sharedEnumeration S.assignmentEnumeration
    (kernel.intervention reference) event

theorem left_response (pair : PositiveRowPair C pivot graph)
    (kernel : Kernel S) (reference : S.Assignment) (event : Event S.Assignment)
    (free : kernel.intervention reference pivot = none) :
    QProb.Equiv ((kernel.distribution pair.leftModel reference).probVal event)
      (pair.response pair.left kernel reference event) :=
  C.withRow_kernel_event_response pivot pair.left C.sharedEnumeration
    C.sharedEnumeration_nodup C.sharedEnumeration_complete S.assignmentEnumeration
    S.assignmentEnumeration_nodup S.assignmentEnumeration_complete kernel reference event free

theorem right_response (pair : PositiveRowPair C pivot graph)
    (kernel : Kernel S) (reference : S.Assignment) (event : Event S.Assignment)
    (free : kernel.intervention reference pivot = none) :
    QProb.Equiv ((kernel.distribution pair.rightModel reference).probVal event)
      (pair.response pair.right kernel reference event) :=
  C.withRow_kernel_event_response pivot pair.right C.sharedEnumeration
    C.sharedEnumeration_nodup C.sharedEnumeration_complete S.assignmentEnumeration
    S.assignmentEnumeration_nodup S.assignmentEnumeration_complete kernel reference event free

/-- A response gap at one original outcome cylinder refutes the entire
joint kernel's equivalence.  Only the supplied non-action pivot is changed;
the original action and outcome node sets are not altered. -/
noncomputable def jointCounterexample (pair : PositiveRowPair C pivot graph)
    (query : JointKernelQuery S) (reference : S.Assignment)
    (free : query.operationKernel.intervention reference pivot = none)
    (separated : Not (QProb.Equiv
      (pair.response pair.left query.operationKernel reference (Kernel.agreesOn query.outcome reference))
      (pair.response pair.right query.operationKernel reference (Kernel.agreesOn query.outcome reference)))) :
    CounterexampleIn (GraphModelClass.positive graph) query where
  left := pair.leftModel
  right := pair.rightModel
  left_mem := pair.left_mem
  right_mem := pair.right_mem
  observationally_equal := pair.observationally_equal
  query_separated := by
    intro equivalent
    rcases equivalent reference with ⟨between⟩
    have cells := ProbabilityResult.trans
      (ProbabilityResult.symm (Kernel.unconditionalDenote pair.leftModel query.outcome query.action reference))
      (ProbabilityResult.trans between
        (Kernel.unconditionalDenote pair.rightModel query.outcome query.action reference))
    cases cells with
    | value equal =>
        exact separated (QProb.equiv_trans
          (QProb.equiv_symm (pair.left_response query.operationKernel reference _ free))
          (QProb.equiv_trans equal (pair.right_response query.operationKernel reference _ free)))

/-- When a balanced perturbation cancels observationally but not against
the queried intervention, the response theorem supplies the joint gap.
No causal separation of the constructed models is assumed as a premise. -/
noncomputable def jointCounterexampleOfBalanced (pair : PositiveRowPair C pivot graph)
    (decrease increase : C.CellProfile pivot)
    (balanced : C.CellsBalanced pivot (C.profileCells pivot pair.left)
      (C.profileCells pivot pair.right) decrease increase)
    (query : JointKernelQuery S) (reference : S.Assignment)
    (free : query.operationKernel.intervention reference pivot = none)
    (separated : Not (QProb.Equiv
      (C.cellEventResponseWith pivot decrease C.sharedEnumeration S.assignmentEnumeration
        (query.operationKernel.intervention reference) (Kernel.agreesOn query.outcome reference))
      (C.cellEventResponseWith pivot increase C.sharedEnumeration S.assignmentEnumeration
        (query.operationKernel.intervention reference) (Kernel.agreesOn query.outcome reference)))) :
    CounterexampleIn (GraphModelClass.positive graph) query :=
  pair.jointCounterexample query reference free (fun equal => separated
    ((C.cellEventResponse_equiv_iff_of_balance pivot _ _ decrease increase balanced
      C.sharedEnumeration S.assignmentEnumeration (query.operationKernel.intervention reference)
      (Kernel.agreesOn query.outcome reference)).mp equal))

/-- Conditional separation must retain both actual conditioning
denominators.  Full observed positivity proves common support at the chosen
reference, and a cross-product gap then refutes agreement there.  This also
handles unequal conditioning marginals; no matched-denominator shortcut or
soundness theorem is used. -/
noncomputable def conditionalCounterexample (pair : PositiveRowPair C pivot graph)
    (query : ConditionalKernelQuery S) (reference : S.Assignment)
    (free : query.operationKernel.intervention reference pivot = none)
    (separated : Not (QProb.Equiv
      (QProb.mul
        (pair.response pair.left query.operationKernel reference (query.operationKernel.numeratorEvent reference))
        (pair.response pair.right query.operationKernel reference (query.operationKernel.conditionEvent reference)))
      (QProb.mul
        (pair.response pair.right query.operationKernel reference (query.operationKernel.numeratorEvent reference))
        (pair.response pair.left query.operationKernel reference (query.operationKernel.conditionEvent reference))))) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query where
  left := pair.leftModel
  right := pair.rightModel
  left_mem := pair.left_mem
  right_mem := pair.right_mem
  observationally_equal := pair.observationally_equal
  query_separated := by
    intro equivalent
    let kernel := query.operationKernel
    let leftLaw := kernel.distribution pair.leftModel reference
    let rightLaw := kernel.distribution pair.rightModel reference
    let leftNumerator := leftLaw.probVal (kernel.numeratorEvent reference)
    let rightNumerator := rightLaw.probVal (kernel.numeratorEvent reference)
    let leftDenominator := leftLaw.probVal (kernel.conditionEvent reference)
    let rightDenominator := rightLaw.probVal (kernel.conditionEvent reference)
    have leftPositive : 0 < leftDenominator.num :=
      pair.left_mem.2.kernel_cylinder_positive kernel kernel.condition reference
    have rightPositive : 0 < rightDenominator.num :=
      pair.right_mem.2.kernel_cylinder_positive kernel kernel.condition reference
    have leftValue : ProbabilityResult.Equivalent (query.sourceTerm.denote pair.leftModel reference)
        (some (QProb.div leftNumerator leftDenominator leftPositive)) := by
      change ProbabilityResult.Equivalent (ProbabilityResult.divide (some leftNumerator) (some leftDenominator)) _
      rw [ProbabilityResult.divide, dif_pos leftPositive]
      exact .value (QProb.equiv_refl _)
    have rightValue : ProbabilityResult.Equivalent (query.sourceTerm.denote pair.rightModel reference)
        (some (QProb.div rightNumerator rightDenominator rightPositive)) := by
      change ProbabilityResult.Equivalent (ProbabilityResult.divide (some rightNumerator) (some rightDenominator)) _
      rw [ProbabilityResult.divide, dif_pos rightPositive]
      exact .value (QProb.equiv_refl _)
    rcases equivalent reference
      (pair.left_mem.2.kernelPositiveSupportedValue kernel reference).toSupported
      (pair.right_mem.2.kernelPositiveSupportedValue kernel reference).toSupported with ⟨between⟩
    have ratios := ProbabilityResult.trans (ProbabilityResult.symm leftValue)
      (ProbabilityResult.trans between rightValue)
    cases ratios with
    | value equal =>
        have cross : QProb.Equiv (QProb.mul leftNumerator rightDenominator)
            (QProb.mul rightNumerator leftDenominator) := by
          simpa only [QProb.Equiv, QProb.mul, QProb.div,
            Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using equal
        exact separated (QProb.equiv_trans
          (QProb.equiv_symm (QProb.mul_congr
            (pair.left_response kernel reference (kernel.numeratorEvent reference) free)
            (pair.right_response kernel reference (kernel.conditionEvent reference) free)))
          (QProb.equiv_trans cross (QProb.mul_congr
            (pair.right_response kernel reference (kernel.numeratorEvent reference) free)
            (pair.left_response kernel reference (kernel.conditionEvent reference) free))))

end PositiveRowPair
end FiniteLatentRationalCPT
end Causality
end Thesis
