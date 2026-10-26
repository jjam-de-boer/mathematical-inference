import Thesis.CausalTransport.BinaryInstrumental.Representation
import Thesis.Probability.FiniteProductReindex

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Exact fixed-law feasibility for the binary instrumental-variable graph

The independent instrument factor is not a free optimization variable: it
is the marginal of the supplied whole observed law.  With that coefficient
fixed, the eight joint-cell equations are linear constraints on the sixteen
response-profile masses.  Joint cells, rather than totalized conditionals,
retain the meaning of these equations when an instrument value has no mass.

This module checks both boundaries of that reduction.  The eight equations
are equivalent to agreement on *every* observed event, and feasible response
records correspond to actual native SCMs on the specified original hidden
DAG.  Conversely, every native SCM with the whole law supplies a feasible
response record and both intervention risks on the same weights.  Hidden and
private-noise alphabet sizes remain arbitrary finite sizes; no monotonicity
or positivity assumption is inserted into the model class.

The attainable-pair equivalence is deliberately simultaneous.  It does not
allow a different response law for each arm, which would lose the dependence
needed for a sharp average-treatment-effect argument. These theorems justify
the exact feasible set used by `BinaryInstrumental.ComputedBounds`.
-/

variable {P : FiniteLatentProjection signature}

def instrumentMarginal (law : FiniteProbRecord signature.Assignment) : FiniteProbRecord Bool :=
  law.map (fun sample => sample z)

/-- A fixed *whole* law, not merely an instrument or outcome marginal. -/
def HasObservedLaw (native : FiniteHiddenDAGSCM signature P)
    (law : FiniteProbRecord signature.Assignment) : Prop :=
  forall event, QProb.Equiv (native.observationalValue event) (law.probVal event)

/-- The eight linear joint-cell constraints.  Normalization and nonnegative
rational weights come from the actual supplied finite response record. -/
def FeasibleResponses (law : FiniteProbRecord signature.Assignment)
    (responses : FiniteProbRecord Profile) : Prop :=
  forall instrument treatment outcome : Bool,
    QProb.Equiv (law.probVal (observedCell instrument treatment outcome))
      (QProb.mul ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent instrument))
        (responses.probVal (responseCell instrument treatment outcome)))

private theorem observedCell_singleton (reference : signature.Assignment) :
    observedCell (reference z) (reference x) (reference y) =
      FiniteProbRecord.singletonEvent reference := by
  funext sample
  apply Bool.eq_iff_iff.mpr
  simp only [observedCell, FiniteProbRecord.singletonEvent, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨atZ, atX, atY⟩
    funext node
    rcases node_cases node with same | same | same <;> subst node
    · exact atZ
    · exact atX
    · exact atY
  · intro same
    subst sample
    exact ⟨rfl, rfl, rfl⟩

/-- Eight-cell agreement really is whole-law agreement.  The explicit
assignment enumeration supplies completeness without classical function
equality, and singleton reduction does not cancel any cell probability. -/
theorem feasibleResponses_iff (law : FiniteProbRecord signature.Assignment)
    (responses : FiniteProbRecord Profile) :
    FeasibleResponses law responses ↔
      forall event, QProb.Equiv ((observedRecord (instrumentMarginal law) responses).probVal event)
        (law.probVal event) := by
  constructor
  · intro feasible
    apply FiniteProbRecord.probVal_extensional_of_singletons _ _ signature.assignmentEnumeration
      signature.assignmentEnumeration_nodup signature.assignmentEnumeration_complete
    intro reference
    rw [← observedCell_singleton reference]
    exact QProb.equiv_trans
      (observedRecord_cell (instrumentMarginal law) responses (reference z) (reference x) (reference y))
      (QProb.equiv_symm (feasible (reference z) (reference x) (reference y)))
  · intro whole instrument treatment outcome
    exact QProb.equiv_trans (QProb.equiv_symm (whole (observedCell instrument treatment outcome)))
      (observedRecord_cell (instrumentMarginal law) responses instrument treatment outcome)

/-- Changing the instrument record to an equal complete marginal preserves
even observed events that mix instrument, treatment and outcome coordinates. -/
theorem observedRecord_instrument_congr (left right : FiniteProbRecord Bool)
    (responses : FiniteProbRecord Profile)
    (equal : forall event, QProb.Equiv (left.probVal event) (right.probVal event))
    (event : Event signature.Assignment) :
    QProb.Equiv ((observedRecord left responses).probVal event)
      ((observedRecord right responses).probVal event) :=
  QProb.equiv_trans
    ((left.product responses).map_probVal (fun pair => observedAssignment pair.1 pair.2) event)
    (QProb.equiv_trans
      (left.product_swap_probVal responses (fun pair => event (observedAssignment pair.1 pair.2)))
      (QProb.equiv_trans
        (responses.product_probVal_equiv_of_slices left right
          (fun pair => event (observedAssignment pair.2 pair.1))
          (fun pair => event (observedAssignment pair.2 pair.1))
          (fun profile => equal (fun value => event (observedAssignment value profile))))
        (QProb.equiv_symm
          (QProb.equiv_trans
            ((right.product responses).map_probVal (fun pair => observedAssignment pair.1 pair.2) event)
            (right.product_swap_probVal responses (fun pair => event (observedAssignment pair.1 pair.2)))))))

/-- The response record extracted from *any* native SCM with this law is
feasible with the observed, fixed instrument marginal. -/
theorem native_responses_feasible (native : FiniteHiddenDAGSCM signature P)
    (graphMatch : HasIVProjection P) (law : FiniteProbRecord signature.Assignment)
    (observed : HasObservedLaw native law) :
    FeasibleResponses law (responseRepresentation native graphMatch).responses := by
  let representation := responseRepresentation native graphMatch
  have marginal (event : Event Bool) : QProb.Equiv (representation.instrument.probVal event)
      ((instrumentMarginal law).probVal event) :=
    QProb.equiv_trans (representation.instrument_observable event)
      (QProb.equiv_trans (observed (fun sample => event (sample z)))
        (QProb.equiv_symm (law.map_probVal (fun sample => sample z) event)))
  apply (feasibleResponses_iff law representation.responses).mpr
  intro event
  exact QProb.equiv_trans
    (observedRecord_instrument_congr (instrumentMarginal law) representation.instrument
      representation.responses (fun event => QProb.equiv_symm (marginal event)) event)
    (QProb.equiv_trans (QProb.equiv_symm (representation.observational event)) (observed event))

/-- A feasible profile record supplies an actual model on the original DAG
with the fixed whole law, not a surrogate or a relaxation of that class. -/
theorem nativeProfileModel_hasObservedLaw (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (responses : FiniteProbRecord Profile) (feasible : FeasibleResponses law responses) :
    HasObservedLaw (nativeProfileModel projection graphMatch (instrumentMarginal law) responses) law :=
  fun event => QProb.equiv_trans
    (nativeProfileModel_observationalValue projection graphMatch (instrumentMarginal law) responses event)
    ((feasibleResponses_iff law responses).mp feasible event)

/-- Both risks must be witnessed by one actual native model. -/
def RisksAttainableAt (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) (risks : Bool → QProb) : Prop :=
  ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law ∧
    forall action, QProb.Equiv
      (native.interventionalValue (intervention action) (fun sample => sample y)) (risks action)

/-- Exact feasible-set transfer for the pair of treatment risks.  The
forward direction retains arbitrary native alphabets; the reverse direction
constructs one original-DAG SCM realizing both risks at once. -/
theorem risksAttainableAt_iff (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (risks : Bool → QProb) :
    RisksAttainableAt projection law risks ↔
      ∃ responses : FiniteProbRecord Profile, FeasibleResponses law responses ∧
        forall action, QProb.Equiv ((effectRecord responses action).probVal id) (risks action) := by
  constructor
  · rintro ⟨native, observed, attained⟩
    let representation := responseRepresentation native graphMatch
    refine ⟨representation.responses, native_responses_feasible native graphMatch law observed, ?_⟩
    intro action
    exact QProb.equiv_trans (QProb.equiv_symm (representation.interventional action)) (attained action)
  · rintro ⟨responses, feasible, attained⟩
    refine ⟨nativeProfileModel projection graphMatch (instrumentMarginal law) responses,
      nativeProfileModel_hasObservedLaw projection graphMatch law responses feasible, ?_⟩
    intro action
    exact QProb.equiv_trans
      (nativeProfileModel_interventionalValue projection graphMatch (instrumentMarginal law) responses action)
      (attained action)

end BinaryInstrumental
end Causality
end Thesis
