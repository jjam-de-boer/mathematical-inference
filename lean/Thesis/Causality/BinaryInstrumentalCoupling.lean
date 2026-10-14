import Thesis.Causality.BinaryInstrumentalProfiles

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# The small transportation representation of binary-IV profiles

A response profile determines two factual `(X,Y)` pairs, one under each
instrument value.  If their treatment bits agree, their outcome bits must
agree too, since both read the same outcome response.  If the treatment bits
differ, both outcomes are available and no further restriction is imposed.
The resulting four-by-four coupling table has twelve permitted cells.

Conversely, a permitted pair determines the response profile except for one
outcome bit when both treatments agree.  `profileOfPair` fills that one bit
with an explicitly supplied Boolean.  It never chooses a profile from an
existence proof.  For any finite coupling concentrated on permitted pairs,
every supplied fill rule preserves the *whole* coupling law, even if the
record lists invalid pairs with zero weight.

This is a constructive route toward the specialized transportation problem
behind sharp binary-IV bounds.  At this stage no algorithm is asserted to
construct a coupling from arbitrary margins or to optimize its cells.
-/

abbrev TreatmentOutcome := Bool × Bool
abbrev ResponsePair := TreatmentOutcome × TreatmentOutcome

/-- Both factual pairs come from the same four-bit response profile. -/
def responsePair (profile : Profile) : ResponsePair :=
  ((treatmentAt profile false, outcomeAt profile (treatmentAt profile false)),
    (treatmentAt profile true, outcomeAt profile (treatmentAt profile true)))

/-- The four forbidden cells have equal treatment but unequal outcomes.
This predicate uses only constructive equality decisions on Boolean data. -/
def permittedPair (pair : ResponsePair) : Bool :=
  decide (pair.1.1 ≠ pair.2.1 ∨ pair.1.2 = pair.2.2)

theorem responsePair_permitted (profile : Profile) : permittedPair (responsePair profile) = true := by
  cases first : treatmentAt profile false <;> cases second : treatmentAt profile true <;>
    simp [permittedPair, responsePair, first, second]

/-- The observable cell of the selected instrument arm in a coupling table. -/
def couplingCell (instrument treatment outcome : Bool) : Event ResponsePair :=
  fun pair =>
    let selected := if instrument then pair.2 else pair.1
    decide (selected.1 = treatment) && decide (selected.2 = outcome)

theorem couplingCell_responsePair (instrument treatment outcome : Bool) (profile : Profile) :
    couplingCell instrument treatment outcome (responsePair profile) =
      responseCell instrument treatment outcome profile := by
  cases instrument with
  | false =>
      by_cases same : treatmentAt profile false = treatment <;>
        simp [couplingCell, responsePair, responseCell, same]
  | true =>
      by_cases same : treatmentAt profile true = treatment <;>
        simp [couplingCell, responsePair, responseCell, same]

/-- An actual coupling record, with the original rational weights retained. -/
def responseCoupling (responses : FiniteProbRecord Profile) : FiniteProbRecord ResponsePair :=
  responses.map responsePair

theorem responseCoupling_cell (responses : FiniteProbRecord Profile) (instrument treatment outcome : Bool) :
    QProb.Equiv ((responseCoupling responses).probVal (couplingCell instrument treatment outcome))
      (responses.probVal (responseCell instrument treatment outcome)) :=
  QProb.equiv_trans (responses.map_probVal responsePair (couplingCell instrument treatment outcome))
    (responses.probVal_congr _ _ (couplingCell_responsePair instrument treatment outcome))

/-- Structural consistency forces the complete mass onto permitted cells;
the input record need not have strictly positive atoms or unique labels. -/
theorem responseCoupling_permitted (responses : FiniteProbRecord Profile) :
    QProb.Equiv ((responseCoupling responses).probVal permittedPair) QProb.one :=
  QProb.equiv_trans (responses.map_probVal responsePair permittedPair)
    (QProb.equiv_trans (responses.probVal_congr _ topEvent (fun profile => responsePair_permitted profile))
      responses.normalization)

/-- Fill only the outcome of a treatment absent from both supplied arms.
When the treatments differ the fill bit is irrelevant; when they agree,
permittedness guarantees that either factual copy supplies the same outcome. -/
def profileOfPair (pair : ResponsePair) (unobservedOutcome : Bool) : Profile :=
  fun bit =>
    if bit.val = 0 then pair.1.1
    else if bit.val = 1 then pair.2.1
    else if bit.val = 2 then
      if pair.1.1 then (if pair.2.1 then unobservedOutcome else pair.2.2) else pair.1.2
    else
      if pair.1.1 then pair.1.2 else (if pair.2.1 then pair.2.2 else unobservedOutcome)

/-- A closed truth table checks this small universal data identity.  It
does not evaluate a probability model, a large source cube, or an optimizer. -/
theorem profileOfPair_responsePair : forall pair : ResponsePair, forall fill : Bool,
    permittedPair pair = true → responsePair (profileOfPair pair fill) = pair := by
  decide +kernel

/-- A coupling can be lifted by any explicit fill rule.  The rule may
depend on the observed pair, which is needed for opposing ATE endpoints. -/
def responsesOfCoupling (coupling : FiniteProbRecord ResponsePair) (fill : ResponsePair → Bool) :
    FiniteProbRecord Profile := coupling.map (fun pair => profileOfPair pair (fill pair))

/-- The lifted record preserves every event of the coupling, not just its
row and column margins.  Invalid zero-weight pairs are discarded only by
the proved probability-one event argument; they are not erased from the data. -/
theorem responsesOfCoupling_preserves (coupling : FiniteProbRecord ResponsePair)
    (permitted : QProb.Equiv (coupling.probVal permittedPair) QProb.one)
    (fill : ResponsePair → Bool) (event : Event ResponsePair) :
    QProb.Equiv ((responseCoupling (responsesOfCoupling coupling fill)).probVal event)
      (coupling.probVal event) :=
  QProb.equiv_trans
    ((responsesOfCoupling coupling fill).map_probVal responsePair event)
    (QProb.equiv_trans
      (coupling.map_probVal (fun pair => profileOfPair pair (fill pair)) (fun profile => event (responsePair profile)))
      (coupling.probVal_congr_on_probability_one permittedPair _ _ permitted
        (fun pair valid => congrArg event (profileOfPair_responsePair pair (fill pair) valid))))

/-- Hence each arm's observable table is preserved by every explicit fill
rule.  Intervention probabilities are intentionally not claimed preserved:
the free outcome bit is precisely what will be optimized. -/
theorem responsesOfCoupling_cell (coupling : FiniteProbRecord ResponsePair)
    (permitted : QProb.Equiv (coupling.probVal permittedPair) QProb.one)
    (fill : ResponsePair → Bool) (instrument treatment outcome : Bool) :
    QProb.Equiv ((responsesOfCoupling coupling fill).probVal (responseCell instrument treatment outcome))
      (coupling.probVal (couplingCell instrument treatment outcome)) :=
  QProb.equiv_trans
    (QProb.equiv_symm (responseCoupling_cell (responsesOfCoupling coupling fill) instrument treatment outcome))
    (responsesOfCoupling_preserves coupling permitted fill (couplingCell instrument treatment outcome))

end BinaryInstrumental
end Causality
end Thesis
