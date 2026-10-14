import Thesis.Causality.BinaryInstrumentalTransportation
import Thesis.CausalTransport.BinaryInstrumentalCoupling

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Actual native IV models from normalized transportation margins

The supplied row and flipped-column masses have one positive common total.
`ArmMarginals` checks their eight linear joint-cell equations against the
given *whole* observed record and its actual instrument marginal.  These
equations are meaningful also when an instrument value has probability zero;
the module never specifies a conditional at that null value.

Any diagonal-free table with those margins now gives a genuine permitted
coupling, a response record with any explicit unobserved-outcome fill rule,
and an actual native model on the original hidden DAG.  Whole observed-law
agreement is proved from the numeric equations and the already proved
realization, rather than assumed as a semantic field of an optimizer output.

The common total is supplied without a denominator cutoff.  Computing it
automatically from a given observed law, obtaining universal rational bounds
for arbitrary native response denominators, and choosing the sharp objective
fill rules remain later steps.  This module certifies the actual witness
construction needed by those steps; it does not claim they are complete.
-/

variable {P : FiniteLatentProjection signature}

/-- Eight actual joint-cell equations for normalized arm margins.  The
second arm's column outcome is flipped to match the transportation diagonal. -/
structure ArmMarginals (law : FiniteProbRecord signature.Assignment)
    (total : Nat) (positive : 0 < total) (rows columns : FourLabelTransportation.Masses) : Prop where
  false_cells : forall treatment outcome, QProb.Equiv (law.probVal (observedCell false treatment outcome))
    (QProb.mul ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent false))
      ⟨rows (encodeCategory treatment outcome), total, positive⟩)
  true_cells : forall treatment outcome, QProb.Equiv (law.probVal (observedCell true treatment outcome))
    (QProb.mul ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent true))
      ⟨columns (encodeCategory treatment (!outcome)), total, positive⟩)

theorem transportationCoupling_fits (law : FiniteProbRecord signature.Assignment)
    (total : Nat) (positive : 0 < total) (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (observed : ArmMarginals law total positive rows columns)
    (table : FourLabelTransportation.Transportation rows columns) :
    CouplingFits law (transportationCoupling total positive rows columns margins table) := by
  intro instrument treatment outcome
  cases instrument with
  | false =>
      exact QProb.equiv_trans (observed.false_cells treatment outcome)
        (QProb.mul_congr (QProb.equiv_refl _)
          (QProb.equiv_symm (transportationCoupling_cell_false total positive rows columns margins table treatment outcome)))
  | true =>
      exact QProb.equiv_trans (observed.true_cells treatment outcome)
        (QProb.mul_congr (QProb.equiv_refl _)
          (QProb.equiv_symm (transportationCoupling_cell_true total positive rows columns margins table treatment outcome)))

def transportationResponses (total : Nat) (positive : 0 < total) (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (table : FourLabelTransportation.Transportation rows columns) (fill : ResponsePair → Bool) : FiniteProbRecord Profile :=
  responsesOfCoupling (transportationCoupling total positive rows columns margins table) fill

/-- Any explicit fill produces a feasible response record.  The fill may
depend on the factual pair, as required for opposing signed-effect endpoints. -/
theorem transportationResponses_feasible (law : FiniteProbRecord signature.Assignment)
    (total : Nat) (positive : 0 < total) (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (observed : ArmMarginals law total positive rows columns)
    (table : FourLabelTransportation.Transportation rows columns) (fill : ResponsePair → Bool) :
    FeasibleResponses law (transportationResponses total positive rows columns margins table fill) :=
  responsesOfCoupling_feasible law _ (transportationCoupling_permitted total positive rows columns margins table)
    (transportationCoupling_fits law total positive rows columns margins observed table) fill

/-- A pure constructed model; observed-law correctness is proved below,
not inserted as an assumed field or a caller-supplied semantic equivalence. -/
def transportationNativeModel (projection : FiniteLatentProjection signature) (graphMatch : HasIVProjection projection)
    (law : FiniteProbRecord signature.Assignment) (total : Nat) (positive : 0 < total)
    (rows columns : FourLabelTransportation.Masses) (margins : FourLabelTransportation.Margins total rows columns)
    (table : FourLabelTransportation.Transportation rows columns) (fill : ResponsePair → Bool) :
    FiniteHiddenDAGSCM signature projection :=
  nativeProfileModel projection graphMatch (instrumentMarginal law)
    (transportationResponses total positive rows columns margins table fill)

theorem transportationNativeModel_hasObservedLaw (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (total : Nat) (positive : 0 < total) (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (observed : ArmMarginals law total positive rows columns)
    (table : FourLabelTransportation.Transportation rows columns) (fill : ResponsePair → Bool) :
    HasObservedLaw (transportationNativeModel projection graphMatch law total positive rows columns margins table fill) law :=
  nativeProfileModel_hasObservedLaw projection graphMatch law _
    (transportationResponses_feasible law total positive rows columns margins observed table fill)

end BinaryInstrumental
end Causality
end Thesis
