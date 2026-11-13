import Thesis.CausalTransport.HiddenDAGSourcePresentation
import Thesis.CausalTransport.HiddenDAGObservationalCompression

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S} {count : Nat}

/-!
# Source compression with actual bounded finite noise alphabets

Source compression previously bounded positive atom occurrences while leaving
the ambient private-noise types unchanged. Present each compressed factor on
its atom positions. The resulting native model now has literal `Fin codeCard`
private sources, their independent product prior, and the same original graph,
endogenous value types and permitted observed intervention targets.

The first interface preserves the supplied finite query family. The second
also preserves every observational event, by the existing automatic observed-
cell compression. Supported ratios are transported with explicit denominator
proofs. No unretained effect of the original model is asserted preserved.

Unit-level readout simulation is stronger in a different sense: at each coded
source assignment, the original equations give the same readout at its decoded
assignment. This does not imply unchanged probabilities for every intervention
after compression has changed the source law. Keeping those two statements
separate prevents a false claim of universal causal-law preservation.

Bounds depend on retained query counts, not denominators, total natural mass,
or the original ambient source cardinalities. This completes source-alphabet
relabelling, not hidden endogenous-value compression, finite mechanism coverage
or a general exact rational identification procedure.
-/

namespace FiniteHiddenDAGSCM
namespace SourceCompression

variable {original : FiniteHiddenDAGSCM S P} {queries : Fin count → NativeProbabilityQuery S}

def codeCard (compressed : SourceCompression original queries) (node : Fin P.hiddenDAG.count) : Nat :=
  (compressed.model.factor node).atoms.length

def codeModel (compressed : SourceCompression original queries) : FiniteHiddenDAGSCM S P :=
  compressed.model.atomSourceModel

/-- A type-level bound, not only a statement about a probability record's
support inside an unchanged larger ambient type. -/
theorem codeModel_noise (compressed : SourceCompression original queries) (node : Fin P.hiddenDAG.count) :
    compressed.codeModel.Noise node = Fin (compressed.codeCard node) := rfl

theorem codeCard_bound (compressed : SourceCompression original queries) (node : Fin P.hiddenDAG.count) :
    compressed.codeCard node ≤ count + 1 := compressed.bounded node

theorem codeModel_noiseEnumeration_length (compressed : SourceCompression original queries) (node : Fin P.hiddenDAG.count) :
    (compressed.codeModel.noiseEnumeration node).length = compressed.codeCard node := List.length_finRange

/-- Decoding reads the original equations. Only the law, not the graph or
unit-level mechanism, was changed by compression. -/
theorem codeModel_evalObserved (compressed : SourceCompression original queries)
    (intervention : HardIntervention S) (codes : compressed.codeModel.NoiseAssignment) :
    compressed.codeModel.evalObserved intervention codes = original.evalObserved intervention
      (FiniteProduct.decodePresentation (fun node => (compressed.model.factor node).atomPresentation) codes) :=
  (compressed.model.atomSourceModel_evalObserved intervention codes).trans
    (original.withSourceLaw_evalObserved compressed.law intervention
      (FiniteProduct.decodePresentation (fun node => (compressed.model.factor node).atomPresentation) codes))

theorem codeModel_preserved (compressed : SourceCompression original queries) (index : Fin count) :
    QProb.Equiv (compressed.codeModel.interventionalValue (queries index).intervention (queries index).event)
      (original.interventionalValue (queries index).intervention (queries index).event) :=
  QProb.equiv_trans
    (compressed.model.atomSourceModel_interventionalValue (queries index).intervention (queries index).event)
    (compressed.preserved index)

theorem codeModel_query_positive_iff (compressed : SourceCompression original queries) (index : Fin count) :
    0 < (compressed.codeModel.interventionalValue (queries index).intervention (queries index).event).num ↔
      0 < (original.interventionalValue (queries index).intervention (queries index).event).num :=
  QProb.equiv_num_pos_iff (compressed.codeModel_preserved index)

/-- The record-level support interface matches `conditionOn` directly.
Keeping this statement separate also avoids unfolding a concrete model's
entire event-mass computation just to convert equivalent positivity types. -/
theorem codeModel_eventPositive_iff (compressed : SourceCompression original queries) (index : Fin count) :
    (compressed.codeModel.interventionalDist (queries index).intervention).EventPositive (queries index).event ↔
      (original.interventionalDist (queries index).intervention).EventPositive (queries index).event :=
  compressed.codeModel_query_positive_iff index

/-- Include the joint event and evidence as retained queries when using this
for a conditional. The original positive denominator is still required. -/
theorem codeModel_quotient_preserved (compressed : SourceCompression original queries) (numerator denominator : Fin count)
    (positive : 0 < (original.interventionalValue (queries denominator).intervention (queries denominator).event).num) :
    QProb.Equiv
      (QProb.div (compressed.codeModel.interventionalValue (queries numerator).intervention (queries numerator).event)
        (compressed.codeModel.interventionalValue (queries denominator).intervention (queries denominator).event)
        ((compressed.codeModel_query_positive_iff denominator).mpr positive))
      (QProb.div (original.interventionalValue (queries numerator).intervention (queries numerator).event)
        (original.interventionalValue (queries denominator).intervention (queries denominator).event) positive) :=
  QProb.div_congr (compressed.codeModel_preserved numerator) (compressed.codeModel_preserved denominator)
    ((compressed.codeModel_query_positive_iff denominator).mpr positive) positive

end SourceCompression

namespace ObservationalSourceCompression

variable {original : FiniteHiddenDAGSCM S P} {targets : List (NativeProbabilityQuery S)}

def codeCard (compressed : ObservationalSourceCompression original targets) (node : Fin P.hiddenDAG.count) : Nat :=
  (compressed.model.factor node).atoms.length

def codeModel (compressed : ObservationalSourceCompression original targets) : FiniteHiddenDAGSCM S P :=
  compressed.model.atomSourceModel

theorem codeModel_noise (compressed : ObservationalSourceCompression original targets) (node : Fin P.hiddenDAG.count) :
    compressed.codeModel.Noise node = Fin (compressed.codeCard node) := rfl

theorem codeCard_bound (compressed : ObservationalSourceCompression original targets) (node : Fin P.hiddenDAG.count) :
    compressed.codeCard node ≤ S.assignmentEnumeration.length + targets.length + 1 := compressed.bounded node

theorem codeModel_noiseEnumeration_length (compressed : ObservationalSourceCompression original targets) (node : Fin P.hiddenDAG.count) :
    (compressed.codeModel.noiseEnumeration node).length = compressed.codeCard node := List.length_finRange

theorem codeModel_evalObserved (compressed : ObservationalSourceCompression original targets)
    (intervention : HardIntervention S) (codes : compressed.codeModel.NoiseAssignment) :
    compressed.codeModel.evalObserved intervention codes = original.evalObserved intervention
      (FiniteProduct.decodePresentation (fun node => (compressed.model.factor node).atomPresentation) codes) :=
  (compressed.model.atomSourceModel_evalObserved intervention codes).trans
    (original.withSourceLaw_evalObserved compressed.law intervention
      (FiniteProduct.decodePresentation (fun node => (compressed.model.factor node).atomPresentation) codes))

/-- Every factual event is preserved, not merely the observational queries
that an application happened to include in its target list. -/
theorem codeModel_observational (compressed : ObservationalSourceCompression original targets) (event : Event S.Assignment) :
    QProb.Equiv (compressed.codeModel.observationalValue event) (original.observationalValue event) :=
  QProb.equiv_trans (compressed.model.atomSourceModel_observationalValue event) (compressed.observational event)

theorem codeModel_preserved (compressed : ObservationalSourceCompression original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    QProb.Equiv (compressed.codeModel.interventionalValue query.intervention query.event)
      (original.interventionalValue query.intervention query.event) :=
  QProb.equiv_trans (compressed.model.atomSourceModel_interventionalValue query.intervention query.event)
    (compressed.preserved query listed)

theorem codeModel_query_positive_iff (compressed : ObservationalSourceCompression original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    0 < (compressed.codeModel.interventionalValue query.intervention query.event).num ↔
      0 < (original.interventionalValue query.intervention query.event).num :=
  QProb.equiv_num_pos_iff (compressed.codeModel_preserved query listed)

/-- Preserve actual record support, in the form required by `conditionOn`.
No numerical reduction of a concrete compressed prior is needed at use sites. -/
theorem codeModel_eventPositive_iff (compressed : ObservationalSourceCompression original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    (compressed.codeModel.interventionalDist query.intervention).EventPositive query.event ↔
      (original.interventionalDist query.intervention).EventPositive query.event :=
  compressed.codeModel_query_positive_iff query listed

theorem codeModel_quotient_preserved (compressed : ObservationalSourceCompression original targets)
    (numerator denominator : NativeProbabilityQuery S) (numeratorListed : numerator ∈ targets) (denominatorListed : denominator ∈ targets)
    (positive : 0 < (original.interventionalValue denominator.intervention denominator.event).num) :
    QProb.Equiv
      (QProb.div (compressed.codeModel.interventionalValue numerator.intervention numerator.event)
        (compressed.codeModel.interventionalValue denominator.intervention denominator.event)
        ((compressed.codeModel_query_positive_iff denominator denominatorListed).mpr positive))
      (QProb.div (original.interventionalValue numerator.intervention numerator.event)
        (original.interventionalValue denominator.intervention denominator.event) positive) :=
  QProb.div_congr (compressed.codeModel_preserved numerator numeratorListed) (compressed.codeModel_preserved denominator denominatorListed)
    ((compressed.codeModel_query_positive_iff denominator denominatorListed).mpr positive) positive

/-- To preserve a conditional, retain its joint event *and* its evidence
under the same intervention. Whole-observation preservation alone does not
promise either interventional probability; original evidence support is
still supplied explicitly. -/
theorem codeModel_conditionOn_probVal (compressed : ObservationalSourceCompression original targets)
    (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (jointListed : (⟨intervention, fun value => evidence value && event value⟩ : NativeProbabilityQuery S) ∈ targets)
    (evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery S) ∈ targets)
    (supported : (original.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      (((compressed.codeModel.interventionalDist intervention).conditionOn evidence
        ((compressed.codeModel_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((original.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  let supportedNew := (compressed.codeModel_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported
  exact QProb.equiv_trans
    ((compressed.codeModel.interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans
      (compressed.codeModel_quotient_preserved ⟨intervention, fun value => evidence value && event value⟩
        ⟨intervention, evidence⟩ jointListed evidenceListed supported)
      (QProb.equiv_symm ((original.interventionalDist intervention).conditionOn_probVal evidence event supported)))

end ObservationalSourceCompression
end FiniteHiddenDAGSCM
end Thesis.Causality
