import Thesis.Causality.LatentTableResponse
import Thesis.Probability.FiniteProductBalance

namespace Thesis
namespace Causality

open Probability

/-!
# Exact responses to coordinated finite blocks of local table changes

A general hedge construction may change several small-forest mechanisms
together.  The single-row response is linear with the other rows fixed;
adding such responses at one old environment would omit the interaction
terms of coordinated changes.  This module keeps those terms by an exact
finite product telescope with mixed old/new environments.

All changed rows are genuine finite probability records on the original
alphabets.  The shared sources, parent encoders, configuration types and
unchanged rows are retained.  The response formulas follow from the actual
independent SCM prior, without enumerating its private response-function
spaces, adding a common mixing source, or dividing by any old cell.

Balanced nonnegative change parts give a necessary and sufficient finite
comparison for the complete interventional event probabilities of these
same models.  Intervened rows contribute their forced-value indicator and
zero change, even if they lie in the replacement mask.  Descendants remain
in the product, and zero cells and unequal rational denominators are allowed.

This removes the one-row restriction from the response calculation.  It
does not assert that a suitable coordinated family exists for every hedge:
constructing that family and proving its factual cancellation and original-
query separation remain the universal positive completeness obligation.
-/

namespace FiniteLatentRationalCPT

variable {S : ObservedSignature.{0}}

/-- Explicit replacement records at every configuration of every observed
node.  Only nodes selected by the supplied block mask are actually changed. -/
abbrev RowProfiles (C : FiniteLatentRationalCPT S) :=
  (child : Fin S.count) -> C.RowProfile child

/-- Nonnegative parts of a coordinated change, without a normalization
requirement.  Probability-record normalization belongs to `RowProfiles`. -/
abbrev BlockCells (C : FiniteLatentRationalCPT S) :=
  (child : Fin S.count) -> C.CellProfile child

/-- Simultaneously replace a finite block of rows.  No ordered update
sequence or transport of private response functions is chosen. -/
def withRows (C : FiniteLatentRationalCPT S) (nodes : NodeSet S) (profiles : C.RowProfiles) :
    FiniteLatentRationalCPT S where
  shared := C.shared
  sharedFactor := C.sharedFactor
  configCount := C.configCount
  encode := C.encode
  row := fun child configuration => if nodes child then profiles child configuration else C.row child configuration

/-- Selected rows are exactly the supplied records, including their stored
finite presentations rather than merely their equivalent event laws. -/
theorem withRows_at (C : FiniteLatentRationalCPT S) (nodes : NodeSet S) (profiles : C.RowProfiles)
    (child : Fin S.count) (selected : nodes child = true) (configuration : Fin (C.configCount child)) :
    (C.withRows nodes profiles).row child configuration = profiles child configuration := by
  simp only [withRows, selected, if_true]

/-- Rows outside the mask are retained literally; responding descendants
are not omitted or replaced by constants in the later likelihood formulas. -/
theorem withRows_away (C : FiniteLatentRationalCPT S) (nodes : NodeSet S) (profiles : C.RowProfiles)
    (child : Fin S.count) (outside : nodes child = false) (configuration : Fin (C.configCount child)) :
    (C.withRows nodes profiles).row child configuration = C.row child configuration := by
  simp only [withRows, outside, Bool.false_eq_true, if_false]

/-- Pointwise balance is required only at selected configurations.  The
raw two-sided parts need not be normalized records or share denominators. -/
def RowsBalanced (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (decrease increase : C.BlockCells) : Prop :=
  forall child, nodes child = true -> C.CellsBalanced child
    (C.profileCells child (left child)) (C.profileCells child (right child)) (decrease child) (increase child)

/-- A raw change factor has the same position as the SCM's real private
response source.  Shared, unchanged and forced coordinates have zero change.
The suffix index is decoded arithmetically from the explicit finite prefix,
not selected from a propositional coordinate-existence theorem. -/
def blockPartFactors (C : FiniteLatentRationalCPT S) (nodes : NodeSet S) (part : C.BlockCells)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (root : Fin C.extension.count) : QProb :=
  if original : root.val < C.shared.count then QProb.zero
  else
    let child : Fin S.count := ⟨root.val - C.shared.count, by
      have bound : root.val < C.shared.count + S.count := root.isLt
      omega⟩
    if nodes child then
      match target child with
      | none => part child (C.rowConfiguration child shared sample) (sample child)
      | some _ => QProb.zero
    else QProb.zero

/-- Shared sources are unchanged, so their raw variation part is zero. -/
theorem blockPartFactors_sharedRoot (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (part : C.BlockCells) (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (root : Fin C.shared.count) :
    C.blockPartFactors nodes part target shared sample (C.sharedRoot root) = QProb.zero := by
  simp only [blockPartFactors, dif_pos (show (C.sharedRoot root).val < C.shared.count from root.isLt)]

/-- Decode the actual private source position back to its observed child.
Forced and unselected children retain zero raw change. -/
theorem blockPartFactors_privateRoot (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (part : C.BlockCells) (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (child : Fin S.count) :
    C.blockPartFactors nodes part target shared sample (C.privateRoot child) =
      if nodes child then
        match target child with
        | none => part child (C.rowConfiguration child shared sample) (sample child)
        | some _ => QProb.zero
      else QProb.zero := by
  have excluded : Not ((C.privateRoot child).val < C.shared.count) := by
    change Not (C.shared.count + child.val < C.shared.count)
    omega
  simp only [blockPartFactors, dif_neg excluded]
  let recovered : Fin S.count := ⟨C.shared.count + child.val - C.shared.count, by
    simpa only [Nat.add_sub_cancel_left] using child.isLt⟩
  have same : recovered = child := Fin.ext (Nat.add_sub_cancel_left _ _)
  change (if nodes recovered then
    match target recovered with
    | none => part recovered (C.rowConfiguration recovered shared sample) (sample recovered)
    | some _ => QProb.zero
    else QProb.zero) = _
  rw [same]

/-- Actual old/new slice factors have exactly the supplied pointwise
balance.  Forced nodes are compared as the same indicator on both sides,
rather than incorrectly retaining their discarded table perturbation. -/
theorem withRows_slice_balance (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (decrease increase : C.BlockCells)
    (balanced : C.RowsBalanced nodes left right decrease increase)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (root : Fin C.extension.count) :
    QProb.Equiv
      (QProb.add ((C.withRows nodes left).sliceFactors target shared sample root)
        (C.blockPartFactors nodes decrease target shared sample root))
      (QProb.add ((C.withRows nodes right).sliceFactors target shared sample root)
        (C.blockPartFactors nodes increase target shared sample root)) := by
  rcases C.extension_root_cases root with ⟨original, same⟩ | ⟨child, same⟩
  · subst root
    rw [C.blockPartFactors_sharedRoot, C.blockPartFactors_sharedRoot]
    change QProb.Equiv
      (QProb.add ((C.withRows nodes left).sliceFactors target shared sample
        ((C.withRows nodes left).sharedRoot original)) QProb.zero)
      (QProb.add ((C.withRows nodes right).sliceFactors target shared sample
        ((C.withRows nodes right).sharedRoot original)) QProb.zero)
    rw [(C.withRows nodes left).sliceFactors_sharedRoot, (C.withRows nodes right).sliceFactors_sharedRoot]
    exact QProb.equiv_refl _
  · subst root
    rw [C.blockPartFactors_privateRoot, C.blockPartFactors_privateRoot]
    change QProb.Equiv
      (QProb.add ((C.withRows nodes left).sliceFactors target shared sample
        ((C.withRows nodes left).privateRoot child)) _)
      (QProb.add ((C.withRows nodes right).sliceFactors target shared sample
        ((C.withRows nodes right).privateRoot child)) _)
    rw [(C.withRows nodes left).sliceFactors_privateRoot, (C.withRows nodes right).sliceFactors_privateRoot]
    cases selected : nodes child with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        unfold rowValueUnder
        cases active : target child with
        | some _ => exact QProb.equiv_refl _
        | none =>
            simp only [C.withRows_away nodes left child selected, C.withRows_away nodes right child selected]
            exact QProb.equiv_refl _
    | true =>
        simp only [if_true]
        unfold rowValueUnder
        cases active : target child with
        | some _ => exact QProb.equiv_refl _
        | none =>
            simp only [C.withRows_at nodes left child selected, C.withRows_at nodes right child selected]
            exact balanced child selected (C.rowConfiguration child shared sample) (sample child)

/-- Integrate one part of the exact mixed-row telescope over the supplied
shared enumeration.  The environments include every unchanged descendant
and each other changed row at its proper old/new stage. -/
def blockVariationWith (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (part : C.BlockCells) (values : List C.shared.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (sample : S.Assignment) : QProb :=
  QProb.listSum (values.map fun shared => FiniteProduct.qProductVariation C.extension.count
    ((C.withRows nodes left).sliceFactors target shared sample)
    ((C.withRows nodes right).sliceFactors target shared sample)
    (C.blockPartFactors nodes part target shared sample))

/-- Coordinate balance telescopes through every product and then through
the shared-state sum.  This keeps all interactions of coordinated changes. -/
theorem blockLikelihood_balance (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (decrease increase : C.BlockCells)
    (balanced : C.RowsBalanced nodes left right decrease increase)
    (values : List C.shared.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (sample : S.Assignment) :
    QProb.Equiv
      (QProb.add ((C.withRows nodes left).likelihoodWith values target sample)
        (C.blockVariationWith nodes left right decrease values target sample))
      (QProb.add ((C.withRows nodes right).likelihoodWith values target sample)
        (C.blockVariationWith nodes left right increase values target sample)) :=
  FiniteLinearResponse.sum_balance values _ _ _ _ (fun shared =>
    FiniteProduct.qProduct_balance C.extension.count _ _ _ _
      (C.withRows_slice_balance nodes left right decrease increase balanced target shared sample))

/-- The exact criterion for equality of the complete singleton
likelihoods, without normalizing or discarding their denominators. -/
theorem blockLikelihood_equiv_iff_of_balance (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (decrease increase : C.BlockCells)
    (balanced : C.RowsBalanced nodes left right decrease increase)
    (values : List C.shared.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (sample : S.Assignment) :
    QProb.Equiv ((C.withRows nodes left).likelihoodWith values target sample)
      ((C.withRows nodes right).likelihoodWith values target sample) ↔
      QProb.Equiv (C.blockVariationWith nodes left right decrease values target sample)
        (C.blockVariationWith nodes left right increase values target sample) :=
  FiniteLinearResponse.sum_equiv_iff_of_balance values _ _ _ _ (fun shared =>
    FiniteProduct.qProduct_balance C.extension.count _ _ _ _
      (C.withRows_slice_balance nodes left right decrease increase balanced target shared sample))

/-- Complete event likelihood, expressed using the integrated local tables
rather than private response-function enumeration. -/
def blockEventLikelihoodWith (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (profiles : C.RowProfiles) (values : List C.shared.Assignment) (samples : List S.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) : QProb :=
  QProb.listSum ((samples.filter event).map ((C.withRows nodes profiles).likelihoodWith values target))

/-- Integrate the mixed-environment variation over the complete observed
event.  Filtering uses the same event on both models; conditioning is not
silently replaced by a comparison of numerator likelihoods. -/
def blockEventVariationWith (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (part : C.BlockCells) (values : List C.shared.Assignment)
    (samples : List S.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) : QProb :=
  QProb.listSum ((samples.filter event).map (C.blockVariationWith nodes left right part values target))

/-- Event-level cancellation keeps the full shared and observed sums.  The
criterion does not require individual singleton responses to cancel. -/
theorem blockEventLikelihood_equiv_iff_of_balance (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (decrease increase : C.BlockCells)
    (balanced : C.RowsBalanced nodes left right decrease increase)
    (values : List C.shared.Assignment) (samples : List S.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv (C.blockEventLikelihoodWith nodes left values samples target event)
      (C.blockEventLikelihoodWith nodes right values samples target event) ↔
      QProb.Equiv (C.blockEventVariationWith nodes left right decrease values samples target event)
        (C.blockEventVariationWith nodes left right increase values samples target event) :=
  FiniteLinearResponse.sum_equiv_iff_of_balance (samples.filter event) _ _ _ _
    (C.blockLikelihood_balance nodes left right decrease increase balanced values target)

/-- These likelihoods are the event probabilities of the actual replaced
SCM.  Every supplied enumeration is checked for completeness and duplicates. -/
theorem withRows_interventional_event_response (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (profiles : C.RowProfiles) (values : List C.shared.Assignment) (nodup : values.Nodup)
    (complete : forall shared, shared ∈ values) (samples : List S.Assignment)
    (samplesNodup : samples.Nodup) (samplesComplete : forall sample, sample ∈ samples)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv ((C.withRows nodes profiles).toSCM.interventionalValue target event)
      (C.blockEventLikelihoodWith nodes profiles values samples target event) :=
  (C.withRows nodes profiles).toSCM_interventionalValue_likelihoodWith values nodup complete
    samples samplesNodup samplesComplete target event

/-- Equality of the actual interventional event probabilities is precisely
cancellation of the two integrated variation parts.  This is a statement
about the complete SCMs, not merely a formal local-table polynomial.

Taking the empty intervention tests factual event equality; taking an
original query intervention tests its separation.  The same mixed-row
calculation is valid for both, including selected rows that are forced by
the intervention.  A graph-specific family must still supply the balance
and the appropriate cancellation or noncancellation. -/
theorem withRows_interventionalValue_equiv_iff_of_balance
    (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (left right : C.RowProfiles) (decrease increase : C.BlockCells)
    (balanced : C.RowsBalanced nodes left right decrease increase)
    (values : List C.shared.Assignment) (nodup : values.Nodup)
    (complete : forall shared, shared ∈ values) (samples : List S.Assignment)
    (samplesNodup : samples.Nodup) (samplesComplete : forall sample, sample ∈ samples)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv ((C.withRows nodes left).toSCM.interventionalValue target event)
      ((C.withRows nodes right).toSCM.interventionalValue target event) ↔
      QProb.Equiv (C.blockEventVariationWith nodes left right decrease values samples target event)
        (C.blockEventVariationWith nodes left right increase values samples target event) := by
  have leftResponse := C.withRows_interventional_event_response nodes left values nodup complete
    samples samplesNodup samplesComplete target event
  have rightResponse := C.withRows_interventional_event_response nodes right values nodup complete
    samples samplesNodup samplesComplete target event
  have criterion := C.blockEventLikelihood_equiv_iff_of_balance nodes left right decrease increase
    balanced values samples target event
  constructor
  · intro compared
    exact criterion.mp (QProb.equiv_trans (QProb.equiv_symm leftResponse)
      (QProb.equiv_trans compared rightResponse))
  · intro cancelled
    exact QProb.equiv_trans leftResponse
      (QProb.equiv_trans (criterion.mpr cancelled) (QProb.equiv_symm rightResponse))

/-- Exact graph compatibility survives the entire block replacement.
No new shared mixing variable or latent incidence is introduced. -/
theorem withRows_toSCM_compatible (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (profiles : C.RowProfiles) (graph : ObservedGraph S)
    (canonical : C.shared.CanonicalSemiMarkovian)
    (projected : forall first second, C.shared.projectedBidirected first second = graph.bidirected first second) :
    Compatible (C.withRows nodes profiles).toSCM graph :=
  (C.withRows nodes profiles).toSCM_compatible graph canonical projected

/-- A single explicit supported shared assignment supplies full observed
positivity for all replaced and unchanged rows.  No representative family
is selected, and unused shared assignments may still contain zero cells. -/
theorem withRows_toSCM_positive (C : FiniteLatentRationalCPT S) (nodes : NodeSet S)
    (profiles : C.RowProfiles) (shared : C.shared.Assignment)
    (sharedPositive : forall root,
      (C.sharedFactor root).EventPositive (FiniteProbRecord.singletonEvent (shared root)))
    (awayPositive : forall (sample : S.Assignment) child, nodes child = false ->
      (C.row child (C.rowConfiguration child shared sample)).EventPositive
        (FiniteProbRecord.singletonEvent (sample child)))
    (selectedPositive : forall (sample : S.Assignment) child, nodes child = true ->
      (profiles child (C.rowConfiguration child shared sample)).EventPositive
        (FiniteProbRecord.singletonEvent (sample child))) :
    ObservationallyPositive (C.withRows nodes profiles).toSCM := by
  apply (C.withRows nodes profiles).toSCM_observationallyPositive_of_supportedShared shared sharedPositive
  intro sample child
  cases selected : nodes child with
  | false =>
      simp only [C.withRows_away nodes profiles child selected]
      exact awayPositive sample child selected
  | true =>
      simp only [C.withRows_at nodes profiles child selected]
      exact selectedPositive sample child selected

end FiniteLatentRationalCPT
end Causality
end Thesis
