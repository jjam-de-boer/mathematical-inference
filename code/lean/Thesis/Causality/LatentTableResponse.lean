import Thesis.Causality.LatentRationalCPT
import Thesis.Probability.FiniteProductResponse
import Thesis.Probability.FiniteLinearResponse

namespace Thesis
namespace Causality

open Probability

/-!
# The finite response operator of one local conditional table

The rational-table realization can be varied at one observed node without
changing its signature, parent inputs, shared sources, or configuration
encoder.  Its private response distribution changes, but it remains a real
independent factor of the resulting SCM prior.

This module isolates the varied row from every full-assignment likelihood.
The remaining product includes all shared-source singleton masses and all
other local responses—including responding descendants.  It is common to
every replacement profile and is never obtained by division by an old row
probability.  Zero factors and arbitrary rational denominators are allowed.

Consequently observational cancellation and interventional separation can
be expressed as finite linear response conditions on a local profile.  The
construction itself has no hedge-routing, sink, parent-uniqueness, or binary
alphabet restriction.  Producing a suitable profile pair for every hedge
remains a separate mathematical obligation; the operator does not assume
or assert that such a universal family already exists.
-/

namespace FiniteLatentRationalCPT

variable {S : ObservedSignature.{0}}

/-- All configurations of the selected node receive explicitly supplied
probability records on that node's original value type. -/
abbrev RowProfile (C : FiniteLatentRationalCPT S) (pivot : Fin S.count) :=
  Fin (C.configCount pivot) → FiniteProbRecord (S.Value pivot)

/-- Replace one table family, preserving all typed input data.  The finite
coordinate equality supplies both transports; no inverse encoder or chosen
response function is used. -/
def withRow (C : FiniteLatentRationalCPT S) (pivot : Fin S.count) (profile : C.RowProfile pivot) :
    FiniteLatentRationalCPT S where
  shared := C.shared
  sharedFactor := C.sharedFactor
  configCount := C.configCount
  encode := C.encode
  row := fun child configuration =>
    if same : child = pivot then same.symm ▸ profile (same ▸ configuration)
    else C.row child configuration

theorem withRow_at (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (configuration : Fin (C.configCount pivot)) :
    (C.withRow pivot profile).row pivot configuration = profile configuration := by
  simp [withRow]

theorem withRow_away (C : FiniteLatentRationalCPT S) (pivot child : Fin S.count)
    (profile : C.RowProfile pivot) (different : child ≠ pivot) (configuration : Fin (C.configCount child)) :
    (C.withRow pivot profile).row child configuration = C.row child configuration := by
  simp only [withRow, dif_neg different]

/-- The selected configuration uses only declared parents and incident
shared values, even though the likelihood fixes a whole observed assignment. -/
def rowConfiguration (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (shared : C.shared.Assignment) (sample : S.Assignment) : Fin (C.configCount pivot) :=
  C.encode pivot (fun parent _edge => sample parent) (fun root _incident => shared root)

def profileCell (C : FiniteLatentRationalCPT S) (pivot : Fin S.count) (profile : C.RowProfile pivot)
    (shared : C.shared.Assignment) (sample : S.Assignment) : QProb :=
  (profile (C.rowConfiguration pivot shared sample)).probVal (FiniteProbRecord.singletonEvent (sample pivot))

theorem withRow_rowValueUnder_at (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (target : (node : Fin S.count) → Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (free : target pivot = none) :
    (C.withRow pivot profile).rowValueUnder target shared sample pivot =
      C.profileCell pivot profile shared sample := by
  unfold rowValueUnder
  rw [free]
  change ((C.withRow pivot profile).row pivot (C.rowConfiguration pivot shared sample)).probVal _ = _
  rw [C.withRow_at]
  rfl

theorem withRow_rowValueUnder_away (C : FiniteLatentRationalCPT S) (pivot child : Fin S.count)
    (profile : C.RowProfile pivot) (target : (node : Fin S.count) → Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (different : child ≠ pivot) :
    (C.withRow pivot profile).rowValueUnder target shared sample child =
      C.rowValueUnder target shared sample child := by
  unfold rowValueUnder
  cases selected : target child with
  | some forced => rfl
  | none =>
      simp only [C.withRow_away pivot child profile different]
      rfl

/-- Changing the node's private response record cannot change any shared
root or any other node's integrated response factor. -/
theorem withRow_sliceFactors_away (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (target : (node : Fin S.count) → Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (root : Fin C.extension.count)
    (different : root ≠ C.privateRoot pivot) :
    (C.withRow pivot profile).sliceFactors target shared sample root =
      C.sliceFactors target shared sample root := by
  rcases C.extension_root_cases root with ⟨original, same⟩ | ⟨child, same⟩
  · subst root
    change (C.withRow pivot profile).sliceFactors target shared sample
      ((C.withRow pivot profile).sharedRoot original) =
        C.sliceFactors target shared sample (C.sharedRoot original)
    rw [(C.withRow pivot profile).sliceFactors_sharedRoot, C.sliceFactors_sharedRoot]
    rfl
  · subst root
    have distinct : child ≠ pivot := by
      intro equal
      exact different (congrArg C.privateRoot equal)
    change (C.withRow pivot profile).sliceFactors target shared sample
      ((C.withRow pivot profile).privateRoot child) =
        C.sliceFactors target shared sample (C.privateRoot child)
    rw [(C.withRow pivot profile).sliceFactors_privateRoot, C.sliceFactors_privateRoot]
    exact C.withRow_rowValueUnder_away pivot child profile target shared sample distinct

/-- All other likelihood factors stay present.  In particular, this is not
a product restricted to ancestors of the pivot or to kept forest edges. -/
def rowEnvironment (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (target : (node : Fin S.count) → Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) : QProb :=
  FiniteProduct.qProductWithout C.extension.count (C.privateRoot pivot)
    (C.sliceFactors target shared sample)

/-- Raw cells also describe the two nonnegative parts of a signed
perturbation.  Unlike a `RowProfile`, they need not be normalized records. -/
abbrev CellProfile (C : FiniteLatentRationalCPT S) (pivot : Fin S.count) :=
  Fin (C.configCount pivot) → S.Value pivot → QProb

def profileCells (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) : C.CellProfile pivot :=
  fun configuration value => (profile configuration).probVal (FiniteProbRecord.singletonEvent value)

/-- The finite response of arbitrary cells against the unchanged actual
environment.  Positivity and normalization are required only when those
cells are used as an actual replacement probability profile. -/
def cellResponseWith (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (cells : C.CellProfile pivot) (values : List C.shared.Assignment)
    (target : (node : Fin S.count) → Option (S.Value node)) (sample : S.Assignment) : QProb :=
  FiniteLinearResponse.applyWith values (fun shared => C.rowEnvironment pivot target shared sample)
    (fun shared => cells (C.rowConfiguration pivot shared sample) (sample pivot))

/-- One shared-assignment slice is linear in the selected local row.  The
factorization follows from the real product prior and integrated response
records; it does not posit a replacement probability law for the SCM. -/
theorem withRow_slice_factorization (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (target : (node : Fin S.count) → Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (free : target pivot = none) :
    QProb.Equiv
      (FiniteProduct.qProduct (C.withRow pivot profile).extension.count
        ((C.withRow pivot profile).sliceFactors target shared sample))
      (QProb.mul (C.profileCell pivot profile shared sample) (C.rowEnvironment pivot target shared sample)) := by
  have factored := FiniteProduct.qProduct_coordinate C.extension.count (C.privateRoot pivot)
    ((C.withRow pivot profile).sliceFactors target shared sample)
  have selected : (C.withRow pivot profile).sliceFactors target shared sample (C.privateRoot pivot) =
      C.profileCell pivot profile shared sample := by
    change (C.withRow pivot profile).sliceFactors target shared sample
      ((C.withRow pivot profile).privateRoot pivot) = _
    rw [(C.withRow pivot profile).sliceFactors_privateRoot]
    exact C.withRow_rowValueUnder_at pivot profile target shared sample free
  rw [selected] at factored
  exact QProb.equiv_trans factored
    (QProb.mul_congr (QProb.equiv_refl _)
      (FiniteProduct.qProductWithout_congr C.extension.count (C.privateRoot pivot) _ _
        (fun root different => by
          rw [C.withRow_sliceFactors_away pivot profile target shared sample root different]
          exact QProb.equiv_refl _)))

/-- The finite local-profile response operator.  The complete shared list
is supplied explicitly, so no hidden-state representative is selected. -/
def rowResponseWith (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (values : List C.shared.Assignment)
    (target : (node : Fin S.count) → Option (S.Value node)) (sample : S.Assignment) : QProb :=
  C.cellResponseWith pivot (C.profileCells pivot profile) values target sample

theorem withRow_likelihood_response (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (values : List C.shared.Assignment)
    (target : (node : Fin S.count) → Option (S.Value node)) (sample : S.Assignment)
    (free : target pivot = none) :
    QProb.Equiv ((C.withRow pivot profile).likelihoodWith values target sample)
      (C.rowResponseWith pivot profile values target sample) :=
  QProb.listSum_map_congr values _ _ (fun shared =>
    C.withRow_slice_factorization pivot profile target shared sample free)

/-- The response operator computes actual interventional singleton values
of the replaced SCM.  Every other local mechanism, including descendants,
is retained, and no soundness or completeness interface is assumed. -/
theorem withRow_interventional_singleton_response (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (values : List C.shared.Assignment)
    (nodup : values.Nodup) (complete : forall shared, shared ∈ values)
    (target : (node : Fin S.count) → Option (S.Value node)) (sample : S.Assignment)
    (free : target pivot = none) :
    QProb.Equiv ((C.withRow pivot profile).toSCM.interventionalValue target (FiniteProbRecord.singletonEvent sample))
      (C.rowResponseWith pivot profile values target sample) :=
  QProb.equiv_trans
    ((C.withRow pivot profile).toSCM_interventional_singleton_likelihoodWith values nodup complete target sample)
    (C.withRow_likelihood_response pivot profile values target sample free)

/-! ## Event responses retain all observed and hidden coordinates -/

/-- An event selects full observed assignments, not merely the pivot or
the hedge roots.  Summation therefore retains descendant responses and the
actual intervention's consistency factors in the common environment. -/
def cellEventResponseWith (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (cells : C.CellProfile pivot) (values : List C.shared.Assignment)
    (samples : List S.Assignment) (target : (node : Fin S.count) → Option (S.Value node))
    (event : Event S.Assignment) : QProb :=
  QProb.listSum ((samples.filter event).map (C.cellResponseWith pivot cells values target))

def rowEventResponseWith (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (values : List C.shared.Assignment)
    (samples : List S.Assignment) (target : (node : Fin S.count) → Option (S.Value node))
    (event : Event S.Assignment) : QProb :=
  C.cellEventResponseWith pivot (C.profileCells pivot profile) values samples target event

/-- Every event response equals the probability of that event in the
actual replaced SCM.  The two enumerations are supplied and verified,
rather than selecting a hidden state or an outcome representative. -/
theorem withRow_interventionalValue_response (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (values : List C.shared.Assignment)
    (nodup : values.Nodup) (complete : forall shared, shared ∈ values)
    (samples : List S.Assignment) (samplesNodup : samples.Nodup)
    (samplesComplete : forall sample, sample ∈ samples)
    (target : (node : Fin S.count) → Option (S.Value node)) (event : Event S.Assignment)
    (free : target pivot = none) :
    QProb.Equiv ((C.withRow pivot profile).toSCM.interventionalValue target event)
      (C.rowEventResponseWith pivot profile values samples target event) :=
  QProb.equiv_trans
    ((C.withRow pivot profile).toSCM_interventionalValue_likelihoodWith
      values nodup complete samples samplesNodup samplesComplete target event)
    (QProb.listSum_map_congr (samples.filter event) _ _ (fun sample =>
      C.withRow_likelihood_response pivot profile values target sample free))

/-- Observation is the empty-intervention response. -/
theorem withRow_observational_singleton_response (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (values : List C.shared.Assignment)
    (nodup : values.Nodup) (complete : forall shared, shared ∈ values) (sample : S.Assignment) :
    QProb.Equiv ((C.withRow pivot profile).toSCM.observationalValue (FiniteProbRecord.singletonEvent sample))
      (C.rowResponseWith pivot profile values (FiniteLatentSCM.noIntervention S) sample) :=
  C.withRow_interventional_singleton_response pivot profile values nodup complete
    (FiniteLatentSCM.noIntervention S) sample rfl

/-- Kernel event probabilities use the same response operator, including
the action-free branch of the intrinsic kernel semantics.  If the finite
action scan is false, its intervention is proved empty coordinate by
coordinate; no arbitrary propositional case distinction is needed. -/
theorem withRow_kernel_event_response (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (values : List C.shared.Assignment)
    (nodup : values.Nodup) (complete : forall shared, shared ∈ values)
    (samples : List S.Assignment) (samplesNodup : samples.Nodup)
    (samplesComplete : forall sample, sample ∈ samples)
    (kernel : Kernel S) (reference : S.Assignment) (event : Event S.Assignment)
    (free : kernel.intervention reference pivot = none) :
    QProb.Equiv ((kernel.distribution (C.withRow pivot profile).toSCM reference).probVal event)
      (C.rowEventResponseWith pivot profile values samples (kernel.intervention reference) event) := by
  have response := C.withRow_interventionalValue_response pivot profile values nodup complete
    samples samplesNodup samplesComplete (kernel.intervention reference) event free
  cases active : kernel.hasAction with
  | true =>
      simpa only [Kernel.distribution, active, if_true] using response
  | false =>
      have empty : kernel.intervention reference = FiniteLatentSCM.noIntervention S := by
        funext node
        have inactive := (finAny_eq_false_iff kernel.action).mp active node
        simp only [Kernel.intervention, inactive, Bool.false_eq_true, if_false, FiniteLatentSCM.noIntervention]
      simpa only [Kernel.distribution, active, Bool.false_eq_true, if_false, empty,
        FiniteLatentSCM.interventionalValue, FiniteLatentSCM.interventionalDist,
        FiniteLatentSCM.observationalDist, FiniteLatentSCM.eval] using response

/-! ## Exact perturbation cancellation and separation -/

/-- A pointwise balance records a signed perturbation without subtraction.
The two directions need not themselves be probability distributions. -/
def CellsBalanced (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (left right decrease increase : C.CellProfile pivot) : Prop :=
  forall configuration value,
    QProb.Equiv (QProb.add (left configuration value) (decrease configuration value))
      (QProb.add (right configuration value) (increase configuration value))

theorem cellResponse_balance (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (left right decrease increase : C.CellProfile pivot)
    (balanced : C.CellsBalanced pivot left right decrease increase)
    (values : List C.shared.Assignment) (target : (node : Fin S.count) → Option (S.Value node))
    (sample : S.Assignment) :
    QProb.Equiv
      (QProb.add (C.cellResponseWith pivot left values target sample)
        (C.cellResponseWith pivot decrease values target sample))
      (QProb.add (C.cellResponseWith pivot right values target sample)
        (C.cellResponseWith pivot increase values target sample)) := by
  apply FiniteLinearResponse.sum_balance values
  intro shared
  exact QProb.equiv_trans (QProb.equiv_symm (QProb.add_mul_distrib _ _ _))
    (QProb.equiv_trans (QProb.mul_congr (balanced _ _) (QProb.equiv_refl _))
      (QProb.add_mul_distrib _ _ _))

/-- Observational invisibility is exactly cancellation against the
factual environment; a changed intervention may break that cancellation. -/
theorem cellResponse_equiv_iff_of_balance (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (left right decrease increase : C.CellProfile pivot)
    (balanced : C.CellsBalanced pivot left right decrease increase)
    (values : List C.shared.Assignment) (target : (node : Fin S.count) → Option (S.Value node))
    (sample : S.Assignment) :
    QProb.Equiv (C.cellResponseWith pivot left values target sample)
      (C.cellResponseWith pivot right values target sample) ↔
      QProb.Equiv (C.cellResponseWith pivot decrease values target sample)
        (C.cellResponseWith pivot increase values target sample) :=
  FiniteLinearResponse.applyWith_equiv_iff_of_balance values _ _ _ _ _ (fun _ => balanced _ _)

/-- The same exact criterion holds for any full event, after summing
the observed assignments selected by that event.  Separation is thus a
finite response inequality, not an assumed causal law for new tables. -/
theorem cellEventResponse_equiv_iff_of_balance (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (left right decrease increase : C.CellProfile pivot)
    (balanced : C.CellsBalanced pivot left right decrease increase)
    (values : List C.shared.Assignment) (samples : List S.Assignment)
    (target : (node : Fin S.count) → Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv (C.cellEventResponseWith pivot left values samples target event)
      (C.cellEventResponseWith pivot right values samples target event) ↔
      QProb.Equiv (C.cellEventResponseWith pivot decrease values samples target event)
        (C.cellEventResponseWith pivot increase values samples target event) :=
  FiniteLinearResponse.sum_equiv_iff_of_balance (samples.filter event) _ _ _ _
    (C.cellResponse_balance pivot left right decrease increase balanced values target)

/-! ## The replaced probability records are genuine models -/

/-- Private response changes preserve exact graph compatibility.  This
does not enlarge the bidirected graph or add a shared mixing variable. -/
theorem withRow_toSCM_compatible (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (graph : ObservedGraph S)
    (canonical : C.shared.CanonicalSemiMarkovian)
    (projected : forall first second, C.shared.projectedBidirected first second = graph.bidirected first second) :
    Compatible (C.withRow pivot profile).toSCM graph :=
  (C.withRow pivot profile).toSCM_compatible graph canonical projected

/-- One explicitly supported shared assignment suffices.  Only the rows
actually used at that assignment must be positive, including the new pivot
rows.  Other shared values or unused configurations may still have zeros. -/
theorem withRow_toSCM_positive (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (profile : C.RowProfile pivot) (shared : C.shared.Assignment)
    (sharedPositive : forall root,
      (C.sharedFactor root).EventPositive (FiniteProbRecord.singletonEvent (shared root)))
    (awayPositive : forall (sample : S.Assignment) child, child ≠ pivot →
      (C.row child (C.rowConfiguration child shared sample)).EventPositive
        (FiniteProbRecord.singletonEvent (sample child)))
    (pivotPositive : forall sample : S.Assignment,
      (profile (C.rowConfiguration pivot shared sample)).EventPositive
        (FiniteProbRecord.singletonEvent (sample pivot))) :
    ObservationallyPositive (C.withRow pivot profile).toSCM := by
  apply (C.withRow pivot profile).toSCM_observationallyPositive_of_supportedShared shared sharedPositive
  intro sample child
  by_cases same : child = pivot
  · subst child
    change ((C.withRow pivot profile).row pivot (C.rowConfiguration pivot shared sample)).EventPositive _
    rw [C.withRow_at]
    exact pivotPositive sample
  · change ((C.withRow pivot profile).row child (C.rowConfiguration child shared sample)).EventPositive _
    rw [C.withRow_away pivot child profile same]
    exact awayPositive sample child same

/-- Singleton response equality implies equality of every observational
event in the two actual SCMs.  Equality is not restricted to the outcome,
the pivot, or any selected subset of observed vertices. -/
theorem withRow_observationally_equivalent (C : FiniteLatentRationalCPT S) (pivot : Fin S.count)
    (left right : C.RowProfile pivot) (values : List C.shared.Assignment)
    (nodup : values.Nodup) (complete : forall shared, shared ∈ values)
    (responses : forall sample,
      QProb.Equiv (C.rowResponseWith pivot left values (FiniteLatentSCM.noIntervention S) sample)
        (C.rowResponseWith pivot right values (FiniteLatentSCM.noIntervention S) sample)) :
    ObservationallyEquivalent (C.withRow pivot left).toSCM (C.withRow pivot right).toSCM := by
  intro event
  apply FiniteProbRecord.probVal_extensional_of_singletons
    (C.withRow pivot left).toSCM.observationalDist (C.withRow pivot right).toSCM.observationalDist
    S.assignmentEnumeration S.assignmentEnumeration_nodup S.assignmentEnumeration_complete
  intro sample
  exact QProb.equiv_trans (C.withRow_observational_singleton_response pivot left values nodup complete sample)
    (QProb.equiv_trans (responses sample)
      (QProb.equiv_symm (C.withRow_observational_singleton_response pivot right values nodup complete sample)))

end FiniteLatentRationalCPT
end Causality
end Thesis
