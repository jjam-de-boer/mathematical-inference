import Thesis.Causality.Reductions
import Thesis.Causality.Identification
import Thesis.Probability.FiniteRecordSlicing

namespace Thesis
namespace Causality

open Probability

/-!
# Rational conditional tables with finite shared latent inputs

`FiniteRationalCPT` functionalizes ordinary Markovian tables.  Hedge
countermodels also need specified independent *shared* sources.  This module
keeps those sources and their incidence literally, and appends one private
finite response table at each observed node.  A response table contains one
potential output for each explicit local configuration; its probability law
is the product of the stated rational rows.

A configuration encoder receives only declared observed parents and incident
shared inputs.  It need not be bijective: configurations with identical rows
may be deliberately merged.  No inverse, representative selection, or chosen
family of response functions is needed.  The complete finite response space
is enumerated constructively using the existing dependent-product machinery.

The resulting object is an actual `FiniteLatentSCM` with a genuine product
prior.  Its private response sources introduce no bidirected edges, and
canonical semi-Markovian incidence is inherited from the supplied shared
family.  The observed signature and directed graph are never enlarged.

The construction is independent of the published soundness/completeness
implementations.  Constructing such an SCM does not by itself establish
observational equality, positivity, or a causal gap for particular tables:
those must be proved against its evaluation and actual prior.
-/

/-- A finite rational table at every local observed/shared configuration.
All alphabets and configuration encoders are supplied as constructive data. -/
structure FiniteLatentRationalCPT (S : ObservedSignature.{0}) where
  shared : LatentExtension.{0, 0} S
  sharedFactor : (root : Fin shared.count) -> FiniteProbRecord (shared.Value root)
  configCount : Fin S.count -> Nat
  encode : (child : Fin S.count) -> S.ParentValues child ->
    shared.Inputs child -> Fin (configCount child)
  row : (child : Fin S.count) -> Fin (configCount child) -> FiniteProbRecord (S.Value child)

namespace FiniteLatentRationalCPT

variable {S : ObservedSignature.{0}}

/-- A private deterministic response function for all configurations at one
node.  This is finite even when the row probabilities have different denominators. -/
abbrev ResponseSeed (C : FiniteLatentRationalCPT S) (child : Fin S.count) :=
  FiniteProduct.Assignment (C.configCount child) (fun _ => S.Value child)

def responseFactor (C : FiniteLatentRationalCPT S) (child : Fin S.count) :
    FiniteProbRecord (C.ResponseSeed child) :=
  FiniteProduct.record (C.configCount child) (fun _ => S.Value child) (C.row child)

def responseEnumeration (C : FiniteLatentRationalCPT S) (child : Fin S.count) :
    List (C.ResponseSeed child) :=
  FiniteProduct.enumeration (C.configCount child) (fun _ => S.Value child)
    (fun _ => S.valueEnumeration child)

theorem responseEnumeration_complete (C : FiniteLatentRationalCPT S)
    (child : Fin S.count) (seed : C.ResponseSeed child) : seed ∈ C.responseEnumeration child :=
  FiniteProduct.enumeration_complete (C.configCount child) (fun _ => S.Value child)
    (fun _ => S.valueEnumeration child) (fun _ => S.value_complete child) seed

def responseDecidableEq (C : FiniteLatentRationalCPT S) (child : Fin S.count) :
    DecidableEq (C.ResponseSeed child) :=
  FiniteProduct.assignmentDecidableEq (C.configCount child) (fun _ => S.Value child)
    (fun _ => S.valueDecidableEq child)

/-- Selecting a table coordinate integrates to the stated local row. -/
theorem responseFactor_preserves_row (C : FiniteLatentRationalCPT S)
    (child : Fin S.count) (parents : S.ParentValues child) (shared : C.shared.Inputs child)
    (event : Event (S.Value child)) :
    QProb.Equiv
      ((C.responseFactor child).probVal (fun seed => event (seed (C.encode child parents shared))))
      ((C.row child (C.encode child parents shared)).probVal event) :=
  FiniteProduct.record_coordinate_probVal (C.configCount child) (S.Value child)
    (C.row child) (C.encode child parents shared) event

/-! ## A shared prefix and a private suffix of typed latent coordinates -/

/-- Embed a supplied shared source in the unchanged prefix. -/
def sharedRoot (C : FiniteLatentRationalCPT S) (root : Fin C.shared.count) :
    Fin (C.shared.count + S.count) :=
  ⟨root.val, Nat.lt_of_lt_of_le root.isLt (Nat.le_add_right _ _)⟩

/-- Exactly one newly appended private source belongs to each observed node. -/
def privateRoot (C : FiniteLatentRationalCPT S) (child : Fin S.count) :
    Fin (C.shared.count + S.count) :=
  ⟨C.shared.count + child.val, Nat.add_lt_add_left child.isLt C.shared.count⟩

private def sharedIndex (C : FiniteLatentRationalCPT S)
    (root : Fin (C.shared.count + S.count)) (selected : root.val < C.shared.count) :
    Fin C.shared.count := ⟨root.val, selected⟩

private def privateIndex (C : FiniteLatentRationalCPT S)
    (root : Fin (C.shared.count + S.count)) (excluded : ¬ root.val < C.shared.count) :
    Fin S.count := ⟨root.val - C.shared.count, by have := root.isLt; omega⟩

theorem sharedRoot_injective (C : FiniteLatentRationalCPT S) :
    Function.Injective C.sharedRoot := by
  intro first second equal
  exact Fin.ext (congrArg (fun root : Fin (C.shared.count + S.count) => root.val) equal)

theorem privateRoot_injective (C : FiniteLatentRationalCPT S) :
    Function.Injective C.privateRoot := by
  intro first second equal
  have values := congrArg Fin.val equal
  apply Fin.ext
  change C.shared.count + first.val = C.shared.count + second.val at values
  omega

theorem sharedRoot_ne_privateRoot (C : FiniteLatentRationalCPT S)
    (root : Fin C.shared.count) (child : Fin S.count) :
    C.sharedRoot root ≠ C.privateRoot child := by
  intro equal
  have values := congrArg Fin.val equal
  have bound := root.isLt
  change root.val = C.shared.count + child.val at values
  omega

/-- Dependent alphabets are retained in both blocks.  Only finite Nat
comparison decides which block a coordinate belongs to. -/
def Value (C : FiniteLatentRationalCPT S) (root : Fin (C.shared.count + S.count)) : Type :=
  if selected : root.val < C.shared.count then C.shared.Value (C.sharedIndex root selected)
  else C.ResponseSeed (C.privateIndex root selected)

private theorem value_of_shared (C : FiniteLatentRationalCPT S)
    (root : Fin (C.shared.count + S.count)) (selected : root.val < C.shared.count) :
    C.Value root = C.shared.Value (C.sharedIndex root selected) := by
  unfold Value
  rw [dif_pos selected]

private theorem value_of_private (C : FiniteLatentRationalCPT S)
    (root : Fin (C.shared.count + S.count)) (excluded : ¬ root.val < C.shared.count) :
    C.Value root = C.ResponseSeed (C.privateIndex root excluded) := by
  unfold Value
  rw [dif_neg excluded]

theorem value_sharedRoot (C : FiniteLatentRationalCPT S) (root : Fin C.shared.count) :
    C.Value (C.sharedRoot root) = C.shared.Value root := by
  have selected : (C.sharedRoot root).val < C.shared.count := root.isLt
  unfold Value
  rw [dif_pos selected]
  rfl

theorem value_privateRoot (C : FiniteLatentRationalCPT S) (child : Fin S.count) :
    C.Value (C.privateRoot child) = C.ResponseSeed child := by
  have excluded : ¬ (C.privateRoot child).val < C.shared.count := by
    change ¬ C.shared.count + child.val < C.shared.count
    omega
  unfold Value
  rw [dif_neg excluded]
  have index : C.privateIndex (C.privateRoot child) excluded = child := by
    apply Fin.ext
    change C.shared.count + child.val - C.shared.count = child.val
    omega
  rw [index]

def enumeration (C : FiniteLatentRationalCPT S) (root : Fin (C.shared.count + S.count)) :
    List (C.Value root) :=
  if selected : root.val < C.shared.count then
    (C.shared.valueEnumeration (C.sharedIndex root selected)).map
      (cast (C.value_of_shared root selected).symm)
  else
    (C.responseEnumeration (C.privateIndex root selected)).map
      (cast (C.value_of_private root selected).symm)

theorem enumeration_complete (C : FiniteLatentRationalCPT S)
    (root : Fin (C.shared.count + S.count)) (value : C.Value root) :
    value ∈ C.enumeration root := by
  unfold enumeration
  by_cases selected : root.val < C.shared.count
  · rw [dif_pos selected]
    exact List.mem_map.mpr ⟨cast (C.value_of_shared root selected) value,
      C.shared.value_complete _ _, by simp⟩
  · rw [dif_neg selected]
    exact List.mem_map.mpr ⟨cast (C.value_of_private root selected) value,
      C.responseEnumeration_complete _ _, by simp⟩

def valueDecidableEq (C : FiniteLatentRationalCPT S)
    (root : Fin (C.shared.count + S.count)) : DecidableEq (C.Value root) := by
  unfold Value
  split
  · exact C.shared.valueDecidableEq (C.sharedIndex root ‹_›)
  · exact C.responseDecidableEq (C.privateIndex root ‹_›)

/-- The shared prefix retains its old children.  A private suffix coordinate
has only its matching observed child, regardless of its response alphabet. -/
def incident (C : FiniteLatentRationalCPT S)
    (root : Fin (C.shared.count + S.count)) (child : Fin S.count) : Bool :=
  if selected : root.val < C.shared.count then C.shared.incident (C.sharedIndex root selected) child
  else decide (child = C.privateIndex root selected)

theorem incident_sharedRoot (C : FiniteLatentRationalCPT S)
    (root : Fin C.shared.count) (child : Fin S.count) :
    C.incident (C.sharedRoot root) child = C.shared.incident root child := by
  have selected : (C.sharedRoot root).val < C.shared.count := root.isLt
  unfold incident
  rw [dif_pos selected]
  rfl

theorem incident_privateRoot (C : FiniteLatentRationalCPT S) (pivot child : Fin S.count) :
    C.incident (C.privateRoot pivot) child = decide (child = pivot) := by
  have excluded : ¬ (C.privateRoot pivot).val < C.shared.count := by
    change ¬ C.shared.count + pivot.val < C.shared.count
    omega
  unfold incident
  rw [dif_neg excluded]
  have index : C.privateIndex (C.privateRoot pivot) excluded = pivot := by
    apply Fin.ext
    change C.shared.count + pivot.val - C.shared.count = pivot.val
    omega
  rw [index]

def extension (C : FiniteLatentRationalCPT S) : LatentExtension S where
  count := C.shared.count + S.count
  Value := C.Value
  valueEnumeration := C.enumeration
  value_complete := C.enumeration_complete
  valueDecidableEq := C.valueDecidableEq
  incident := C.incident

/-! ## The actual product prior and declared-input mechanism -/

def factor (C : FiniteLatentRationalCPT S) (root : Fin C.extension.count) :
    FiniteProbRecord (C.extension.Value root) :=
  if selected : root.val < C.shared.count then
    (C.sharedFactor (C.sharedIndex root selected)).map
      (cast (C.value_of_shared root selected).symm)
  else
    (C.responseFactor (C.privateIndex root selected)).map
      (cast (C.value_of_private root selected).symm)

/-- Decoding a shared coordinate of the real product prior recovers exactly
its supplied factor, including its original rational denominator. -/
theorem factor_sharedRoot_probVal (C : FiniteLatentRationalCPT S)
    (root : Fin C.shared.count) (event : Event (C.shared.Value root)) :
    QProb.Equiv
      ((C.factor (C.sharedRoot root)).probVal (fun value => event (cast (C.value_sharedRoot root) value)))
      ((C.sharedFactor root).probVal event) := by
  have selected : (C.sharedRoot root).val < C.shared.count := root.isLt
  unfold factor
  rw [dif_pos selected]
  let encoded := cast (C.value_of_shared (C.sharedRoot root) selected).symm
  let decoded := fun value => event (cast (C.value_sharedRoot root) value)
  have mapped := (C.sharedFactor root).map_probVal encoded decoded
  exact QProb.equiv_trans mapped
    ((C.sharedFactor root).probVal_congr (fun value => decoded (encoded value)) event (by
      intro value
      simp only [encoded, decoded, cast_cast]
      change event (cast (Eq.refl (C.shared.Value root)) value) = event value
      rfl))

private theorem responseFactor_probVal_cast (C : FiniteLatentRationalCPT S)
    (first second : Fin S.count) (same : first = second) (event : Event (C.ResponseSeed second)) :
    QProb.Equiv ((C.responseFactor first).probVal
      (fun seed => event (cast (congrArg C.ResponseSeed same) seed)))
      ((C.responseFactor second).probVal event) := by
  cases same
  exact QProb.equiv_refl _

/-- The private source in the actual model has the response-function law,
not an assumed row-valued or correlated prior. -/
theorem factor_privateRoot_probVal (C : FiniteLatentRationalCPT S)
    (child : Fin S.count) (event : Event (C.ResponseSeed child)) :
    QProb.Equiv
      ((C.factor (C.privateRoot child)).probVal (fun value => event (cast (C.value_privateRoot child) value)))
      ((C.responseFactor child).probVal event) := by
  have excluded : ¬ (C.privateRoot child).val < C.shared.count := by
    change ¬ C.shared.count + child.val < C.shared.count
    omega
  unfold factor
  rw [dif_neg excluded]
  let index := C.privateIndex (C.privateRoot child) excluded
  have indexEq : index = child := by
    apply Fin.ext
    change C.shared.count + child.val - C.shared.count = child.val
    omega
  let encoded := cast (C.value_of_private (C.privateRoot child) excluded).symm
  let decoded := fun value => event (cast (C.value_privateRoot child) value)
  have mapped := (C.responseFactor index).map_probVal encoded decoded
  exact QProb.equiv_trans mapped
    (QProb.equiv_trans ((C.responseFactor index).probVal_congr
      (fun seed => decoded (encoded seed))
      (fun seed => event (cast (congrArg C.ResponseSeed indexEq) seed)) (by
        intro seed
        simp only [decoded, encoded, cast_cast]))
      (C.responseFactor_probVal_cast index child indexEq event))

/-- Decode only the supplied incident shared block of a mechanism's inputs. -/
def sharedInputs (C : FiniteLatentRationalCPT S) (child : Fin S.count)
    (inputs : C.extension.Inputs child) : C.shared.Inputs child :=
  fun root selected => cast (C.value_sharedRoot root)
    (inputs (C.sharedRoot root) (by
      change C.incident (C.sharedRoot root) child = true
      rw [C.incident_sharedRoot]
      exact selected))

/-- Decode the one private response table incident to the current node. -/
def responseInput (C : FiniteLatentRationalCPT S) (child : Fin S.count)
    (inputs : C.extension.Inputs child) : C.ResponseSeed child :=
  cast (C.value_privateRoot child)
    (inputs (C.privateRoot child) (by
      change C.incident (C.privateRoot child) child = true
      rw [C.incident_privateRoot]
      exact decide_eq_true rfl))

/-- No mechanism can read an unlisted shared source or observed parent.
The complete response table is exogenous and private, not a shared switch. -/
def toSCM (C : FiniteLatentRationalCPT S) : ExactModel S where
  latent := C.extension
  factor := C.factor
  prior := FiniteProduct.record C.extension.count C.extension.Value C.factor
  product_law := FiniteProduct.record_rectangular_probVal
    C.extension.count C.extension.Value C.factor
  mechanism := fun child parents inputs =>
    C.responseInput child inputs (C.encode child parents (C.sharedInputs child inputs))

/-- Recover the original shared assignment from a complete augmented unit. -/
def sharedAssignment (C : FiniteLatentRationalCPT S) (unit : C.extension.Assignment) :
    C.shared.Assignment :=
  fun root => cast (C.value_sharedRoot root) (unit (C.sharedRoot root))

/-- Recover the private response function at every observed node. -/
def responseAssignment (C : FiniteLatentRationalCPT S) (unit : C.extension.Assignment)
    (child : Fin S.count) : C.ResponseSeed child :=
  cast (C.value_privateRoot child) (unit (C.privateRoot child))

/-- An intervened node enforces its actual supplied label; at every
free node the selected private response must reproduce the queried assignment.
The event is typed on a *single* node's response source, with the other
shared values fixed explicitly. -/
def responseEventUnder (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (child : Fin S.count) :
    Event (C.ResponseSeed child) :=
  fun seed => match target child with
    | some forced => decide (forced = sample child)
    | none => FiniteProbRecord.singletonEvent (sample child)
        (seed (C.encode child (fun parent _edge => sample parent) (fun root _incident => shared root)))

/-- Topological reconstruction uses the actual intervention and actual
private response source.  No downstream mechanism is silently omitted. -/
theorem toSCM_evalNodeUnder_eq_of_responseEvents (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (unit : C.extension.Assignment) (sample : S.Assignment)
    (agree : forall child, C.responseEventUnder target (C.sharedAssignment unit) sample child
      (C.responseAssignment unit child) = true) (child : Fin S.count) :
    C.toSCM.evalNodeUnder target unit child = sample child := by
  rw [FiniteLatentSCM.evalNodeUnder]
  cases selected : target child with
  | some forced =>
      simp only [FiniteLatentSCM.equationUnder, selected]
      exact of_decide_eq_true (by
        simpa only [responseEventUnder, selected] using agree child)
  | none =>
      simp only [FiniteLatentSCM.equationUnder, selected]
      have parents :
          (fun parent (_edge : S.directed parent child = true) => C.toSCM.evalNodeUnder target unit parent) =
          (fun parent (_edge : S.directed parent child = true) => sample parent) := by
        funext parent edge
        exact C.toSCM_evalNodeUnder_eq_of_responseEvents target unit sample agree parent
      change C.responseAssignment unit child
        (C.encode child
          (fun parent _edge => C.toSCM.evalNodeUnder target unit parent)
          (fun root _incident => C.sharedAssignment unit root)) = sample child
      rw [parents]
      exact of_decide_eq_true (by
        simpa only [responseEventUnder, selected, FiniteProbRecord.singletonEvent] using agree child)
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Complete evaluation under an arbitrary hard intervention is equivalent
to the local response-source events, with the shared unit held fixed. -/
theorem toSCM_evalUnder_eq_iff_responseEvents (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (unit : C.extension.Assignment) (sample : S.Assignment) :
    C.toSCM.evalUnder target unit = sample ↔ forall child,
      C.responseEventUnder target (C.sharedAssignment unit) sample child
        (C.responseAssignment unit child) = true := by
  constructor
  · intro evaluated child
    have childEq := congrFun evaluated child
    change C.toSCM.evalNodeUnder target unit child = sample child at childEq
    rw [FiniteLatentSCM.evalNodeUnder] at childEq
    cases selected : target child with
    | some forced =>
        simp only [FiniteLatentSCM.equationUnder, selected] at childEq
        simpa only [responseEventUnder, selected] using decide_eq_true childEq
    | none =>
        simp only [FiniteLatentSCM.equationUnder, selected] at childEq
        have parents :
            (fun parent (_edge : S.directed parent child = true) => C.toSCM.evalNodeUnder target unit parent) =
            (fun parent (_edge : S.directed parent child = true) => sample parent) := by
          funext parent edge
          exact congrFun evaluated parent
        change C.responseAssignment unit child
          (C.encode child
            (fun parent _edge => C.toSCM.evalNodeUnder target unit parent)
            (fun root _incident => C.sharedAssignment unit root)) = sample child at childEq
        rw [parents] at childEq
        simpa only [responseEventUnder, selected, FiniteProbRecord.singletonEvent] using decide_eq_true childEq
  · intro agree
    funext child
    exact C.toSCM_evalNodeUnder_eq_of_responseEvents target unit sample agree child

/-! ## Complete-assignment slices of the actual product prior -/

private theorem dependent_event_cast {n : Nat} (Value : Fin n -> Type)
    (events : (index : Fin n) -> Event (Value index))
    (first second : Fin n) (same : first = second) (value : Value second) :
    events first (cast (congrArg Value same.symm) value) = events second value := by
  cases same
  rfl

/-- A fixed shared assignment and a complete observed assignment define a
rectangular event on the *real* shared/private latent coordinates.  Forced
nodes contribute a constant consistency event, not a sampled mechanism. -/
def sliceEvents (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment)
    (root : Fin C.extension.count) : Event (C.extension.Value root) :=
  if selected : root.val < C.shared.count then
    fun value => FiniteProbRecord.singletonEvent (shared (C.sharedIndex root selected))
      (cast (C.value_of_shared root selected) value)
  else
    fun value => C.responseEventUnder target shared sample (C.privateIndex root selected)
      (cast (C.value_of_private root selected) value)

theorem sliceEvents_sharedRoot (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment)
    (root : Fin C.shared.count) (value : C.extension.Value (C.sharedRoot root)) :
    C.sliceEvents target shared sample (C.sharedRoot root) value =
      FiniteProbRecord.singletonEvent (shared root) (cast (C.value_sharedRoot root) value) := by
  have selected : (C.sharedRoot root).val < C.shared.count := root.isLt
  unfold sliceEvents
  rw [dif_pos selected]
  rfl

theorem sliceEvents_privateRoot (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment)
    (child : Fin S.count) (value : C.extension.Value (C.privateRoot child)) :
    C.sliceEvents target shared sample (C.privateRoot child) value =
      C.responseEventUnder target shared sample child (cast (C.value_privateRoot child) value) := by
  have excluded : ¬ (C.privateRoot child).val < C.shared.count := by
    change ¬ C.shared.count + child.val < C.shared.count
    omega
  unfold sliceEvents
  rw [dif_neg excluded]
  let index := C.privateIndex (C.privateRoot child) excluded
  have indexEq : index = child := by
    apply Fin.ext
    change C.shared.count + child.val - C.shared.count = child.val
    omega
  have encoded : cast (C.value_of_private (C.privateRoot child) excluded) value =
      cast (congrArg C.ResponseSeed indexEq.symm) (cast (C.value_privateRoot child) value) := by
    simp only [cast_cast]
  change C.responseEventUnder target shared sample index _ = _
  rw [encoded]
  exact dependent_event_cast C.ResponseSeed (C.responseEventUnder target shared sample)
    index child indexEq _

/-- Matching a full shared/observed slice is exactly the rectangular event
above.  The proof accounts for every observed descendant and every latent
coordinate; independence is invoked only after this preimage equality. -/
theorem slice_preimage_eq_rectangular (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) :
    (fun unit => decide (C.sharedAssignment unit = shared) &&
      FiniteProbRecord.singletonEvent sample (C.toSCM.evalUnder target unit)) =
      C.extension.rectangularEvent (C.sliceEvents target shared sample) := by
  funext unit
  apply Bool.eq_iff_iff.mpr
  rw [LatentExtension.rectangularEvent, FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro selected
    have parts := Bool.and_eq_true_iff.mp selected
    have sharedEq : C.sharedAssignment unit = shared := of_decide_eq_true parts.1
    have evaluated : C.toSCM.evalUnder target unit = sample := of_decide_eq_true parts.2
    have localEvents := (C.toSCM_evalUnder_eq_iff_responseEvents target unit sample).mp evaluated
    rw [sharedEq] at localEvents
    intro root
    by_cases selected : root.val < C.shared.count
    · have rootEq : C.sharedRoot (C.sharedIndex root selected) = root := Fin.ext rfl
      rw [← rootEq, C.sliceEvents_sharedRoot]
      exact decide_eq_true (congrFun sharedEq (C.sharedIndex root selected))
    · have rootEq : C.privateRoot (C.privateIndex root selected) = root := by
        apply Fin.ext
        change C.shared.count + (root.val - C.shared.count) = root.val
        omega
      rw [← rootEq, C.sliceEvents_privateRoot]
      exact localEvents (C.privateIndex root selected)
  · intro rectangular
    have sharedEq : C.sharedAssignment unit = shared := by
      funext root
      have selected := rectangular (C.sharedRoot root)
      rw [C.sliceEvents_sharedRoot] at selected
      exact of_decide_eq_true selected
    have localEvents : forall child, C.responseEventUnder target (C.sharedAssignment unit) sample child
        (C.responseAssignment unit child) = true := by
      intro child
      rw [sharedEq]
      have selected := rectangular (C.privateRoot child)
      rw [C.sliceEvents_privateRoot] at selected
      exact selected
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true sharedEq, decide_eq_true
      ((C.toSCM_evalUnder_eq_iff_responseEvents target unit sample).mpr localEvents)⟩

/-- A forced node integrates to one or zero according to consistency with
the supplied assignment.  A free node integrates to its actual rational row. -/
def rowValueUnder (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (child : Fin S.count) : QProb :=
  match target child with
  | some forced => if forced = sample child then QProb.one else QProb.zero
  | none => (C.row child (C.encode child (fun parent _edge => sample parent)
      (fun root _incident => shared root))).probVal (FiniteProbRecord.singletonEvent (sample child))

theorem responseFactor_responseEventUnder (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (child : Fin S.count) :
    QProb.Equiv ((C.responseFactor child).probVal (C.responseEventUnder target shared sample child))
      (C.rowValueUnder target shared sample child) := by
  unfold responseEventUnder rowValueUnder
  cases selected : target child with
  | none =>
      exact C.responseFactor_preserves_row child (fun parent _edge => sample parent)
        (fun root _incident => shared root) (FiniteProbRecord.singletonEvent (sample child))
  | some forced =>
      by_cases same : forced = sample child
      · simpa only [if_pos same, decide_eq_true same, topEvent] using
          (C.responseFactor child).normalization
      · simpa only [if_neg same, decide_eq_false same] using
          (C.responseFactor child).probVal_false

/-- The elementary likelihood factors in the same coordinate order as the
actual product prior.  Private response-table denominators have been fully
integrated away before any concrete likelihood is computed. -/
def sliceFactors (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (root : Fin C.extension.count) : QProb :=
  if selected : root.val < C.shared.count then
    (C.sharedFactor (C.sharedIndex root selected)).probVal
      (FiniteProbRecord.singletonEvent (shared (C.sharedIndex root selected)))
  else C.rowValueUnder target shared sample (C.privateIndex root selected)

private theorem factor_sliceEvents (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) (root : Fin C.extension.count) :
    QProb.Equiv ((C.factor root).probVal (C.sliceEvents target shared sample root))
      (C.sliceFactors target shared sample root) := by
  by_cases selected : root.val < C.shared.count
  · unfold factor sliceEvents sliceFactors
    simp only [dif_pos selected]
    let original := C.sharedFactor (C.sharedIndex root selected)
    let event := FiniteProbRecord.singletonEvent (shared (C.sharedIndex root selected))
    have mapped := original.map_probVal (cast (C.value_of_shared root selected).symm)
      (fun value => event (cast (C.value_of_shared root selected) value))
    exact QProb.equiv_trans mapped (original.probVal_congr _ event (by
      intro value
      simp only [cast_cast, cast_eq]))
  · unfold factor sliceEvents sliceFactors
    simp only [dif_neg selected]
    let child := C.privateIndex root selected
    let event := C.responseEventUnder target shared sample child
    have mapped := (C.responseFactor child).map_probVal (cast (C.value_of_private root selected).symm)
      (fun value => event (cast (C.value_of_private root selected) value))
    exact QProb.equiv_trans mapped
      (QProb.equiv_trans ((C.responseFactor child).probVal_congr _ event (by
        intro value
        simp only [cast_cast, cast_eq]))
        (C.responseFactor_responseEventUnder target shared sample child))

/-- Exact full-assignment slice probability for the actual SCM, under every
intervention.  This is the semantic bridge from independent response-function
priors to the ordinary finite hidden-table likelihood calculation. -/
theorem toSCM_slice_probability (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (shared : C.shared.Assignment) (sample : S.Assignment) :
    QProb.Equiv
      (C.toSCM.prior.probVal (fun unit => decide (C.sharedAssignment unit = shared) &&
        FiniteProbRecord.singletonEvent sample (C.toSCM.evalUnder target unit)))
      (FiniteProduct.qProduct C.extension.count (C.sliceFactors target shared sample)) :=
  QProb.equiv_trans
    (C.toSCM.prior.probVal_congr _ _ (fun unit =>
      congrFun (C.slice_preimage_eq_rectangular target shared sample) unit))
    (QProb.equiv_trans (C.toSCM.product_law (C.sliceEvents target shared sample))
      (FiniteProduct.qProduct_congr C.extension.count
        (C.factor_sliceEvents target shared sample)))

/-- Only the original shared assignment space is enumerated for likelihood
integration.  The generally much larger private response spaces are already
integrated by the coordinate and product-law theorems. -/
def sharedEnumeration (C : FiniteLatentRationalCPT S) : List C.shared.Assignment :=
  deduplicate (FiniteProduct.enumeration C.shared.count C.shared.Value C.shared.valueEnumeration)

theorem sharedEnumeration_complete (C : FiniteLatentRationalCPT S)
    (unit : C.shared.Assignment) : unit ∈ C.sharedEnumeration := by
  rw [sharedEnumeration, mem_deduplicate]
  exact FiniteProduct.enumeration_complete C.shared.count C.shared.Value
    C.shared.valueEnumeration C.shared.value_complete unit

theorem sharedEnumeration_nodup (C : FiniteLatentRationalCPT S) : C.sharedEnumeration.Nodup :=
  deduplicate_nodup _

/-- Likelihood sum over any supplied complete repetition-free shared
enumeration.  Keeping this list explicit permits compact concrete regression
enumerations without unfolding a response-function prior. -/
def likelihoodWith (C : FiniteLatentRationalCPT S)
    (values : List C.shared.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (sample : S.Assignment) : QProb :=
  QProb.listSum (values.map fun shared =>
    FiniteProduct.qProduct C.extension.count (C.sliceFactors target shared sample))

/-- Full interventional singleton probability equals the ordinary truncated
hidden-table likelihood.  All shared values are summed, and every private
response source is integrated against its genuine independent factor. -/
theorem toSCM_interventional_singleton_likelihoodWith (C : FiniteLatentRationalCPT S)
    (values : List C.shared.Assignment) (nodup : values.Nodup)
    (complete : forall unit, unit ∈ values)
    (target : (node : Fin S.count) -> Option (S.Value node)) (sample : S.Assignment) :
    QProb.Equiv (C.toSCM.interventionalValue target (FiniteProbRecord.singletonEvent sample))
      (C.likelihoodWith values target sample) :=
  QProb.equiv_trans (C.toSCM.interventionalValue_eq target _)
    (QProb.equiv_trans (C.toSCM.prior.probVal_equiv_listSum_fibres C.sharedAssignment
      (fun unit => FiniteProbRecord.singletonEvent sample (C.toSCM.evalUnder target unit))
      values nodup complete)
      (QProb.listSum_map_congr values _ _ (C.toSCM_slice_probability target · sample)))

/-- The canonical finite shared enumeration gives a premise-free
interventional likelihood formula, including empty signatures and sources. -/
theorem toSCM_interventional_singleton_likelihood (C : FiniteLatentRationalCPT S)
    (target : (node : Fin S.count) -> Option (S.Value node)) (sample : S.Assignment) :
    QProb.Equiv (C.toSCM.interventionalValue target (FiniteProbRecord.singletonEvent sample))
      (C.likelihoodWith C.sharedEnumeration target sample) :=
  C.toSCM_interventional_singleton_likelihoodWith C.sharedEnumeration
    C.sharedEnumeration_nodup C.sharedEnumeration_complete target sample

/-- Factual likelihood is the empty-intervention specialization, with no
independent semantic premise about the observed marginal. -/
theorem toSCM_observational_singleton_likelihoodWith (C : FiniteLatentRationalCPT S)
    (values : List C.shared.Assignment) (nodup : values.Nodup)
    (complete : forall unit, unit ∈ values) (sample : S.Assignment) :
    QProb.Equiv (C.toSCM.observationalValue (FiniteProbRecord.singletonEvent sample))
      (C.likelihoodWith values (FiniteLatentSCM.noIntervention S) sample) :=
  C.toSCM_interventional_singleton_likelihoodWith values nodup complete
    (FiniteLatentSCM.noIntervention S) sample

/-- Arbitrary event probabilities follow by summing the complete assignment
likelihoods selected by the event.  The intervention may force nonbinary
labels, and the event need not be a singleton or a coordinate cylinder. -/
theorem toSCM_interventionalValue_likelihoodWith (C : FiniteLatentRationalCPT S)
    (values : List C.shared.Assignment) (nodup : values.Nodup)
    (complete : forall unit, unit ∈ values)
    (samples : List S.Assignment) (samplesNodup : samples.Nodup)
    (samplesComplete : forall sample, sample ∈ samples)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv (C.toSCM.interventionalValue target event)
      (QProb.listSum ((samples.filter event).map (C.likelihoodWith values target))) :=
  QProb.equiv_trans
    ((C.toSCM.interventionalDist target).probVal_equiv_listSum_singletons
      samples samplesNodup samplesComplete event)
    (QProb.listSum_map_congr (samples.filter event) _ _
      (C.toSCM_interventional_singleton_likelihoodWith values nodup complete target))

private theorem qProduct_num_positive (n : Nat) (values : Fin n -> QProb)
    (positive : forall index, 0 < (values index).num) :
    0 < (FiniteProduct.qProduct n values).num := by
  induction n with
  | zero => change (0 : Nat) < 1; decide
  | succ n inductionHypothesis =>
      exact Nat.mul_pos (positive (Fin.last n))
        (inductionHypothesis (fun index => values index.castSucc) (fun index => positive index.castSucc))

/-- One explicitly supported shared assignment suffices for full observed
positivity when all rows at that assignment are positive.  Shared factors
may have zero-weight values elsewhere.  Supplying this finite witness as
data avoids choosing a family of supported latent representatives. -/
theorem toSCM_observationallyPositive_of_supportedShared (C : FiniteLatentRationalCPT S)
    (shared : C.shared.Assignment)
    (sharedPositive : forall root,
      (C.sharedFactor root).EventPositive (FiniteProbRecord.singletonEvent (shared root)))
    (rowsPositive : forall (sample : S.Assignment) child,
      (C.row child (C.encode child (fun parent _edge => sample parent)
        (fun root _incident => shared root))).EventPositive
          (FiniteProbRecord.singletonEvent (sample child))) :
    ObservationallyPositive C.toSCM := by
  intro sample
  let target := FiniteLatentSCM.noIntervention S
  have factorsPositive : forall root, 0 < (C.sliceFactors target shared sample root).num := by
    intro root
    unfold sliceFactors
    by_cases selected : root.val < C.shared.count
    · rw [dif_pos selected]
      exact sharedPositive (C.sharedIndex root selected)
    · rw [dif_neg selected]
      change 0 < ((C.row _ (C.encode _ (fun parent _edge => sample parent)
        (fun root _incident => shared root))).probVal
          (FiniteProbRecord.singletonEvent (sample _))).num
      exact rowsPositive sample (C.privateIndex root selected)
  have slicePositive := (QProb.equiv_num_pos_iff
    (C.toSCM_slice_probability target shared sample)).mpr
      (qProduct_num_positive C.extension.count _ factorsPositive)
  have enlarged : 0 < FiniteProbRecord.eventMass C.toSCM.prior.atoms
      (fun unit => FiniteProbRecord.singletonEvent sample (C.toSCM.evalUnder target unit)) :=
    Nat.lt_of_lt_of_le slicePositive (FiniteProbRecord.eventMass_mono _ _ _ (by
      intro unit selected
      exact (Bool.and_eq_true_iff.mp selected).2))
  exact (QProb.equiv_num_pos_iff
    (C.toSCM.observationalValue_eq (FiniteProbRecord.singletonEvent sample))).mpr enlarged

/-! ## Private response sources preserve the exact projected graph -/

theorem extension_canonical (C : FiniteLatentRationalCPT S)
    (canonical : C.shared.CanonicalSemiMarkovian) : C.extension.CanonicalSemiMarkovian := by
  intro root first second third one two three
  by_cases selected : root.val < C.shared.count
  · have rootEq : C.sharedRoot (C.sharedIndex root selected) = root := Fin.ext rfl
    change C.incident root first = true at one
    change C.incident root second = true at two
    change C.incident root third = true at three
    rw [← rootEq, C.incident_sharedRoot] at one two three
    exact canonical _ first second third one two three
  · have rootEq : C.privateRoot (C.privateIndex root selected) = root := by
      apply Fin.ext
      change C.shared.count + (root.val - C.shared.count) = root.val
      omega
    change C.incident root first = true at one
    change C.incident root second = true at two
    rw [← rootEq, C.incident_privateRoot] at one two
    exact Or.inl ((of_decide_eq_true one).trans (of_decide_eq_true two).symm)

/-- Every projected edge has an original shared witness.  A private table
cannot witness an edge between distinct observed endpoints. -/
theorem extension_projectedBidirected (C : FiniteLatentRationalCPT S)
    (first second : Fin S.count) :
    C.extension.projectedBidirected first second = C.shared.projectedBidirected first second := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro edge
    have parts := Bool.and_eq_true_iff.mp edge
    rcases (finAny_eq_true_iff _).mp parts.2 with ⟨root, selectedAt⟩
    have incidents := Bool.and_eq_true_iff.mp selectedAt
    by_cases selected : root.val < C.shared.count
    · have rootEq : C.sharedRoot (C.sharedIndex root selected) = root := Fin.ext rfl
      change C.incident root first = true ∧ C.incident root second = true at incidents
      rw [← rootEq, C.incident_sharedRoot, C.incident_sharedRoot] at incidents
      exact Bool.and_eq_true_iff.mpr ⟨parts.1,
        (finAny_eq_true_iff _).mpr ⟨C.sharedIndex root selected, Bool.and_eq_true_iff.mpr incidents⟩⟩
    · have rootEq : C.privateRoot (C.privateIndex root selected) = root := by
        apply Fin.ext
        change C.shared.count + (root.val - C.shared.count) = root.val
        omega
      change C.incident root first = true ∧ C.incident root second = true at incidents
      rw [← rootEq, C.incident_privateRoot, C.incident_privateRoot] at incidents
      have same := (of_decide_eq_true incidents.1).trans (of_decide_eq_true incidents.2).symm
      subst second
      have impossible := parts.1
      change (!(Nat.beq first.val first.val)) = true at impossible
      rw [natBeq_refl] at impossible
      cases impossible
  · intro edge
    have parts := Bool.and_eq_true_iff.mp edge
    rcases (finAny_eq_true_iff _).mp parts.2 with ⟨root, selectedAt⟩
    have incidents := Bool.and_eq_true_iff.mp selectedAt
    apply Bool.and_eq_true_iff.mpr
    refine ⟨parts.1, (finAny_eq_true_iff _).mpr ⟨C.sharedRoot root, ?_⟩⟩
    change (C.incident (C.sharedRoot root) first && C.incident (C.sharedRoot root) second) = true
    rw [C.incident_sharedRoot, C.incident_sharedRoot]
    exact Bool.and_eq_true_iff.mpr incidents

/-- Compatibility is established for the actual functionalized model,
without weakening the supplied graph to a supergraph. -/
theorem toSCM_compatible (C : FiniteLatentRationalCPT S) (graph : ObservedGraph S)
    (canonical : C.shared.CanonicalSemiMarkovian)
    (projected : forall first second, C.shared.projectedBidirected first second = graph.bidirected first second) :
    Compatible C.toSCM graph :=
  ⟨C.extension_canonical canonical,
    fun first second => (C.extension_projectedBidirected first second).trans (projected first second)⟩

end FiniteLatentRationalCPT
end Causality
end Thesis
