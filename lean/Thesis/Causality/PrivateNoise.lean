import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# A fresh private Boolean source for constructive readout mechanisms

Positive hedge readouts need independent biased noise at each modified
coordinate.  A noisy event record alone is not a structural causal model:
the extra source must have a typed mechanism input, a genuine product prior,
and no new projected bidirected edges.  This module provides that extension
for an arbitrary exact finite SCM and an arbitrary Boolean noise record.

The new source is appended after all old latent coordinates.  This agrees
with the dependent product's last-coordinate recursion and lets the prior
be the literal pushforward of `noise × old prior`, not an assumed product
law.  Old value types, factors, and incidence are transported explicitly.
Only the selected observed mechanism is replaced; every other mechanism
receives its old latent inputs unchanged.

Full support has a separate constructive proof: an explicit bit restoring the
old pivot value restores the whole evaluated assignment by topological
induction.  Thus a restoring readout preserves positivity even when other
mechanisms read the pivot.  The non-influence assumption is retained only by
the stronger common-observable-law arguments, not by this support theorem.

Coordinate data use the project's constructive `FiniteProduct.extend`.
The standard `Fin.lastCases_castSucc` reduction theorem carries a choice
dependency, so it must not be used to reduce these enumerations or factors.
The last/castSucc laws of `extend` prove the same reductions constructively.

This is structural infrastructure, not a claim that an arbitrary replacement
preserves observational equality or positivity.  A readout construction must
still prove those semantic properties for its particular mechanism.  The
module does not import either published theorem implementation.
-/

namespace PrivateBooleanNoise

variable {S : ObservedSignature.{0}}

/-- Append a Boolean coordinate without homogenizing the old value types. -/
def Value (latent : LatentExtension S) : Fin (latent.count + 1) -> Type :=
  FiniteProduct.extend (Value := fun _ => Type) Bool latent.Value

@[simp] theorem value_last (latent : LatentExtension S) :
    Value latent (Fin.last latent.count) = Bool :=
  FiniteProduct.extend_last (Value := fun _ => Type) Bool latent.Value

@[simp] theorem value_castSucc (latent : LatentExtension S) (root : Fin latent.count) :
    Value latent root.castSucc = latent.Value root :=
  FiniteProduct.extend_castSucc (Value := fun _ => Type) Bool latent.Value root

/-- The appended root is private to `pivot`; old incidence is retained. -/
def incident (latent : LatentExtension S) (pivot : Fin S.count)
    (root : Fin (latent.count + 1)) (child : Fin S.count) : Bool :=
  FiniteProduct.extend (Value := fun _ => Bool) (decide (child = pivot))
    (fun old => latent.incident old child) root

@[simp] theorem incident_last (latent : LatentExtension S) (pivot child : Fin S.count) :
    incident latent pivot (Fin.last latent.count) child = decide (child = pivot) :=
  FiniteProduct.extend_last (Value := fun _ => Bool) _ _

@[simp] theorem incident_castSucc (latent : LatentExtension S) (pivot child : Fin S.count)
    (root : Fin latent.count) : incident latent pivot root.castSucc child = latent.incident root child :=
  FiniteProduct.extend_castSucc (Value := fun _ => Bool) _ _ root

/-- Enumerate both new Boolean values and every transported old value. -/
def enumeration (latent : LatentExtension S) (root : Fin (latent.count + 1)) :
    List (Value latent root) :=
  FiniteProduct.extend (Value := fun root => List (Value latent root))
    ([false, true].map (cast (value_last latent).symm))
    (fun old => (latent.valueEnumeration old).map (cast (value_castSucc latent old).symm)) root

theorem enumeration_complete (latent : LatentExtension S) (root : Fin (latent.count + 1))
    (value : Value latent root) : value ∈ enumeration latent root := by
  refine Fin.lastCases
    (motive := fun root => forall value : Value latent root, value ∈ enumeration latent root)
    ?_ (fun old => ?_) root value
  · intro value
    simp only [enumeration, FiniteProduct.extend_last]
    apply List.mem_map.mpr
    refine ⟨cast (value_last latent) value, ?_, by simp⟩
    cases cast (value_last latent) value <;> simp
  · intro value
    simp only [enumeration, FiniteProduct.extend_castSucc]
    exact List.mem_map.mpr
      ⟨cast (value_castSucc latent old) value, latent.value_complete _ _, by simp⟩

/-- The extra private source changes neither the observed signature nor
the incidence of any old source. -/
def extension (latent : LatentExtension S) (pivot : Fin S.count) : LatentExtension S where
  count := latent.count + 1
  Value := Value latent
  valueEnumeration := enumeration latent
  value_complete := enumeration_complete latent
  valueDecidableEq := fun root => by
    refine Fin.lastCases
      (motive := fun root => DecidableEq (Value latent root)) ?_ (fun old => ?_) root
    · change DecidableEq (Value latent (Fin.last latent.count))
      rw [value_last]; infer_instance
    · change DecidableEq (Value latent old.castSucc)
      rw [value_castSucc]; exact latent.valueDecidableEq old
  incident := incident latent pivot

/-- Encode the actual independent pair used by the augmented prior. -/
def assignment (latent : LatentExtension S) (bit : Bool) (old : latent.Assignment) :
    (root : Fin (latent.count + 1)) -> Value latent root :=
  FiniteProduct.extend (cast (value_last latent).symm bit)
    (fun root => cast (value_castSucc latent root).symm (old root))

@[simp] theorem assignment_last (latent : LatentExtension S) (bit : Bool) (old : latent.Assignment) :
    cast (value_last latent) (assignment latent bit old (Fin.last latent.count)) = bit := by
  simp [assignment]

@[simp] theorem assignment_castSucc (latent : LatentExtension S) (bit : Bool) (old : latent.Assignment)
    (root : Fin latent.count) : cast (value_castSucc latent root)
      (assignment latent bit old root.castSucc) = old root := by
  simp [assignment]

/-- Recover the old typed latent inputs available to any observed child. -/
def oldInputs (latent : LatentExtension S) (pivot child : Fin S.count)
    (inputs : (extension latent pivot).Inputs child) : latent.Inputs child :=
  fun root selected => cast (value_castSucc latent root)
    (inputs root.castSucc (by simpa only [extension, incident_castSucc] using selected))

/-- Read the new Boolean only at its unique incident child. -/
def bit (latent : LatentExtension S) (pivot : Fin S.count)
    (inputs : (extension latent pivot).Inputs pivot) : Bool :=
  cast (value_last latent)
    (inputs (Fin.last latent.count) (by simp only [extension, incident_last, decide_true]))

/-- Encoding an independent pair does not alter any old incident input. -/
theorem oldInputs_assignment (latent : LatentExtension S) (pivot child : Fin S.count)
    (bit : Bool) (old : latent.Assignment) :
    oldInputs latent pivot child (fun root _selected => assignment latent bit old root) =
      (fun root _selected => old root) := by
  funext root selected
  exact assignment_castSucc latent bit old root

/-- The new mechanism reads exactly the encoded independent Boolean. -/
theorem bit_assignment (latent : LatentExtension S) (pivot : Fin S.count)
    (value : Bool) (old : latent.Assignment) :
    bit latent pivot (fun root _selected => assignment latent value old root) = value :=
  assignment_last latent value old

/-- Transport the old factor records and install the supplied noise factor. -/
def factor (base : ExactModel S) (noise : FiniteProbRecord Bool)
    (root : Fin (base.latent.count + 1)) : FiniteProbRecord (Value base.latent root) :=
  FiniteProduct.extend (Value := fun root => FiniteProbRecord (Value base.latent root))
    (noise.map (cast (value_last base.latent).symm))
    (fun old => (base.factor old).map (cast (value_castSucc base.latent old).symm)) root

/-- A literal product prior, relabelled as an augmented dependent assignment. -/
def prior (base : ExactModel S) (noise : FiniteProbRecord Bool) :
    FiniteProbRecord ((root : Fin (base.latent.count + 1)) -> Value base.latent root) :=
  (noise.product base.prior).map (fun pair => assignment base.latent pair.1 pair.2)

/-- Coordinate-wise relabelling commutes with the finite rectangular test.
Here it transports old typed coordinates into their appended positions. -/
private theorem rectangularEvent_map (count : Nat) (source target : Fin count -> Type)
    (maps : (root : Fin count) -> source root -> target root)
    (events : (root : Fin count) -> target root -> Bool)
    (values : (root : Fin count) -> source root) :
    FiniteProduct.rectangularEvent count target events (fun root => maps root (values root)) =
      FiniteProduct.rectangularEvent count source (fun root value => events root (maps root value)) values := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [FiniteProduct.rectangularEvent]
      rw [inductionHypothesis]

/-- The relabelled product has exactly the source-wise rectangular-event
law required by `FiniteLatentSCM`.  Nonrectangular readout events are not
silently assumed to factor; only the explicit independent prior is used. -/
theorem product_law (base : ExactModel S) (noise : FiniteProbRecord Bool)
    (events : (root : Fin (base.latent.count + 1)) -> Value base.latent root -> Bool) :
    QProb.Equiv
      ((prior base noise).probVal (FiniteProduct.rectangularEvent _ _ events))
      (FiniteProduct.qProduct (base.latent.count + 1)
        (fun root => (factor base noise root).probVal (events root))) := by
  let oldEvents := fun root value => events root.castSucc
    (cast (value_castSucc base.latent root).symm value)
  let noiseEvent := fun bit => events (Fin.last base.latent.count)
    (cast (value_last base.latent).symm bit)
  have eventEqual (pair : Bool × base.latent.Assignment) :
      FiniteProduct.rectangularEvent _ _ events (assignment base.latent pair.1 pair.2) =
        (noiseEvent pair.1 && base.latent.rectangularEvent oldEvents pair.2) := by
    simp only [FiniteProduct.rectangularEvent, assignment, FiniteProduct.extend_last,
      FiniteProduct.extend_castSucc]
    rw [rectangularEvent_map]
    rfl
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => assignment base.latent pair.1 pair.2) (FiniteProduct.rectangularEvent _ _ events)
  have rectangular := (noise.product base.prior).probVal_congr _ _ eventEqual
  have independent := noise.product_probVal base.prior noiseEvent (base.latent.rectangularEvent oldEvents)
  have old := base.product_law oldEvents
  have factors : QProb.Equiv
      (FiniteProduct.qProduct (base.latent.count + 1)
        (fun root => (factor base noise root).probVal (events root)))
      (QProb.mul (noise.probVal noiseEvent)
        (FiniteProduct.qProduct base.latent.count (fun root => (base.factor root).probVal (oldEvents root)))) := by
    simp only [FiniteProduct.qProduct, factor, FiniteProduct.extend_last, FiniteProduct.extend_castSucc]
    exact QProb.mul_congr
      (noise.map_probVal (cast (value_last base.latent).symm) _)
      (FiniteProduct.qProduct_congr _ (fun root =>
        (base.factor root).map_probVal (cast (value_castSucc base.latent root).symm) _))
  exact QProb.equiv_trans pushed
    (QProb.equiv_trans rectangular
      (QProb.equiv_trans independent
        (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) old) (QProb.equiv_symm factors))))

/-! ## The private source preserves the projected graph and canonical class -/

theorem projectedBidirected_eq (latent : LatentExtension S) (pivot left right : Fin S.count) :
    (extension latent pivot).projectedBidirected left right = latent.projectedBidirected left right := by
  by_cases same : left = right
  · subst right
    rw [LatentExtension.projectedBidirected_irreflexive, LatentExtension.projectedBidirected_irreflexive]
  · have privateFalse : (decide (left = pivot) && decide (right = pivot)) = false := by
      by_cases first : left = pivot
      · by_cases second : right = pivot
        · exact False.elim (same (first.trans second.symm))
        · simp [first, second]
      · simp [first]
    have anyEqual : finAny (latent.count + 1)
        (fun root => incident latent pivot root left && incident latent pivot root right) =
        finAny latent.count (fun root => latent.incident root left && latent.incident root right) := by
      simp only [finAny, incident_last, incident_castSucc, privateFalse, Bool.or_false]
    simp only [LatentExtension.projectedBidirected, extension, anyEqual]

theorem canonical (latent : LatentExtension S) (pivot : Fin S.count)
    (old : latent.CanonicalSemiMarkovian) : (extension latent pivot).CanonicalSemiMarkovian := by
  intro root
  refine Fin.lastCases
    (motive := fun root => forall left right third,
      (extension latent pivot).incident root left = true ->
      (extension latent pivot).incident root right = true ->
      (extension latent pivot).incident root third = true ->
      left = right ∨ left = third ∨ right = third) ?_ (fun earlier => ?_) root
  · intro left right _third first second _thirdSelected
    have firstEqual : left = pivot := of_decide_eq_true (by simpa only [extension, incident_last] using first)
    have secondEqual : right = pivot := of_decide_eq_true (by simpa only [extension, incident_last] using second)
    exact Or.inl (firstEqual.trans secondEqual.symm)
  · intro left right third first second thirdSelected
    exact old earlier left right third
      (by simpa only [extension, incident_castSucc] using first)
      (by simpa only [extension, incident_castSucc] using second)
      (by simpa only [extension, incident_castSucc] using thirdSelected)

end PrivateBooleanNoise

/-- Append a private Boolean source and replace exactly one observed
mechanism.  The replacement receives the declared parents, old incident
latents, and the fresh independent bit.  It cannot inspect another observed
node directly or acquire an undeclared shared noise source. -/
def FiniteLatentSCM.withPrivateBooleanNoise
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot) : ExactModel S where
  latent := PrivateBooleanNoise.extension base.latent pivot
  factor := PrivateBooleanNoise.factor base noise
  prior := PrivateBooleanNoise.prior base noise
  product_law := PrivateBooleanNoise.product_law base noise
  mechanism := by
    intro child parents inputs
    by_cases same : child = pivot
    · subst child
      exact replacement parents (PrivateBooleanNoise.oldInputs base.latent pivot pivot inputs)
        (PrivateBooleanNoise.bit base.latent pivot inputs)
    · exact base.mechanism child parents (PrivateBooleanNoise.oldInputs base.latent pivot child inputs)

/-- The fresh private root does not alter any projected bidirected edge and
preserves the canonical at-most-two-children latent restriction. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_compatible
    {S : ObservedSignature.{0}} {graph : ObservedGraph S}
    (base : ExactModel S) (compatible : Compatible base graph) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot) :
    Compatible (base.withPrivateBooleanNoise pivot noise replacement) graph :=
  ⟨PrivateBooleanNoise.canonical base.latent pivot compatible.1, fun left right =>
    (PrivateBooleanNoise.projectedBidirected_eq base.latent pivot left right).trans (compatible.2 left right)⟩

/-- An unchanged child mechanism receives exactly its old typed inputs. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (child : Fin S.count) (different : child ≠ pivot) (parents : S.ParentValues child)
    (inputs : (PrivateBooleanNoise.extension base.latent pivot).Inputs child) :
    (base.withPrivateBooleanNoise pivot noise replacement).mechanism child parents inputs =
      base.mechanism child parents (PrivateBooleanNoise.oldInputs base.latent pivot child inputs) := by
  simp only [FiniteLatentSCM.withPrivateBooleanNoise, dif_neg different]

/-- The selected mechanism receives its old inputs and the fresh bit. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_mechanism_pivot
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (parents : S.ParentValues pivot)
    (inputs : (PrivateBooleanNoise.extension base.latent pivot).Inputs pivot) :
    (base.withPrivateBooleanNoise pivot noise replacement).mechanism pivot parents inputs =
      replacement parents (PrivateBooleanNoise.oldInputs base.latent pivot pivot inputs)
        (PrivateBooleanNoise.bit base.latent pivot inputs) := by
  simp only [FiniteLatentSCM.withPrivateBooleanNoise, dite_true]

/-- Semantic non-influence needed by a topologically ordered readout update.
Every other mechanism ignores the selected coordinate, though the ambient
signature may still allow it as a parent.  In a hedge construction this holds
for an unmodified outside-forest coordinate, and for a common forest root:
kept forest mechanisms do not read its output, while earlier readouts cannot
have a later observed parent.  It is not assumed for arbitrary replacements. -/
def FiniteLatentSCM.OtherMechanismsIgnore
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count) : Prop :=
  forall child, child ≠ pivot ->
    forall (first second : S.ParentValues child) (inputs : base.latent.Inputs child),
      (forall parent (edge : S.directed parent child = true), parent ≠ pivot ->
        first parent edge = second parent edge) ->
      base.mechanism child first inputs = base.mechanism child second inputs

/-- Replacing an earlier mechanism preserves non-influence of a later
coordinate.  More generally, the replaced vertex only needs to have no
incoming edge from the ignored coordinate.

The new mechanism may inspect all of its declared parents: since the ignored
coordinate is not one of them, agreement off that coordinate is agreement on
the entire parent input.  Every unchanged mechanism inherits the old
non-influence proof with its explicitly recovered old latent inputs.  This
is the invariant needed to perform more than one private readout; no claim
about arbitrary reverse-topological replacements is made. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_otherMechanismsIgnore
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot later : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore later)
    (notParent : S.directed later pivot = false) :
    (base.withPrivateBooleanNoise pivot noise replacement).OtherMechanismsIgnore later := by
  intro child childDifferent first second inputs agree
  by_cases modified : child = pivot
  · subst child
    rw [base.withPrivateBooleanNoise_mechanism_pivot, base.withPrivateBooleanNoise_mechanism_pivot]
    have parentsEqual : first = second := by
      funext parent edge
      apply agree parent edge
      intro same
      subst parent
      rw [notParent] at edge
      cases edge
    rw [parentsEqual]
  · rw [base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child modified,
      base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child modified]
    exact ignored child childDifferent first second _ agree

/-- In the signature's topological order, a private replacement cannot
introduce dependence on a later coordinate.  The strict inequality supplies
both distinctness and absence of a backward parent edge constructively. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_otherMechanismsIgnore_of_earlier
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot later : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore later) (earlier : pivot.val < later.val) :
    (base.withPrivateBooleanNoise pivot noise replacement).OtherMechanismsIgnore later := by
  apply base.withPrivateBooleanNoise_otherMechanismsIgnore pivot later noise replacement ignored
  cases edge : S.directed later pivot with
  | false => rfl
  | true => exact False.elim (Nat.lt_asymm earlier (S.directed_earlier edge))

/-- A fresh-noise update cannot change another coordinate when every other
base mechanism ignores the pivot.  The proof follows the observed topological
order, so each declared non-pivot parent has already been matched.  Both
arbitrary interventions and empty latent signatures are included. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (bit : Bool)
    (child : Fin S.count) (different : child ≠ pivot) :
    (base.withPrivateBooleanNoise pivot noise replacement).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment base.latent bit old) child =
      base.evalNodeUnder intervention old child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases intervention child with
  | some value => rfl
  | none =>
      simp only [base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child different]
      unfold PrivateBooleanNoise.oldInputs
      simp only [PrivateBooleanNoise.assignment_castSucc]
      apply ignored child different
      intro parent edge parentDifferent
      exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne pivot noise replacement
        ignored intervention old bit parent parentDifferent
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- A private replacement preserves every interventional event supported
on coordinates other than its pivot, provided the other mechanisms ignore
that pivot.  This is stronger than a statement about the observational law:
the intervention is arbitrary and may itself fix the replaced coordinate.

The augmented prior is the actual independent product of the fresh bit and
the old prior.  For each such pair, the preceding coordinate theorem matches
every node inspected by the event.  The event therefore ignores the fresh
bit, which integrates out by the finite product marginal law.  In particular,
no common latent assignment or unproved denominator equality is required
when applying this result to the two sides of a countermodel separately. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_interventionalValue_equiv_of_off
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (off : nodes pivot = false)
    (event : S.Assignment -> Bool) (eventLocal : EventDependsOnlyOn nodes event) :
    QProb.Equiv
      ((base.withPrivateBooleanNoise pivot noise replacement).interventionalValue intervention event)
      (base.interventionalValue intervention event) := by
  let model := base.withPrivateBooleanNoise pivot noise replacement
  have eventEqual (pair : Bool × base.latent.Assignment) :
      event (model.evalUnder intervention (PrivateBooleanNoise.assignment base.latent pair.1 pair.2)) =
        event (base.evalUnder intervention pair.2) := by
    apply eventLocal
    intro child selected
    apply base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne pivot noise replacement
      ignored intervention pair.2 pair.1 child
    intro same
    subst child
    rw [off] at selected
    cases selected
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => event (model.evalUnder intervention latent))
  have unchanged := (noise.product base.prior).probVal_congr _ _ eventEqual
  have marginal := noise.product_probVal_right base.prior
    (fun latent => event (base.evalUnder intervention latent))
  exact QProb.equiv_trans (model.interventionalValue_eq intervention event)
    (QProb.equiv_trans pushed (QProb.equiv_trans unchanged
      (QProb.equiv_trans marginal (QProb.equiv_symm (base.interventionalValue_eq intervention event)))))

/-- At a free pivot the replacement sees the base model's unchanged parent
values, its old latent inputs, and the independent bit.  Acyclicity prevents
the pivot from being its own parent. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_evalNodeUnder_pivot
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : intervention pivot = none) (old : base.latent.Assignment) (bit : Bool) :
    (base.withPrivateBooleanNoise pivot noise replacement).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment base.latent bit old) pivot =
      replacement (fun parent _edge => base.evalNodeUnder intervention old parent)
        (fun root _selected => old root) bit := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  simp only [base.withPrivateBooleanNoise_mechanism_pivot]
  unfold PrivateBooleanNoise.oldInputs
  simp only [PrivateBooleanNoise.bit, PrivateBooleanNoise.assignment_castSucc,
    PrivateBooleanNoise.assignment_last]
  have parentsEqual :
      (fun parent (_edge : S.directed parent pivot = true) =>
        (base.withPrivateBooleanNoise pivot noise replacement).evalNodeUnder intervention
          (PrivateBooleanNoise.assignment base.latent bit old) parent) =
        (fun parent (_edge : S.directed parent pivot = true) => base.evalNodeUnder intervention old parent) := by
    funext parent edge
    apply base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne pivot noise replacement ignored
    intro same
    have earlier := S.directed_earlier edge
    subst parent
    exact (Nat.lt_irrefl _ earlier).elim
  rw [parentsEqual]

/-! ## Readout mechanisms and topological restoring assignments -/

/-- A readout acts on the old coordinate value and declared parent values,
not on hidden information unavailable in the old observed assignment.  Its
fresh Boolean input is still a private independent latent source. -/
def FiniteLatentSCM.withPrivateReadout
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot) : ExactModel S :=
  base.withPrivateBooleanNoise pivot noise
    (fun parents inputs bit => readout parents (base.mechanism pivot parents inputs) bit)

/-- If a readout restores its old pivot value on one evaluated assignment,
it restores every coordinate of that assignment.  The other mechanisms need
not ignore the pivot: they may genuinely read its output, including at kept
children inside a hedge forest.  Matching all earlier parents in topological
order makes their unchanged equations return the original values again.

The intervention is arbitrary.  An intervened coordinate is already fixed
in both models; at a free pivot the displayed restoring equation is used.
The old latent unit and fresh bit are explicit data, so this statement does
not select a latent realization from an existence proposition. -/
theorem FiniteLatentSCM.withPrivateReadout_evalNodeUnder_eq_of_restores
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (bit : Bool)
    (restores : readout (fun parent _edge => base.evalNodeUnder intervention old parent)
      (base.evalNodeUnder intervention old pivot) bit = base.evalNodeUnder intervention old pivot)
    (child : Fin S.count) :
    (base.withPrivateReadout pivot noise readout).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment base.latent bit old) child =
      base.evalNodeUnder intervention old child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases fixed : intervention child with
  | some value => rfl
  | none =>
      have parentsEqual :
          (fun parent (_edge : S.directed parent child = true) =>
            (base.withPrivateReadout pivot noise readout).evalNodeUnder intervention
              (PrivateBooleanNoise.assignment base.latent bit old) parent) =
          (fun parent (_edge : S.directed parent child = true) => base.evalNodeUnder intervention old parent) := by
        funext parent edge
        exact base.withPrivateReadout_evalNodeUnder_eq_of_restores pivot noise readout
          intervention old bit restores parent
      rw [parentsEqual]
      by_cases same : child = pivot
      · subst child
        simp only [FiniteLatentSCM.withPrivateReadout, base.withPrivateBooleanNoise_mechanism_pivot]
        unfold PrivateBooleanNoise.oldInputs PrivateBooleanNoise.bit
        simp only [PrivateBooleanNoise.assignment_castSucc, PrivateBooleanNoise.assignment_last]
        have oldEquation : base.evalNodeUnder intervention old pivot =
            base.mechanism pivot (fun parent _edge => base.evalNodeUnder intervention old parent)
              (fun root _selected => old root) := by
          rw [FiniteLatentSCM.evalNodeUnder]
          unfold FiniteLatentSCM.equationUnder
          rw [fixed]
        rw [← oldEquation]
        exact restores
      · simp only [FiniteLatentSCM.withPrivateReadout,
          base.withPrivateBooleanNoise_mechanism_of_ne pivot noise _ child same]
        unfold PrivateBooleanNoise.oldInputs
        simp only [PrivateBooleanNoise.assignment_castSucc]
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Assignment-level form of the restoring theorem.  This is a local
fixed-point statement for one old unit and bit, not a claim that arbitrary
readouts preserve the old observed law. -/
theorem FiniteLatentSCM.withPrivateReadout_evalUnder_eq_of_restores
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (bit : Bool)
    (restores : readout (fun parent _edge => base.evalUnder intervention old parent)
      (base.evalUnder intervention old pivot) bit = base.evalUnder intervention old pivot) :
    (base.withPrivateReadout pivot noise readout).evalUnder intervention
        (PrivateBooleanNoise.assignment base.latent bit old) = base.evalUnder intervention old := by
  funext child
  exact base.withPrivateReadout_evalNodeUnder_eq_of_restores pivot noise readout
    intervention old bit restores child

/-! ## Common observable readouts preserve full observational equality -/

/-- The observable assignment transformation realized by one readout.
Coordinates other than the pivot are retained, including all old parents. -/
def ObservedSignature.privateReadoutAssignment
    (S : ObservedSignature.{0}) (pivot : Fin S.count)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (sample : S.Assignment) (bit : Bool) : S.Assignment :=
  S.replace sample pivot (readout (fun parent _edge => sample parent) (sample pivot) bit)

/-- Under a free-pivot intervention, the new SCM realizes the common
assignment transformation exactly at each explicitly encoded latent pair.
This is stronger than an observational probability identity and retains
arbitrary interventions for the later hedge signal argument. -/
theorem FiniteLatentSCM.withPrivateReadout_evalUnder
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : intervention pivot = none) (old : base.latent.Assignment) (bit : Bool) :
    (base.withPrivateReadout pivot noise readout).evalUnder intervention
        (PrivateBooleanNoise.assignment base.latent bit old) =
      S.privateReadoutAssignment pivot readout (base.evalUnder intervention old) bit := by
  funext child
  by_cases same : child = pivot
  · subst child
    simp only [ObservedSignature.privateReadoutAssignment, ObservedSignature.replace_at]
    change (base.withPrivateBooleanNoise pivot noise
      (fun parents inputs bit => readout parents (base.mechanism pivot parents inputs) bit)).evalNodeUnder
      intervention (PrivateBooleanNoise.assignment base.latent bit old) pivot = _
    rw [base.withPrivateBooleanNoise_evalNodeUnder_pivot pivot noise _ ignored intervention free old bit]
    congr 1
    change base.mechanism pivot (fun parent _edge => base.evalNodeUnder intervention old parent)
      (fun root _selected => old root) = base.evalNodeUnder intervention old pivot
    symm
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder
    rw [free]
  · rw [ObservedSignature.privateReadoutAssignment, S.replace_ne _ pivot child _ same]
    exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne pivot noise _ ignored
      intervention old bit child same

/-- The complete observational law of a private readout is the pushforward
of its independent bit and the base model's complete observed law.

The non-influence hypothesis is used only to identify the new recursive
evaluation with the common observed transformation.  The product slices
may mix the bit with any number of observed coordinates; no rectangular-event
factorization is incorrectly applied to such a readout event. -/
theorem FiniteLatentSCM.withPrivateReadout_observationalValue_equiv
    {S : ObservedSignature.{0}} (base : ExactModel S) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore pivot) (event : S.Assignment -> Bool) :
    QProb.Equiv ((base.withPrivateReadout pivot noise readout).observationalValue event)
      ((noise.product base.observationalDist).probVal
        (fun pair => event (S.privateReadoutAssignment pivot readout pair.2 pair.1))) := by
  let model := base.withPrivateReadout pivot noise readout
  have evaluation (pair : Bool × base.latent.Assignment) :
      model.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2) =
        S.privateReadoutAssignment pivot readout (base.eval pair.2) pair.1 :=
    base.withPrivateReadout_evalUnder pivot noise readout ignored
      (FiniteLatentSCM.noIntervention S) rfl pair.2 pair.1
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => event (model.eval latent))
  have observed := (noise.product base.prior).probVal_congr _ _
    (fun pair => congrArg event (evaluation pair))
  have originals := noise.product_map_right_probVal base.prior base.eval
    (fun pair => event (S.privateReadoutAssignment pivot readout pair.2 pair.1))
  exact QProb.equiv_trans (model.observationalValue_eq event)
    (QProb.equiv_trans pushed (QProb.equiv_trans observed (QProb.equiv_symm originals)))

/-- Applying the same observable private readout to two observationally
equivalent models preserves equality of their entire observed laws.

The old latent spaces may differ: independence comes from each new product
prior, and equality is applied separately to every Boolean-noise slice of
the common observed transformation.  This theorem makes no assumption that
an arbitrary latent-dependent mechanism replacement preserves equivalence. -/
theorem FiniteLatentSCM.withPrivateReadout_observationally_equivalent
    {S : ObservedSignature.{0}} (left right : ExactModel S)
    (observational : ObservationallyEquivalent left right) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (leftIgnored : left.OtherMechanismsIgnore pivot)
    (rightIgnored : right.OtherMechanismsIgnore pivot) :
    ObservationallyEquivalent (left.withPrivateReadout pivot noise readout)
      (right.withPrivateReadout pivot noise readout) := by
  intro event
  exact QProb.equiv_trans
    (left.withPrivateReadout_observationalValue_equiv pivot noise readout leftIgnored event)
    (QProb.equiv_trans
      (noise.product_probVal_equiv_of_slices left.observationalDist right.observationalDist
        (fun pair => event (S.privateReadoutAssignment pivot readout pair.2 pair.1))
        (fun pair => event (S.privateReadoutAssignment pivot readout pair.2 pair.1))
        (fun bit => observational (fun sample =>
          event (S.privateReadoutAssignment pivot readout sample bit))))
      (QProb.equiv_symm
        (right.withPrivateReadout_observationalValue_equiv pivot noise readout rightIgnored event)))

/-! ## Full support without a non-influence premise -/

/-- A private readout preserves strict positivity when each target
assignment has an explicit noise bit restoring its pivot value.  The bit is
given as data, not selected from a proposition.  A positive rectangle in the
actual `noise × old prior` consists of this bit and all old units realizing
the target.  Topological restoration puts the whole rectangle in the new
assignment's preimage, even when other mechanisms read the modified pivot.

The full observed alphabet is retained: `target` is an arbitrary dependent
assignment, not a Boolean encoding or a two-value subset of it.  No
non-influence, sink, or readout-order premise is needed for positivity;
observational equivalence remains a separate, stronger obligation. -/
theorem FiniteLatentSCM.withPrivateReadout_positive
    {S : ObservedSignature.{0}} (base : ExactModel S) (positive : ObservationallyPositive base)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (restoreBit : S.Assignment -> Bool)
    (restore : forall target, readout (fun parent _edge => target parent)
      (target pivot) (restoreBit target) = target pivot) :
    ObservationallyPositive (base.withPrivateReadout pivot noise readout) := by
  intro target
  let model := base.withPrivateReadout pivot noise readout
  let oldEvent := fun old : base.latent.Assignment => FiniteProbRecord.singletonEvent target (base.eval old)
  let rectangle := fun pair : Bool × base.latent.Assignment =>
    FiniteProbRecord.singletonEvent (restoreBit target) pair.1 &&
      oldEvent pair.2
  let event := fun pair : Bool × base.latent.Assignment =>
    FiniteProbRecord.singletonEvent target (model.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2))
  have oldPositive : 0 < FiniteProbRecord.eventMass base.prior.atoms oldEvent := by
    simpa only [FiniteLatentSCM.observationalDist, FiniteProbRecord.map,
      FiniteProbRecord.probVal, FiniteProbRecord.eventMass_map_labels, oldEvent] using positive target
  have rectanglePositive :
      0 < FiniteProbRecord.eventMass (noise.product base.prior).atoms rectangle := by
    rw [FiniteProbRecord.product, FiniteProbRecord.eventMass_weightedCartesian]
    exact Nat.mul_pos (noisePositive (restoreBit target)) oldPositive
  have included : forall pair, rectangle pair = true -> event pair = true := by
    intro pair selected
    have parts := Bool.and_eq_true_iff.mp selected
    have sameBit : pair.1 = restoreBit target := of_decide_eq_true parts.1
    have oldTarget : base.eval pair.2 = target := of_decide_eq_true parts.2
    have restores : readout (fun parent _edge => base.eval pair.2 parent)
        (base.eval pair.2 pivot) pair.1 = base.eval pair.2 pivot := by
      rw [oldTarget, sameBit]
      exact restore target
    have restored := base.withPrivateReadout_evalUnder_eq_of_restores pivot noise readout
      (FiniteLatentSCM.noIntervention S) pair.2 pair.1 restores
    change decide (model.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2) = target) = true
    exact decide_eq_true (restored.trans oldTarget)
  have bound := FiniteProbRecord.eventMass_mono (noise.product base.prior).atoms rectangle event included
  have pushedPositive := Nat.lt_of_lt_of_le rectanglePositive bound
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => FiniteProbRecord.singletonEvent target (model.eval latent))
  exact (QProb.equiv_num_pos_iff (QProb.equiv_trans
    (model.observationalValue_eq (FiniteProbRecord.singletonEvent target)) pushed)).mpr pushedPositive

end Causality
end Thesis
