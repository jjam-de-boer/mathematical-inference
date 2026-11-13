import Thesis.Causality.PrivateNoise

namespace Thesis
namespace Causality

open Probability

/-!
# A fresh Boolean source on an existing bidirected pair

An active back-door path can start at a shared latent parent rather than an
observed incoming arrow.  A private-mask readout cannot realize that first
edge: both observed mechanisms must receive the same genuine independent
source.  This module appends such a source with exactly the two displayed
incident children.

Value types, enumerations, assignment encoding, factor records, the literal
product prior, and its rectangular product law are reused from
`PrivateBooleanNoise`.  None of those constructions depends on which observed
nodes receive the appended coordinate.  Only incidence and typed input access
change here.  The old source incidences and old factors remain unchanged.

The extension remains canonical semi-Markovian because its fresh root has at
most two distinct children.  Its projected graph is preserved only when the
displayed bidirected edge already belongs to the original graph.  This is an
explicit compatibility hypothesis, not permission to add a new confounding
edge while constructing a countermodel.

The readout layer replaces both incident mechanisms by a common transformation
of their own old output and the shared bit.  Its semantic theorems keep the
actual product prior and arbitrary interventions visible.  Graph preservation
alone does not imply observational equality or positivity; particular readout
constructions must still establish those properties.
-/

namespace SharedBooleanNoise

variable {S : ObservedSignature.{0}}

/-- The new root feeds the displayed pair, including the harmless private
boundary when the two coordinates coincide. -/
def membership (first second child : Fin S.count) : Bool :=
  decide (child = first) || decide (child = second)

theorem membership_eq_true_iff (first second child : Fin S.count) :
    membership first second child = true ↔ child = first ∨ child = second := by
  simp only [membership, Bool.or_eq_true_iff, decide_eq_true_eq]

def incident (latent : LatentExtension S) (first second : Fin S.count)
    (root : Fin (latent.count + 1)) (child : Fin S.count) : Bool :=
  FiniteProduct.extend (Value := fun _ => Bool) (membership first second child)
    (fun old => latent.incident old child) root

@[simp] theorem incident_last (latent : LatentExtension S) (first second child : Fin S.count) :
    incident latent first second (Fin.last latent.count) child = membership first second child :=
  FiniteProduct.extend_last (Value := fun _ => Bool) _ _

@[simp] theorem incident_castSucc (latent : LatentExtension S) (first second child : Fin S.count)
    (root : Fin latent.count) : incident latent first second root.castSucc child = latent.incident root child :=
  FiniteProduct.extend_castSucc (Value := fun _ => Bool) _ _ root

/-- The same appended typed coordinate as the private construction, with
pair incidence instead of singleton incidence. -/
def extension (latent : LatentExtension S) (first second : Fin S.count) : LatentExtension S :=
  { PrivateBooleanNoise.extension latent first with incident := incident latent first second }

/-- Recover every old incident input at any observed node. -/
def oldInputs (latent : LatentExtension S) (first second child : Fin S.count)
    (inputs : (extension latent first second).Inputs child) : latent.Inputs child :=
  fun root selected => cast (PrivateBooleanNoise.value_castSucc latent root)
    (inputs root.castSucc (by simpa only [extension, incident_castSucc] using selected))

/-- A child may read the fresh bit only through its certified incidence. -/
def bit (latent : LatentExtension S) (first second child : Fin S.count)
    (selected : membership first second child = true)
    (inputs : (extension latent first second).Inputs child) : Bool :=
  cast (PrivateBooleanNoise.value_last latent)
    (inputs (Fin.last latent.count) (by simpa only [extension, incident_last] using selected))

theorem oldInputs_assignment (latent : LatentExtension S) (first second child : Fin S.count)
    (value : Bool) (old : latent.Assignment) :
    oldInputs latent first second child
      (fun root _selected => PrivateBooleanNoise.assignment latent value old root) =
      (fun root _selected => old root) := by
  funext root selected
  exact PrivateBooleanNoise.assignment_castSucc latent value old root

theorem bit_assignment (latent : LatentExtension S) (first second child : Fin S.count)
    (selected : membership first second child = true) (value : Bool) (old : latent.Assignment) :
    bit latent first second child selected
      (fun root _selected => PrivateBooleanNoise.assignment latent value old root) = value :=
  PrivateBooleanNoise.assignment_last latent value old

/-! ## The graph and canonical model class are preserved -/

theorem canonical (latent : LatentExtension S) (first second : Fin S.count)
    (old : latent.CanonicalSemiMarkovian) : (extension latent first second).CanonicalSemiMarkovian := by
  intro root
  refine Fin.lastCases
    (motive := fun root => forall left right third,
      (extension latent first second).incident root left = true ->
      (extension latent first second).incident root right = true ->
      (extension latent first second).incident root third = true ->
      left = right ∨ left = third ∨ right = third) ?_ (fun earlier => ?_) root
  · intro left right third leftSelected rightSelected thirdSelected
    have leftPair := (membership_eq_true_iff first second left).mp
      (by simpa only [extension, incident_last] using leftSelected)
    have rightPair := (membership_eq_true_iff first second right).mp
      (by simpa only [extension, incident_last] using rightSelected)
    have thirdPair := (membership_eq_true_iff first second third).mp
      (by simpa only [extension, incident_last] using thirdSelected)
    cases leftPair with
    | inl leftFirst =>
        cases rightPair with
        | inl rightFirst => exact .inl (leftFirst.trans rightFirst.symm)
        | inr rightSecond =>
            cases thirdPair with
            | inl thirdFirst => exact .inr (.inl (leftFirst.trans thirdFirst.symm))
            | inr thirdSecond => exact .inr (.inr (rightSecond.trans thirdSecond.symm))
    | inr leftSecond =>
        cases rightPair with
        | inr rightSecond => exact .inl (leftSecond.trans rightSecond.symm)
        | inl rightFirst =>
            cases thirdPair with
            | inl thirdFirst => exact .inr (.inr (rightFirst.trans thirdFirst.symm))
            | inr thirdSecond => exact .inr (.inl (leftSecond.trans thirdSecond.symm))
  · intro left right third leftSelected rightSelected thirdSelected
    exact old earlier left right third
      (by simpa only [extension, incident_castSucc] using leftSelected)
      (by simpa only [extension, incident_castSucc] using rightSelected)
      (by simpa only [extension, incident_castSucc] using thirdSelected)

/-- Coincident displayed coordinates recover the original private-source
extension literally.  No reflexive bidirected edge is required or added. -/
theorem extension_same (latent : LatentExtension S) (pivot : Fin S.count) :
    extension latent pivot pivot = PrivateBooleanNoise.extension latent pivot := by
  have sameIncident : incident latent pivot pivot = PrivateBooleanNoise.incident latent pivot := by
    funext root child
    simp only [incident, membership, Bool.or_self, PrivateBooleanNoise.incident]
  unfold extension
  rw [sameIncident]
  rfl

/-- Sharing an independent new root over an already confounded pair changes
neither that edge nor any other projected edge.  The proof inspects the new
source explicitly; it does not assume that arbitrary latent augmentation is
graph-conservative. -/
theorem projectedBidirected_eq (latent : LatentExtension S) (first second : Fin S.count)
    (existing : latent.projectedBidirected first second = true) (left right : Fin S.count) :
    (extension latent first second).projectedBidirected left right = latent.projectedBidirected left right := by
  have anyEqual : finAny (latent.count + 1)
      (fun root => incident latent first second root left && incident latent first second root right) =
      (finAny latent.count (fun root => latent.incident root left && latent.incident root right) ||
        (membership first second left && membership first second right)) := by
    simp only [finAny, incident_last, incident_castSucc]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro augmented
    have parts : (!Nat.beq left.val right.val) = true ∧
        (finAny latent.count (fun root => latent.incident root left && latent.incident root right) ||
          (membership first second left && membership first second right)) = true := by
      change (!Nat.beq left.val right.val && finAny (latent.count + 1)
        (fun root => incident latent first second root left && incident latent first second root right)) = true at augmented
      rw [anyEqual] at augmented
      exact Bool.and_eq_true_iff.mp augmented
    cases Bool.or_eq_true_iff.mp parts.2 with
    | inl old => exact Bool.and_eq_true_iff.mpr ⟨parts.1, old⟩
    | inr fresh =>
        have selected := Bool.and_eq_true_iff.mp fresh
        have leftPair := (membership_eq_true_iff first second left).mp selected.1
        have rightPair := (membership_eq_true_iff first second right).mp selected.2
        cases leftPair with
        | inl leftFirst =>
            cases rightPair with
            | inl rightFirst =>
                have same := leftFirst.trans rightFirst.symm
                simp only [same, natBeq_refl, Bool.not_true, Bool.false_eq_true] at parts
                exact False.elim parts.1
            | inr rightSecond => simpa only [leftFirst, rightSecond] using existing
        | inr leftSecond =>
            cases rightPair with
            | inl rightFirst =>
                simpa only [leftSecond, rightFirst] using latent.projectedBidirected_symmetric existing
            | inr rightSecond =>
                have same := leftSecond.trans rightSecond.symm
                simp only [same, natBeq_refl, Bool.not_true, Bool.false_eq_true] at parts
                exact False.elim parts.1
  · intro old
    have parts := Bool.and_eq_true_iff.mp old
    have selected : (finAny latent.count (fun root => latent.incident root left && latent.incident root right) ||
        (membership first second left && membership first second right)) = true :=
      Bool.or_eq_true_iff.mpr (.inl parts.2)
    change (!Nat.beq left.val right.val && finAny (latent.count + 1)
      (fun root => incident latent first second root left && incident latent first second root right)) = true
    rw [anyEqual]
    exact Bool.and_eq_true_iff.mpr ⟨parts.1, selected⟩

end SharedBooleanNoise

/-- Install an independent shared bit and update exactly its two incident
observed readouts.  Each readout sees only its own old output and the new bit;
it cannot inspect an undeclared observed parent or an unrelated latent input. -/
def FiniteLatentSCM.withSharedReadout
    {S : ObservedSignature.{0}} (base : ExactModel S) (first second : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node) : ExactModel S where
  latent := SharedBooleanNoise.extension base.latent first second
  factor := PrivateBooleanNoise.factor base noise
  prior := PrivateBooleanNoise.prior base noise
  product_law := PrivateBooleanNoise.product_law base noise
  mechanism := fun child parents inputs =>
    let old := base.mechanism child parents (SharedBooleanNoise.oldInputs base.latent first second child inputs)
    if selected : SharedBooleanNoise.membership first second child = true then
      readout child old (SharedBooleanNoise.bit base.latent first second child selected inputs)
    else old

/-- The same projected graph and canonical class are retained because the
new shared source uses an edge already present in that graph. -/
theorem FiniteLatentSCM.withSharedReadout_compatible
    {S : ObservedSignature.{0}} {graph : ObservedGraph S}
    (base : ExactModel S) (compatible : Compatible base graph) (first second : Fin S.count)
    (edge : graph.bidirected first second = true) (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node) :
    Compatible (base.withSharedReadout first second noise readout) graph :=
  ⟨SharedBooleanNoise.canonical base.latent first second compatible.1,
    fun left right => (SharedBooleanNoise.projectedBidirected_eq base.latent first second
      ((compatible.2 first second).trans edge) left right).trans (compatible.2 left right)⟩

/-- The coincident-coordinate boundary is private and preserves the graph
without asking for an impossible self-confounding edge. -/
theorem FiniteLatentSCM.withSharedReadout_same_compatible
    {S : ObservedSignature.{0}} {graph : ObservedGraph S}
    (base : ExactModel S) (compatible : Compatible base graph) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node) :
    Compatible (base.withSharedReadout pivot pivot noise readout) graph :=
  ⟨SharedBooleanNoise.canonical base.latent pivot pivot compatible.1,
    fun left right => (by
      change (SharedBooleanNoise.extension base.latent pivot pivot).projectedBidirected left right = graph.bidirected left right
      rw [SharedBooleanNoise.extension_same]
      exact (PrivateBooleanNoise.projectedBidirected_eq base.latent pivot left right).trans (compatible.2 left right))⟩

end Causality
end Thesis
