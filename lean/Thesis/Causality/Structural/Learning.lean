import Thesis.Causality.Learning

namespace Thesis
namespace Causality

open Probability

/-! Endogenous-variable and exogenous-root creation with provenance-guided destruction. -/

/-! ## Endogenous-variable creation and provenance-guided destruction -/

/--
Data for a fresh terminal endogenous variable.  Its position at the end of the
topological order lets it depend on any declared old parent, and its latent
input mask may select any number of the source record's exogenous roots.
-/
structure EndogenousVariableSpec {S : ObservedSignature}
    (R : CausalEpistemicRecord S) where
  Value : Type
  valueEnumeration : List Value
  value_complete : forall value, value ∈ valueEnumeration
  value_nodup : valueEnumeration.Nodup
  defaultValue : Value
  valueDecidableEq : DecidableEq Value
  parents : NodeSet S
  latentInputs : Fin R.model.latent.count -> Bool
  mechanism :
    ((parent : Fin S.count) -> parents parent = true -> S.Value parent) ->
    ((source : Fin R.model.latent.count) -> latentInputs source = true ->
      R.model.latent.Value source) -> Value

namespace EndogenousVariableSpec

instance {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R) : DecidableEq spec.Value :=
  spec.valueDecidableEq

/-- The observed-signature component of endogenous learning. -/
def terminalSpec {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R) : TerminalVariableSpec S where
  Value := spec.Value
  valueEnumeration := spec.valueEnumeration
  value_complete := spec.value_complete
  value_nodup := spec.value_nodup
  defaultValue := spec.defaultValue
  valueDecidableEq := spec.valueDecidableEq
  parents := spec.parents
  mechanism := fun _parents => spec.defaultValue

abbrev extendSignature {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (spec : EndogenousVariableSpec R) :
    ObservedSignature :=
  spec.terminalSpec.extendSignature

def oldNode {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R) (node : Fin S.count) :
    Fin spec.extendSignature.count :=
  node.castSucc

def newNode {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R) :
    Fin spec.extendSignature.count :=
  Fin.last S.count

/-- Reuse all old roots, connecting the selected ones to the fresh node. -/
def extendLatent {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R) :
    LatentExtension spec.extendSignature where
  count := R.model.latent.count
  Value := R.model.latent.Value
  valueEnumeration := R.model.latent.valueEnumeration
  value_complete := R.model.latent.value_complete
  valueDecidableEq := R.model.latent.valueDecidableEq
  incident := fun source child =>
    TerminalVariableSpec.terminalCases (motive := fun _ => Bool)
      (spec.latentInputs source)
      (fun oldChild => R.model.latent.incident source oldChild) child

@[simp] theorem extendLatent_incident_new
    {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R)
    (source : Fin R.model.latent.count) :
    spec.extendLatent.incident source spec.newNode =
      spec.latentInputs source := by
  simp [extendLatent, newNode]

@[simp] theorem extendLatent_incident_old
    {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R)
    (source : Fin R.model.latent.count) (child : Fin S.count) :
    spec.extendLatent.incident source (spec.oldNode child) =
      R.model.latent.incident source child := by
  simp [extendLatent, oldNode]

def learnedParentValues {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (spec : EndogenousVariableSpec R)
    (parents : spec.extendSignature.ParentValues spec.newNode) :
    (parent : Fin S.count) -> spec.parents parent = true -> S.Value parent :=
  spec.terminalSpec.learnedParentValues parents

def learnedLatentInputs {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (spec : EndogenousVariableSpec R)
    (latents : spec.extendLatent.Inputs spec.newNode) :
    (source : Fin R.model.latent.count) -> spec.latentInputs source = true ->
      R.model.latent.Value source :=
  fun source incident => latents source (by simpa using incident)

def oldParentValues {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (spec : EndogenousVariableSpec R)
    {child : Fin S.count}
    (parents : spec.extendSignature.ParentValues (spec.oldNode child)) :
    S.ParentValues child :=
  spec.terminalSpec.oldParentValues parents

def oldLatentInputs {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (spec : EndogenousVariableSpec R)
    {child : Fin S.count}
    (latents : spec.extendLatent.Inputs (spec.oldNode child)) :
    R.model.latent.Inputs child :=
  fun source incident => latents source (by simpa using incident)

/-- Old equations are retained; the fresh equation receives its declared inputs. -/
def extendMechanism {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (spec : EndogenousVariableSpec R) :
    (child : Fin spec.extendSignature.count) ->
      spec.extendSignature.ParentValues child ->
      spec.extendLatent.Inputs child -> spec.extendSignature.Value child :=
  fun child => TerminalVariableSpec.terminalCases
    (motive := fun child =>
      spec.extendSignature.ParentValues child ->
      spec.extendLatent.Inputs child -> spec.extendSignature.Value child)
    (fun parents latents =>
      cast spec.terminalSpec.value_newNode.symm
        (spec.mechanism (spec.learnedParentValues parents)
          (spec.learnedLatentInputs latents)))
    (fun oldChild parents latents =>
      cast (spec.terminalSpec.value_oldNode oldChild).symm
        (R.model.mechanism oldChild (spec.oldParentValues parents)
          (spec.oldLatentInputs latents)))
    child

def extendModel {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R) :
    ExactModel spec.extendSignature where
  latent := spec.extendLatent
  factor := R.model.factor
  prior := R.model.prior
  product_law := R.model.product_law
  mechanism := spec.extendMechanism

def learnRecord {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (spec : EndogenousVariableSpec R) :
    CausalEpistemicRecord spec.extendSignature where
  model := spec.extendModel
  belief := R.belief
  intervention := spec.terminalSpec.liftIntervention R.intervention

end EndogenousVariableSpec

/-! ## Exogenous-root creation and provenance-guided destruction -/

structure ExogenousVariableSpec where
  Value : Type
  valueEnumeration : List Value
  value_complete : forall value, value ∈ valueEnumeration
  valueDecidableEq : DecidableEq Value
  factor : FiniteProbRecord Value

namespace ExogenousVariableSpec

instance (spec : ExogenousVariableSpec) : DecidableEq spec.Value :=
  spec.valueDecidableEq

structure FiniteLatentData where
  Value : Type
  enumeration : List Value
  complete : forall value, value ∈ enumeration
  valueDecidableEq : DecidableEq Value
  factor : FiniteProbRecord Value

def extendedData (spec : ExogenousVariableSpec) (M : ExactModel S) :
    Fin (M.latent.count + 1) -> FiniteLatentData :=
  TerminalVariableSpec.terminalCases
    { Value := spec.Value
      enumeration := spec.valueEnumeration
      complete := spec.value_complete
      valueDecidableEq := spec.valueDecidableEq
      factor := spec.factor }
    (fun source =>
      { Value := M.latent.Value source
        enumeration := M.latent.valueEnumeration source
        complete := M.latent.value_complete source
        valueDecidableEq := M.latent.valueDecidableEq source
        factor := M.factor source })

def extendedValue (spec : ExogenousVariableSpec) (M : ExactModel S) :
    Fin (M.latent.count + 1) -> Type :=
  fun source => (spec.extendedData M source).Value

def extendedEnumeration (spec : ExogenousVariableSpec) (M : ExactModel S) :
    (source : Fin (M.latent.count + 1)) ->
      List (spec.extendedValue M source) :=
  fun source => (spec.extendedData M source).enumeration

def extendedDecidableEq (spec : ExogenousVariableSpec) (M : ExactModel S) :
    (source : Fin (M.latent.count + 1)) ->
      DecidableEq (spec.extendedValue M source) :=
  fun source => (spec.extendedData M source).valueDecidableEq

def extendedFactor (spec : ExogenousVariableSpec) (M : ExactModel S) :
    (source : Fin (M.latent.count + 1)) ->
      FiniteProbRecord (spec.extendedValue M source) :=
  fun source => (spec.extendedData M source).factor

@[simp] theorem extendedValue_new (spec : ExogenousVariableSpec)
    (M : ExactModel S) :
    spec.extendedValue M (Fin.last M.latent.count) = spec.Value := by
  simp [extendedValue, extendedData]

@[simp] theorem extendedValue_old (spec : ExogenousVariableSpec)
    (M : ExactModel S) (source : Fin M.latent.count) :
    spec.extendedValue M source.castSucc = M.latent.Value source := by
  simp [extendedValue, extendedData]

/-- A fresh exogenous root is initially unrelated to every endogenous node. -/
def extendLatent (spec : ExogenousVariableSpec) (M : ExactModel S) :
    LatentExtension S where
  count := M.latent.count + 1
  Value := spec.extendedValue M
  valueEnumeration := spec.extendedEnumeration M
  value_complete := fun source => (spec.extendedData M source).complete
  valueDecidableEq := spec.extendedDecidableEq M
  incident := fun source child =>
    TerminalVariableSpec.terminalCases (motive := fun _ => Bool) false
      (fun old => M.latent.incident old child) source

def newSource (spec : ExogenousVariableSpec) (M : ExactModel S) :
    Fin (spec.extendLatent M).count :=
  Fin.last M.latent.count

def oldSource (spec : ExogenousVariableSpec) (M : ExactModel S)
    (source : Fin M.latent.count) : Fin (spec.extendLatent M).count :=
  source.castSucc

@[simp] theorem extendLatent_value_new (spec : ExogenousVariableSpec)
    (M : ExactModel S) :
    (spec.extendLatent M).Value (spec.newSource M) = spec.Value := by
  simp [extendLatent, newSource]

@[simp] theorem extendLatent_value_old (spec : ExogenousVariableSpec)
    (M : ExactModel S) (source : Fin M.latent.count) :
    (spec.extendLatent M).Value (spec.oldSource M source) =
      M.latent.Value source := by
  simp [extendLatent, oldSource]

@[simp] theorem extendLatent_incident_new (spec : ExogenousVariableSpec)
    (M : ExactModel S) (child : Fin S.count) :
    (spec.extendLatent M).incident (spec.newSource M) child = false := by
  simp [extendLatent, newSource]

@[simp] theorem extendLatent_incident_old (spec : ExogenousVariableSpec)
    (M : ExactModel S) (source : Fin M.latent.count)
    (child : Fin S.count) :
    (spec.extendLatent M).incident (spec.oldSource M source) child =
      M.latent.incident source child := by
  simp [extendLatent, oldSource]

def extendAssignment (spec : ExogenousVariableSpec) (M : ExactModel S)
    (old : M.latent.Assignment) (fresh : spec.Value) :
    (spec.extendLatent M).Assignment :=
  fun source => TerminalVariableSpec.terminalCases
    (motive := fun source => (spec.extendLatent M).Value source)
    (cast (spec.extendLatent_value_new M).symm fresh)
    (fun oldSource =>
      cast (spec.extendLatent_value_old M oldSource).symm (old oldSource))
    source

@[simp] theorem extendAssignment_new (spec : ExogenousVariableSpec)
    (M : ExactModel S) (old : M.latent.Assignment) (fresh : spec.Value) :
    cast (spec.extendLatent_value_new M)
      (spec.extendAssignment M old fresh (spec.newSource M)) = fresh := by
  simp only [extendAssignment, newSource,
    TerminalVariableSpec.terminalCases_last]
  exact TerminalVariableSpec.cast_symm_cast
    (spec.extendLatent_value_new M) fresh

@[simp] theorem extendAssignment_old (spec : ExogenousVariableSpec)
    (M : ExactModel S) (old : M.latent.Assignment) (fresh : spec.Value)
    (source : Fin M.latent.count) :
    cast (spec.extendLatent_value_old M source)
      (spec.extendAssignment M old fresh (spec.oldSource M source)) =
        old source := by
  simp only [extendAssignment, oldSource,
    TerminalVariableSpec.terminalCases_castSucc]
  exact TerminalVariableSpec.cast_symm_cast
    (spec.extendLatent_value_old M source) (old source)

def extendBelief (spec : ExogenousVariableSpec)
    (R : CausalEpistemicRecord S) :
    FiniteProbRecord (spec.extendLatent R.model).Assignment := by
  exact (R.belief.product spec.factor).map
    (fun pair => spec.extendAssignment R.model pair.1 pair.2)

def extendModel (spec : ExogenousVariableSpec) (M : ExactModel S) :
    ExactModel S where
  latent := spec.extendLatent M
  factor := fun source => spec.extendedFactor M source
  prior := by
    exact FiniteProduct.record (M.latent.count + 1)
      (spec.extendedValue M) (spec.extendedFactor M)
  product_law := by
    exact FiniteProduct.record_rectangular_probVal
      (M.latent.count + 1) (spec.extendedValue M) (spec.extendedFactor M)
  mechanism := fun child parents latents =>
    M.mechanism child parents (fun source incident =>
      cast (spec.extendLatent_value_old M source)
        (latents (spec.oldSource M source) (by
          simpa using incident)))

def learnRecord (spec : ExogenousVariableSpec)
    (R : CausalEpistemicRecord S) : CausalEpistemicRecord S where
  model := spec.extendModel R.model
  belief := spec.extendBelief R
  intervention := R.intervention

end ExogenousVariableSpec

end Causality
end Thesis
