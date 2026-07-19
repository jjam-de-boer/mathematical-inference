import Thesis.CausalTransport.Correspondence

namespace Thesis
namespace Causality

open Probability

/-!
An independently declared finite classical source presentation.

Observed value spaces are cardinalities and their values are table indices.
The interpretation turns those indices into an intrinsic dependent observed
signature.  Source probabilities are finite sums over exogenous assignments;
the target semantics forms finite pushforward distributions.  The agreement
theorems below connect those independently stated semantics pointwise.
-/

structure FiniteTableSignature where
  count : Nat
  arity : Fin count -> Nat
  defaultCode : (i : Fin count) -> Fin (arity i)
  codeEnumeration : (i : Fin count) -> List (Fin (arity i))
  code_complete : forall i value, value ∈ codeEnumeration i
  code_nodup : forall i, (codeEnumeration i).Nodup
  directed : Fin count -> Fin count -> Bool
  directed_earlier : forall {parent child},
    directed parent child = true -> parent.val < child.val

namespace FiniteTableSignature

def toObserved (T : FiniteTableSignature) : ObservedSignature where
  count := T.count
  Value := fun i => Fin (T.arity i)
  valueEnumeration := T.codeEnumeration
  value_complete := T.code_complete
  value_nodup := T.code_nodup
  defaultValue := T.defaultCode
  valueDecidableEq := fun _ => inferInstance
  directed := T.directed
  directed_earlier := T.directed_earlier

abbrev Value (T : FiniteTableSignature) (i : Fin T.count) := Fin (T.arity i)

abbrev Assignment (T : FiniteTableSignature) :=
  (i : Fin T.count) -> T.Value i

def ParentValues (T : FiniteTableSignature) (child : Fin T.count) :=
  (parent : Fin T.count) ->
    T.directed parent child = true -> T.Value parent

end FiniteTableSignature

/--
Finite latent table data declared independently of the intrinsic target
LatentExtension. Carriers may differ from one latent coordinate to another,
but each is supplied with explicit finite enumeration and decidable equality.
-/
structure FiniteTableLatent (T : FiniteTableSignature) where
  count : Nat
  Value : Fin count -> Type
  valueEnumeration : (l : Fin count) -> List (Value l)
  value_complete : forall l value, value ∈ valueEnumeration l
  valueDecidableEq : (l : Fin count) -> DecidableEq (Value l)
  incident : Fin count -> Fin T.count -> Bool

namespace FiniteTableLatent

instance (L : FiniteTableLatent T) (l : Fin L.count) :
    DecidableEq (L.Value l) :=
  L.valueDecidableEq l

abbrev Assignment (L : FiniteTableLatent T) :=
  (l : Fin L.count) -> L.Value l

def Inputs (L : FiniteTableLatent T) (child : Fin T.count) :=
  (l : Fin L.count) -> L.incident l child = true -> L.Value l

def rectangularEvent (L : FiniteTableLatent T)
    (events : (l : Fin L.count) -> L.Value l -> Bool)
    (u : L.Assignment) : Bool :=
  FiniteProduct.rectangularEvent L.count L.Value events u

def projectedBidirected (L : FiniteTableLatent T)
    (i j : Fin T.count) : Bool :=
  !(Nat.beq i.val j.val) &&
    finAny L.count (fun latent => L.incident latent i && L.incident latent j)

def CanonicalSemiMarkovian (L : FiniteTableLatent T) : Prop :=
  forall l i j k,
    L.incident l i = true ->
    L.incident l j = true ->
    L.incident l k = true ->
    i = j \/ i = k \/ j = k

def interpret (L : FiniteTableLatent T) : LatentExtension T.toObserved where
  count := L.count
  Value := L.Value
  valueEnumeration := L.valueEnumeration
  value_complete := L.value_complete
  valueDecidableEq := L.valueDecidableEq
  incident := L.incident

def ofIntrinsic (L : LatentExtension T.toObserved) : FiniteTableLatent T where
  count := L.count
  Value := L.Value
  valueEnumeration := L.valueEnumeration
  value_complete := L.value_complete
  valueDecidableEq := L.valueDecidableEq
  incident := L.incident

theorem interpret_projectedBidirected (L : FiniteTableLatent T)
    (i j : Fin T.count) :
    L.interpret.projectedBidirected i j = L.projectedBidirected i j :=
  rfl

theorem interpret_canonical_iff (L : FiniteTableLatent T) :
    L.interpret.CanonicalSemiMarkovian <-> L.CanonicalSemiMarkovian :=
  Iff.rfl

end FiniteTableLatent

/-- A graph table over the source node codes. -/
structure FiniteTableGraph (T : FiniteTableSignature) where
  bidirected : Fin T.count -> Fin T.count -> Bool
  bidirected_symmetric : forall {i j},
    bidirected i j = true -> bidirected j i = true
  bidirected_irreflexive : forall i, bidirected i i = false

def FiniteTableGraph.interpret (G : FiniteTableGraph T) :
    ObservedGraph T.toObserved where
  bidirected := G.bidirected
  bidirected_symmetric := G.bidirected_symmetric
  bidirected_irreflexive := G.bidirected_irreflexive

/--
A classical finite table model.  Every structural function has a finite coded
domain because all observed values are `Fin` codes and every latent carrier is
explicitly enumerated.
-/
structure FiniteTableSCM (T : FiniteTableSignature) where
  latent : FiniteTableLatent T
  factor : (l : Fin latent.count) -> FiniteProbRecord (latent.Value l)
  prior : FiniteProbRecord latent.Assignment
  product_law :
    forall events : (l : Fin latent.count) -> latent.Value l -> Bool,
      QProb.Equiv
        (prior.probVal (latent.rectangularEvent events))
        (FiniteProduct.qProduct latent.count
          (fun l => (factor l).probVal (events l)))
  table :
    (child : Fin T.count) ->
      T.ParentValues child -> latent.Inputs child -> T.Value child

namespace FiniteTableSCM

def interpret (M : FiniteTableSCM T) : ExactModel T.toObserved where
  latent := M.latent.interpret
  factor := M.factor
  prior := M.prior
  product_law := M.product_law
  mechanism := M.table

def ofExact (M : ExactModel T.toObserved) : FiniteTableSCM T where
  latent := FiniteTableLatent.ofIntrinsic M.latent
  factor := M.factor
  prior := M.prior
  product_law := M.product_law
  table := M.mechanism

def equationUnder (M : FiniteTableSCM T)
    (target : (i : Fin T.count) -> Option (T.toObserved.Value i))
    (child : Fin T.count) (parents : T.toObserved.ParentValues child)
    (latents : M.latent.Inputs child) : T.toObserved.Value child :=
  match target child with
  | some value => value
  | none => M.table child parents latents

/-- Recursive evaluation stated independently on the finite source tables. -/
def evalNodeUnder (M : FiniteTableSCM T)
    (target : (i : Fin T.count) -> Option (T.toObserved.Value i))
    (u : M.latent.Assignment) (child : Fin T.count) :
    T.toObserved.Value child :=
  M.equationUnder target child
    (fun parent _edge => M.evalNodeUnder target u parent)
    (fun latent _ => u latent)
termination_by child.val
decreasing_by
  exact T.directed_earlier _edge

def evalUnder (M : FiniteTableSCM T)
    (target : (i : Fin T.count) -> Option (T.toObserved.Value i))
    (u : M.latent.Assignment) : T.Assignment :=
  fun child => M.evalNodeUnder target u child

def eval (M : FiniteTableSCM T) (u : M.latent.Assignment) : T.Assignment :=
  M.evalUnder (FiniteLatentSCM.noIntervention T.toObserved) u

/-- Source semantics: sum the prior directly over the recursive table result. -/
def observationalValue (M : FiniteTableSCM T)
    (event : T.Assignment -> Bool) : QProb :=
  M.prior.probVal (fun u => event (M.eval u))

def interventionalValue (M : FiniteTableSCM T)
    (target : (i : Fin T.count) -> Option (T.toObserved.Value i))
    (event : T.Assignment -> Bool) : QProb :=
  M.prior.probVal (fun u => event (M.evalUnder target u))

theorem evalNodeUnder_preserved (M : FiniteTableSCM T)
    (target : (i : Fin T.count) -> Option (T.toObserved.Value i))
    (u : M.latent.Assignment) (child : Fin T.count) :
    M.evalNodeUnder target u child =
      M.interpret.evalNodeUnder target u child := by
  rw [evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold equationUnder FiniteLatentSCM.equationUnder interpret
  cases selected : target child with
  | some value => rfl
  | none =>
    apply congrArg (fun parents => M.table child parents (fun latent _ => u latent))
    funext parent edge
    exact M.evalNodeUnder_preserved target u parent
termination_by child.val
decreasing_by
  exact T.directed_earlier edge

theorem evalUnder_preserved (M : FiniteTableSCM T)
    (target : (i : Fin T.count) -> Option (T.toObserved.Value i))
    (u : M.latent.Assignment) (child : Fin T.count) :
    M.evalUnder target u child = M.interpret.evalUnder target u child :=
  M.evalNodeUnder_preserved target u child

theorem eval_preserved (M : FiniteTableSCM T)
    (u : M.latent.Assignment) (child : Fin T.count) :
    M.eval u child = M.interpret.eval u child :=
  M.evalNodeUnder_preserved _ u child

theorem observational_preserved (M : FiniteTableSCM T)
    (event : T.Assignment -> Bool) :
    QProb.Equiv (M.observationalValue event)
      (M.interpret.observationalValue event) :=
  QProb.equiv_trans
    (FiniteProbRecord.probVal_congr M.prior _ _ (fun u => by
      apply congrArg event
      funext child
      exact M.eval_preserved u child))
    (QProb.equiv_symm (M.interpret.observationalValue_eq event))

theorem interventional_preserved (M : FiniteTableSCM T)
    (target : (i : Fin T.count) -> Option (T.toObserved.Value i))
    (event : T.Assignment -> Bool) :
    QProb.Equiv (M.interventionalValue target event)
      (M.interpret.interventionalValue target event) :=
  QProb.equiv_trans
    (FiniteProbRecord.probVal_congr M.prior _ _ (fun u => by
      apply congrArg event
      funext child
      exact M.evalUnder_preserved target u child))
    (QProb.equiv_symm (M.interpret.interventionalValue_eq target event))

/-- Source-native kernel semantics, computed directly from finite source sums. -/
def kernelDenote (M : FiniteTableSCM T) (kernel : Kernel T.toObserved)
    (reference : T.Assignment) : ProbabilityResult.Result :=
  let denominator :=
    if kernel.hasAction then
      M.interventionalValue (kernel.intervention reference)
        (kernel.conditionEvent reference)
    else
      M.observationalValue (kernel.conditionEvent reference)
  let numerator :=
    if kernel.hasAction then
      M.interventionalValue (kernel.intervention reference)
        (kernel.numeratorEvent reference)
    else
      M.observationalValue (kernel.numeratorEvent reference)
  ProbabilityResult.divide (some numerator) (some denominator)

noncomputable def kernelDenote_preserved (M : FiniteTableSCM T)
    (kernel : Kernel T.toObserved) (reference : T.Assignment) :
    ProbabilityResult.Equivalent
      (M.kernelDenote kernel reference)
      (kernel.denote M.interpret reference) := by
  cases selected : kernel.hasAction with
  | false =>
      simp only [kernelDenote, Kernel.denote, Kernel.distribution, selected,
        Bool.false_eq_true, if_false]
      exact ProbabilityResult.divide_congr
        (.value (M.observational_preserved
          (kernel.numeratorEvent reference)))
        (.value (M.observational_preserved
          (kernel.conditionEvent reference)))
  | true =>
      simp only [kernelDenote, Kernel.denote, Kernel.distribution, selected,
        if_true]
      exact ProbabilityResult.divide_congr
        (.value (M.interventional_preserved (kernel.intervention reference)
          (kernel.numeratorEvent reference)))
        (.value (M.interventional_preserved (kernel.intervention reference)
          (kernel.conditionEvent reference)))

def KernelSupportedAt (M : FiniteTableSCM T)
    (kernel : Kernel T.toObserved) (assignment : T.Assignment) : Type :=
  Sigma fun value =>
    ProbabilityResult.Equivalent (M.kernelDenote kernel assignment) (some value)

noncomputable def kernelSupportedAt_to_target (M : FiniteTableSCM T)
    (kernel : Kernel T.toObserved) (assignment : T.Assignment)
    (supported : M.KernelSupportedAt kernel assignment) :
    ProbabilityTerm.SupportedAt M.interpret (.kernel kernel) assignment := by
  rcases supported with ⟨value, equivalent⟩
  exact ⟨value, ProbabilityResult.trans
    (ProbabilityResult.symm (M.kernelDenote_preserved kernel assignment))
    equivalent⟩

noncomputable def kernelSupportedAt_of_target (M : FiniteTableSCM T)
    (kernel : Kernel T.toObserved) (assignment : T.Assignment)
    (supported : ProbabilityTerm.SupportedAt
      M.interpret (.kernel kernel) assignment) :
    M.KernelSupportedAt kernel assignment := by
  rcases supported with ⟨value, equivalent⟩
  exact ⟨value, ProbabilityResult.trans
    (M.kernelDenote_preserved kernel assignment) equivalent⟩

theorem interpret_ofExact_agrees {T : FiniteTableSignature}
    (M : ExactModel T.toObserved) :
    ModelAgreement (ofExact M).interpret M := by
  constructor
  · intro event
    exact QProb.equiv_refl _
  · intro target event
    exact QProb.equiv_refl _
  · intro i j
    rfl

theorem ofExact_interpret_agrees (M : FiniteTableSCM T) :
    ModelAgreement (ofExact M.interpret).interpret M.interpret := by
  constructor
  · intro event
    exact QProb.equiv_refl _
  · intro target event
    exact QProb.equiv_refl _
  · intro i j
    rfl

end FiniteTableSCM

def FiniteSourceCompatible (M : FiniteTableSCM T)
    (G : FiniteTableGraph T) : Prop :=
  M.latent.CanonicalSemiMarkovian /\
    forall i j, M.latent.projectedBidirected i j = G.bidirected i j

theorem finiteSourceCompatible_iff (M : FiniteTableSCM T)
    (G : FiniteTableGraph T) :
    FiniteSourceCompatible M G <-> Compatible M.interpret G.interpret :=
  Iff.rfl

def FiniteSourceObservationallyEquivalent
    (M N : FiniteTableSCM T) : Prop :=
  forall event : T.Assignment -> Bool,
    QProb.Equiv (M.observationalValue event) (N.observationalValue event)

def JointKernelQuery.sourceKernel {T : FiniteTableSignature}
    (query : JointKernelQuery T.toObserved) :
    Kernel T.toObserved :=
  { outcome := query.outcome
    action := query.action
    condition := NodeSet.empty }

def ConditionalKernelQuery.sourceKernel
    {T : FiniteTableSignature}
    (query : ConditionalKernelQuery T.toObserved) : Kernel T.toObserved :=
  { outcome := query.outcome
    action := query.action
    condition := query.condition }

theorem finiteSource_observational_iff (M N : FiniteTableSCM T) :
    FiniteSourceObservationallyEquivalent M N <->
      ObservationallyEquivalent M.interpret N.interpret := by
  constructor
  · intro agreement event
    exact QProb.equiv_trans
      (QProb.equiv_symm (M.observational_preserved event))
      (QProb.equiv_trans (agreement event)
        (N.observational_preserved event))
  · intro agreement event
    exact QProb.equiv_trans (M.observational_preserved event)
      (QProb.equiv_trans (agreement event)
        (QProb.equiv_symm (N.observational_preserved event)))

def FiniteSourceKernelEquivalent (M N : FiniteTableSCM T)
    (kernel : Kernel T.toObserved) : Prop :=
  forall assignment,
    Nonempty (ProbabilityResult.Equivalent
      (M.kernelDenote kernel assignment) (N.kernelDenote kernel assignment))

def FiniteSourceConditionalKernelEquivalent (M N : FiniteTableSCM T)
    (kernel : Kernel T.toObserved) : Prop :=
  forall assignment,
    M.KernelSupportedAt kernel assignment ->
    N.KernelSupportedAt kernel assignment ->
    Nonempty (ProbabilityResult.Equivalent
      (M.kernelDenote kernel assignment) (N.kernelDenote kernel assignment))

theorem finiteSourceKernelEquivalent_iff (M N : FiniteTableSCM T)
    (kernel : Kernel T.toObserved) :
    FiniteSourceKernelEquivalent M N kernel <->
      (forall assignment, Nonempty (ProbabilityResult.Equivalent
        (kernel.denote M.interpret assignment)
        (kernel.denote N.interpret assignment))) := by
  constructor
  · intro equivalent assignment
    rcases equivalent assignment with ⟨sourceEquivalent⟩
    exact ⟨ProbabilityResult.trans
      (ProbabilityResult.symm (M.kernelDenote_preserved kernel assignment))
      (ProbabilityResult.trans sourceEquivalent
        (N.kernelDenote_preserved kernel assignment))⟩
  · intro equivalent assignment
    rcases equivalent assignment with ⟨targetEquivalent⟩
    exact ⟨ProbabilityResult.trans
      (M.kernelDenote_preserved kernel assignment)
      (ProbabilityResult.trans targetEquivalent
        (ProbabilityResult.symm
          (N.kernelDenote_preserved kernel assignment)))⟩

theorem finiteSourceConditionalKernelEquivalent_iff
    (M N : FiniteTableSCM T) (kernel : Kernel T.toObserved) :
    FiniteSourceConditionalKernelEquivalent M N kernel <->
      (forall assignment,
        ProbabilityTerm.SupportedAt M.interpret (.kernel kernel) assignment ->
        ProbabilityTerm.SupportedAt N.interpret (.kernel kernel) assignment ->
        Nonempty (ProbabilityResult.Equivalent
          (kernel.denote M.interpret assignment)
          (kernel.denote N.interpret assignment))) := by
  constructor
  · intro equivalent assignment supportedM supportedN
    rcases equivalent assignment
      (M.kernelSupportedAt_of_target kernel assignment supportedM)
      (N.kernelSupportedAt_of_target kernel assignment supportedN) with
      ⟨sourceEquivalent⟩
    exact ⟨ProbabilityResult.trans
      (ProbabilityResult.symm (M.kernelDenote_preserved kernel assignment))
      (ProbabilityResult.trans sourceEquivalent
        (N.kernelDenote_preserved kernel assignment))⟩
  · intro equivalent assignment supportedM supportedN
    rcases equivalent assignment
      (M.kernelSupportedAt_to_target kernel assignment supportedM)
      (N.kernelSupportedAt_to_target kernel assignment supportedN) with
      ⟨targetEquivalent⟩
    exact ⟨ProbabilityResult.trans
      (M.kernelDenote_preserved kernel assignment)
      (ProbabilityResult.trans targetEquivalent
        (ProbabilityResult.symm
          (N.kernelDenote_preserved kernel assignment)))⟩

def FiniteSourceIdentifiable (G : FiniteTableGraph T)
    (query : JointKernelQuery T.toObserved) : Prop :=
  forall (M N : FiniteTableSCM T),
    FiniteSourceCompatible M G ->
    FiniteSourceCompatible N G ->
    FiniteSourceObservationallyEquivalent M N ->
    FiniteSourceKernelEquivalent M N query.sourceKernel

def FiniteSourceConditionalIdentifiable (G : FiniteTableGraph T)
    (query : ConditionalKernelQuery T.toObserved) : Prop :=
  forall (M N : FiniteTableSCM T),
    FiniteSourceCompatible M G ->
    FiniteSourceCompatible N G ->
    FiniteSourceObservationallyEquivalent M N ->
    FiniteSourceConditionalKernelEquivalent M N query.sourceKernel

theorem target_identifiable_implies_finiteSource
    (G : FiniteTableGraph T) (query : JointKernelQuery T.toObserved)
    (identifiable : TypeTheoreticIdentifiable G.interpret query) :
    FiniteSourceIdentifiable G query := by
  intro M N hM hN observational
  apply (finiteSourceKernelEquivalent_iff M N query.sourceKernel).mpr
  simpa [JointKernelQuery.sourceTerm, JointKernelQuery.sourceKernel] using
    identifiable M.interpret N.interpret
    ((finiteSourceCompatible_iff M G).mp hM)
    ((finiteSourceCompatible_iff N G).mp hN)
    ((finiteSource_observational_iff M N).mp observational)

theorem target_conditionalIdentifiable_implies_finiteSource
    (G : FiniteTableGraph T) (query : ConditionalKernelQuery T.toObserved)
    (identifiable : TypeTheoreticConditionalIdentifiable G.interpret query) :
    FiniteSourceConditionalIdentifiable G query := by
  intro M N hM hN observational
  apply (finiteSourceConditionalKernelEquivalent_iff
    M N query.sourceKernel).mpr
  simpa [ConditionalKernelQuery.sourceTerm,
    ConditionalKernelQuery.sourceKernel] using
    identifiable M.interpret N.interpret
    ((finiteSourceCompatible_iff M G).mp hM)
    ((finiteSourceCompatible_iff N G).mp hN)
    ((finiteSource_observational_iff M N).mp observational)

theorem finiteSource_identifiable_implies_target
    (G : FiniteTableGraph T) (query : JointKernelQuery T.toObserved)
    (identifiable : FiniteSourceIdentifiable G query) :
    TypeTheoreticIdentifiable G.interpret query := by
  intro M N hM hN observational
  let sourceM := FiniteTableSCM.ofExact M
  let sourceN := FiniteTableSCM.ofExact N
  have sourceEquivalent := identifiable sourceM sourceN
    ((finiteSourceCompatible_iff sourceM G).mpr hM)
    ((finiteSourceCompatible_iff sourceN G).mpr hN)
    ((finiteSource_observational_iff sourceM sourceN).mpr observational)
  have targetEquivalent :=
    (finiteSourceKernelEquivalent_iff sourceM sourceN
      query.sourceKernel).mp sourceEquivalent
  simpa [JointKernelQuery.sourceTerm, JointKernelQuery.sourceKernel] using
    targetEquivalent

theorem finiteSource_conditionalIdentifiable_implies_target
    (G : FiniteTableGraph T) (query : ConditionalKernelQuery T.toObserved)
    (identifiable : FiniteSourceConditionalIdentifiable G query) :
    TypeTheoreticConditionalIdentifiable G.interpret query := by
  intro M N hM hN observational
  let sourceM := FiniteTableSCM.ofExact M
  let sourceN := FiniteTableSCM.ofExact N
  have sourceEquivalent := identifiable sourceM sourceN
    ((finiteSourceCompatible_iff sourceM G).mpr hM)
    ((finiteSourceCompatible_iff sourceN G).mpr hN)
    ((finiteSource_observational_iff sourceM sourceN).mpr observational)
  have targetEquivalent :=
    (finiteSourceConditionalKernelEquivalent_iff sourceM sourceN
      query.sourceKernel).mp sourceEquivalent
  simpa [ConditionalKernelQuery.sourceTerm,
    ConditionalKernelQuery.sourceKernel] using targetEquivalent

theorem finiteSource_identifiable_iff
    (G : FiniteTableGraph T) (query : JointKernelQuery T.toObserved) :
    FiniteSourceIdentifiable G query <->
      TypeTheoreticIdentifiable G.interpret query :=
  ⟨finiteSource_identifiable_implies_target G query,
    target_identifiable_implies_finiteSource G query⟩

theorem finiteSource_conditionalIdentifiable_iff
    (G : FiniteTableGraph T) (query : ConditionalKernelQuery T.toObserved) :
    FiniteSourceConditionalIdentifiable G query <->
      TypeTheoreticConditionalIdentifiable G.interpret query :=
  ⟨finiteSource_conditionalIdentifiable_implies_target G query,
    target_conditionalIdentifiable_implies_finiteSource G query⟩

/-- A source-native finite rational witness that a joint kernel is separated. -/
structure FiniteSourceCounterexample (G : FiniteTableGraph T)
    (query : JointKernelQuery T.toObserved) where
  left : FiniteTableSCM T
  right : FiniteTableSCM T
  left_compatible : FiniteSourceCompatible left G
  right_compatible : FiniteSourceCompatible right G
  observationally_equal : FiniteSourceObservationallyEquivalent left right
  query_separated :
    Not (FiniteSourceKernelEquivalent left right query.sourceKernel)

noncomputable def FiniteSourceCounterexample.toTarget
    (counterexample : FiniteSourceCounterexample G query) :
    Counterexample G.interpret query where
  left := counterexample.left.interpret
  right := counterexample.right.interpret
  left_compatible :=
    (finiteSourceCompatible_iff counterexample.left G).mp
      counterexample.left_compatible
  right_compatible :=
    (finiteSourceCompatible_iff counterexample.right G).mp
      counterexample.right_compatible
  observationally_equal :=
    (finiteSource_observational_iff counterexample.left
      counterexample.right).mp counterexample.observationally_equal
  query_separated := by
    intro targetEquivalent
    apply counterexample.query_separated
    apply (finiteSourceKernelEquivalent_iff counterexample.left
      counterexample.right query.sourceKernel).mpr
    simpa [JointKernelQuery.sourceTerm, JointKernelQuery.sourceKernel] using
      targetEquivalent

/-- Published source certificate before interpretation into the target layer. -/
structure FiniteSourceJointCertificate (G : FiniteTableGraph T)
    (correct : DSeparationCorrectness G.interpret)
    (query : JointKernelQuery T.toObserved) where
  formula : ProbabilityTerm T.toObserved
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G.interpret query.sourceTerm formula
  supported : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G -> forall assignment,
      model.KernelSupportedAt query.sourceKernel assignment ->
        LocalDerivationSupport model.interpret assignment
          (derivation.compile correct)

structure FiniteSourceConditionalCertificate (G : FiniteTableGraph T)
    (correct : DSeparationCorrectness G.interpret)
    (query : ConditionalKernelQuery T.toObserved) where
  formula : ProbabilityTerm T.toObserved
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G.interpret query.sourceTerm formula
  supported : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G -> forall assignment,
      model.KernelSupportedAt query.sourceKernel assignment ->
        LocalDerivationSupport model.interpret assignment
          (derivation.compile correct)

noncomputable def FiniteSourceJointCertificate.toPublished
    (certificate : FiniteSourceJointCertificate G correct query) :
    PublishedJointCertificate G.interpret correct query where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := by
    intro model compatible assignment sourceSupported
    let source := FiniteTableSCM.ofExact model
    exact certificate.supported source
      ((finiteSourceCompatible_iff source G).mpr compatible)
      assignment (by
        apply source.kernelSupportedAt_of_target query.sourceKernel assignment
        simpa [JointKernelQuery.sourceTerm,
          JointKernelQuery.sourceKernel] using sourceSupported)

noncomputable def FiniteSourceConditionalCertificate.toPublished
    (certificate : FiniteSourceConditionalCertificate G correct query) :
    PublishedConditionalCertificate G.interpret correct query where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := by
    intro model compatible assignment sourceSupported
    let source := FiniteTableSCM.ofExact model
    exact certificate.supported source
      ((finiteSourceCompatible_iff source G).mpr compatible)
      assignment (by
        apply source.kernelSupportedAt_of_target query.sourceKernel assignment
        simpa [ConditionalKernelQuery.sourceTerm,
          ConditionalKernelQuery.sourceKernel] using sourceSupported)

/--
The exact external theorem boundary.  It specializes the cited completeness
result to finite coded tables and binary/fair-rational hedge countermodels;
it does not mention `TypeTheoreticModel` or encoded target certificates.
-/
structure PublishedFiniteSourceCompleteness (T : FiniteTableSignature)
    (G : FiniteTableGraph T) where
  dseparation : DSeparationCorrectness G.interpret
  joint_complete : forall query,
    FiniteSourceIdentifiable G query ->
      FiniteSourceJointCertificate G dseparation query
  conditional_complete : forall query,
    FiniteSourceConditionalIdentifiable G query ->
      FiniteSourceConditionalCertificate G dseparation query
  hedge_counterexample : forall query,
    HedgeWitness G.interpret query -> FiniteSourceCounterexample G query

/-- Source-only finite specialization of the published primitive soundness laws. -/
structure PublishedFiniteSourceSoundness (T : FiniteTableSignature)
    (G : FiniteTableGraph T) where
  dseparation : DSeparationCorrectness G.interpret
  pathPrimitive : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G ->
      PathPrimitiveSoundness G.interpret model.interpret

def PublishedFiniteSourceSoundness.toPublished
    (published : PublishedFiniteSourceSoundness T G) :
    PublishedSoundness T.toObserved G.interpret where
  dseparation := published.dseparation
  pathPrimitive := by
    intro model compatible
    let source := FiniteTableSCM.ofExact model
    exact published.pathPrimitive source
      ((finiteSourceCompatible_iff source G).mpr compatible)

noncomputable def PublishedFiniteSourceCompleteness.toPublished
    (published : PublishedFiniteSourceCompleteness T G) :
    PublishedCompleteness T.toObserved G.interpret where
  dseparation := published.dseparation
  joint_complete := by
    intro query identifiable
    apply FiniteSourceJointCertificate.toPublished
    apply published.joint_complete query
    apply target_identifiable_implies_finiteSource G query
    exact identifiable
  conditional_complete := by
    intro query identifiable
    apply FiniteSourceConditionalCertificate.toPublished
    apply published.conditional_complete query
    apply target_conditionalIdentifiable_implies_finiteSource G query
    exact identifiable
  hedge_counterexample := fun query hedge =>
    (published.hedge_counterexample query hedge).toTarget

theorem finiteSource_completeness_transport
    (published : PublishedFiniteSourceCompleteness T G) :
    (forall query,
      TypeTheoreticIdentifiable G.interpret query ->
        Nonempty (EncodedJointDerivation G.interpret query)) /\
    (forall query,
      TypeTheoreticConditionalIdentifiable G.interpret query ->
        Nonempty (EncodedConditionalDerivation G.interpret query)) /\
    (forall query, HedgeWitness G.interpret query ->
      Not (TypeTheoreticIdentifiable G.interpret query)) :=
  finite_causal_completeness_transport published.toPublished

theorem finiteSource_transported_joint_iff
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    TypeTheoreticIdentifiable G.interpret query <->
      Nonempty (EncodedJointDerivation G.interpret query) :=
  transported_joint_iff complete.toPublished sound.toPublished query

theorem finiteSource_transported_conditional_iff
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    TypeTheoreticConditionalIdentifiable G.interpret query <->
      Nonempty (EncodedConditionalDerivation G.interpret query) :=
  transported_conditional_iff complete.toPublished sound.toPublished query

end Causality
end Thesis
