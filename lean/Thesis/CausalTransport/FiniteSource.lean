import Thesis.CausalTransport.Correspondence

namespace Thesis
namespace Causality

open Probability

/-!
An independently declared finite coded source presentation.

Observed value spaces are cardinalities and their values are table indices.
The interpretation turns those indices into an intrinsic dependent observed
signature.  Source probabilities are finite sums over exogenous assignments;
the target semantics forms finite pushforward distributions.  The agreement
theorems below connect those independently stated semantics pointwise.

Reading order: finite source data and its intrinsic re-presentation; independent
node, kernel, and expression evaluation; identifiability equivalence; recursive
source derivation support; then explicit packages for published finite results.
`interpret` and `ofExact` are intentionally transparent re-presentations of
the same finite data. The semantic content lies in agreement of the independent
recursive evaluators, not in pretending the two record encodings are unrelated.
-/

/-- A finite coded observed signature used by the source-table presentation. -/
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

/--
A graph table over the source node codes. Directed edges are held by the
signature; this structure contains only the bidirected projection and its two
graph invariants.
-/
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

/-- Re-present a finite table SCM as the intrinsic theorem-facing exact model. -/
def interpret (M : FiniteTableSCM T) : ExactModel T.toObserved where
  latent := M.latent.interpret
  factor := M.factor
  prior := M.prior
  product_law := M.product_law
  mechanism := M.table

/-- Re-present any intrinsic exact model on this signature as finite source data. -/
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

/-!
The probability-expression syntax is deliberately shared by the finite-table
source and intrinsic target.  Its denotation is not shared: the definitions
below evaluate every constructor directly with the independently recursive
source semantics.  The subsequent preservation maps are therefore the bridge
to `ProbabilityTerm.denote`, rather than an implicit appeal to target
semantics inside a source certificate.
-/

/-- Source-native partial denotation of a finite probability expression. -/
def termDenote (M : FiniteTableSCM T) :
    ProbabilityTerm T.toObserved -> T.Assignment -> ProbabilityResult.Result
  | .zero, _ => some QProb.zero
  | .kernel K, assignment => M.kernelDenote K assignment
  | .marginalize nodes inner, assignment =>
      ProbabilityResult.sum
        ((ProbabilityTerm.marginalAssignments T.toObserved nodes assignment).map
          (fun variant => M.termDenote inner variant))
  | .evaluateAt fixed inner, _ => M.termDenote inner fixed
  | .add left right, assignment =>
      ProbabilityResult.add
        (M.termDenote left assignment) (M.termDenote right assignment)
  | .multiply left right, assignment =>
      ProbabilityResult.multiply
        (M.termDenote left assignment) (M.termDenote right assignment)
  | .divide numerator denominator, assignment =>
      ProbabilityResult.divide
        (M.termDenote numerator assignment) (M.termDenote denominator assignment)

/-- Source-native support of an expression at one coded valuation. -/
def TermSupportedAt (M : FiniteTableSCM T)
    (term : ProbabilityTerm T.toObserved) (assignment : T.Assignment) : Type :=
  Sigma fun value =>
    ProbabilityResult.Equivalent (M.termDenote term assignment) (some value)

/-- Source-native equality of two expressions at one coded valuation. -/
def TermEquivalentAt (M : FiniteTableSCM T)
    (left right : ProbabilityTerm T.toObserved)
    (assignment : T.Assignment) : Type :=
  ProbabilityResult.Equivalent
    (M.termDenote left assignment) (M.termDenote right assignment)

/-- Every source expression denotes the same value after interpretation. -/
noncomputable def termDenote_preserved (M : FiniteTableSCM T)
    (term : ProbabilityTerm T.toObserved) : forall assignment,
    ProbabilityResult.Equivalent
      (M.termDenote term assignment)
      (term.denote M.interpret assignment) := by
  intro assignment
  induction term generalizing assignment with
  | zero => exact ProbabilityResult.refl _
  | kernel kernel => exact M.kernelDenote_preserved kernel assignment
  | marginalize nodes term ih =>
      simpa only [termDenote, ProbabilityTerm.denote] using
        (ProbabilityResult.sum_map_congr
          (ProbabilityTerm.marginalAssignments T.toObserved nodes assignment)
          (fun variant => M.termDenote term variant)
          (fun variant => term.denote M.interpret variant)
          (fun variant => ih variant))
  | evaluateAt fixed term ih =>
      exact ih fixed
  | add left right leftIH rightIH =>
      simpa only [termDenote, ProbabilityTerm.denote] using
        ProbabilityResult.add_congr
          (leftIH assignment) (rightIH assignment)
  | multiply left right leftIH rightIH =>
      simpa only [termDenote, ProbabilityTerm.denote] using
        ProbabilityResult.multiply_congr
          (leftIH assignment) (rightIH assignment)
  | divide numerator denominator numeratorIH denominatorIH =>
      simpa only [termDenote, ProbabilityTerm.denote] using
        ProbabilityResult.divide_congr
          (numeratorIH assignment) (denominatorIH assignment)

noncomputable def termSupportedAt_to_target (M : FiniteTableSCM T)
    (term : ProbabilityTerm T.toObserved) (assignment : T.Assignment)
    (supported : M.TermSupportedAt term assignment) :
    term.SupportedAt M.interpret assignment := by
  rcases supported with ⟨value, equivalent⟩
  exact ⟨value, ProbabilityResult.trans
    (ProbabilityResult.symm (M.termDenote_preserved term assignment))
    equivalent⟩

noncomputable def termSupportedAt_of_target (M : FiniteTableSCM T)
    (term : ProbabilityTerm T.toObserved) (assignment : T.Assignment)
    (supported : term.SupportedAt M.interpret assignment) :
    M.TermSupportedAt term assignment := by
  rcases supported with ⟨value, equivalent⟩
  exact ⟨value, ProbabilityResult.trans
    (M.termDenote_preserved term assignment) equivalent⟩

noncomputable def termEquivalentAt_to_target (M : FiniteTableSCM T)
    (left right : ProbabilityTerm T.toObserved) (assignment : T.Assignment)
    (equivalent : M.TermEquivalentAt left right assignment) :
    ProbabilityTerm.EquivalentAt M.interpret left right assignment :=
  ProbabilityResult.trans
    (ProbabilityResult.symm (M.termDenote_preserved left assignment))
    (ProbabilityResult.trans equivalent
      (M.termDenote_preserved right assignment))

noncomputable def termEquivalentAt_of_target (M : FiniteTableSCM T)
    (left right : ProbabilityTerm T.toObserved) (assignment : T.Assignment)
    (equivalent : ProbabilityTerm.EquivalentAt
      M.interpret left right assignment) :
    M.TermEquivalentAt left right assignment :=
  ProbabilityResult.trans
    (M.termDenote_preserved left assignment)
    (ProbabilityResult.trans equivalent
      (ProbabilityResult.symm (M.termDenote_preserved right assignment)))

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

/--
Compatibility of a source model with a source ADMG. Canonical
semi-Markovianity constrains each latent root to at most two distinct observed
children; the second field fixes its projected bidirected graph exactly.
-/
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

/-- Source-facing name for the query's concrete operation kernel. -/
abbrev JointKernelQuery.sourceKernel {T : FiniteTableSignature}
    (query : JointKernelQuery T.toObserved) :
    Kernel T.toObserved := query.operationKernel

/-- Source-facing name for the query's concrete conditional operation kernel. -/
abbrev ConditionalKernelQuery.sourceKernel
    {T : FiniteTableSignature}
    (query : ConditionalKernelQuery T.toObserved) : Kernel T.toObserved :=
  query.operationKernel

/-- A joint source query is supported directly by finite-table normalization. -/
noncomputable def JointKernelQuery.finiteSourceSupportedAt
    {T : FiniteTableSignature} (query : JointKernelQuery T.toObserved)
    (model : FiniteTableSCM T) (assignment : T.Assignment) :
    model.TermSupportedAt query.sourceTerm assignment := by
  change model.KernelSupportedAt query.sourceKernel assignment
  let kernel := query.sourceKernel
  change model.KernelSupportedAt kernel assignment
  cases selected : kernel.hasAction with
  | false =>
      let value := model.observationalValue (kernel.numeratorEvent assignment)
      let denominator :=
        model.observationalValue (kernel.conditionEvent assignment)
      have normalized : QProb.Equiv denominator QProb.one := by
        exact QProb.equiv_trans
          (FiniteProbRecord.probVal_congr model.prior _ Probability.topEvent
            (fun latent => by
              simp [kernel, JointKernelQuery.operationKernel,
                Kernel.conditionEvent, Kernel.agreesOn, NodeSet.empty,
                finAll_true, Probability.topEvent]))
          model.prior.normalization
      have positive : 0 < denominator.num :=
        (QProb.equiv_num_pos_iff normalized).mpr (by decide)
      refine ⟨value, ?_⟩
      simp only [FiniteTableSCM.kernelDenote, selected, Bool.false_eq_true,
        if_false, ProbabilityResult.divide]
      rw [dif_pos positive]
      exact .value
        (QProb.div_equiv_of_den_equiv_one _ _ positive normalized)
  | true =>
      let intervention := kernel.intervention assignment
      let value := model.interventionalValue intervention
        (kernel.numeratorEvent assignment)
      let denominator := model.interventionalValue intervention
        (kernel.conditionEvent assignment)
      have normalized : QProb.Equiv denominator QProb.one := by
        exact QProb.equiv_trans
          (FiniteProbRecord.probVal_congr model.prior _ Probability.topEvent
            (fun latent => by
              simp [kernel, JointKernelQuery.operationKernel,
                Kernel.conditionEvent, Kernel.agreesOn, NodeSet.empty,
                finAll_true, Probability.topEvent]))
          model.prior.normalization
      have positive : 0 < denominator.num :=
        (QProb.equiv_num_pos_iff normalized).mpr (by decide)
      refine ⟨value, ?_⟩
      simp only [FiniteTableSCM.kernelDenote, selected, if_true,
        ProbabilityResult.divide]
      rw [dif_pos positive]
      exact .value
        (QProb.div_equiv_of_den_equiv_one _ _ positive normalized)

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

/--
Source-table identifiability quantifies over source models compatible with the
same graph and observational table. The following equivalence theorems show
that this is neither stronger nor weaker than intrinsic identifiability after
interpretation.
-/
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
  left_mem :=
    (finiteSourceCompatible_iff counterexample.left G).mp
      counterexample.left_compatible
  right_mem :=
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

/-!
## Source-native expression and derivation semantics

This section intentionally repeats the target-side support-tree structure.
Doing so prevents a source certificate from silently invoking intrinsic target
semantics before the explicit preservation map is applied.
-/

/-- Action-free expressions depend only on the source observational table. -/
noncomputable def finiteSource_actionFree_invariant
    (left right : FiniteTableSCM T)
    (observational : FiniteSourceObservationallyEquivalent left right)
    (term : ProbabilityTerm T.toObserved) (actionFree : term.ActionFree) :
    forall assignment,
      ProbabilityResult.Equivalent
        (left.termDenote term assignment)
        (right.termDenote term assignment) := by
  intro assignment
  induction term generalizing assignment with
  | zero => exact ProbabilityResult.refl _
  | kernel kernel =>
      have noAction := ProbabilityTerm.actionFree_hasAction_false kernel actionFree
      simp only [FiniteTableSCM.termDenote, FiniteTableSCM.kernelDenote,
        noAction, Bool.false_eq_true, if_false]
      exact ProbabilityResult.divide_congr
        (.value (observational (kernel.numeratorEvent assignment)))
        (.value (observational (kernel.conditionEvent assignment)))
  | marginalize nodes term ih =>
      simpa only [FiniteTableSCM.termDenote] using
        (ProbabilityResult.sum_map_congr
          (ProbabilityTerm.marginalAssignments T.toObserved nodes assignment)
          (fun variant => left.termDenote term variant)
          (fun variant => right.termDenote term variant)
          (fun variant => ih actionFree variant))
  | evaluateAt fixed term ih =>
      exact ih actionFree fixed
  | add first second firstIH secondIH =>
      exact ProbabilityResult.add_congr
        (firstIH actionFree.1 assignment)
        (secondIH actionFree.2 assignment)
  | multiply first second firstIH secondIH =>
      exact ProbabilityResult.multiply_congr
        (firstIH actionFree.1 assignment)
        (secondIH actionFree.2 assignment)
  | divide numerator denominator numeratorIH denominatorIH =>
      exact ProbabilityResult.divide_congr
        (numeratorIH actionFree.1 assignment)
        (denominatorIH actionFree.2 assignment)

/-- Primitive source-table semantics for the executable do-rule syntax. -/
structure FiniteSourceLocalPrimitiveSoundness (G : FiniteTableGraph T)
    (model : FiniteTableSCM T) where
  doRule : forall {left right} (assignment : T.Assignment),
    DoRuleApplication G.interpret left right ->
      model.TermSupportedAt (.kernel left) assignment ->
      model.TermSupportedAt (.kernel right) assignment ->
      model.TermEquivalentAt (.kernel left) (.kernel right) assignment
  marginalization : forall (x y z w : NodeSet T.toObserved)
      (assignment : T.Assignment),
    FourWayDisjoint x y z w ->
      model.TermSupportedAt (.kernel ⟨y, x, w⟩) assignment ->
      model.TermSupportedAt
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment ->
      model.TermEquivalentAt
        (.kernel ⟨y, x, w⟩)
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment
  conditioning : forall (x y z w : NodeSet T.toObserved)
      (assignment : T.Assignment),
    FourWayDisjoint x y z w ->
      model.TermSupportedAt
        (.kernel ⟨y, x, NodeSet.union z w⟩) assignment ->
      model.TermSupportedAt
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      model.TermEquivalentAt
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment
  chain : forall (x y z w : NodeSet T.toObserved)
      (assignment : T.Assignment),
    FourWayDisjoint x y z w ->
      model.TermSupportedAt
        (.kernel ⟨NodeSet.union y z, x, w⟩) assignment ->
      model.TermSupportedAt
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      model.TermEquivalentAt
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment

/-- Source-table primitive semantics stated with active-path side conditions. -/
structure FiniteSourcePathPrimitiveSoundness (G : FiniteTableGraph T)
    (model : FiniteTableSCM T) where
  doRule : forall {left right} (assignment : T.Assignment),
    PathDoRuleApplication G.interpret left right ->
      model.TermSupportedAt (.kernel left) assignment ->
      model.TermSupportedAt (.kernel right) assignment ->
      model.TermEquivalentAt (.kernel left) (.kernel right) assignment
  marginalization : forall (x y z w : NodeSet T.toObserved)
      (assignment : T.Assignment),
    FourWayDisjoint x y z w ->
      model.TermSupportedAt (.kernel ⟨y, x, w⟩) assignment ->
      model.TermSupportedAt
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment ->
      model.TermEquivalentAt
        (.kernel ⟨y, x, w⟩)
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment
  conditioning : forall (x y z w : NodeSet T.toObserved)
      (assignment : T.Assignment),
    FourWayDisjoint x y z w ->
      model.TermSupportedAt
        (.kernel ⟨y, x, NodeSet.union z w⟩) assignment ->
      model.TermSupportedAt
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      model.TermEquivalentAt
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.divide
          (.kernel ⟨NodeSet.union y z, x, w⟩)
          (.kernel ⟨z, x, w⟩)) assignment
  chain : forall (x y z w : NodeSet T.toObserved)
      (assignment : T.Assignment),
    FourWayDisjoint x y z w ->
      model.TermSupportedAt
        (.kernel ⟨NodeSet.union y z, x, w⟩) assignment ->
      model.TermSupportedAt
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment ->
      model.TermEquivalentAt
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.multiply
          (.kernel ⟨y, x, NodeSet.union z w⟩)
          (.kernel ⟨z, x, w⟩)) assignment

def FiniteSourcePathPrimitiveSoundness.compile
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {model : FiniteTableSCM T}
    (correct : DSeparationCorrectness G.interpret)
    (semantics : FiniteSourcePathPrimitiveSoundness G model) :
    FiniteSourceLocalPrimitiveSoundness G model where
  doRule := fun assignment application leftSupported rightSupported =>
    semantics.doRule assignment (application.toPath correct)
      leftSupported rightSupported
  marginalization := semantics.marginalization
  conditioning := semantics.conditioning
  chain := semantics.chain

/-- Recursive source support for every endpoint and subderivation. -/
def FiniteSourceLocalDerivationSupport {T : FiniteTableSignature}
    {G : FiniteTableGraph T} (model : FiniteTableSCM T)
    (assignment : T.Assignment) {left right : ProbabilityTerm T.toObserved}
    (derivation : DoCalculusDerivation G.interpret left right) : Type :=
  model.TermSupportedAt left assignment ×
    model.TermSupportedAt right assignment ×
      match derivation with
      | .refl _ => Unit
      | .symm inner =>
          FiniteSourceLocalDerivationSupport model assignment inner
      | .trans first second =>
          FiniteSourceLocalDerivationSupport model assignment first ×
            FiniteSourceLocalDerivationSupport model assignment second
      | .doRule _ => Unit
      | .marginalization _ _ _ _ _ => Unit
      | .conditioning _ _ _ _ _ => Unit
      | .chain _ _ _ _ _ => Unit
      | .marginalizeCongr nodes inner =>
          forall variant,
            variant ∈ ProbabilityTerm.marginalAssignments
                T.toObserved nodes assignment ->
              FiniteSourceLocalDerivationSupport model variant inner
      | .evaluateAtCongr fixed inner =>
          FiniteSourceLocalDerivationSupport model fixed inner
      | .addCongr first second =>
          FiniteSourceLocalDerivationSupport model assignment first ×
            FiniteSourceLocalDerivationSupport model assignment second
      | .multiplyCongr first second =>
          FiniteSourceLocalDerivationSupport model assignment first ×
            FiniteSourceLocalDerivationSupport model assignment second
      | .divideCongr numerator denominator =>
          FiniteSourceLocalDerivationSupport model assignment numerator ×
            FiniteSourceLocalDerivationSupport model assignment denominator
      | .eqCongr _ _ inner =>
          FiniteSourceLocalDerivationSupport model assignment inner

/-- Interpret a complete source support tree in the intrinsic target. -/
noncomputable def FiniteSourceLocalDerivationSupport.toTarget
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {model : FiniteTableSCM T} {assignment : T.Assignment}
    {left right : ProbabilityTerm T.toObserved}
    {derivation : DoCalculusDerivation G.interpret left right}
    (supported : FiniteSourceLocalDerivationSupport
      model assignment derivation) :
    LocalDerivationSupport model.interpret assignment derivation := by
  induction derivation generalizing assignment with
  | refl =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1, ()⟩
  | symm derivation ih =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        ih supported.2.2⟩
  | trans first second firstIH secondIH =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | doRule =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1, ()⟩
  | marginalization =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1, ()⟩
  | conditioning =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1, ()⟩
  | chain =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1, ()⟩
  | marginalizeCongr nodes inner ih =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        fun variant member => ih (supported.2.2 variant member)⟩
  | evaluateAtCongr fixed inner ih =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        ih supported.2.2⟩
  | addCongr first second firstIH secondIH =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | multiplyCongr first second firstIH secondIH =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | divideCongr numerator denominator numeratorIH denominatorIH =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        numeratorIH supported.2.2.1, denominatorIH supported.2.2.2⟩
  | eqCongr _hleft _hright inner ih =>
      exact ⟨model.termSupportedAt_to_target _ _ supported.1,
        model.termSupportedAt_to_target _ _ supported.2.1,
        ih supported.2.2⟩

/-- Internal induction proving source semantics for an entire derivation. -/
noncomputable def DoCalculusDerivation.finiteSource_denotational_soundAt
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {model : FiniteTableSCM T} {assignment : T.Assignment}
    {left right : ProbabilityTerm T.toObserved}
    (semantics : FiniteSourceLocalPrimitiveSoundness G model)
    (derivation : DoCalculusDerivation G.interpret left right)
    (supported : FiniteSourceLocalDerivationSupport
      model assignment derivation) :
    model.TermEquivalentAt left right assignment := by
  induction derivation generalizing assignment with
  | refl => exact ProbabilityResult.refl _
  | symm derivation ih =>
      exact ProbabilityResult.symm (ih supported.2.2)
  | trans first second firstIH secondIH =>
      exact ProbabilityResult.trans
        (firstIH supported.2.2.1) (secondIH supported.2.2.2)
  | doRule rule =>
      exact semantics.doRule assignment rule supported.1 supported.2.1
  | marginalization x y z w disjoint =>
      exact semantics.marginalization x y z w assignment disjoint
        supported.1 supported.2.1
  | conditioning x y z w disjoint =>
      exact semantics.conditioning x y z w assignment disjoint
        supported.1 supported.2.1
  | chain x y z w disjoint =>
      exact semantics.chain x y z w assignment disjoint
        supported.1 supported.2.1
  | marginalizeCongr nodes derivation ih =>
      simpa only [FiniteTableSCM.TermEquivalentAt,
        FiniteTableSCM.termDenote] using
        (ProbabilityResult.sum_map_congr_mem
          (ProbabilityTerm.marginalAssignments T.toObserved nodes assignment)
          (fun variant => model.termDenote _ variant)
          (fun variant => model.termDenote _ variant)
          (fun variant member => ih (supported.2.2 variant member)))
  | evaluateAtCongr fixed derivation ih =>
      exact ih supported.2.2
  | addCongr first second firstIH secondIH =>
      simpa only [FiniteTableSCM.TermEquivalentAt,
        FiniteTableSCM.termDenote] using
        ProbabilityResult.add_congr
          (firstIH supported.2.2.1) (secondIH supported.2.2.2)
  | multiplyCongr first second firstIH secondIH =>
      simpa only [FiniteTableSCM.TermEquivalentAt,
        FiniteTableSCM.termDenote] using
        ProbabilityResult.multiply_congr
          (firstIH supported.2.2.1) (secondIH supported.2.2.2)
  | divideCongr numerator denominator numeratorIH denominatorIH =>
      simpa only [FiniteTableSCM.TermEquivalentAt,
        FiniteTableSCM.termDenote] using
        ProbabilityResult.divide_congr
          (numeratorIH supported.2.2.1) (denominatorIH supported.2.2.2)
  | eqCongr hleft hright inner ih =>
      subst hleft
      subst hright
      exact ih supported.2.2

/-- Source primitive laws imply target primitive laws only through preservation. -/
noncomputable def FiniteSourcePathPrimitiveSoundness.toTarget
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {model : FiniteTableSCM T}
    (semantics : FiniteSourcePathPrimitiveSoundness G model) :
    PathPrimitiveSoundness G.interpret model.interpret where
  doRule := by
    intro left right assignment application leftSupported rightSupported
    apply model.termEquivalentAt_to_target
    exact semantics.doRule assignment application
      (model.termSupportedAt_of_target _ _ leftSupported)
      (model.termSupportedAt_of_target _ _ rightSupported)
  marginalization := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_to_target
    exact semantics.marginalization x y z w assignment disjoint
      (model.termSupportedAt_of_target _ _ leftSupported)
      (model.termSupportedAt_of_target _ _ rightSupported)
  conditioning := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_to_target
    exact semantics.conditioning x y z w assignment disjoint
      (model.termSupportedAt_of_target _ _ leftSupported)
      (model.termSupportedAt_of_target _ _ rightSupported)
  chain := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_to_target
    exact semantics.chain x y z w assignment disjoint
      (model.termSupportedAt_of_target _ _ leftSupported)
      (model.termSupportedAt_of_target _ _ rightSupported)

/--
Published certificate with source-native support and shared finite syntax.
The formula and derivation are inspectable Lean data. The `supported` field is
stronger than a bare external derivability predicate: it supplies the local
support tree needed to evaluate every primitive and intermediate expression.
-/
structure FiniteSourceJointCertificate (G : FiniteTableGraph T)
    (correct : DSeparationCorrectness G.interpret)
    (query : JointKernelQuery T.toObserved) where
  formula : ProbabilityTerm T.toObserved
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G.interpret query.sourceTerm formula
  supported : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G -> forall assignment,
      model.TermSupportedAt query.sourceTerm assignment ->
        FiniteSourceLocalDerivationSupport model assignment
          (derivation.compile correct)

structure FiniteSourceConditionalCertificate (G : FiniteTableGraph T)
    (correct : DSeparationCorrectness G.interpret)
    (query : ConditionalKernelQuery T.toObserved) where
  formula : ProbabilityTerm T.toObserved
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G.interpret query.sourceTerm formula
  supported : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G -> forall assignment,
      model.TermSupportedAt query.sourceTerm assignment ->
        FiniteSourceLocalDerivationSupport model assignment
          (derivation.compile correct)

noncomputable def FiniteSourceJointCertificate.toPublished
    (certificate : FiniteSourceJointCertificate G correct query) :
    PublishedJointCertificate (GraphModelClass.all G.interpret) correct query where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := by
    intro model compatible assignment sourceSupported
    let source := FiniteTableSCM.ofExact model
    exact (certificate.supported source
      ((finiteSourceCompatible_iff source G).mpr compatible)
      assignment
      (source.termSupportedAt_of_target query.sourceTerm assignment
        sourceSupported)).toTarget

noncomputable def FiniteSourceConditionalCertificate.toPublished
    (certificate : FiniteSourceConditionalCertificate G correct query) :
    PublishedConditionalCertificate (GraphModelClass.all G.interpret) correct
      query where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := by
    intro model compatible assignment sourceSupported
    let source := FiniteTableSCM.ofExact model
    exact (certificate.supported source
      ((finiteSourceCompatible_iff source G).mpr compatible)
      assignment
      (source.termSupportedAt_of_target query.sourceTerm assignment
        sourceSupported)).toTarget

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

/--
Source-native finite specialization of the published primitive soundness laws.
This is an explicit boundary: Lean checks how these laws are consumed and
transported, but does not manufacture an inhabitant from the cited literature.
-/
structure PublishedFiniteSourceSoundness (T : FiniteTableSignature)
    (G : FiniteTableGraph T) where
  dseparation : DSeparationCorrectness G.interpret
  pathPrimitive : forall model : FiniteTableSCM T,
    FiniteSourceCompatible model G ->
      FiniteSourcePathPrimitiveSoundness G model

noncomputable def PublishedFiniteSourceSoundness.toPublished
    (published : PublishedFiniteSourceSoundness T G) :
    PublishedSoundness T.toObserved G.interpret where
  dseparation := published.dseparation
  pathPrimitive := by
    intro model compatible
    let source := FiniteTableSCM.ofExact model
    exact (published.pathPrimitive source
      ((finiteSourceCompatible_iff source G).mpr compatible)).toTarget

/-- A source certificate is sound before any target model is constructed. -/
noncomputable def FiniteSourceJointCertificate.source_denotational_soundAt
    (sound : PublishedFiniteSourceSoundness T G)
    (certificate : FiniteSourceJointCertificate G correct query)
    (model : FiniteTableSCM T) (compatible : FiniteSourceCompatible model G)
    (assignment : T.Assignment)
    (sourceSupported : model.TermSupportedAt query.sourceTerm assignment) :
    model.TermEquivalentAt query.sourceTerm certificate.formula assignment :=
  (certificate.derivation.compile correct).finiteSource_denotational_soundAt
    ((sound.pathPrimitive model compatible).compile correct)
    (certificate.supported model compatible assignment sourceSupported)

noncomputable def
    FiniteSourceConditionalCertificate.source_denotational_soundAt
    (sound : PublishedFiniteSourceSoundness T G)
    (certificate : FiniteSourceConditionalCertificate G correct query)
    (model : FiniteTableSCM T) (compatible : FiniteSourceCompatible model G)
    (assignment : T.Assignment)
    (sourceSupported : model.TermSupportedAt query.sourceTerm assignment) :
    model.TermEquivalentAt query.sourceTerm certificate.formula assignment :=
  (certificate.derivation.compile correct).finiteSource_denotational_soundAt
    ((sound.pathPrimitive model compatible).compile correct)
    (certificate.supported model compatible assignment sourceSupported)

/-- Source completeness certificates plus source primitive laws imply source identifiability. -/
theorem FiniteSourceJointCertificate.source_identifiable
    (sound : PublishedFiniteSourceSoundness T G)
    (certificate : FiniteSourceJointCertificate G correct query) :
    FiniteSourceIdentifiable G query := by
  intro M N compatibleM compatibleN observational assignment
  let supportedM : M.TermSupportedAt query.sourceTerm assignment :=
    query.finiteSourceSupportedAt M assignment
  let supportedN : N.TermSupportedAt query.sourceTerm assignment :=
    query.finiteSourceSupportedAt N assignment
  let leftToFormula := certificate.source_denotational_soundAt sound M
    compatibleM assignment supportedM
  let rightToFormula := certificate.source_denotational_soundAt sound N
    compatibleN assignment supportedN
  let formulaInvariant := finiteSource_actionFree_invariant M N observational
    certificate.formula certificate.actionFree assignment
  refine ⟨?_⟩
  simpa [JointKernelQuery.sourceTerm, JointKernelQuery.sourceKernel,
    FiniteTableSCM.TermEquivalentAt, FiniteTableSCM.termDenote] using
      (ProbabilityResult.trans leftToFormula
        (ProbabilityResult.trans formulaInvariant
          (ProbabilityResult.symm rightToFormula)))

theorem FiniteSourceConditionalCertificate.source_identifiable
    (sound : PublishedFiniteSourceSoundness T G)
    (certificate : FiniteSourceConditionalCertificate G correct query) :
    FiniteSourceConditionalIdentifiable G query := by
  intro M N compatibleM compatibleN observational assignment
    kernelSupportedM kernelSupportedN
  have supportedM : M.TermSupportedAt query.sourceTerm assignment := by
    simpa [ConditionalKernelQuery.sourceTerm,
      ConditionalKernelQuery.sourceKernel, FiniteTableSCM.TermSupportedAt,
      FiniteTableSCM.termDenote] using kernelSupportedM
  have supportedN : N.TermSupportedAt query.sourceTerm assignment := by
    simpa [ConditionalKernelQuery.sourceTerm,
      ConditionalKernelQuery.sourceKernel, FiniteTableSCM.TermSupportedAt,
      FiniteTableSCM.termDenote] using kernelSupportedN
  let leftToFormula := certificate.source_denotational_soundAt sound M
    compatibleM assignment supportedM
  let rightToFormula := certificate.source_denotational_soundAt sound N
    compatibleN assignment supportedN
  let formulaInvariant := finiteSource_actionFree_invariant M N observational
    certificate.formula certificate.actionFree assignment
  refine ⟨?_⟩
  simpa [ConditionalKernelQuery.sourceTerm,
    ConditionalKernelQuery.sourceKernel, FiniteTableSCM.TermEquivalentAt,
    FiniteTableSCM.termDenote] using
      (ProbabilityResult.trans leftToFormula
        (ProbabilityResult.trans formulaInvariant
          (ProbabilityResult.symm rightToFormula)))

noncomputable def PublishedFiniteSourceCompleteness.toPublished
    (published : PublishedFiniteSourceCompleteness T G) :
    PublishedCompleteness (GraphModelClass.all G.interpret) where
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
        Nonempty (EncodedJointDerivation (GraphModelClass.all G.interpret)
          query)) /\
    (forall query,
      TypeTheoreticConditionalIdentifiable G.interpret query ->
        Nonempty (EncodedConditionalDerivation
          (GraphModelClass.all G.interpret) query)) /\
    (forall query, HedgeWitness G.interpret query ->
      Not (TypeTheoreticIdentifiable G.interpret query)) :=
  finite_causal_completeness_transport published.toPublished

theorem finiteSource_transported_joint_iff
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    TypeTheoreticIdentifiable G.interpret query <->
      Nonempty (EncodedJointDerivation (GraphModelClass.all G.interpret)
        query) :=
  transported_joint_iff complete.toPublished sound.toPublished query

theorem finiteSource_transported_conditional_iff
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    TypeTheoreticConditionalIdentifiable G.interpret query <->
      Nonempty (EncodedConditionalDerivation
        (GraphModelClass.all G.interpret) query) :=
  transported_conditional_iff complete.toPublished sound.toPublished query

end Causality
end Thesis
