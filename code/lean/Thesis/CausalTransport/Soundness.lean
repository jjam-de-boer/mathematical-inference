import Thesis.CausalTransport.SoundnessRules

namespace Thesis
namespace Causality

open Probability

/-!
Constructive ingredients for inhabiting the finite-source soundness interface.

This module proves the graph-independent probability-algebra leaves first.
The d-separation/global-Markov layer and the three causal rules are kept
separate so that each stage can be audited independently.  Empty-`W` rule 1
and empty-`W` rule 2 now inhabit their product-partition witnesses from
path d-separation and a projected graph: rule 2 uses open ancestral cores
in `G_{\overline{X}\underline{Z}}` so a directed `Z → Y` edge does not
identify the two cores.  For the general global-Markov step,
`ObservedGraph.moralLeftSide` computes the left component of the open
ancestral moral graph, and `FiniteLatentSCM.latentMoralLeftSide` lifts that
separator to the concrete latent coordinates of any compatible model;
shared-root incidence is proved unable to cross the partition.  Generic
agreement cylinders over left and right open ancestral regions are then
routed to complementary halves of the canonical independent latent product.
For rule 3, `Rule3GivenWFactorization` records the more delicate conditioned
case: a `W` factor shared with `Y` is retained on the selected roots, while
only the intervention-sensitive residual factors are separated.  Topological
local conditioning factors fix earlier `W` coordinates before reading each
equation, so conditioned non-colliders do not spuriously transmit latent
relevance into later factors.  Finite root reachability constructs the
`Y`-connected component; structural induction over its exact root walks now
proves that every common factor is locally intervention-invariant after earlier
conditioned coordinates have been fixed.  This closes general rule 3 without
the false requirement that conditioned `W` share no latent root with `Y`, and
without the overly coarse demand that every common node be invariant before
its conditioning prefix is fixed.  Rule 1 uses the analogous component in
`G_{̅X}`: projection transports the canonical moral-side label along every
exact root walk, proving that the `Y` component excludes all roots needed by
`Z`; its common and residual local factors therefore inhabit complementary
latent blocks.  Rule 2 uses the dual `Z`-generated component in
`G_{̅X̲Z}`.  Minimal directed routes place its seeds on the `Z` moral side;
factor-parent transport carries that label through every local `W` adjacency,
so path separation excludes every root needed by `Y`.  The three component
arguments assemble below into `ObservedGraph.publishedSoundness` without any
residual graph premise.
-/

/-!
# Public soundness assembly and compilation boundary

SoundnessFoundations, SoundnessRegions and SoundnessRules retain the original
constructive derivations in smaller compilation units. This module re-exports
their existing public names and keeps the published assemblers. The extraction
changes neither theorem statements nor proof bodies; the three independent
product lemmas simply live alongside their private finite-list helpers.
Kernel checking and the transitive axiom audit remain the gates.
-/


/--
All graph-dependent work for primitive soundness, stated before ratio algebra.
This is the target of the finite global-Markov/do-calculus proof.
-/
structure PathDoRuleCrossProductSoundness (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  crossProduct : forall {left right} (assignment : S.Assignment),
    PathDoRuleApplication G left right ->
      Kernel.CrossProductEquivalentAt model left right assignment

/-- Separate cross-product obligations for the three do-calculus rules. -/
structure PathDoRuleCrossProductLaws (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.CrossProductEquivalentAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.CrossProductEquivalentAt model
      (rule2Left x y z w) (rule2Right x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.CrossProductEquivalentAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment

/-- The three graph-dependent laws reduced to the canonical independent
latent product.  This is the input expected from the finite factor-graph
separation proof. -/
structure PathDoRuleProductCrossProductLaws (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule2Left x y z w) (rule2Right x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment

/-- The remaining graph layer may provide explicit latent partitions rather
than opaque kernel-level mass equalities.  Rules 1 and 2 use the stronger
conditional-independence shape.  Rule 3 uses general rectangular factors,
because its two conditioning cylinders live under different interventions
and need not be pointwise nested.  Rule 2 is oriented in reverse because its
composition proof naturally identifies the observational-action kernel as
the joint side of conditional independence. -/
structure PathDoRulePartitionWitnesses (G : ObservedGraph S)
    (model : FiniteLatentSCM S) where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment
  -- `rule3RectangularWitness_of_path_factorization` cases empty
  -- `Z`/`Y`/`W` and `Z(W) = Z` before using the common/residual `W`
  -- decomposition.  Unlike the older no-overlap leaf, this decomposition
  -- permits the ordinary latent dependence of nonempty `Y` and `W`.
  -- `rule1PartitionWitness_of_path_projected` closes rule 1 through the
  -- finite `Y`-connected component of topological local `W` factors.
  -- `rule2PartitionWitness_of_path_projected` closes rule 2 through the
  -- dual `Z`-generated component in `G_{̅X̲Z}`.  The older split-based
  -- constructors remain below as useful stronger compatibility interfaces.

/--
Assemble the three path-do-rule partition witnesses from path d-separation,
a projected graph, the remaining rule-1/rule-2 Bools, and the rule-3
common/residual factorization.

The rule-1/rule-2 Bools and the rule-3 factorization are required only on
queries that survive the cheap empty or one-sided branches inside the local
assemblers.  They are stated uniformly here so this package does not hide a
case split from its caller.
-/
def PathDoRulePartitionWitnesses.ofPathFactorizedRule3
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G)
    (hRule1Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedAncestralLatentsOverlap
        model G x y z w assignment = false)
    (hRule1Unsel : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedUnselectedMeetsZCore
        model G x y z w assignment = false)
    (hRule2Extra : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2WSplitSelectedClosedExtraLatent
        model G x z w assignment = false)
    (hRule2MeetsY : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2SelectedMeetsYAncestral
        model G x y z w assignment = false)
    (hRule3Factorization : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated G
        { removeIncoming :=
            NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
          removeOutgoing := NodeSet.empty }
        y z (NodeSet.union x w) →
      Kernel.Rule3GivenWFactorization model G x y z w assignment) :
    PathDoRulePartitionWitnesses G model where
  rule1 := fun x y z w assignment _disjoint separated =>
    Kernel.rule1PartitionWitness_of_path model G projected
      x y z w assignment separated
      (hRule1Overlap x y z w assignment separated)
      (hRule1Unsel x y z w assignment separated)
  rule2 := fun x y z w assignment disjoint separated =>
    Kernel.rule2PartitionWitness_of_path model G projected
      x y z w assignment disjoint separated
      (hRule2Extra x y z w assignment separated)
      (hRule2MeetsY x y z w assignment separated)
  rule3 := fun x y z w assignment disjoint separated =>
    Kernel.rule3RectangularWitness_of_path_factorization model G
      x y z w assignment disjoint separated
      (hRule3Factorization x y z w assignment separated)

/--
Specialize the factorized rule-3 assembler to the checked topological local
component.  This exposes one graph obligation for rule 3 rather than an
opaque event factorization: path separation must place every `Y`-connected
conditioning factor in the locally intervention-invariant `W` block obtained
after its earlier conditioning prefix has been fixed.
-/
def PathDoRulePartitionWitnesses.ofPathLocalConditionComponent
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G)
    (hRule1Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedAncestralLatentsOverlap
        model G x y z w assignment = false)
    (hRule1Unsel : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedUnselectedMeetsZCore
        model G x y z w assignment = false)
    (hRule2Extra : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2WSplitSelectedClosedExtraLatent
        model G x z w assignment = false)
    (hRule2MeetsY : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2SelectedMeetsYAncestral
        model G x y z w assignment = false)
    (hRule3CommonLocalInvariant : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated G
        { removeIncoming :=
            NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
          removeOutgoing := NodeSet.empty }
        y z (NodeSet.union x w) →
      NodeSet.Subset
        (Kernel.rule3WConditionCommon model G x y z w assignment)
        (Kernel.rule3WLocalInterventionInvariant G x z w)) :
    PathDoRulePartitionWitnesses G model :=
  PathDoRulePartitionWitnesses.ofPathFactorizedRule3 G model projected
    hRule1Overlap hRule1Unsel hRule2Extra hRule2MeetsY
    (fun x y z w assignment separated =>
      Kernel.Rule3GivenWFactorization.of_local_condition_component model G
        x y z w assignment
        (hRule3CommonLocalInvariant x y z w assignment separated))

/-- Assemble all three path-do-rule witnesses after closing rule 3 from the
projected graph.  Only the two explicit graph conditions for each of rules 1
and 2 remain; rule 3 is now derived directly from its published path
separation side condition and `FourWayDisjoint`. -/
def PathDoRulePartitionWitnesses.ofPathProjectedRule3
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G)
    (hRule1Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedAncestralLatentsOverlap
        model G x y z w assignment = false)
    (hRule1Unsel : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedUnselectedMeetsZCore
        model G x y z w assignment = false)
    (hRule2Extra : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2WSplitSelectedClosedExtraLatent
        model G x z w assignment = false)
    (hRule2MeetsY : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2SelectedMeetsYAncestral
        model G x y z w assignment = false) :
    PathDoRulePartitionWitnesses G model where
  rule1 := fun x y z w assignment _disjoint separated =>
    Kernel.rule1PartitionWitness_of_path model G projected
      x y z w assignment separated
      (hRule1Overlap x y z w assignment separated)
      (hRule1Unsel x y z w assignment separated)
  rule2 := fun x y z w assignment disjoint separated =>
    Kernel.rule2PartitionWitness_of_path model G projected
      x y z w assignment disjoint separated
      (hRule2Extra x y z w assignment separated)
      (hRule2MeetsY x y z w assignment separated)
  rule3 := fun x y z w assignment disjoint separated =>
    Kernel.rule3RectangularWitness_of_path_projected model G projected
      x y z w assignment disjoint separated

/-- Compatibility checkpoint after closing rules 1 and 3 from path separation
and the projected graph.  Its two explicit Rule 2 conditions preserve the
older split-based API; `ofPathProjected` below is the premise-free published
constructor. -/
def PathDoRulePartitionWitnesses.ofPathProjectedRule13
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G)
    (hRule2Extra : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2WSplitSelectedClosedExtraLatent
        model G x z w assignment = false)
    (hRule2MeetsY : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2SelectedMeetsYAncestral
        model G x y z w assignment = false) :
    PathDoRulePartitionWitnesses G model where
  rule1 := fun x y z w assignment disjoint separated =>
    Kernel.rule1PartitionWitness_of_path_projected model G projected
      x y z w assignment disjoint separated
  rule2 := fun x y z w assignment disjoint separated =>
    Kernel.rule2PartitionWitness_of_path model G projected
      x y z w assignment disjoint separated
      (hRule2Extra x y z w assignment separated)
      (hRule2MeetsY x y z w assignment separated)
  rule3 := fun x y z w assignment disjoint separated =>
    Kernel.rule3RectangularWitness_of_path_projected model G projected
      x y z w assignment disjoint separated

/-- Assemble all three path do-rule partition witnesses directly from path
d-separation and projected-graph compatibility.

Rules 1 and 3 use their respective finite local-factor components.  Rule 2
uses the `Z`-generated component closed through topological `W` factors; its
moral-route theorem places every `Y`-relevant root in the complementary
block.  Thus this constructor has no residual graph or semantic premise. -/
def PathDoRulePartitionWitnesses.ofPathProjected
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G) :
    PathDoRulePartitionWitnesses G model where
  rule1 := fun x y z w assignment disjoint separated =>
    Kernel.rule1PartitionWitness_of_path_projected model G projected
      x y z w assignment disjoint separated
  rule2 := fun x y z w assignment disjoint separated =>
    Kernel.rule2PartitionWitness_of_path_projected model G projected
      x y z w assignment disjoint separated
  rule3 := fun x y z w assignment disjoint separated =>
    Kernel.rule3RectangularWitness_of_path_projected model G projected
      x y z w assignment disjoint separated

/--
Compatibility assembler for the former rule-3 no-overlap premise.  New
clients should use `ofPathProjected`, which supplies all three rules without
extra graph premises. Path separation does not in general imply that `Y`
and conditioned `W` share no latent root.
-/
def PathDoRulePartitionWitnesses.ofPath
    (G : ObservedGraph S) (model : FiniteLatentSCM S)
    (projected : HasProjectedGraph model G)
    (hRule1Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedAncestralLatentsOverlap
        model G x y z w assignment = false)
    (hRule1Unsel : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.bar x) y z (NodeSet.union x w) →
      Kernel.rule1WSplitClosedUnselectedMeetsZCore
        model G x y z w assignment = false)
    (hRule2Extra : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2WSplitSelectedClosedExtraLatent
        model G x z w assignment = false)
    (hRule2MeetsY : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated
        G (.barUnderline x z) y z (NodeSet.union x w) →
      Kernel.rule2SelectedMeetsYAncestral
        model G x y z w assignment = false)
    (hRule3Overlap : forall (x y z w : NodeSet S)
      (assignment : S.Assignment),
      PathSpecification.PathDSeparated G
        { removeIncoming :=
            NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
          removeOutgoing := NodeSet.empty }
        y z (NodeSet.union x w) →
      Kernel.rule3YWLatentOverlap model G x y z w assignment = false) :
    PathDoRulePartitionWitnesses G model :=
  PathDoRulePartitionWitnesses.ofPathFactorizedRule3 G model projected
    hRule1Overlap hRule1Unsel hRule2Extra hRule2MeetsY
    (fun x y z w assignment separated =>
      Kernel.Rule3GivenWFactorization.of_no_overlap model G x y z w
        assignment (hRule3Overlap x y z w assignment separated))

def PathDoRulePartitionWitnesses.toProductCrossProductLaws
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (witnesses : PathDoRulePartitionWitnesses G model) :
    PathDoRuleProductCrossProductLaws G model where
  rule1 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule1 x y z w assignment disjoint separated).toCrossProduct
  rule2 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule2 x y z w assignment disjoint separated).toCrossProduct.symm
  rule3 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule3 x y z w assignment disjoint separated).toCrossProduct

def PathDoRuleProductCrossProductLaws.toDistributionLaws
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (laws : PathDoRuleProductCrossProductLaws G model) :
    PathDoRuleCrossProductLaws G model where
  rule1 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule1 x y z w assignment disjoint separated).toDistribution
  rule2 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule2 x y z w assignment disjoint separated).toDistribution
  rule3 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule3 x y z w assignment disjoint separated).toDistribution

/-- Package the three independently checkable laws as application soundness. -/
def PathDoRuleCrossProductLaws.toCrossProductSoundness
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (laws : PathDoRuleCrossProductLaws G model) :
    PathDoRuleCrossProductSoundness G model where
  crossProduct := by
    intro left right assignment application
    cases application with
    | rule1 x y z w disjoint sideCondition =>
        exact laws.rule1 x y z w assignment disjoint sideCondition
    | rule2 x y z w disjoint sideCondition =>
        exact laws.rule2 x y z w assignment disjoint sideCondition
    | rule3 x y z w disjoint sideCondition =>
        exact laws.rule3 x y z w assignment disjoint sideCondition

/-- Cross-product do-rule laws supply the semantic do-rule leaf. -/
noncomputable def PathDoRuleCrossProductSoundness.toDoRule
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (sound : PathDoRuleCrossProductSoundness G model)
    {left right : Kernel S} (assignment : S.Assignment)
    (application : PathDoRuleApplication G left right)
    (_leftSupported : ProbabilityTerm.SupportedAt model (.kernel left) assignment)
    (_rightSupported : ProbabilityTerm.SupportedAt model (.kernel right) assignment) :
    ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
      assignment := by
  simpa only [ProbabilityTerm.denote] using
    (sound.crossProduct assignment application).denote
      _leftSupported _rightSupported

/-- Assemble all primitive laws once the graph-dependent do-rule leaf is supplied. -/
noncomputable def PathPrimitiveSoundness.ofDoRule
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (doRuleSound : ∀ {left right} (assignment : S.Assignment),
      PathDoRuleApplication G left right ->
        ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
        ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
        ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
          assignment) :
    PathPrimitiveSoundness G model where
  doRule := doRuleSound
  marginalization := by
    intro x y z w assignment disjoint leftSupported rightSupported
    exact ProbabilityTerm.marginalization_soundAt model x y z w assignment
      disjoint leftSupported rightSupported
  conditioning := by
    intro x y z w assignment _ leftSupported rightSupported
    exact ProbabilityTerm.conditioning_soundAt model x y z w assignment
      leftSupported rightSupported
  chain := by
    intro x y z w assignment _ leftSupported rightSupported
    exact ProbabilityTerm.chain_soundAt model x y z w assignment
      leftSupported rightSupported

/-- Compile path-based primitive semantics to executable rule syntax using the
proved algorithm-to-path implication.  The converse (path to algorithm) is
inhabited as `ObservedGraph.dSeparationCorrectness` and is used by
`PublishedSoundness`, not by semantic soundness of an executable derivation.
-/
def PathPrimitiveSoundness.compileChecked
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (semantics : PathPrimitiveSoundness G model) :
    LocalPrimitiveSoundness G model where
  doRule := by
    intro left right assignment application leftSupported rightSupported
    exact semantics.doRule assignment application.toPathChecked
      leftSupported rightSupported
  marginalization := semantics.marginalization
  conditioning := semantics.conditioning
  chain := semantics.chain

/-- Assemble executable primitive soundness directly from the three path
cross-product laws, without assuming full d-separation completeness. -/
noncomputable def LocalPrimitiveSoundness.ofPathCrossProductLaws
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (laws : PathDoRuleCrossProductLaws G model) :
    LocalPrimitiveSoundness G model :=
  (PathPrimitiveSoundness.ofDoRule model G
    laws.toCrossProductSoundness.toDoRule).compileChecked

/--
Soundness package for executable derivations.  Unlike `PublishedSoundness`,
this needs only the proved algorithm-to-path implication; the reverse
direction remains relevant to compiling published path certificates, not to
semantic soundness of an executable derivation.
-/
structure CheckedSoundness (S : ObservedSignature)
    (G : ObservedGraph S) where
  pathPrimitive : forall model : ExactModel S,
    Compatible model G -> PathPrimitiveSoundness G model

def CheckedSoundness.primitive (sound : CheckedSoundness S G)
    (model : ExactModel S) (compatible : Compatible model G) :
    LocalPrimitiveSoundness G model :=
  (sound.pathPrimitive model compatible).compileChecked

/-- Construct the executable package from the remaining global-Markov
cross-product laws. -/
noncomputable def CheckedSoundness.ofCrossProductLaws
    (G : ObservedGraph S)
    (laws : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductLaws G model) :
    CheckedSoundness S G where
  pathPrimitive := by
    intro model compatible
    exact PathPrimitiveSoundness.ofDoRule model G
      (laws model compatible).toCrossProductSoundness.toDoRule

/-- Assemble executable soundness from explicit graph-derived latent
partition witnesses. -/
noncomputable def CheckedSoundness.ofPartitionWitnesses
    (G : ObservedGraph S)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    CheckedSoundness S G :=
  CheckedSoundness.ofCrossProductLaws G (fun model compatible =>
    (witnesses model compatible).toProductCrossProductLaws.toDistributionLaws)

/-- Transport target primitive soundness back to the finite source semantics. -/
noncomputable def PathPrimitiveSoundness.toFiniteSource
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {model : FiniteTableSCM T}
    (semantics : PathPrimitiveSoundness G.interpret model.interpret) :
    FiniteSourcePathPrimitiveSoundness G model where
  doRule := by
    intro left right assignment application leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.doRule assignment application
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  marginalization := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.marginalization x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  conditioning := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.conditioning x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  chain := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.chain x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)

/--
The checked constructor isolates the two remaining graph-dependent obligations:
correctness of executable d-separation and semantic validity of a path do-rule.
-/
noncomputable def PublishedSoundness.ofDSeparationDoRule
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (doRuleSound : ∀ (model : ExactModel S), Compatible model G ->
      ∀ {left right} (assignment : S.Assignment),
        PathDoRuleApplication G left right ->
          ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
          ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
          ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
            assignment) :
    PublishedSoundness S G where
  dseparation := correct
  pathPrimitive := by
    intro model compatible
    exact PathPrimitiveSoundness.ofDoRule model G
      (doRuleSound model compatible)

/-- Assemble published soundness from raw global-Markov cylinder equalities. -/
noncomputable def PublishedSoundness.ofDSeparationCrossProduct
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (crossProductSound : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductSoundness G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationDoRule G correct (by
    intro model compatible left right assignment application
      leftSupported rightSupported
    exact (crossProductSound model compatible).toDoRule assignment application
      leftSupported rightSupported)

/-- Published soundness assembled from three separately proved cross-product laws. -/
noncomputable def PublishedSoundness.ofDSeparationCrossProductLaws
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (laws : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductLaws G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationCrossProduct G correct
    (fun model compatible =>
      (laws model compatible).toCrossProductSoundness)

/-- Assemble published soundness from explicit graph-derived latent
partitions plus the complete d-separation correctness theorem. -/
noncomputable def PublishedSoundness.ofDSeparationPartitionWitnesses
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationCrossProductLaws G correct
    (fun model compatible =>
      (witnesses model compatible).toProductCrossProductLaws.toDistributionLaws)

/--
Published soundness from a path do-rule, using the inhabited d-separation
correctness theorem.  The remaining obligation is global-Markov soundness
of the three rules on compatible models.
-/
noncomputable def PublishedSoundness.ofDoRule
    (G : ObservedGraph S)
    (doRuleSound : ∀ (model : ExactModel S), Compatible model G ->
      ∀ {left right} (assignment : S.Assignment),
        PathDoRuleApplication G left right ->
          ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
          ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
          ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
            assignment) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationDoRule G G.dSeparationCorrectness doRuleSound

/--
Published soundness from graph-derived latent partitions, using the
inhabited d-separation correctness theorem.  The remaining obligation is
the three do-rule partition witnesses on compatible models.
-/
noncomputable def PublishedSoundness.ofPartitionWitnesses
    (G : ObservedGraph S)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationPartitionWitnesses G
    G.dSeparationCorrectness witnesses

/-- The constructive published soundness theorem for an arbitrary finite
observed ADMG.

Compatibility supplies exactly the projected-graph equality used by the
three graph-to-latent partition arguments.  The preceding premise-free
assembler proves all path do-rules; the generic probability-algebra layer
then supplies marginalization, conditioning, and chain multiplication. -/
noncomputable def ObservedGraph.publishedSoundness
    (G : ObservedGraph S) : PublishedSoundness S G :=
  PublishedSoundness.ofPartitionWitnesses G (fun model compatible =>
    PathDoRulePartitionWitnesses.ofPathProjected G model compatible.2)

/-- A generic soundness package specializes constructively to finite source tables. -/
noncomputable def PublishedSoundness.toFiniteSource
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (sound : PublishedSoundness T.toObserved G.interpret) :
    PublishedFiniteSourceSoundness T G where
  dseparation := sound.dseparation
  pathPrimitive := by
    intro model compatible
    apply PathPrimitiveSoundness.toFiniteSource
    exact sound.pathPrimitive model.interpret
      ((finiteSourceCompatible_iff model G).mp compatible)

/-- Finite-source package assembled from the three target mass laws. -/
noncomputable def PublishedFiniteSourceSoundness.ofDSeparationCrossProductLaws
    {T : FiniteTableSignature} (G : FiniteTableGraph T)
    (correct : DSeparationCorrectness G.interpret)
    (laws : forall (model : ExactModel T.toObserved),
      Compatible model G.interpret ->
        PathDoRuleCrossProductLaws G.interpret model) :
    PublishedFiniteSourceSoundness T G :=
  (PublishedSoundness.ofDSeparationCrossProductLaws
    G.interpret correct laws).toFiniteSource

end Causality
end Thesis
