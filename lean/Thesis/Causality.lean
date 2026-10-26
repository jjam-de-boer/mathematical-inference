import Thesis.Causality.Graph
import Thesis.Causality.NodeSetCardinality
import Thesis.Causality.NodeSetEnumeration
import Thesis.Causality.Derivation
import Thesis.Causality.Model
import Thesis.Causality.SelectedAssignment
import Thesis.Causality.SelectedEntropy
import Thesis.Causality.HardIntervention
import Thesis.Causality.SharedResponseTables
import Thesis.Causality.SharedResponseModel
import Thesis.Causality.Identification
import Thesis.Causality.HedgeQuery
import Thesis.Causality.KernelConditioning
import Thesis.Causality.ConditionalCounterexampleWitness
import Thesis.Causality.CoordinateAssignment
import Thesis.Causality.LocalEventComparison
import Thesis.Causality.PrivateNoise
import Thesis.Causality.PrivateNoiseNonInfluence
import Thesis.Causality.PrivateNoiseResponse
import Thesis.Causality.SharedNoise
import Thesis.Causality.SharedNoiseSemantics
import Thesis.Causality.PrivateNoiseClosure
import Thesis.Causality.ValueRefinement
import Thesis.Causality.BinaryEncoding
import Thesis.Causality.BinaryRecoding
import Thesis.Causality.ValueRefinementConditional
import Thesis.Causality.ValueRefinementMarginal
import Thesis.Causality.IdentificationSearch
import Thesis.Causality.ComponentConnectivity
import Thesis.Causality.ReachabilityCorrectness
import Thesis.Causality.IdentificationRank
import Thesis.Causality.HedgeSelectionSearch
import Thesis.Causality.ConditionalUniqueness
import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.Causality.Reductions
import Thesis.Causality.HiddenPathSearch
import Thesis.Causality.HiddenCommonCauseSearch
import Thesis.Causality.LatentRationalCPT
import Thesis.Causality.LatentTableResponse
import Thesis.Causality.LatentTableBlockResponse
import Thesis.Causality.LatentTableCounterexample
import Thesis.Causality.CompactHiddenDAG
import Thesis.Causality.LatentRootDAG
import Thesis.Causality.LatentRootProjection
import Thesis.Causality.CliqueRootGraph
import Thesis.Causality.LatentRootGrouping
import Thesis.Causality.PairRoot
import Thesis.Causality.PairRootUniqueness
import Thesis.Causality.PairRootChannels
import Thesis.Causality.PairRootChannelsEnvironment
import Thesis.Causality.Semantics
import Thesis.Causality.SupportAwareSemantics
import Thesis.Causality.ProbabilityStatus
import Thesis.Causality.SupportAwareTerms
import Thesis.Causality.ObservationalSupport
import Thesis.Causality.AlmostSureIntervention
import Thesis.Causality.ConsistencyBounds
import Thesis.Causality.BinaryBowModel
import Thesis.Causality.BinaryBowEndpoints
import Thesis.Causality.BinaryBowMixture
import Thesis.Causality.BinaryInstrumental.Profiles
import Thesis.Causality.BinaryInstrumental.Coupling
import Thesis.Causality.BinaryInstrumental.Transportation
import Thesis.Causality.BinaryInstrumental.RiskEvents
import Thesis.Causality.BinaryInstrumental.Response
import Thesis.Causality.BinaryInstrumental.Model
import Thesis.Causality.Admissibility
import Thesis.Causality.UsedConditionalAdmissibility
import Thesis.Causality.SupportAwareKernelAlgebra
import Thesis.Causality.PositiveDerivationSupport
import Thesis.Causality.ProbabilityTermEquality
import Thesis.Causality.ProbabilityTermCode
import Thesis.Causality.DerivationCode
import Thesis.Causality.DerivationLinearization
import Thesis.Causality.ProbabilityTermEnumeration
import Thesis.Causality.DerivationEnumeration
import Thesis.Causality.CodeEnumerationCounts
import Thesis.Causality.CodeSearchPreflight
import Thesis.Causality.CodeSearchMetadata
import Thesis.Causality.ModalDerivation
import Thesis.Causality.Modalities
import Thesis.Causality.ConservativeLearning
import Thesis.Causality.Forgetting
import Thesis.Causality.Structural
import Thesis.Causality.EndpointSemantics
import Thesis.Causality.Counterfactual
import Thesis.Causality.Multiworld
import Thesis.Causality.ExecutedMultiworld
import Thesis.Causality.ModalRealization
import Thesis.Causality.ModalCounterfactual
import Thesis.Causality.EndpointAgreement
import Thesis.Causality.ModeTheory

/-!
# Finite causal syntax, models and executed states

This facade reexports causal foundations. Semantic soundness and
identification completeness are assembled in `Thesis.CausalTransport`.
Implementations should import focused foundational modules.

## Queries and identification programs

A useful reading order is `Graph`, `Derivation`, `Model`, `SelectedEntropy`, `HardIntervention`,
`Semantics`, `SupportAwareSemantics` and `Identification`.
These define graph operations, kernel queries, interventions, probability
terms and their partial interpretation. Defined zero and an undefined
conditional remain distinct.

`IdentificationKernel` implements current-kernel joint ID;
`ConditionalIdentificationKernel` implements IDC by repeated conditioner
exchange and a terminal joint call. `IdentificationSearch`,
`IdentificationRank` and their graph/search companions prove structural
properties and termination. The incorrect old recursion survives only in
`Examples.IdentificationRegression` as a checked negative example.

## Finite structural constructions

`CompactHiddenDAG`, `LatentRootDAG`, `PairRoot*`, `CliqueRootGraph` and
`LatentRootGrouping` describe finite hidden structures and actual independent
source encodings. `PrivateNoise*`, `SharedNoise*`, `ValueRefinement*` and
`LatentTable*` provide local countermodel constructions. Their statements
retain the required mechanism, support and observed-law conditions.

`BinaryBow*` and `BinaryInstrumental.Profiles` through
`BinaryInstrumental.Model` own the corresponding graph and response-model
foundations. Native bounds and classification belong to causal transport.

`ProbabilityTermCode`, `DerivationCode` and their enumeration companions
separate checked finite syntax from semantic interpretation.
`DerivationLinearization` preserves an existing proof's endpoints.
Admission checks retain their explicitly bounded catalogue; native support
checking is supplied downstream.

## Modal, counterfactual and mode-theory interfaces

`Modalities`, `Structural` and `EndpointSemantics` describe actual edit paths,
current beliefs and accumulated interventions. `ModalRealization`,
`ModalCounterfactual` and `EndpointAgreement` connect executions to queries.
`ModeTheory` packages the named states and paths.

`Counterfactual`, `Multiworld` and `ExecutedMultiworld` own finite
counterfactual and shared-noise world evaluation. Their model classes,
support conditions and world-family hypotheses are stated at those owners.
-/
