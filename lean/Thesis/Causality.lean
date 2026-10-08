import Thesis.Causality.Graph
import Thesis.Causality.Derivation
import Thesis.Causality.Model
import Thesis.Causality.SelectedAssignment
import Thesis.Causality.HardIntervention
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
import Thesis.Causality.IdentificationSearch
import Thesis.Causality.HedgeSelectionSearch
import Thesis.Causality.ConditionalUniqueness
import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.Causality.IdentificationInduction
import Thesis.Causality.Reductions
import Thesis.Causality.LatentRationalCPT
import Thesis.Causality.LatentTableResponse
import Thesis.Causality.LatentTableCounterexample
import Thesis.Causality.CompactHiddenDAG
import Thesis.Causality.PairRoot
import Thesis.Causality.Semantics
import Thesis.Causality.ProbabilityTermEquality
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
Stable facade for the finite causal, modal, and counterfactual development.

Suggested reading order for a reader familiar with the thesis but new to the
source is `Graph`, `Derivation`, `Model`, `HardIntervention`, `Reductions`,
`CompactHiddenDAG`, `PairRoot`, `Semantics`, `Identification`, and
`IdentificationSearch`; `HedgeSelectionSearch` exhaustively scans alternative
forest selections with an additional Boolean requirement tested before
accepting a leaf.  Its candidate-completeness theorem is independent of
countermodel semantics and does not assert universal geometric coverage.
`IdentificationInduction` supplies exact structural
traces for failed, successful, and unfinished arbitrary nested ID runs; then
`IdentificationKernel` provides the replacement current-kernel recursion,
separating ordinary ancestral pruning from action augmentation and retaining
the actual recursive input when extracting chain factors; then
`ConditionalIdentificationKernel` performs arbitrary finite sequences of IDC
rule-2 conditioner promotions and delegates its terminal joint call to that
corrected engine; then
`Modalities` and `Structural`; then
`Counterfactual`, `Multiworld`, and the modules below `ExecutedMultiworld`.
`ModalRealization` and `ModalCounterfactual` connect the executable edit paths
back to query semantics. `ModeTheory` names the existing one-shots as
morphisms and the edit paths as a 1-category of named states.
`ProbabilityTermEquality` supplies explicit finite syntax comparison for
node selections, kernels, and complete expressions, without deciding
denotational equivalence or using classical function equality.
The facade excludes the external completeness
interfaces; those begin in `Thesis.CausalTransport`.
`HedgeQuery` retains a hedge's actual forests and action seed while reindexing
it at an outcome containing every common root.  An explicit root supplies the
new outcome seed; this graph-only adapter does not assume a countermodel.
Its outside-coordinate lemma also exposes the common roots' containment in
the large forest, used to derive conditioner avoidance in routed constructions.
`KernelConditioning` identifies an actual conditional kernel with the
genuinely conditioned latent prior under its own reference-compatible action.
Its support proof uses intrinsic observational positivity and finite SCM
consistency, not do-calculus soundness or a selected latent realization.
`ConditionalCounterexampleWitness` finds an actual separated supported kernel
cell in any positive countermodel by finite assignment search.  It returns
the reference and both rational values as data without converting a
propositional existence claim into a chosen assignment.
`SelectedAssignment` constructs duplicate-free finite presentations of values
on a selected coordinate set, using canonical projection rather than chosen
representatives.  `ConditionalUniqueness` applies the two-way normalization
theorem to actual positive causal kernels at a fixed intervention.  Agreement
on both conditional directions forces joint-numerator agreement even when
the conditioning marginals differ; graph compatibility and soundness are
not needed for this intrinsic semantic argument.
`CoordinateAssignment` gives the complementary compact dependent-product
presentation, with exactly one coordinate per selected observed node.  Its
restriction, background-preserving extension, and omitted-coordinate cylinders
connect full-coordinate conditional comparison to the actual interventional
SCM law.  Support is derived only on action-free selected coordinates, not
falsely asserted for every complete intervened assignment.
`LocalEventComparison` turns equality of selected-coordinate cylinders into
equality of every local event, using the signature's default values and finite
assignment enumeration.  The compared records need not share atoms, weights,
or rational denominators; no representative or proof family is chosen.
`PrivateNoise` appends a genuinely private Boolean latent coordinate with a
checked independent product prior.  Its common observable readout theorem
preserves full observed-law equality under explicit non-influence, and earlier
replacements preserve the later-coordinate invariant needed by a finite
topologically ordered readout construction.  The separate restoring argument
preserves strict positivity without non-influence: a supported fresh bit can
restore the old pivot value even when other mechanisms respond to that pivot.
`PrivateNoiseNonInfluence` supplies the complementary mechanism-level check:
a replacement respecting parent agreement away from an ignored coordinate
preserves that coordinate's non-influence, even when the ambient signature
allows an incoming edge which the actual replacement does not read.
`PrivateNoiseResponse` extends that restoring argument to typed replacements
depending on incident latent inputs.  Its separate observable-response bridge
preserves whole-law equality only when the actual replacement response is
proved to be a common function of the old observed assignment and noise.
`SharedNoise` reuses the independent typed product encoding while feeding the
fresh bit to a displayed pair.  Canonical semi-Markovian structure and every
projected edge are preserved when that pair is already bidirected-connected;
coincident pivots recover the private boundary without a reflexive edge.
`SharedNoiseSemantics` proves exact evaluation under arbitrary interventions
and full observed-law preservation when both base pivots are ignored.  Shared
readout positivity requires an explicit bit restoring both full values; graph
conservation alone is not mistaken for that support property.
`PrivateNoiseClosure` supplies the more local protected-mechanism invariant:
selected rows read only selected parent values, while unprotected descendants
may respond to a replaced row.  Off-set replacements preserve full protected
values and interventional event probabilities without ordering, noise-support,
or bias conditions.  Finite readout folds use that invariant to retain the
actual conditioning denominator of a routed countermodel.
`ValueRefinement` adds an independent private label sweep for mechanisms
depending only on declared parent bits.  Positive decoded atoms become a
strictly positive full-alphabet law, while whole observed-law equality and
every bit-dependent interventional probability are retained.  It does not
construct the missing unrestricted binary hedge countermodel.
`BinaryEncoding` accepts ordinary Boolean-valued SCMs on the same graph and
proves those parent-bit and decoded-support hypotheses automatically.  The
deterministic encoding and private support sweep remain separate, so an
encoded binary model is not incorrectly claimed to have full label support.
`LatentRationalCPT` realizes finite rational local tables with supplied shared
sources as actual SCMs.  Private response functions retain the exact projected
graph.  Their full interventional likelihood theorem integrates the genuine
product prior, without enumerating those potentially large private function
spaces; a supported shared assignment and positive local rows supply full
observed positivity.  Particular table pairs still need their observational
equality and original-query gap before they give a counterexample.
`LatentTableResponse` isolates a selected non-action row from the full
likelihood, retaining all shared masses and responding descendant factors.
Balanced nonnegative perturbation parts cancel exactly when the two profile
responses agree, even with zero environment factors. `LatentTableCounterexample`
constructs positive normalized profiles from raw balanced weights and turns
factual response cancellation and an original-query response gap into actual
positive countermodels. Conditional separation retains the same models'
two conditioning denominators and proves common support intrinsically.
These constructions impose no routing or binary-alphabet hypothesis; they
do not prove the remaining existence of suitable directions for every hedge
or irreducible conditional failure.
-/
