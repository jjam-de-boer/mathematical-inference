import Thesis.Causality.Graph
import Thesis.Causality.Derivation
import Thesis.Causality.Model
import Thesis.Causality.SelectedAssignment
import Thesis.Causality.HardIntervention
import Thesis.Causality.Identification
import Thesis.Causality.LocalEventComparison
import Thesis.Causality.PrivateNoise
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
`SelectedAssignment` constructs duplicate-free finite presentations of values
on a selected coordinate set, using canonical projection rather than chosen
representatives.  `ConditionalUniqueness` applies the two-way normalization
theorem to actual positive causal kernels at a fixed intervention.  Agreement
on both conditional directions forces joint-numerator agreement even when
the conditioning marginals differ; graph compatibility and soundness are
not needed for this intrinsic semantic argument.
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
