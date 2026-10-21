import Thesis.CausalTransport.CompletenessHedgeCountermodels

/-!
# Historical completeness compatibility facade

This import preserves the original certificate constructors, legacy control-flow
and failure proofs, shared graph machinery and locally qualified countermodels.
The legacy engine's successful outputs are not generally sound: the retained
positive front-door regression refutes that claim. Its checked trace and failure
facts remain useful historical results, not an alternative supported ID API.

Current clients should import the focused implementation that they use. In
particular, `Hedge.ReadoutGeometry` and `Hedge.Models` provide shared graph and
parity mathematics without the legacy failure-stack dependencies. This facade
deliberately keeps the complete old import surface for existing clients and
mandatory historical build and axiom-verification coverage.

The completed positive-class `PublishedCompleteness` package is constructed in
`HedgeChannelCompleteness`, using `identifyJointKernel` and
`identifyConditionalKernel`. `KernelSuccessCompilation` and
`KernelFailureExtraction` prove their structural success and failure results;
`ConditionalFailureExtraction` handles conditional exchange traces, and the
channel countermodel modules establish original-query separation. Native hidden
DAG transfer and supported-zero qualifications are described in
`lean/THEOREM_COVERAGE.md`; no local ready-case theorem silently replaces those
published statements.

The earlier detailed development inventory is preserved verbatim in
`lean/docs/history/completeness-development.md`. Its historical obligations
must not be read as current open gaps or a roadmap for deeper failure stacks.
-/
