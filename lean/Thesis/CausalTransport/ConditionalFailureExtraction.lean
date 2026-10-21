import Thesis.CausalTransport.ConditionalFailureCore
import Thesis.CausalTransport.ConditionalFailureCarrierCases

/-!
# Compatibility imports for conditional failure transport

`ConditionalFailureCore` contains the unchanged general IDC failure extraction,
exchange traces, denominator-agreement transport and terminal assembly. Current
universal completeness modules import that focused core directly.

The separately qualified carrier case remains in
`ConditionalFailureCarrierCases`. This facade reexports both developments,
preserving all original declarations and import compatibility. Both remain
covered by the complete build and the transitive axiom audit.
-/
