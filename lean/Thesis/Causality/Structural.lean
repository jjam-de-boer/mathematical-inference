import Thesis.Causality.Structural.Links
import Thesis.Causality.Structural.Learning
import Thesis.Causality.Structural.SurgeryCore
import Thesis.Causality.Structural.Core
import Thesis.Causality.Structural.Atomic
import Thesis.Causality.Structural.Surgery

/-!
Stable facade for proof-carrying structural edits.

`Links` and `Learning` provide the primitive typed changes to a causal record.
`SurgeryCore` is the compact reference construction for a hard intervention.
`Core` composes those primitives into the public causal-edit vocabulary;
despite its historic name, it is an orchestration layer rather than the lowest
dependency layer.  `Atomic` expands a compact intervention into constant
setting, directed-cut, latent-cut, and probability-endpoint phases.
`Surgery` is retained as a compatibility facade for the theorem comparing the
compact and atomic presentations.
-/
