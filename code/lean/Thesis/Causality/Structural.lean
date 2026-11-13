import Thesis.Causality.Structural.Links
import Thesis.Causality.Structural.Learning
import Thesis.Causality.Structural.SurgeryCore
import Thesis.Causality.Structural.Core
import Thesis.Causality.Structural.Commit
import Thesis.Causality.Structural.Atomic
import Thesis.Causality.Structural.AtomicExecution
import Thesis.Causality.Structural.Surgery

/-!
Stable facade for proof-carrying structural edits.

`Links` and `Learning` provide the primitive typed changes to a causal record.
`SurgeryCore` is the compact reference construction for a hard intervention.
`Core` composes those primitives into the public causal-edit vocabulary.
`Atomic` expands a compact intervention into constant-setting, directed-cut,
and latent-cut phases. `AtomicExecution` supplies coordinate transport and
probability-bearing endpoint closures.
`Surgery` exposes the comparison between the compact and atomic presentations.
-/
