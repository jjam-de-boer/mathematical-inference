import Thesis.Probability.Core
import Thesis.Probability.Urn
import Thesis.Probability.FiniteRecord
import Thesis.Probability.Construction

/-!
Stable facade for the finite constructive probability development.

The implementation is split by responsibility while existing imports of
`Thesis.Probability` continue to expose the complete public API.

Reading order:

1. `Core` defines Boolean decidable events, finite inspection, and elementary
   finite counting;
2. `Urn` presents probability as a finite urn and proves its elementary laws;
3. `FiniteRecord` gives weighted, common-denominator finite distributions and
   conditioning; and
4. `Construction` builds finite dependent products and the rational
   constructions used by causal models.

No result here concerns countable additivity or arbitrary propositions:
events are explicit Boolean predicates on finite enumerations.
-/
