import Thesis.Probability.Core
import Thesis.Probability.ConstructivePermutation
import Thesis.Probability.Reindexing
import Thesis.Probability.FiniteCellProduct
import Thesis.Probability.Urn
import Thesis.Probability.QualitativeUrn
import Thesis.Probability.FiniteRecord
import Thesis.Probability.Construction

/-!
Stable facade for the finite constructive probability development.

This facade imports the complete public probability API, whose implementation
is split by responsibility.

Reading order:

1. `Core` defines Boolean decidable events, finite inspection, elementary
   finite counting, and the cross-multiplication order on `QProb`;
2. `ConstructivePermutation` reconstructs list permutations from decidable
   occurrence counts without choice;
3. `Reindexing` records the additive-carrier finite-sum permutation theorem
   and its `Nat` and `QProb` specializations;
4. `FiniteCellProduct` constructs finite product cells and verifies rectangular
   event counts;
5. `Urn` presents probability as a finite urn and proves its elementary laws;
6. `QualitativeUrn` derives the finite qualitative ratio representation from
   an event-level plausibility interface;
7. `FiniteRecord` gives weighted, common-denominator finite distributions and
   conditioning; and
8. `Construction` builds finite dependent products and the rational
   constructions used by causal models.

No result here concerns countable additivity or arbitrary propositions:
events are explicit Boolean predicates on finite enumerations.
-/
