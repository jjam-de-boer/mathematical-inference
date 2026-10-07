import Thesis.Probability.Core
import Thesis.Probability.Combinatorics
import Thesis.Probability.ConstructivePermutation
import Thesis.Probability.Reindexing
import Thesis.Probability.FiniteCellProduct
import Thesis.Probability.Urn
import Thesis.Probability.QualitativeUrn
import Thesis.Probability.FiniteRecord
import Thesis.Probability.FiniteProductReindex
import Thesis.Probability.FiniteRecordSlicing
import Thesis.Probability.FiniteRecordPerturbation
import Thesis.Probability.FiniteLinearResponse
import Thesis.Probability.ConditionalUniqueness
import Thesis.Probability.BooleanNoise
import Thesis.Probability.ColliderChannel
import Thesis.Probability.Construction
import Thesis.Probability.FiniteProductResponse
import Thesis.Probability.Distros

/-!
Stable facade for the finite constructive probability development.

This facade imports the complete public probability API, whose implementation
is split by responsibility.

Reading order:

1. `Core` defines Boolean decidable events, finite inspection, elementary
   finite counting, and the cross-multiplication order on `QProb`;
2. `Combinatorics` records finite Nat identities used by named distros;
3. `ConstructivePermutation` reconstructs list permutations from decidable
   occurrence counts without choice;
4. `Reindexing` records the additive-carrier finite-sum permutation theorem
   and its `Nat` and `QProb` specializations;
5. `FiniteCellProduct` constructs finite product cells and verifies rectangular
   event counts;
6. `Urn` presents probability as a finite urn and proves its elementary laws;
7. `QualitativeUrn` derives the finite qualitative ratio representation from
   an event-level plausibility interface;
8. `FiniteRecord` gives weighted, common-denominator finite distributions and
   conditioning; `FiniteProductReindex` swaps and reassociates independent
   weighted records for arbitrary mixed events, not only rectangles;
   `FiniteRecordSlicing` sums arbitrary events over a finite
   projection's disjoint fibres without enumerating or selecting the source
   values; `FiniteRecordPerturbation` builds strictly positive normalized
   record pairs from raw balanced natural weights, including repeated labels;
   `FiniteLinearResponse` proves exact cancellation and separation criteria
   against a fixed finite rational environment without subtraction or division
   by its coefficients; `ConditionalUniqueness` proves that positive joint laws
   agreeing in both conditional directions agree on every joint event,
   without assuming equal conditioning marginals;
9. `BooleanNoise` proves finite biased XOR-channel injectivity, exact parity
   bias through independent flips, and support restoration without real-valued
   limiting arguments; `ColliderChannel` constructs an independent fair parent
   and noisy collider, proving exact posterior laws, full supported-noise
   readout support, and bias-dependent gap preservation even when the two
   source contexts have unequal conditioning probabilities;
10. `Construction` builds finite dependent products and the rational
   constructions used by causal models; `FiniteProductResponse` isolates one
   factor while retaining all other factors, including zeros; and
11. `Distros` packages named finite distros (Bernoulli, binomial, lattice
    Gaussian, and the finite counterparts of the classical limiting
    families).

No result here concerns countable additivity or arbitrary propositions:
events are explicit Boolean predicates on finite enumerations.
-/
