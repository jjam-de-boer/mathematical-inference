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
import Thesis.Probability.FiniteSignedMass
import Thesis.Probability.FiniteSignedProduct
import Thesis.Probability.FiniteProductBlocks
import Thesis.Probability.FinitePowerProduct
import Thesis.Probability.FiniteUniformProduct
import Thesis.Probability.FiniteProductSupport
import Thesis.Probability.FiniteSupportedSum
import Thesis.Probability.ConditionalUniqueness
import Thesis.Probability.FiniteProductConditionals
import Thesis.Probability.BooleanNoise
import Thesis.Probability.BooleanChannelTable
import Thesis.Probability.BooleanChannelExpansion
import Thesis.Probability.ConditionalNoise
import Thesis.Probability.ColliderChannel
import Thesis.Probability.ColliderRealization
import Thesis.Probability.Construction
import Thesis.Probability.FiniteProductResponse
import Thesis.Probability.FiniteProductBalance
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
   by its coefficients; `FiniteSignedMass` provides exact integer-valued
   integrands over the same nonnegative weighted atoms, and
   `FiniteSignedProduct` expands complete finite products and integrates
   rectangular integrands against the actual independent product record.
   It also separates scalar coefficients from Boolean characters and relates
   their complete product to an explicitly indexed finite XOR fold.
   These auxiliary integer integrands do not introduce signed probability
   records or replace natural-weight probability semantics;
   `FiniteUniformProduct` identifies the literal unit-weight atoms and
   denominators of independent products, and transports all mixed event
   masses and signed integrands through explicit support permutations;
   `FiniteProductSupport` characterizes membership in restricted dependent
   choice products by their actual coordinate lists; `FiniteSupportedSum`
   deletes only proved-zero integer terms after checking inclusion and
   duplicate-freeness of the complete and canonical lists;
   `FiniteProductBlocks` splits literal numerator and denominator products
   across an actual shared prefix and private suffix, retaining zero cells;
   `FinitePowerProduct` identifies exact anchored and binary-mask natural
   products with their finite powers, without choosing an anchor or assuming
   a mask cardinal instead of counting its actual finite indices;
   `ConditionalUniqueness` proves that positive joint laws
   agreeing in both conditional directions agree on every joint event,
   without assuming equal conditioning marginals; `FiniteProductConditionals`
   proves the full-coordinate counterpart on arbitrary finite dependent
   products and returns a separated coordinate conditional by finite search
   whenever a joint event differs;
9. `BooleanNoise` proves normalized complement equality for independently
   presented records, finite biased XOR-channel injectivity, exact parity
   bias through independent flips, and support restoration without real-valued
   limiting arguments; `BooleanChannelTable` constructs positive normalized
   rows from finitely many natural-weight channel signals, with a fixed
   signal-independent capacity and exact two-sided deviation from a fair row;
   `BooleanChannelExpansion` relates their complete character expansion to
   actual row-product numerators, retaining interactions and respecting hard
   interventions with their actual forced-value indicators;
   its hidden-independent local coefficients retain forced zero terms before
   the causal channel construction groups complete monomials;
   `ConditionalNoise` retains the full mixed-event law
   after independent noise is conditioned on source-only evidence.  Its XOR
   transport uses each source's actual evidence mass rather than a common
   denominator; `ColliderChannel` constructs an independent fair parent
   and noisy collider, proving exact posterior laws, full supported-noise
   readout support, and bias-dependent gap preservation even when the two
   source contexts have unequal conditioning probabilities;
   `ColliderRealization` transports that calculation to an actual finite
   record only after its all-event prior encoding and pointwise evidence and
   readout equations have been proved.  It retains each record's own evidence
   denominator and reflects source gaps through supported biased posteriors;
10. `Construction` builds finite dependent products and the rational
   constructions used by causal models; `FiniteProductResponse` isolates one
   factor while retaining all other factors, including zeros;
   `FiniteProductBalance` telescopes coordinated changes of several factors
   in mixed old/new environments, retaining their interaction terms and
   characterizing exact cancellation without dividing by old cells; and
11. `Distros` packages named finite distros (Bernoulli, binomial, lattice
    Gaussian, and the finite counterparts of the classical limiting
    families).

No result here concerns countable additivity or arbitrary propositions:
events are explicit Boolean predicates on finite enumerations.
-/
