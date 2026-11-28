import Thesis.Probability.Distros.RationalUpdates

namespace Thesis.Probability.Distros

/-!
# Count likelihoods from a common sampling experiment

A likelihood is the probability of the *observed object*, not merely a
nonnegative score. In particular, the probability of two marginal histograms
does not equal the probability of the paired joint histogram: the latter also
records which first-coordinate and second-coordinate observations occurred
together. Comparing the former under one hypothesis with the latter under
another changes the statistical experiment and therefore changes Bayes factors.

This module constructs the required laws before extracting any likelihood.
`iidCountDistro` counts independent draws from a fixed finite law. The separate
`pairedDirichletCountDistro` first draws independent Pólya histories for two
coordinates and then counts their *positionwise pairs*. Thus it integrates
independent Dirichlet parameter priors while retaining the same joint count
observation used by a saturated Dirichlet--multinomial model. All alphabets,
trial counts, rational parameters, and supported zeros remain explicit.

The construction is deliberately generative. Its normalization and all-event
sampling correspondence hold for every input, rather than being a correction
factor fitted to one numerical example. Enumerating histories can be expensive;
closed-form optimizations may replace it only after proving law equivalence.
-/

/-- Independent repetitions of a fixed finite law, retaining their order.
The product at each step expresses independence of the next observation and
the remaining word. No urn reinforcement or parameter uncertainty is added. -/
def iidWordDistro (law : Distro Ω) : Nat → Distro (List Ω)
  | 0 => Distro.pointMass []
  | n + 1 => (law.product (iidWordDistro law n)).map (fun pair => pair.1 :: pair.2)

/-- Equal finite laws produce equal laws of ordered IID histories, including
when the input records use different weights for the same rational law. -/
theorem iidWordDistro_sameLaw {left right : Distro Ω} (same : left.SameLaw right)
    (trials : Nat) : (iidWordDistro left trials).SameLaw (iidWordDistro right trials) := by
  induction trials with
  | zero => exact fun _ => QProb.equiv_refl _
  | succ trials ih =>
    exact (same.product ih).map (fun pair => pair.1 :: pair.2)

/-- Relabelling each draw commutes with independently sampling a fixed
finite law. The conclusion concerns the full word law, before counting. -/
theorem iidWordDistro_map (law : Distro Ω) (rename : Ω → X) (trials : Nat) :
    (iidWordDistro (law.map rename) trials).SameLaw
      ((iidWordDistro law trials).map (List.map rename)) := by
  induction trials with
  | zero => exact fun _ => QProb.equiv_refl _
  | succ trials ih =>
    intro event
    let cons := fun pair : X × List X => pair.1 :: pair.2
    let sameHead : (law.map rename).SameLaw (law.map rename) := fun _ => QProb.equiv_refl _
    refine QProb.equiv_trans (Distro.map_probVal _ _ _) ?_
    refine QProb.equiv_trans ((sameHead.product ih) (fun pair => event (cons pair))) ?_
    refine QProb.equiv_trans (FiniteProbRecord.product_map_right_probVal
      (law.map rename).record (iidWordDistro law trials).record (List.map rename)
      (fun pair => event (cons pair))) ?_
    refine QProb.equiv_trans (FiniteProbRecord.product_map_left_probVal
      law.record (iidWordDistro law trials).record rename
      (fun pair => event (cons (pair.1, pair.2.map rename)))) ?_
    exact QProb.equiv_symm (QProb.equiv_trans (Distro.map_probVal _ _ _)
      (Distro.map_probVal _ _ _))

/-- Counts in the caller's declared label order. Observable labels, rather
than atom occurrences, are counted, so repeated record labels are combined.
Clients that describe a complete joint table supply distinct exhaustive labels. -/
def labelledHistogram [DecidableEq Ω] (labels : List Ω) (word : List Ω) : List Nat :=
  labels.map fun label => word.count label

/-- A histogram preserves the declared label dimension, including zero-count labels. -/
theorem labelledHistogram_length [DecidableEq Ω] (labels : List Ω) (word : List Ω) :
    (labelledHistogram labels word).length = labels.length := by
  simp only [labelledHistogram, List.length_map]

/-- The multinomial sampling law of a fixed distribution, expressed directly
as the histogram of actual independent repetitions. Zeros in the fixed law
stay impossible; there is no pseudocount or empirical-law replacement. -/
def iidCountDistro [DecidableEq Ω] (law : Distro Ω) (labels : List Ω)
    (trials : Nat) : Distro (List Nat) :=
  (iidWordDistro law trials).map (labelledHistogram labels)

/-- Every count event is precisely the event that independent samples have
that histogram. This statement applies to all events, including unions of
histograms, rather than only to a fitted singleton likelihood. -/
theorem iidCountDistro_sampling [DecidableEq Ω] (law : Distro Ω)
    (labels : List Ω) (trials : Nat) (event : Event (List Nat)) :
    QProb.Equiv ((iidCountDistro law labels trials).record.probVal event)
      ((iidWordDistro law trials).record.probVal
        (fun word => event (labelledHistogram labels word))) :=
  Distro.map_probVal _ _ _

/-- The sampling law is normalized before it is used as a likelihood. -/
theorem iidCountDistro_normalization [DecidableEq Ω] (law : Distro Ω)
    (labels : List Ω) (trials : Nat) :
    QProb.Equiv ((iidCountDistro law labels trials).record.probVal topEvent) QProb.one :=
  Distro.normalization _

/-- Row-major code of the two values observed in the same trial. For example,
two binary coordinates give cells `00,01,10,11`. Pairing is performed before
counting, which retains the association discarded by separate margins. -/
def pairedColourWord (columns : Nat) (words : List Nat × List Nat) : List Nat :=
  (words.1.zip words.2).map fun pair => pair.1 * columns + pair.2

/-- The complete joint histogram of positionwise paired histories. Actual
Pólya histories on both sides have the same supplied trial count. -/
def pairedHistogram (rows columns : Nat) (words : List Nat × List Nat) : List Nat :=
  colourCounts (rows * columns) (pairedColourWord columns words)

/-- Every paired histogram retains all joint cells, with fixed dimension equal to the
product alphabet. -/
theorem pairedHistogram_length (rows columns : Nat) (words : List Nat × List Nat) :
    (pairedHistogram rows columns words).length = rows * columns :=
  colourCounts_length _ _

/-- Independent parameter priors produce independent ordered histories.
Within each history the Pólya reinforcement represents the shared unknown
categorical parameter. Independence is between the two coordinate models,
not between successive observations after integrating out their parameters. -/
def independentPolyaHistories (trials : Nat) (alphas betas : List QProb)
    (firstPositive : 0 < (QProb.listSum alphas).num)
    (secondPositive : 0 < (QProb.listSum betas).num) :
    Distro (List Nat × List Nat) :=
  (rationalPolyaDistro trials alphas firstPositive).product
    (rationalPolyaDistro trials betas secondPositive)

/-- The two history events factor under their product law. This is the
explicit independence premise of the two-parameter-family hypothesis. -/
theorem independentPolyaHistories_rectangular (trials : Nat) (alphas betas : List QProb)
    (firstPositive : 0 < (QProb.listSum alphas).num)
    (secondPositive : 0 < (QProb.listSum betas).num)
    (firstEvent secondEvent : Event (List Nat)) :
    QProb.Equiv
      ((independentPolyaHistories trials alphas betas firstPositive secondPositive).record.probVal
        (fun words => firstEvent words.1 && secondEvent words.2))
      (QProb.mul
        ((rationalPolyaDistro trials alphas firstPositive).record.probVal firstEvent)
        ((rationalPolyaDistro trials betas secondPositive).record.probVal secondEvent)) :=
  FiniteProbRecord.product_probVal _ _ _ _

/-- Integrated likelihood law for a *joint count table* under independent
Dirichlet/Pólya coordinate models. It counts matched observations, not just
the two marginal histograms. Nonnegative rational parameters are permitted;
the existing urn interpretation handles supported structural zeros. -/
def pairedDirichletCountDistro (trials : Nat) (alphas betas : List QProb)
    (firstPositive : 0 < (QProb.listSum alphas).num)
    (secondPositive : 0 < (QProb.listSum betas).num) : Distro (List Nat) :=
  (independentPolyaHistories trials alphas betas firstPositive secondPositive).map
    (pairedHistogram alphas.length betas.length)

/-- General sampling-process correctness: every joint-table event has its
probability under the same paired experiment. In particular, selecting one
histogram includes all and only ordered pairings realizing that histogram. -/
theorem pairedDirichletCountDistro_sampling (trials : Nat) (alphas betas : List QProb)
    (firstPositive : 0 < (QProb.listSum alphas).num)
    (secondPositive : 0 < (QProb.listSum betas).num)
    (event : Event (List Nat)) :
    QProb.Equiv
      ((pairedDirichletCountDistro trials alphas betas firstPositive secondPositive).record.probVal event)
      ((independentPolyaHistories trials alphas betas firstPositive secondPositive).record.probVal
        (fun words => event (pairedHistogram alphas.length betas.length words))) :=
  Distro.map_probVal _ _ _

/-- A full normalized count law, so its singleton probabilities are valid
likelihoods on the same sample space as a saturated count model. -/
theorem pairedDirichletCountDistro_normalization (trials : Nat) (alphas betas : List QProb)
    (firstPositive : 0 < (QProb.listSum alphas).num)
    (secondPositive : 0 < (QProb.listSum betas).num) :
    QProb.Equiv
      ((pairedDirichletCountDistro trials alphas betas firstPositive secondPositive).record.probVal topEvent)
      QProb.one :=
  Distro.normalization _

/-- Extract a likelihood only after constructing its normalized law. The
sum of the supplied counts determines the number of paired observations. -/
def pairedDirichletCountMass (alphas betas : List QProb)
    (firstPositive : 0 < (QProb.listSum alphas).num)
    (secondPositive : 0 < (QProb.listSum betas).num) (counts : List Nat) : QProb :=
  (pairedDirichletCountDistro counts.sum alphas betas firstPositive secondPositive).pmf counts

end Thesis.Probability.Distros
