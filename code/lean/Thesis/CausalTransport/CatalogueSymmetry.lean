import Thesis.Causality.FiniteSymmetry
import Thesis.CausalTransport.CatalogueInference

namespace Thesis.Causality.FiniteSymmetry
open Probability Probability.Distros

/-!
# Bayesian symmetry and representation-independent class mass

Bayes updating commutes with a bijective change of hypothesis names when the
likelihood is transported as well. That statement does not require a
symmetric prior. With a symmetric prior one may reuse the original prior
after transforming the data; asymmetric evidence is still allowed to break
invariance of the posterior at the *fixed* dataset.

The final section treats duplicate encodings as a probability pushforward.
The mass of an equivalence class is the sum of the masses of its encodings;
it is not silently reset to a uniform prior on whichever representatives
happen to remain in a list. The same pushforward commutes with updating when
the evidence depends only on the class.
-/

variable {G : Group} {H : Type u}

/-- A likelihood is a function of a hypothesis, so its forward transport
uses the inverse hypothesis action. This is the same contravariance as
pulling back an event predicate when pushing forward a probability law. -/
def transportWeight (A : Action G H) (g : G.Carrier) (weight : H → Nat) : H → Nat :=
  fun h => weight (A.act (G.inv g) h)

/-- Renaming every atom and the likelihood leaves the unnormalised evidence
mass exactly unchanged. Hence exhaustion and positive support are preserved,
including catalogues containing zero-prior or zero-likelihood hypotheses. -/
theorem normalizer_transport (A : Action G H) (g : G.Carrier)
    (prior : Distro H) (weight : H → Nat) :
    natIntegral (prior.map (A.act g)).record.atoms (transportWeight A g weight) =
      natIntegral prior.record.atoms weight := by
  simp only [Distro.map, FiniteProbRecord.map, natIntegral_map,
    transportWeight, A.inv_act]

/-- Actual normalized records, not just posterior odds, commute with
consistent relabelling. The support proof is obtained from the preceding
normalizer identity, rather than assumed separately on the renamed side. -/
theorem reweight_transport (A : Action G H) (g : G.Carrier)
    (prior : Distro H) (weight : H → Nat)
    (positive : 0 < natIntegral prior.record.atoms weight) :
    ((prior.reweightNat weight positive).map (A.act g)) =
      (prior.map (A.act g)).reweightNat (transportWeight A g weight)
        (by rw [normalizer_transport]; exact positive) := by
  have targetPositive :
      0 < natIntegral (prior.map (A.act g)).record.atoms (transportWeight A g weight) := by
    rw [normalizer_transport]
    exact positive
  simpa only [transportWeight, A.inv_act] using
    prior.reweightNat_map (A.act g) (transportWeight A g weight) targetPositive

/-- The existing catalogue engine has the same transport property at the
`Option` boundary. In particular a renamed exhausted catalogue remains
`none`; equivariance never invents a fallback posterior. -/
theorem posterior_transport (A : Action G (Fin n)) (g : G.Carrier)
    (prior : Distro (Fin n)) (weight : Fin n → Nat) :
    CatalogueInference.posterior? (prior.map (A.act g)) (transportWeight A g weight) =
      (CatalogueInference.posterior? prior weight).map (fun posterior => posterior.map (A.act g)) := by
  by_cases positive : 0 < natIntegral prior.record.atoms weight
  · have targetPositive :
        0 < natIntegral (prior.map (A.act g)).record.atoms (transportWeight A g weight) := by
      rw [normalizer_transport]
      exact positive
    simp only [CatalogueInference.posterior?, dif_pos positive,
      dif_pos targetPositive, Option.map_some]
    exact congrArg some (reweight_transport A g prior weight positive).symm
  · have targetNotPositive :
        ¬ 0 < natIntegral (prior.map (A.act g)).record.atoms (transportWeight A g weight) := by
      rw [normalizer_transport]
      exact positive
    simp only [CatalogueInference.posterior?, dif_neg positive,
      dif_neg targetNotPositive, Option.map_none]

/-- Invariance of *knowledge* is a law on the hypothesis space. It does not
require every individual hypothesis graph or mechanism to be fixed. -/
def PriorInvariant (A : Action G H) (prior : Distro H) : Prop :=
  ∀ g, (prior.map (A.act g)).SameLaw prior

/-- A generative experiment interface supplies how data transform, as well
as the likelihood. Jointly transforming data and hypotheses must preserve
the likelihood of that same observation. For causal data, the data action
must include the experimental setting; outcome-only transforms do not meet
this contract in general. -/
def LikelihoodEquivariant (A : Action G H) (D : Action G Data)
    (likelihood : Data → H → Nat) : Prop :=
  ∀ g datum hypothesis,
    likelihood (D.act g datum) (A.act g hypothesis) = likelihood datum hypothesis

theorem likelihood_transport (A : Action G H) (D : Action G Data)
    (likelihood : Data → H → Nat) (equivariant : LikelihoodEquivariant A D likelihood)
    (g : G.Carrier) (datum : Data) :
    likelihood (D.act g datum) = transportWeight A g (likelihood datum) := by
  funext hypothesis
  have same := equivariant g datum (A.act (G.inv g) hypothesis)
  simpa only [A.act_inv, transportWeight] using same

/-- Dataset-level form of the actual catalogue posterior theorem. No
assumption is made that the particular observed datum is invariant. -/
theorem posterior_data_transport (A : Action G (Fin n)) (D : Action G Data)
    (likelihood : Data → Fin n → Nat)
    (equivariant : LikelihoodEquivariant A D likelihood)
    (g : G.Carrier) (datum : Data) (prior : Distro (Fin n)) :
    CatalogueInference.posterior? (prior.map (A.act g)) (likelihood (D.act g datum)) =
      (CatalogueInference.posterior? prior (likelihood datum)).map
        (fun posterior => posterior.map (A.act g)) := by
  rw [likelihood_transport A D likelihood equivariant]
  exact posterior_transport A g prior (likelihood datum)

/-- A symmetric prior lets the original prior be used after renaming the
data. The positive target support follows from prior law invariance; it is
not an additional independent assumption about the transformed dataset. -/
theorem invariant_prior_posterior (A : Action G H) (g : G.Carrier)
    (prior : Distro H) (invariant : PriorInvariant A prior) (weight : H → Nat)
    (positive : 0 < natIntegral prior.record.atoms weight) :
    ∃ targetPositive : 0 < natIntegral prior.record.atoms (transportWeight A g weight),
      ((prior.reweightNat weight positive).map (A.act g)).SameLaw
        (prior.reweightNat (transportWeight A g weight) targetPositive) := by
  have mappedPositive :
      0 < natIntegral (prior.map (A.act g)).record.atoms (transportWeight A g weight) := by
    rw [normalizer_transport]
    exact positive
  have expectation := (invariant g).expectNat (transportWeight A g weight)
  have targetPositive : 0 < natIntegral prior.record.atoms (transportWeight A g weight) :=
    (QProb.equiv_num_pos_iff expectation).mp mappedPositive
  refine ⟨targetPositive, ?_⟩
  rw [reweight_transport A g prior weight positive]
  exact (invariant g).reweightNat _ _ _

/-- A posterior is invariant at a fixed dataset only when the evidence
likelihood is itself invariant, in addition to the prior. This is a stronger
claim than transporting the dataset and is deliberately a separate theorem.
The same positive normalizer is reused after the likelihood equality. -/
theorem posterior_invariant_of_weight_invariant (A : Action G H)
    (prior : Distro H) (invariant : PriorInvariant A prior) (weight : H → Nat)
    (fixed : ∀ g hypothesis, weight (A.act g hypothesis) = weight hypothesis)
    (positive : 0 < natIntegral prior.record.atoms weight) :
    PriorInvariant A (prior.reweightNat weight positive) := by
  intro g
  rcases invariant_prior_posterior A g prior invariant weight positive with
    ⟨targetPositive, agreement⟩
  have likelihood : transportWeight A g weight = weight := by
    funext hypothesis
    exact fixed (G.inv g) hypothesis
  simpa only [likelihood] using agreement

/-- When the actual observation is unchanged by every data transformation,
likelihood equivariance supplies the additional invariant-evidence premise.
Asymmetric data are covered by `posterior_data_transport` instead; there is
no automatic posterior-invariance conclusion for those observations. -/
theorem posterior_invariant_of_fixed_data (A : Action G H) (D : Action G Data)
    (likelihood : Data → H → Nat) (equivariant : LikelihoodEquivariant A D likelihood)
    (datum : Data) (datumFixed : ∀ g, D.act g datum = datum)
    (prior : Distro H) (invariant : PriorInvariant A prior)
    (positive : 0 < natIntegral prior.record.atoms (likelihood datum)) :
    PriorInvariant A (prior.reweightNat (likelihood datum) positive) := by
  apply posterior_invariant_of_weight_invariant A prior invariant (likelihood datum) ?_ positive
  intro g hypothesis
  have transported := equivariant g datum hypothesis
  rw [datumFixed g] at transported
  exact transported

/-- A complexity preference inherits the score's declared symmetry. This
does not justify a score which depends on arbitrary node names. -/
theorem complexityWeight_invariant (A : Action G H) (score : H → Nat)
    (symmetric : A.ScoreInvariant score) (budget : Nat) (g : G.Carrier) (h : H) :
    CatalogueInference.complexityWeight budget (score (A.act g h)) =
      CatalogueInference.complexityWeight budget (score h) := by
  rw [symmetric g h]

/-- A complexity-sensitive prior retains declared representation symmetry
when both the reference knowledge and the description score are invariant.
The support premise is only that some weighted prior mass survives the
chosen budget; individual hypotheses may receive weight zero. -/
theorem complexityPrior_invariant (A : Action G H) (prior : Distro H)
    (invariant : PriorInvariant A prior) (score : H → Nat)
    (symmetric : A.ScoreInvariant score) (budget : Nat)
    (positive : 0 < natIntegral prior.record.atoms
      (fun h => CatalogueInference.complexityWeight budget (score h))) :
    PriorInvariant A (prior.reweightNat
      (fun h => CatalogueInference.complexityWeight budget (score h)) positive) := by
  apply posterior_invariant_of_weight_invariant A prior invariant _ ?_ positive
  intro g h
  exact complexityWeight_invariant A score symmetric budget g h

/-- Aggregate a presentation onto explicit class labels. Repeated encodings
contribute their actual mass; changing presentation never resets that mass. -/
def aggregateClasses (prior : Distro H) (classOf : H → Class) : Distro Class :=
  prior.map classOf

/-- A class probability is precisely the mass of all encodings in its
fibre, including split atoms and null encodings. -/
theorem aggregateClasses_pmf [DecidableEq Class] (prior : Distro H)
    (classOf : H → Class) (label : Class) :
    QProb.Equiv ((aggregateClasses prior classOf).pmf label)
      (prior.record.probVal (fun h => decide (classOf h = label))) := by
  exact prior.map_pmf classOf label

/-- Updating encodings by a class-level likelihood and then aggregating is
exactly updating the class prior. This is the operational protection against
accidental duplication of equivalent representations in a catalogue. -/
theorem aggregateClasses_reweight (prior : Distro H) (classOf : H → Class)
    (weight : Class → Nat)
    (positive : 0 < natIntegral (aggregateClasses prior classOf).record.atoms weight) :
    aggregateClasses
      (prior.reweightNat (fun h => weight (classOf h))
        (by simpa only [aggregateClasses, Distro.map, FiniteProbRecord.map,
          natIntegral_map] using positive)) classOf =
      (aggregateClasses prior classOf).reweightNat weight positive :=
  prior.reweightNat_map classOf weight positive

end Thesis.Causality.FiniteSymmetry
