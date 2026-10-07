import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeObstructionLikelihood

open Probability

/-!
# Positive rational tables beyond the carrier-routing obstruction

This is the algebraic first stage of a different countermodel construction
for the seven-node graph `A,R,U,V,B,Q,Y`.  Its arrows are
`A → V`, `R → U`, `U → V`, `V → B`, `V → Y`, `B → Q`, and `Q → Y`.
There are four independent uniform hidden sources: `H` on `A,R`, `L` on
`R,Q`, `J` on `A,B`, and `K` on `B,V`.  The first two are Boolean, `J`
has six values, and `K` has three.  No source is shared by three observed
vertices.  In particular, larger *latent* alphabets are being used, not
larger observed alphabets or an extra observed coordinate.

Both table systems are strictly positive and differ only at `R`.  The
perturbation at that row has opposite signs at the two values of `L` and
coefficients `256,-255` at the two values of `H`.  At `B = true`, the `Q`
table forgets `L`, so that perturbation cancels immediately.  At `B = false`,
the chosen `A,V,B` tables make its complete observed likelihood cancel.
After intervening on `A = false, B = false`, the likelihood at `A,B` is
removed, and the residual causal gap is exactly `1/62208`.

The checks below concern exact rational table products, summed over every
hidden source.  They are not numerical approximations or native reduction
proofs.  Complete observational equality, positive normalized observed
weights, and both truncated-table intervention values are kernel checked.

IMPORTANT: this module does not yet construct a `FiniteLatentSCM`, relate
these table products to its evaluation, or return `CounterexampleIn`.
That functional realization and semantic bridge are the next stage.  Nor
does this one graph replace the universal hedge countermodel obligation.
Keeping the boundary explicit prevents a successful table calculation from
being mistaken for finished published completeness.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The complete Boolean observed assignment in the graph's topological
order.  Named fields keep the local parent dependencies inspectable. -/
structure Observation where
  a : Bool
  r : Bool
  u : Bool
  v : Bool
  b : Bool
  q : Bool
  y : Bool
  deriving DecidableEq

/-- Four independent pair sources, with their finite cardinalities stored
as types rather than as unchecked numerical bounds. -/
structure Hidden where
  h : Bool
  l : Bool
  j : Fin 6
  k : Fin 3

private def booleans : List Bool := [false, true]

/-- Each observed assignment is listed once; no partial event is substituted
for the full observational comparison. -/
def observations : List Observation :=
  booleans.flatMap fun a => booleans.flatMap fun r =>
  booleans.flatMap fun u => booleans.flatMap fun v =>
  booleans.flatMap fun b => booleans.flatMap fun q =>
  booleans.map fun y => ⟨a, r, u, v, b, q, y⟩

private theorem boolean_mem (value : Bool) : value ∈ booleans := by
  cases value <;> decide

theorem observations_complete (sample : Observation) : sample ∈ observations := by
  rcases sample with ⟨a, r, u, v, b, q, y⟩
  exact List.mem_flatMap.mpr ⟨a, boolean_mem a,
    List.mem_flatMap.mpr ⟨r, boolean_mem r,
    List.mem_flatMap.mpr ⟨u, boolean_mem u,
    List.mem_flatMap.mpr ⟨v, boolean_mem v,
    List.mem_flatMap.mpr ⟨b, boolean_mem b,
    List.mem_flatMap.mpr ⟨q, boolean_mem q,
    List.mem_map.mpr ⟨y, boolean_mem y, rfl⟩⟩⟩⟩⟩⟩⟩

theorem observations_nodup : observations.Nodup := by decide +kernel

/-- The 72 equally weighted assignments of the four independent sources. -/
def hiddenAssignments : List Hidden :=
  booleans.flatMap fun h => booleans.flatMap fun l =>
  (List.finRange 6).flatMap fun j => (List.finRange 3).map fun k => ⟨h, l, j, k⟩

theorem hiddenAssignments_complete (unit : Hidden) : unit ∈ hiddenAssignments := by
  rcases unit with ⟨h, l, j, k⟩
  exact List.mem_flatMap.mpr ⟨h, boolean_mem h,
    List.mem_flatMap.mpr ⟨l, boolean_mem l,
    List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
    List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩⟩⟩⟩

theorem hiddenAssignments_length : hiddenAssignments.length = 72 := by decide +kernel

/-- A Bernoulli row's natural weight at its actual output.  The other
weight is the complement within the same declared denominator. -/
def outputWeight (den trueWeight : Nat) (output : Bool) : Nat :=
  if output then trueWeight else den - trueWeight

def aTrueWeight (unit : Hidden) : Nat :=
  -- These six entries solve the likelihood-cancellation equations.  At
  -- `A = false`, contracting with the `H` coefficients `256,-255` gives
  -- the vector `(-35,-301,345,79,269,-339)/3`.  Its sum is six, rather
  -- than zero: the nonzero unweighted contraction survives `do(A)`.
  if unit.h then 768 else match unit.j.val with
    | 0 => 841
    | 1 => 1373
    | 2 => 81
    | 3 => 613
    | 4 => 233
    | _ => 1449

/-- Only this row differs between the models.  Its perturbation has a
nonzero average over `H`, while its average over `L` vanishes. -/
def rTrueWeight (perturbed : Bool) (unit : Hidden) : Nat :=
  if perturbed then
    if unit.h then (if unit.l then 767 else 257)
    else (if unit.l then 256 else 768)
  else 512

def vTrueWeight (sample : Observation) (unit : Hidden) : Nat :=
  if sample.a then 3 else
    if sample.u then match unit.k.val with
      | 0 => 4
      | 1 => 1
      | _ => 3
    else match unit.k.val with
      | 0 => 1
      | 1 => 4
      | _ => 5

/-- `J` indexes the six pairs `(V,K)`.  This row can read exactly those
parents/sources allowed at `B`, namely observed `V` and hidden `J,K`. -/
def bTrueWeight (sample : Observation) (unit : Hidden) : Nat :=
  if unit.j.val = (if sample.v then 3 else 0) + unit.k.val then 2 else 3

def qTrueWeight (sample : Observation) (unit : Hidden) : Nat :=
  if sample.b then 3 else if unit.l then 5 else 1

def yTrueWeight (sample : Observation) : Nat :=
  if Bool.xor sample.v sample.q then 5 else 1

/-- The seven row weights depend only on the graph's declared parents and
incident pair sources.  No other observed bit is read by a row. -/
def rowWeights (perturbed : Bool) (sample : Observation) (unit : Hidden) : List Nat :=
  [outputWeight 1536 (aTrueWeight unit) sample.a,
   outputWeight 1024 (rTrueWeight perturbed unit) sample.r,
   outputWeight 6 (if sample.r then 5 else 1) sample.u,
   outputWeight 6 (vTrueWeight sample unit) sample.v,
   outputWeight 6 (bTrueWeight sample unit) sample.b,
   outputWeight 6 (qTrueWeight sample unit) sample.q,
   outputWeight 6 (yTrueWeight sample) sample.y]

private theorem outputWeight_positive (den numerator : Nat) (output : Bool)
    (bounds : 0 < numerator ∧ numerator < den) :
    0 < outputWeight den numerator output := by
  cases output <;> simp only [outputWeight, Bool.false_eq_true, if_false, if_true] <;> omega

/-- Every Bernoulli row has positive mass at both outputs, not just after
mixing over hidden values.  This excludes support-zero artefacts from the
candidate before any functional realization is attempted. -/
theorem rowWeights_positive (perturbed : Bool) (sample : Observation) (unit : Hidden)
    (weight : Nat) (listed : weight ∈ rowWeights perturbed sample unit) : 0 < weight := by
  have aBounds : 0 < aTrueWeight unit ∧ aTrueWeight unit < 1536 := by
    unfold aTrueWeight
    split
    · decide
    · split <;> decide
  have rBounds : 0 < rTrueWeight perturbed unit ∧ rTrueWeight perturbed unit < 1024 := by
    unfold rTrueWeight
    split
    · split <;> split <;> decide
    · decide
  have uBounds : 0 < (if sample.r then 5 else 1) ∧ (if sample.r then 5 else 1) < 6 := by
    cases sample.r <;> decide
  have vBounds : 0 < vTrueWeight sample unit ∧ vTrueWeight sample unit < 6 := by
    unfold vTrueWeight
    split
    · decide
    · split <;> split <;> decide
  have bBounds : 0 < bTrueWeight sample unit ∧ bTrueWeight sample unit < 6 := by
    unfold bTrueWeight
    split <;> split <;> decide
  have qBounds : 0 < qTrueWeight sample unit ∧ qTrueWeight sample unit < 6 := by
    unfold qTrueWeight
    split
    · decide
    · split <;> decide
  have yBounds : 0 < yTrueWeight sample ∧ yTrueWeight sample < 6 := by
    unfold yTrueWeight
    split <;> decide
  simp only [rowWeights, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with same | same | same | same | same | same | same
  · subst weight; exact outputWeight_positive _ _ _ aBounds
  · subst weight; exact outputWeight_positive _ _ _ rBounds
  · subst weight; exact outputWeight_positive _ _ _ uBounds
  · subst weight; exact outputWeight_positive _ _ _ vBounds
  · subst weight; exact outputWeight_positive _ _ _ bBounds
  · subst weight; exact outputWeight_positive _ _ _ qBounds
  · subst weight; exact outputWeight_positive _ _ _ yBounds

/-- Unnormalized weight of the complete observed assignment after summing
all hidden values.  The common denominator includes their uniform prior. -/
def observationalNumerator (perturbed : Bool) (sample : Observation) : Nat :=
  ((hiddenAssignments.map fun unit => (rowWeights perturbed sample unit).foldl Nat.mul 1)).sum

def observationalDenominator : Nat := 72 * 1536 * 1024 * 6 ^ 5

/-- One finite check covers the entire observed law, not only its selected
outcome marginal.  Positive weights are checked at the same time. -/
private theorem observational_checks :
    observations.all (fun sample => decide
      (observationalNumerator false sample = observationalNumerator true sample ∧
        0 < observationalNumerator false sample)) = true := by decide +kernel

theorem observationalNumerator_equal (sample : Observation) :
    observationalNumerator false sample = observationalNumerator true sample :=
  (of_decide_eq_true
    (List.all_eq_true.mp observational_checks sample (observations_complete sample))).1

theorem observationalNumerator_positive (perturbed : Bool) (sample : Observation) :
    0 < observationalNumerator perturbed sample := by
  have positive := (of_decide_eq_true
    (List.all_eq_true.mp observational_checks sample (observations_complete sample))).2
  cases perturbed
  · exact positive
  · rw [← observationalNumerator_equal sample]; exact positive

/-- The table products normalize exactly.  This is checked separately from
the equality, so equal but incorrectly scaled likelihoods cannot pass. -/
private theorem observational_total :
    FiniteProbRecord.totalMass
        (observations.map fun sample => (sample, observationalNumerator false sample)) =
      observationalDenominator := by decide +kernel

def observationalRecord (perturbed : Bool) : FiniteProbRecord Observation where
  atoms := observations.map fun sample => (sample, observationalNumerator perturbed sample)
  den := observationalDenominator
  den_pos := by decide
  total_mass := by
    cases perturbed
    · exact observational_total
    · have same :
          (observations.map fun sample => (sample, observationalNumerator true sample)) =
          (observations.map fun sample => (sample, observationalNumerator false sample)) := by
        apply List.map_congr_left
        intro sample _listed
        exact congrArg (fun weight => (sample, weight)) (observationalNumerator_equal sample).symm
      rw [same]
      exact observational_total

private theorem atom_le_singleton (atoms : List (Observation × Nat))
    (atom : Observation × Nat) (listed : atom ∈ atoms) :
    atom.2 ≤ FiniteProbRecord.eventMass atoms (FiniteProbRecord.singletonEvent atom.1) := by
  induction atoms with
  | nil => cases listed
  | cons head rest inductionHypothesis =>
      cases List.mem_cons.mp listed with
      | inl same =>
          subst head
          simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            decide_true, if_true]
          exact Nat.le_add_right _ _
      | inr later =>
          exact Nat.le_trans (inductionHypothesis later) (by
            cases selected : FiniteProbRecord.singletonEvent atom.1 head.1 <;>
              simp only [FiniteProbRecord.eventMass, selected, Bool.false_eq_true,
                if_false, if_true] <;> omega)

/-- Positivity belongs to the normalized probability record itself, not
merely to an unrelated expression for a candidate likelihood. -/
theorem observationalRecord_positive (perturbed : Bool) (sample : Observation) :
    (observationalRecord perturbed).EventPositive (FiniteProbRecord.singletonEvent sample) := by
  have listed : (sample, observationalNumerator perturbed sample) ∈
      (observations.map fun sample => (sample, observationalNumerator perturbed sample)) :=
    List.mem_map.mpr ⟨sample, observations_complete sample, rfl⟩
  change 0 < FiniteProbRecord.eventMass
    (observations.map fun sample => (sample, observationalNumerator perturbed sample))
    (FiniteProbRecord.singletonEvent sample)
  exact Nat.lt_of_lt_of_le (observationalNumerator_positive perturbed sample)
    (atom_le_singleton
      (observations.map fun sample => (sample, observationalNumerator perturbed sample))
      (sample, observationalNumerator perturbed sample) listed)

/-- Equality for every Boolean event follows from equality of the actual
complete weighted atom lists.  No family of pointwise witnesses is chosen. -/
theorem observationalRecord_equivalent (event : Event Observation) :
    QProb.Equiv ((observationalRecord false).probVal event)
      ((observationalRecord true).probVal event) := by
  have same : (observationalRecord false).atoms = (observationalRecord true).atoms := by
    change (observations.map fun sample => (sample, observationalNumerator false sample)) =
      (observations.map fun sample => (sample, observationalNumerator true sample))
    apply List.map_congr_left
    intro sample _listed
    exact congrArg (fun weight => (sample, weight)) (observationalNumerator_equal sample)
  change FiniteProbRecord.eventMass _ event * observationalDenominator =
    FiniteProbRecord.eventMass _ event * observationalDenominator
  rw [same]

/-! ## The exact truncated-table calculation for `do(A = false, B = false)` -/

/-- Delete the two intervened mechanisms, retaining every other response
and integrating all four pair sources.  The free bits `R,U,V,Q` are summed
below; `Y = true` is the event, not a further intervention. -/
def interventionNumerator (perturbed : Bool) : Nat :=
  (observations.filter (fun sample => !sample.a && !sample.b && sample.y)).map
    (fun sample => ((hiddenAssignments.map fun unit =>
      outputWeight 1024 (rTrueWeight perturbed unit) sample.r *
      outputWeight 6 (if sample.r then 5 else 1) sample.u *
      outputWeight 6 (vTrueWeight sample unit) sample.v *
      outputWeight 6 (qTrueWeight sample unit) sample.q *
      outputWeight 6 (yTrueWeight sample) sample.y)).sum)
    |>.sum

def interventionDenominator : Nat := 72 * 1024 * 6 ^ 4

def interventionProbability (perturbed : Bool) : QProb :=
  ⟨interventionNumerator perturbed, interventionDenominator, by decide⟩

theorem interventionProbability_unperturbed :
    QProb.Equiv (interventionProbability false) ⟨1, 2, by decide⟩ := by decide +kernel

theorem interventionProbability_perturbed :
    QProb.Equiv (interventionProbability true) ⟨31103, 62208, by decide⟩ := by decide +kernel

/-- The causal-table gap is positive and exact, not just a syntactic
inequality between two unreduced common-denominator representations. -/
theorem interventionProbability_gap :
    QProb.Equiv (QProb.add (interventionProbability true) ⟨1, 62208, by decide⟩)
      (interventionProbability false) :=
  QProb.equiv_trans
    (QProb.add_congr interventionProbability_perturbed (QProb.equiv_refl _))
    (QProb.equiv_trans (by decide : QProb.Equiv
      (QProb.add (⟨31103, 62208, by decide⟩ : QProb) ⟨1, 62208, by decide⟩) ⟨1, 2, by decide⟩)
      (QProb.equiv_symm interventionProbability_unperturbed))

/-- Exact nonzero separation of the stated truncated table products.  A
later SCM realization must prove that its query values are these values. -/
theorem interventionProbability_separated :
    Not (QProb.Equiv (interventionProbability false) (interventionProbability true)) := by
  intro equal
  have impossible := QProb.equiv_trans
    (QProb.equiv_symm interventionProbability_unperturbed)
    (QProb.equiv_trans equal interventionProbability_perturbed)
  exact (by decide : Not (QProb.Equiv (⟨1, 2, by decide⟩ : QProb) ⟨31103, 62208, by decide⟩)) impossible

end HedgeObstructionLikelihood
end Examples
end Causality
end Thesis
