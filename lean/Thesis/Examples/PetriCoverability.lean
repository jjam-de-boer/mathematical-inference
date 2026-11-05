import Thesis.Causality.PetriCoverability

namespace Thesis.Causality.Examples.PetriCoverability

open PetriNet CoordinateBoxes

/-!
# Witnessed saturation and premature box-discard regressions

The exchange net exercises actual predecessor-prefix construction,
including overshoot and lifting the resulting two-step word to a larger
source. Its two stored basis points have real executions to the target.
The surrounding boxes arise from the proved splitting updates, rather
than from an unrelated geometric fixture.

The central box has no currently fresh predecessor inside it, but it
contains a still-uncovered point with a successful two-step execution.
Discarding that box loses the coverage invariant. A later predecessor
enters precisely that region. This refutes that pruning shortcut, not
backward coverability search or the decreasing split construction.

A second fixture supplies a genuinely saturated witnessed basis and
uses the general certificate theorem for every natural source count.
The empty-basis example shows why saturation alone cannot justify a
negative answer. Empty place and transition families are also covered.
No search procedure or runtime solver is used in these regressions.
-/

def pair (x y : Nat) : Marking 2 := fun i => if i = 0 then x else y

def exchange : Thesis.Causality.PetriNet 2 3 where
  consume := fun t => if t = 0 then pair 1 0 else if t = 1 then pair 0 2 else pair 1 2
  produce := fun t => if t = 0 then pair 0 2 else pair 2 0

def target := pair 2 1
def second := pair 1 3
def query := pair 1 2

def initialWitness := CoverabilityWitness.initial exchange target
def secondWitness := initialWitness.prepend 2
def queryWitness := (initialWitness.prepend 0).prepend 1

theorem second_source : secondWitness.source = second :=
  (markingEq_exact _ _).mp (by decide +kernel)

theorem query_source : queryWitness.source = query :=
  (markingEq_exact _ _).mp (by decide +kernel)

/-- The constructed word reaches (2,2), overshooting the target (2,1).
The exact execution checker is exercised on those independently stated
coordinates, in addition to the witness's general semantic proof. -/
theorem query_witness_computed :
    queryWitness.word = [1, 0] ∧
      (queryWitness.endpoint 0, queryWitness.endpoint 1) = (2, 2) ∧
      exchange.check query queryWitness.word (pair 2 2) = true := by
  decide +kernel

theorem query_coverable : exchange.Coverable query target := by
  simpa only [query_source] using queryWitness.coverable

def largerWitness := queryWitness.lift (pair 4 7) (by
  rw [query_source]
  unfold Below
  decide +kernel)

theorem larger_witness_computed :
    (largerWitness.endpoint 0, largerWitness.endpoint 1) = (5, 7) ∧
      exchange.check (pair 4 7) largerWitness.word (pair 5 7) = true := by
  decide +kernel

def basis : List (Marking 2) := [second, target]
def unrestricted : Box 2 := fun _ => none
def firstBox := cut unrestricted 0 (target 0)
def rightArm := cut unrestricted 1 (target 1)
def leftArm := cut firstBox 0 (second 0)
def central := cut firstBox 1 (second 1)

private theorem second_inside_first : Contains firstBox second := by
  simp only [Contains, Fin.forall_fin_succ, Fin.forall_fin_zero]
  dsimp [firstBox, unrestricted, cut, target, second, pair]
  decide +kernel

/-- These are exactly the two successive splits inserting the target
and the second point. The resulting boxes cover every point outside the
basis's upward closure; overlap between the boxes is allowed. -/
theorem before_discard_covers : CoversUncovered [leftArm, central, rightArm] basis := by
  have firstCoverage := coversUncovered_after_replace [] [] unrestricted target []
    (fun _ => True.intro) (unbounded_covers [])
  change CoversUncovered [firstBox, rightArm] [target] at firstCoverage
  have secondCoverage := coversUncovered_after_replace [] [rightArm] firstBox second [target]
    second_inside_first firstCoverage
  exact secondCoverage

private theorem basis_covered_iff (point : Marking 2) :
    Covered basis point ↔ Below second point ∨ Below target point := by
  constructor
  · rintro ⟨old, listed, below⟩
    rcases List.mem_cons.mp listed with equal | listed
    · subst old
      exact .inl below
    · have equal := List.mem_singleton.mp listed
      subst old
      exact .inr below
  · rintro (below | below)
    · exact ⟨second, List.mem_cons_self, below⟩
    · exact ⟨target, List.mem_cons_of_mem second List.mem_cons_self, below⟩

theorem basis_points_cover_target : ∀ point ∈ basis, exchange.Coverable point target := by
  intro point listed
  rcases List.mem_cons.mp listed with equal | listed
  · subst point
    simpa only [second_source] using secondWitness.coverable
  · have equal := List.mem_singleton.mp listed
    subst point
    exact initialWitness.coverable

private theorem current_predecessor_cases : ∀ t : Fin 3,
    (Contains central (exchange.predecessor t second) →
      Below second (exchange.predecessor t second) ∨ Below target (exchange.predecessor t second)) ∧
    (Contains central (exchange.predecessor t target) →
      Below second (exchange.predecessor t target) ∨ Below target (exchange.predecessor t target)) := by
  simp only [Contains, Below, Fin.forall_fin_succ, Fin.forall_fin_zero]
  dsimp [central, firstBox, unrestricted, cut, target, second, pair]
  simp [predecessor, exchange, pair]

/-- No currently fresh candidate lies in the central box. This local
fact does not license removing it from the global coverage invariant. -/
theorem no_current_fresh_inside : ∀ point ∈ basis, ∀ transition,
    Contains central (exchange.predecessor transition point) →
      Covered basis (exchange.predecessor transition point) := by
  intro point listed transition inside
  apply (basis_covered_iff _).mpr
  rcases List.mem_cons.mp listed with equal | listed
  · subst point
    exact (current_predecessor_cases transition).1 inside
  · have equal := List.mem_singleton.mp listed
    subst point
    exact (current_predecessor_cases transition).2 inside

theorem query_in_central : Contains central query := by
  simp only [Contains, Fin.forall_fin_succ, Fin.forall_fin_zero]
  dsimp [central, firstBox, unrestricted, cut, target, second, pair]
  decide +kernel

theorem query_not_covered : ¬ Covered basis query := by
  intro covered
  rcases (basis_covered_iff query).mp covered with below | below
  · exact Nat.not_succ_le_self 2 (below 1)
  · exact Nat.not_succ_le_self 1 (below 0)

theorem query_outside_remaining : ¬ Region [leftArm, rightArm] query := by
  rintro ⟨box, listed, inside⟩
  rcases List.mem_cons.mp listed with equal | listed
  · subst box
    have impossible := inside 0
    change 1 < 1 at impossible
    exact Nat.lt_irrefl 1 impossible
  · have equal := List.mem_singleton.mp listed
    subst box
    have impossible := inside 1
    change 2 < 1 at impossible
    exact Nat.not_lt_of_ge (by decide +kernel : 1 ≤ 2) impossible

/-- The omitted point actually covers the target. The failure is not
only a loose geometric over-approximation: a later covering predecessor
enters the discarded region, with a concrete successful execution. -/
theorem later_predecessor_enters_central :
    (exchange.predecessor 1 (initialWitness.prepend 0).source) = query :=
  query_source

theorem discarding_central_loses_coverage : ¬ CoversUncovered [leftArm, rightArm] basis := by
  intro coverage
  exact query_outside_remaining (coverage query query_not_covered)

def needsSeed : Thesis.Causality.PetriNet 1 1 where
  consume := fun _ _ => 1
  produce := fun _ _ => 2

def tokens (count : Nat) : Marking 1 := fun _ => count

/-- The singleton basis is already saturated: every covering predecessor
of one token again requires one token. Its empty word is a real witness. -/
def seedCertificate : CoverabilityCertificate needsSeed (tokens 1) where
  entries := [CoverabilityWitness.initial needsSeed (tokens 1)]
  targetCovered := ⟨tokens 1, List.mem_cons_self, Below.refl _⟩
  saturated := by
    change Saturated needsSeed [tokens 1]
    intro point listed transition
    have equal := List.mem_singleton.mp listed
    subst point
    refine ⟨tokens 1, List.mem_cons_self, ?_⟩
    intro place
    change 1 ≤ 1
    exact Nat.le_refl _

theorem seed_coverability_exact (count : Nat) :
    needsSeed.Coverable (tokens count) (tokens 1) ↔ 1 ≤ count := by
  rw [seedCertificate.coverable_iff_covered]
  change Covered [tokens 1] (tokens count) ↔ 1 ≤ count
  constructor
  · rintro ⟨point, listed, below⟩
    have equal := List.mem_singleton.mp listed
    subst point
    exact below 0
  · intro enough
    exact ⟨tokens 1, List.mem_cons_self, fun _ => enough⟩

theorem zero_seed_not_coverable : ¬ needsSeed.Coverable (tokens 0) (tokens 1) := by
  apply seedCertificate.not_coverable
  rintro ⟨point, listed, below⟩
  have equal := List.mem_singleton.mp listed
  subst point
  exact Nat.not_succ_le_zero 0 (below 0)

/-- Saturation of an empty list is vacuous. Without target coverage it
cannot certify a negative answer, even for the target's empty execution. -/
theorem empty_saturation_is_insufficient :
    Saturated needsSeed [] ∧ ¬ Covered [] (tokens 1) ∧
      needsSeed.Coverable (tokens 1) (tokens 1) := by
  refine ⟨?_, ?_, (CoverabilityWitness.initial needsSeed (tokens 1)).coverable⟩
  · intro point impossible
    exact False.elim (List.not_mem_nil impossible)
  · rintro ⟨point, impossible, _⟩
    exact List.not_mem_nil impossible

def emptyNet : Thesis.Causality.PetriNet 0 0 where
  consume := Fin.elim0
  produce := Fin.elim0

def emptyCertificate : CoverabilityCertificate emptyNet Fin.elim0 where
  entries := [CoverabilityWitness.initial emptyNet Fin.elim0]
  targetCovered := ⟨Fin.elim0, List.mem_cons_self, Below.refl _⟩
  saturated := by
    intro point listed transition
    exact Fin.elim0 transition

theorem empty_dimensions_coverable (source : Marking 0) : emptyNet.Coverable source Fin.elim0 :=
  (emptyCertificate.coverable_iff_covered source).mpr
    ⟨Fin.elim0, List.mem_cons_self, fun place => Fin.elim0 place⟩

end Thesis.Causality.Examples.PetriCoverability
