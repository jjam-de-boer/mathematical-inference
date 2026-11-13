import Thesis.Probability.EntropyGrouping
import Thesis.Probability.Distros.EntropyGibbs

namespace Thesis.Probability

/-- A normalized finite vector, with unreduced rational entries. Coordinate
positions are observable alternatives, not raw atom occurrences. -/
structure ProbabilityVector where
  masses : List QProb
  normalized : QProb.Equiv (QProb.listSum masses) QProb.one

namespace ProbabilityVector

theorem ext {first second : ProbabilityVector} (same : first.masses = second.masses) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Equality of each coordinate as a rational value; denominators may differ. -/
def SameMasses : List QProb → List QProb → Prop
  | [], [] => True
  | p :: ps, q :: qs => QProb.Equiv p q ∧ SameMasses ps qs
  | _, _ => False

instance decidableSameMasses : (xs ys : List QProb) → Decidable (SameMasses xs ys)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun impossible => impossible)
  | _ :: _, [] => isFalse (fun impossible => impossible)
  | p :: ps, q :: qs =>
      letI := decidableSameMasses ps qs
      inferInstanceAs (Decidable (QProb.Equiv p q ∧ SameMasses ps qs))

def entropy (vector : ProbabilityVector) : ExactLog := entropySum vector.masses

theorem entropy_congr {first second : ProbabilityVector}
    (same : SameMasses first.masses second.masses) : ExactLog.Equiv first.entropy second.entropy := by
  have pointwise (xs ys : List QProb) (equal : SameMasses xs ys) :
      ExactLog.Equiv (entropySum xs) (entropySum ys) := by
    induction xs generalizing ys with
    | nil => cases ys with
      | nil => exact ExactLog.equiv_refl _
      | cons _ _ => exact False.elim equal
    | cons p ps ih => cases ys with
      | nil => exact False.elim equal
      | cons q qs => exact ExactLog.add_congr (entropyTerm_congr equal.1) (ih qs equal.2)
  exact pointwise first.masses second.masses same

def addNull (vector : ProbabilityVector) : ProbabilityVector :=
  ⟨QProb.zero :: vector.masses, QProb.equiv_trans
    (QProb.equiv_trans (QProb.add_comm QProb.zero _) (QProb.add_zero _)) vector.normalized⟩

theorem entropy_addNull (vector : ProbabilityVector) : (vector.addNull).entropy = vector.entropy :=
  entropySum_cons_zero vector.masses

def uniform (size : Nat) (positive : 0 < size) : ProbabilityVector where
  masses := List.replicate size ⟨1, size, positive⟩
  normalized := by
    have common := QProb.listSum_mk_same_den size positive (List.replicate size 1)
    simp only [List.map_replicate, List.sum_replicate_nat, Nat.mul_one] at common
    exact QProb.equiv_trans common (by simp only [QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul])

theorem uniform_entropy (size : Nat) (positive : 0 < size) :
    ExactLog.Equiv (uniform size positive).entropy (ExactLog.log (PositiveRatio.ofNat size positive)) := by
  let vector := uniform size positive
  let score := ExactLog.log (PositiveRatio.ofNat size positive)
  have terms : ExactLog.Equiv vector.entropy
      (ExactLog.listSum (vector.masses.map (fun q => ExactLog.scaleRatio q score))) := by
    apply ExactLog.listSum_map_congr
    intro q member
    have same : q = (⟨1, size, positive⟩ : QProb) := List.eq_of_mem_replicate member
    subst q
    exact ExactLog.equiv_refl _
  have normalized := ExactLog.scaleRatio_weight_congr vector.normalized score
  rw [ExactLog.scaleRatio_one] at normalized
  exact ExactLog.equiv_trans terms
    (ExactLog.equiv_trans (ExactLog.listSum_scaleRatio_weights vector.masses score) normalized)

theorem uniform_entropy_mono (first second : Nat) (positiveFirst : 0 < first) (positiveSecond : 0 < second)
    (ordered : first ≤ second) : ExactLog.LE (uniform first positiveFirst).entropy (uniform second positiveSecond).entropy := by
  apply (ExactLog.le_congr (uniform_entropy first positiveFirst) (uniform_entropy second positiveSecond)).mpr
  apply (ExactLog.log_le_log_iff _ _).mpr
  simpa only [PositiveRatio.LE, PositiveRatio.ofNat, QProb.LE, PositiveRatio.toQProb, Nat.mul_one] using ordered

/-- Finite two-stage choices. Even a zero-probability branch retains a
normalized conditional vector; its contribution is independent of that choice. -/
structure Compound where
  branches : List (QProb × ProbabilityVector)
  normalized : QProb.Equiv (QProb.listSum (branches.map Prod.fst)) QProb.one

def Compound.outer (choice : Compound) : ProbabilityVector := ⟨choice.branches.map Prod.fst, choice.normalized⟩

def Compound.refined (choice : Compound) : ProbabilityVector where
  masses := choice.branches.flatMap (fun branch => branch.2.masses.map (QProb.mul branch.1))
  normalized := by
    have summed := QProb.listSum_flatMap choice.branches
      (fun branch => branch.2.masses.map (QProb.mul branch.1))
    have collapsed := QProb.listSum_map_congr choice.branches
      (fun branch => QProb.listSum (branch.2.masses.map (QProb.mul branch.1))) Prod.fst (fun branch =>
        QProb.equiv_trans (QProb.equiv_symm (QProb.mul_listSum branch.1 branch.2.masses))
          (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) branch.2.normalized) (QProb.mul_one _)))
    exact QProb.equiv_trans summed (QProb.equiv_trans collapsed choice.normalized)

theorem Compound.entropy_grouping (choice : Compound) :
    ExactLog.Equiv choice.refined.entropy
      (ExactLog.add choice.outer.entropy (ExactLog.listSum (choice.branches.map
        (fun branch => ExactLog.scaleRatio branch.1 branch.2.entropy)))) := by
  have grouping := entropySum_grouping (choice.branches.map (fun branch => (branch.1, branch.2.masses))) (by
    intro branch member
    rcases List.mem_map.mp member with ⟨source, _, rfl⟩
    exact source.2.normalized)
  simpa only [Compound.refined, Compound.outer, entropy, List.flatMap_map, List.map_map, Function.comp_def] using grouping

/-- Read the existing law through aggregated singleton masses. Split atoms
and null outliers never become new uncertainty coordinates. -/
def ofDistro [DecidableEq A] (law : Distros.Distro A) (grid : Distros.EntropyGrid A)
    (support : law.AlmostSurely (fun value => value ∈ grid.cells)) : ProbabilityVector :=
  ⟨grid.cells.map law.pmf, law.pmf_grid_normalization grid support⟩

theorem ofDistro_entropy [DecidableEq A] (law : Distros.Distro A) (grid : Distros.EntropyGrid A)
    (support : law.AlmostSurely (fun value => value ∈ grid.cells)) :
    (ofDistro law grid support).entropy = law.entropy grid support := by
  simp only [ofDistro, entropy, entropySum, Distros.Distro.entropy, List.map_map, Function.comp_def]

end ProbabilityVector

/-- Explicit rational Shannon requirements. The value space is `ExactLog`
with its existing rational-power equivalence and order. No uniform logarithm
formula, derivative, continuity or uniqueness conclusion is assumed here. -/
structure UncertaintyMeasure where
  value : ProbabilityVector → ExactLog
  representation : ∀ first second, ProbabilityVector.SameMasses first.masses second.masses →
    ExactLog.Equiv (value first) (value second)
  permutation : ∀ first second, first.masses.Perm second.masses → ExactLog.Equiv (value first) (value second)
  null : ∀ vector, ExactLog.Equiv (value vector.addNull) (value vector)
  grouping : ∀ choice : ProbabilityVector.Compound, ExactLog.Equiv (value choice.refined)
    (ExactLog.add (value choice.outer) (ExactLog.listSum (choice.branches.map
      (fun branch => ExactLog.scaleRatio branch.1 (value branch.2)))))
  uniform_mono : ∀ first second (positiveFirst : 0 < first) (positiveSecond : 0 < second), first ≤ second →
    ExactLog.LE (value (ProbabilityVector.uniform first positiveFirst)) (value (ProbabilityVector.uniform second positiveSecond))
  fair : ExactLog.Equiv (value (ProbabilityVector.uniform 2 (by decide)))
    (ExactLog.log (PositiveRatio.ofNat 2 (by decide)))

/-- The implemented entropy satisfies every listed requirement. This
inhabited specification is a prerequisite, not yet the uniqueness theorem. -/
def UncertaintyMeasure.shannon : UncertaintyMeasure where
  value := ProbabilityVector.entropy
  representation := fun _ _ same => ProbabilityVector.entropy_congr same
  permutation := fun _ _ same => entropySum_perm same
  null := fun vector => by rw [ProbabilityVector.entropy_addNull]; exact ExactLog.equiv_refl _
  grouping := ProbabilityVector.Compound.entropy_grouping
  uniform_mono := ProbabilityVector.uniform_entropy_mono
  fair := ProbabilityVector.uniform_entropy 2 (by decide)

end Thesis.Probability
