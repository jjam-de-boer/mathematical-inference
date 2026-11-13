import Thesis.Probability.Distros.RationalMoments
import Thesis.Probability.Distros.SignedConcentration

namespace Thesis.Probability.Distros

/-- A finite partition of actual weighted atom occurrences. Empty and
zero-mass cells are allowed; flattening preserves every occurrence and weight.
`ofEvents` below constructs partitions directly from Boolean evidence. -/
structure AtomPartition (μ : Distro Ω) where
  cells : List (List (Ω × Nat))
  perm : cells.flatten.Perm μ.record.atoms

private theorem totalMass_perm {left right : List (Ω × Nat)} (same : left.Perm right) :
    FiniteProbRecord.totalMass left = FiniteProbRecord.totalMass right := by
  induction same with
  | nil => rfl
  | cons atom _ ih => change atom.2 + _ = atom.2 + _; rw [ih]
  | swap a b atoms => exact Nat.add_left_comm _ _ _
  | trans _ _ first second => exact first.trans second

private theorem totalMass_cells (cells : List (List (Ω × Nat))) :
    FiniteProbRecord.totalMass (cells.map (fun cell => (cell, FiniteProbRecord.totalMass cell))) =
      FiniteProbRecord.totalMass cells.flatten := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      simp only [List.map_cons, FiniteProbRecord.totalMass, List.flatten_cons,
        FiniteProbRecord.totalMass_append, ih]

/-- Distribution of the partition cell, with its actual mass as weight. -/
def AtomPartition.distro {μ : Distro Ω} (partition : AtomPartition μ) : Distro (List (Ω × Nat)) :=
  ⟨⟨partition.cells.map (fun cell => (cell, FiniteProbRecord.totalMass cell)), μ.record.den, μ.record.den_pos,
    (totalMass_cells partition.cells).trans ((totalMass_perm partition.perm).trans μ.record.total_mass)⟩⟩

/-- Successive cuts make disjoint cells and retain the final complement.
Thus even overlapping or incomplete input event lists define an exhaustive
finite partition without a positivity assumption on individual cells. -/
def partitionAtomCuts : List (Event Ω) → List (Ω × Nat) → List (List (Ω × Nat))
  | [], atoms => [atoms]
  | event :: events, atoms => atoms.filter (fun atom => event atom.1) ::
      partitionAtomCuts events (atoms.filter (fun atom => !event atom.1))

theorem partitionAtomCuts_perm (events : List (Event Ω)) (atoms : List (Ω × Nat)) :
    (partitionAtomCuts events atoms).flatten.Perm atoms := by
  induction events generalizing atoms with
  | nil => simp only [partitionAtomCuts, List.flatten_cons, List.flatten_nil, List.append_nil]; exact List.Perm.refl _
  | cons event events ih =>
      change ((atoms.filter (fun atom => event atom.1)) ++
        (partitionAtomCuts events (atoms.filter (fun atom => !event atom.1))).flatten).Perm atoms
      exact ((ih _).append_left _).trans (List.filter_append_perm (fun atom => event atom.1) atoms)

def AtomPartition.ofEvents (μ : Distro Ω) (events : List (Event Ω)) : AtomPartition μ :=
  ⟨partitionAtomCuts events μ.record.atoms, partitionAtomCuts_perm events μ.record.atoms⟩

/-- The conditional expectation in a cell is its genuine normalized
rational integral when supported. Its zero-mass value is the explicit zero. -/
def conditionalBlockMean (atoms : List (Ω × Nat)) (f : Ω → SignedRatio) : SignedRatio :=
  if positive : 0 < FiniteProbRecord.totalMass atoms then
    SignedRatio.divideNat (FiniteProbRecord.rationalAtomSum atoms f) (FiniteProbRecord.totalMass atoms) positive
  else SignedRatio.zero

def conditionalBlockCovariance (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio) : SignedRatio :=
  SignedRatio.sub (conditionalBlockMean atoms (fun x => SignedRatio.mul (f x) (g x)))
    (SignedRatio.mul (conditionalBlockMean atoms f) (conditionalBlockMean atoms g))

def conditionalBlockVariance (atoms : List (Ω × Nat)) (f : Ω → SignedRatio) : SignedRatio :=
  conditionalBlockCovariance atoms f f

/-- Supported event cells use exactly the library's existing conditioning
operation, rather than a separate assumed conditional probability law. -/
theorem conditionalBlockMean_conditionOn (μ : Distro Ω) (event : Event Ω)
    (positive : μ.record.EventPositive event) (f : Ω → SignedRatio) :
    conditionalBlockMean (μ.record.atoms.filter (fun atom => event atom.1)) f =
      (μ.record.conditionOn event positive).rationalMean f := by
  have massPositive : 0 < FiniteProbRecord.totalMass (μ.record.atoms.filter (fun atom => event atom.1)) := by
    rw [FiniteProbRecord.totalMass_filter_event]; exact positive
  unfold conditionalBlockMean
  rw [dif_pos massPositive]
  simp only [FiniteProbRecord.rationalMean, FiniteProbRecord.conditionOn,
    FiniteProbRecord.totalMass_filter_event]

private theorem rationalAtomSum_zero_mass (atoms : List (Ω × Nat)) (zero : FiniteProbRecord.totalMass atoms = 0)
    (f : Ω → SignedRatio) : SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms f) SignedRatio.zero := by
  induction atoms with
  | nil => exact SignedRatio.equiv_refl _
  | cons atom atoms ih =>
      have head : atom.2 = 0 := by change atom.2 + _ = 0 at zero; omega
      have tail : FiniteProbRecord.totalMass atoms = 0 := by change atom.2 + _ = 0 at zero; omega
      refine SignedRatio.equiv_trans (SignedRatio.add_congr ?_ (ih tail)) (SignedRatio.add_zero _)
      simp only [SignedRatio.Equiv, SignedRatio.scaleNat, head, Int.natCast_zero,
        Int.zero_mul, SignedRatio.zero]

/-- Multiplying a cell's conditional mean by its mass recovers the
unnormalized integral. The zero-mass case is included without dividing by zero. -/
theorem conditionalBlockMean_weighted (atoms : List (Ω × Nat)) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (SignedRatio.scaleNat (FiniteProbRecord.totalMass atoms) (conditionalBlockMean atoms f))
      (FiniteProbRecord.rationalAtomSum atoms f) := by
  unfold conditionalBlockMean
  split
  · simp only [SignedRatio.Equiv, SignedRatio.scaleNat, SignedRatio.divideNat, Int.natCast_mul]
    ac_rfl
  · rename_i unsupported
    have zero : FiniteProbRecord.totalMass atoms = 0 := by omega
    refine SignedRatio.equiv_trans ?_ (SignedRatio.equiv_symm (rationalAtomSum_zero_mass atoms zero f))
    simp only [SignedRatio.Equiv, SignedRatio.scaleNat, zero, SignedRatio.zero, Int.natCast_zero, Int.zero_mul]

theorem rationalAtomSum_append (left right : List (Ω × Nat)) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum (left ++ right) f)
      (SignedRatio.add (FiniteProbRecord.rationalAtomSum left f) (FiniteProbRecord.rationalAtomSum right f)) := by
  have result := SignedRatio.listSum_append (left.map (fun atom => SignedRatio.scaleNat atom.2 (f atom.1)))
    (right.map (fun atom => SignedRatio.scaleNat atom.2 (f atom.1)))
  simpa only [FiniteProbRecord.rationalAtomSum, List.map_append] using result

theorem rationalAtomSum_flatten (cells : List (List (Ω × Nat))) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum cells.flatten f)
      (SignedRatio.listSum (cells.map (fun cell => FiniteProbRecord.rationalAtomSum cell f))) := by
  induction cells with
  | nil => exact SignedRatio.equiv_refl _
  | cons cell cells ih =>
      exact SignedRatio.equiv_trans (rationalAtomSum_append _ _ f)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) ih)

theorem rationalAtomSum_perm {left right : List (Ω × Nat)} (same : left.Perm right) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum left f) (FiniteProbRecord.rationalAtomSum right f) := by
  induction same with
  | nil => exact SignedRatio.equiv_refl _
  | cons atom _ ih => exact SignedRatio.add_congr (SignedRatio.equiv_refl _) ih
  | swap a b atoms => exact SignedRatio.add_left_comm _ _ _
  | trans _ _ first second => exact SignedRatio.equiv_trans first second

/-- Total expectation over every finite atom partition, for arbitrary
signed rational observables and including unsupported cells. -/
theorem AtomPartition.total_expectation {μ : Distro Ω} (partition : AtomPartition μ) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (partition.distro.rationalExpectation (fun cell => conditionalBlockMean cell f))
      (μ.rationalExpectation f) := by
  apply SignedRatio.divideNat_congr (denominator := μ.record.den) (positive := μ.record.den_pos)
  simp only [AtomPartition.distro, FiniteProbRecord.rationalAtomSum, List.map_map, Function.comp_def]
  change SignedRatio.Equiv
    (SignedRatio.listSum (partition.cells.map (fun cell =>
      SignedRatio.scaleNat (FiniteProbRecord.totalMass cell) (conditionalBlockMean cell f))))
    (FiniteProbRecord.rationalAtomSum μ.record.atoms f)
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr partition.cells _ _
    (fun cell => conditionalBlockMean_weighted cell f)) ?_
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (rationalAtomSum_flatten partition.cells f))
    (rationalAtomSum_perm partition.perm f)

end Thesis.Probability.Distros
