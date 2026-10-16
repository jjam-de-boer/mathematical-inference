import Thesis.Probability.Distros.Moments

namespace Thesis.Probability.Distros

/-! Repeated independent sums and their regrouping laws. -/

theorem record_eq_of_atoms {μ ν : FiniteProbRecord Ω} (h : μ.atoms = ν.atoms) : μ = ν := by
  have hd : μ.den = ν.den := by rw [← μ.total_mass, ← ν.total_mass, h]
  cases μ
  cases ν
  cases h
  cases hd
  rfl

/-- Natural-outcome convolution, retaining each pair as a separate atom. -/
def convolutionAtoms (left right : List (Nat × Nat)) : List (Nat × Nat) :=
  (FiniteProbRecord.weightedCartesian left right).map
    (fun atom => (atom.1.1 + atom.1.2, atom.2))

theorem convolutionAtoms_assoc (a b c : List (Nat × Nat)) :
    convolutionAtoms (convolutionAtoms a b) c =
      convolutionAtoms a (convolutionAtoms b c) := by
  simp only [convolutionAtoms, FiniteProbRecord.weightedCartesian,
    List.map_flatMap, List.flatMap_map, List.map_map, List.flatMap_assoc,
    Function.comp_def, Nat.add_assoc, Nat.mul_assoc]

theorem convolutionAtoms_zero_right (atoms : List (Nat × Nat)) :
    convolutionAtoms atoms [(0, 1)] = atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [convolutionAtoms, FiniteProbRecord.weightedCartesian,
        List.flatMap_cons, List.map_cons, List.map_nil,
        List.singleton_append, Nat.add_zero, Nat.mul_one] at *
      rw [ih]

/-- Independent sum as a probability record on natural outcomes. -/
def sumRecord (μ ν : FiniteProbRecord Nat) : FiniteProbRecord Nat :=
  (μ.product ν).map (fun pair => pair.1 + pair.2)

theorem sumRecord_assoc (a b c : FiniteProbRecord Nat) :
    sumRecord (sumRecord a b) c = sumRecord a (sumRecord b c) :=
  record_eq_of_atoms (convolutionAtoms_assoc a.atoms b.atoms c.atoms)

/-- Sum of `n` independent copies; zero copies are the point mass at zero. -/
def iteratedSumRecord (μ : FiniteProbRecord Nat) : Nat → FiniteProbRecord Nat
  | 0 => ⟨[(0, 1)], 1, by decide, rfl⟩
  | n + 1 => sumRecord (iteratedSumRecord μ n) μ

theorem iteratedSumRecord_add (μ : FiniteProbRecord Nat) (n m : Nat) :
    iteratedSumRecord μ (n + m) =
      sumRecord (iteratedSumRecord μ n) (iteratedSumRecord μ m) := by
  induction m with
  | zero =>
      exact record_eq_of_atoms (convolutionAtoms_zero_right _).symm
  | succ m ih =>
      change sumRecord (iteratedSumRecord μ (n + m)) μ =
        sumRecord (iteratedSumRecord μ n) (sumRecord (iteratedSumRecord μ m) μ)
      rw [ih, sumRecord_assoc]

theorem sumRecord_map (μ : FiniteProbRecord Ω) (ν : FiniteProbRecord X)
    (f : Ω → Nat) (g : X → Nat) :
    sumRecord (μ.map f) (ν.map g) =
      (μ.product ν).map (fun pair => f pair.1 + g pair.2) := by
  apply record_eq_of_atoms
  simp only [sumRecord, FiniteProbRecord.map, FiniteProbRecord.product,
    FiniteProbRecord.weightedCartesian, List.flatMap_map, List.map_map,
    List.map_flatMap, Function.comp_def]

def naturalDistro (μ : FiniteProbRecord Nat) : NatDistro Nat := ⟨⟨μ⟩, id⟩

theorem sumRecord_mean (μ ν : FiniteProbRecord Nat) :
    QProb.Equiv (mean (naturalDistro (sumRecord μ ν)))
      (QProb.add (mean (naturalDistro μ)) (mean (naturalDistro ν))) := by
  have transport := NatDistro.mean_map (independentSum (naturalDistro μ) (naturalDistro ν))
    (fun pair => pair.1 + pair.2) id
  change mean (naturalDistro (sumRecord μ ν)) =
    mean (independentSum (naturalDistro μ) (naturalDistro ν)) at transport
  rw [transport]
  exact independentSum_mean _ _

theorem sumRecord_variance (μ ν : FiniteProbRecord Nat) :
    QProb.Equiv (variance (naturalDistro (sumRecord μ ν)))
      (QProb.add (variance (naturalDistro μ)) (variance (naturalDistro ν))) := by
  have transport := NatDistro.variance_map (independentSum (naturalDistro μ) (naturalDistro ν))
    (fun pair => pair.1 + pair.2) id
  change variance (naturalDistro (sumRecord μ ν)) =
    variance (independentSum (naturalDistro μ) (naturalDistro ν)) at transport
  rw [transport]
  exact independentSum_variance _ _

theorem sumRecord_pgf (μ ν : FiniteProbRecord Nat) (s : QProb) :
    QProb.Equiv (pgf (naturalDistro (sumRecord μ ν)) s)
      (QProb.mul (pgf (naturalDistro μ) s) (pgf (naturalDistro ν) s)) := by
  have transport := NatDistro.pgf_map (independentSum (naturalDistro μ) (naturalDistro ν))
    (fun pair => pair.1 + pair.2) id s
  change pgf (naturalDistro (sumRecord μ ν)) s =
    pgf (independentSum (naturalDistro μ) (naturalDistro ν)) s at transport
  rw [transport]
  exact independentSum_pgf _ _ _

theorem qprob_scale_succ (n : Nat) (value : QProb) :
    QProb.Equiv (QProb.add (QProb.scale n value) value) (QProb.scale (n + 1) value) := by
  simp only [QProb.Equiv, QProb.add, QProb.scale, Nat.succ_mul, Nat.add_mul]
  ac_rfl

theorem iteratedSumRecord_mean (μ : FiniteProbRecord Nat) (n : Nat) :
    QProb.Equiv (mean (naturalDistro (iteratedSumRecord μ n)))
      (QProb.scale n (mean (naturalDistro μ))) := by
  induction n with
  | zero => simp only [mean_expectNat, naturalDistro, iteratedSumRecord, Distro.expectNat,
      natIntegral, id, Nat.mul_zero, Nat.add_zero, QProb.Equiv, QProb.scale, Nat.zero_mul]
  | succ n ih =>
      exact QProb.equiv_trans (sumRecord_mean _ _)
        (QProb.equiv_trans (QProb.add_congr ih (QProb.equiv_refl _)) (qprob_scale_succ n _))

theorem iteratedSumRecord_variance (μ : FiniteProbRecord Nat) (n : Nat) :
    QProb.Equiv (variance (naturalDistro (iteratedSumRecord μ n)))
      (QProb.scale n (variance (naturalDistro μ))) := by
  induction n with
  | zero => simp only [variance, QProb.sub, secondMomentScaled, meanSq, secondMoment,
      rawMoment, mean, natAtoms, naturalDistro, iteratedSumRecord,
      List.map_cons, List.map_nil, Combinatorics.weightedPowSum,
      QProb.Equiv, QProb.scale, id, Nat.zero_pow (by decide : 0 < 1),
      Nat.mul_zero, Nat.zero_mul, Nat.add_zero,
      Nat.sub_self]
  | succ n ih =>
      exact QProb.equiv_trans (sumRecord_variance _ _)
        (QProb.equiv_trans (QProb.add_congr ih (QProb.equiv_refl _)) (qprob_scale_succ n _))

theorem iteratedSumRecord_pgf (μ : FiniteProbRecord Nat) (n : Nat) (s : QProb) :
    QProb.Equiv (pgf (naturalDistro (iteratedSumRecord μ n)) s)
      (qpow (pgf (naturalDistro μ) s) n) := by
  induction n with
  | zero => simp only [pgf, naturalDistro, iteratedSumRecord, id, qpow,
      List.map_cons, List.map_nil, QProb.listSum, QProb.scale, QProb.one, QProb.zero,
      QProb.Equiv, QProb.div, QProb.ofNat, QProb.add, Nat.mul_one, Nat.add_zero]
  | succ n ih =>
      exact QProb.equiv_trans (sumRecord_pgf _ _ _)
        (QProb.equiv_trans (QProb.mul_congr ih (QProb.equiv_refl _)) (QProb.mul_comm _ _))

end Thesis.Probability.Distros
