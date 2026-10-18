import Thesis.Probability.Distros.ConditionalTower
import Thesis.Probability.Distros.RationalCovarianceAlgebra
import Thesis.Probability.FiniteRecordSupport

namespace Thesis.Probability.Distros

/-- Equal unnormalized fibre integrals have equal conditional means,
including unsupported fibres with the existing explicit zero convention. -/
theorem conditionalBlockMean_congr_integral (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio)
    (same : SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum atoms f) (FiniteProbRecord.rationalAtomSum atoms g)) :
    SignedRatio.Equiv (conditionalBlockMean atoms f) (conditionalBlockMean atoms g) := by
  by_cases positive : 0 < FiniteProbRecord.totalMass atoms
  · simpa only [conditionalBlockMean, dif_pos positive] using
      (SignedRatio.divideNat_congr same (FiniteProbRecord.totalMass atoms) positive)
  · simp only [conditionalBlockMean, dif_neg positive]
    exact SignedRatio.equiv_refl _

theorem conditionalBlockMean_congr_on_support (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio)
    (same : ∀ atom ∈ atoms, SignedRatio.Equiv (f atom.1) (g atom.1)) :
    SignedRatio.Equiv (conditionalBlockMean atoms f) (conditionalBlockMean atoms g) :=
  conditionalBlockMean_congr_integral atoms f g (rationalAtomSum_congr_on_support atoms f g same)

theorem conditionalBlockMean_add (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (conditionalBlockMean atoms (fun x => SignedRatio.add (f x) (g x)))
      (SignedRatio.add (conditionalBlockMean atoms f) (conditionalBlockMean atoms g)) := by
  by_cases positive : 0 < FiniteProbRecord.totalMass atoms
  · let ν : Distro Ω := ⟨⟨atoms, FiniteProbRecord.totalMass atoms, positive, rfl⟩⟩
    simpa only [conditionalBlockMean, dif_pos positive] using ν.rationalExpectation_add f g
  · simp only [conditionalBlockMean, dif_neg positive]
    exact SignedRatio.equiv_symm (SignedRatio.add_zero _)

theorem conditionalBlockMean_mul_left (atoms : List (Ω × Nat)) (c : SignedRatio) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (conditionalBlockMean atoms (fun x => SignedRatio.mul c (f x)))
      (SignedRatio.mul c (conditionalBlockMean atoms f)) := by
  by_cases positive : 0 < FiniteProbRecord.totalMass atoms
  · let ν : Distro Ω := ⟨⟨atoms, FiniteProbRecord.totalMass atoms, positive, rfl⟩⟩
    simpa only [conditionalBlockMean, dif_pos positive] using ν.rationalExpectation_mul_left c f
  · simp only [conditionalBlockMean, dif_neg positive]
    exact SignedRatio.equiv_symm (SignedRatio.mul_zero _)

theorem conditionalBlockMean_sub (atoms : List (Ω × Nat)) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (conditionalBlockMean atoms (fun x => SignedRatio.sub (f x) (g x)))
      (SignedRatio.sub (conditionalBlockMean atoms f) (conditionalBlockMean atoms g)) := by
  by_cases positive : 0 < FiniteProbRecord.totalMass atoms
  · let ν : Distro Ω := ⟨⟨atoms, FiniteProbRecord.totalMass atoms, positive, rfl⟩⟩
    simpa only [conditionalBlockMean, dif_pos positive] using ν.rationalExpectation_sub f g
  · simp only [conditionalBlockMean, dif_neg positive]
    exact SignedRatio.equiv_refl _

theorem conditionalBlockMean_constant (atoms : List (Ω × Nat)) (c : SignedRatio)
    (positive : 0 < FiniteProbRecord.totalMass atoms) :
    SignedRatio.Equiv (conditionalBlockMean atoms (fun _ => c)) c := by
  let ν : Distro Ω := ⟨⟨atoms, FiniteProbRecord.totalMass atoms, positive, rfl⟩⟩
  simpa only [conditionalBlockMean, dif_pos positive] using ν.rationalExpectation_constant c

theorem Distro.conditionalExpectation_add (μ : Distro Ω) (key : Ω → Fin colours)
    (f g : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation key (fun y => SignedRatio.add (f y) (g y)) x)
      (SignedRatio.add (μ.conditionalExpectation key f x) (μ.conditionalExpectation key g x)) :=
  conditionalBlockMean_add _ f g

theorem Distro.conditionalExpectation_scale (μ : Distro Ω) (key : Ω → Fin colours)
    (c : SignedRatio) (f : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation key (fun y => SignedRatio.mul c (f y)) x)
      (SignedRatio.mul c (μ.conditionalExpectation key f x)) :=
  conditionalBlockMean_mul_left _ c f

theorem Distro.conditionalExpectation_sub (μ : Distro Ω) (key : Ω → Fin colours)
    (f g : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation key (fun y => SignedRatio.sub (f y) (g y)) x)
      (SignedRatio.sub (μ.conditionalExpectation key f x) (μ.conditionalExpectation key g x)) :=
  conditionalBlockMean_sub _ f g

theorem Distro.conditionalExpectation_linear (μ : Distro Ω) (key : Ω → Fin colours)
    (a b : SignedRatio) (f g : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation key
      (fun y => SignedRatio.add (SignedRatio.mul a (f y)) (SignedRatio.mul b (g y))) x)
      (SignedRatio.add (SignedRatio.mul a (μ.conditionalExpectation key f x))
        (SignedRatio.mul b (μ.conditionalExpectation key g x))) :=
  SignedRatio.equiv_trans (μ.conditionalExpectation_add key _ _ x)
    (SignedRatio.add_congr (μ.conditionalExpectation_scale key a f x) (μ.conditionalExpectation_scale key b g x))

/-- A function of the evidence label pulls outside its conditional mean.
The statement is pointwise even on unsupported fibres: both sides vanish. -/
theorem Distro.conditionalExpectation_pull_out (μ : Distro Ω) (key : Ω → Fin colours)
    (h : Fin colours → SignedRatio) (f : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation key (fun y => SignedRatio.mul (h (key y)) (f y)) x)
      (SignedRatio.mul (h (key x)) (μ.conditionalExpectation key f x)) := by
  let cell := μ.record.atoms.filter (fun atom => decide (key atom.1 = key x))
  refine SignedRatio.equiv_trans (conditionalBlockMean_congr_on_support cell
    (fun y => SignedRatio.mul (h (key y)) (f y)) (fun y => SignedRatio.mul (h (key x)) (f y)) ?_)
    (conditionalBlockMean_mul_left cell (h (key x)) f)
  intro atom member
  have same := of_decide_eq_true (List.mem_filter.mp member).2
  change SignedRatio.Equiv (SignedRatio.mul (h (key atom.1)) (f atom.1))
    (SignedRatio.mul (h (key x)) (f atom.1))
  rw [same]
  exact SignedRatio.equiv_refl _

theorem Distro.conditionalExpectation_idempotent (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation key (μ.conditionalExpectation key f) x)
      (μ.conditionalExpectation key f x) :=
  conditionalBlockMean_congr_integral _ _ _ (μ.conditionalExpectation_fibre_integral key f (key x))

theorem Distro.observableFibre_positive (μ : Distro Ω) (key : Ω → Fin colours)
    (atom : Ω × Nat) (member : atom ∈ μ.record.atoms) (weight : 0 < atom.2) :
    μ.record.EventPositive (fun y => decide (key y = key atom.1)) :=
  (FiniteProbRecord.eventMass_pos_iff_exists_atom μ.record.atoms _).mpr
    ⟨atom, member, weight, decide_eq_true rfl⟩

theorem Distro.conditionalExpectation_of_key (μ : Distro Ω) (key : Ω → Fin colours)
    (h : Fin colours → SignedRatio) (x : Ω)
    (positive : μ.record.EventPositive (fun y => decide (key y = key x))) :
    SignedRatio.Equiv (μ.conditionalExpectation key (fun y => h (key y)) x) (h (key x)) := by
  let cell := μ.record.atoms.filter (fun atom => decide (key atom.1 = key x))
  have mass : 0 < FiniteProbRecord.totalMass cell := by
    change 0 < FiniteProbRecord.totalMass (μ.record.atoms.filter (fun atom => decide (key atom.1 = key x)))
    rw [FiniteProbRecord.totalMass_filter_event μ.record.atoms (fun y => decide (key y = key x))]
    exact positive
  refine SignedRatio.equiv_trans (conditionalBlockMean_congr_on_support cell _ (fun _ => h (key x)) ?_)
    (conditionalBlockMean_constant cell (h (key x)) mass)
  intro atom member
  have same := of_decide_eq_true (List.mem_filter.mp member).2
  change SignedRatio.Equiv (h (key atom.1)) (h (key x))
  rw [same]
  exact SignedRatio.equiv_refl _

/-- Fibre-integral preservation characterizes the conditional mean among
label observables up to almost-sure rational equivalence. Values on null
fibres are retained and impose no pointwise uniqueness requirement. -/
theorem Distro.conditionalExpectation_unique (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (h : Fin colours → SignedRatio)
    (preserves : ∀ label, SignedRatio.Equiv
      (FiniteProbRecord.rationalAtomSum (μ.record.atoms.filter (fun atom => decide (key atom.1 = label))) f)
      (FiniteProbRecord.rationalAtomSum (μ.record.atoms.filter (fun atom => decide (key atom.1 = label))) (fun y => h (key y)))) :
    μ.AlmostSurely (fun x => SignedRatio.Equiv (μ.conditionalExpectation key f x) (h (key x))) := by
  intro atom member weight
  exact SignedRatio.equiv_trans (conditionalBlockMean_congr_integral _ _ _ (preserves (key atom.1)))
    (μ.conditionalExpectation_of_key key h atom.1 (μ.observableFibre_positive key atom member weight))

end Thesis.Probability.Distros
