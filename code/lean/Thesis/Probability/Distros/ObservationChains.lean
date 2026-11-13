import Thesis.Probability.Distros.AlmostSureTower
import Thesis.Probability.Distros.RefinementGain

namespace Thesis.Probability.Distros

/-- A finite observation sequence with possibly different finite label
spaces. Only successive refinements through the declared horizon are required,
and they are required only on positive-weight occurrences. -/
structure ObservationChain (μ : Distro Ω) (horizon : Nat) where
  labels : Nat → Nat
  observe : (stage : Nat) → Ω → Fin (labels stage)
  merge : (stage : Nat) → Fin (labels (stage + 1)) → Fin (labels stage)
  agrees : ∀ stage, stage < horizon → μ.AlmostSurely
    (fun x => observe stage x = merge stage (observe (stage + 1) x))

namespace ObservationChain
variable {μ : Distro Ω} {horizon : Nat}

def mergeTo (chain : ObservationChain μ horizon) (start : Nat) :
    (steps : Nat) → Fin (chain.labels (start + steps)) → Fin (chain.labels start)
  | 0, label => label
  | steps + 1, label => chain.mergeTo start steps (chain.merge (start + steps) label)

theorem agreesTo (chain : ObservationChain μ horizon) (start steps : Nat) (within : start + steps ≤ horizon) :
    μ.AlmostSurely (fun x => chain.observe start x = chain.mergeTo start steps (chain.observe (start + steps) x)) := by
  induction steps with
  | zero => intro atom _ _; rfl
  | succ steps ih =>
      intro atom member weight
      have previous := ih (by omega) atom member weight
      have last := chain.agrees (start + steps) (by omega) atom member weight
      exact previous.trans (congrArg (chain.mergeTo start steps) last)

/-- The tower law between any two stages, pointwise even at unsupported
fibres, while the chain's refinement obligations are only almost sure. -/
theorem tower (chain : ObservationChain μ horizon) (start steps : Nat) (within : start + steps ≤ horizon)
    (f : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation (chain.observe start)
      (μ.conditionalExpectation (chain.observe (start + steps)) f) x)
      (μ.conditionalExpectation (chain.observe start) f x) :=
  μ.conditionalExpectation_tower_almostSurely (chain.observe (start + steps)) (chain.observe start)
    (chain.mergeTo start steps) (chain.agreesTo start steps within) f x

def predictor (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (stage : Nat)
    (label : Fin (chain.labels stage)) : SignedRatio :=
  conditionalBlockMean (μ.record.atoms.filter (fun atom => decide (chain.observe stage atom.1 = label))) f

def mean (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (stage : Nat) : Ω → SignedRatio :=
  μ.conditionalExpectation (chain.observe stage) f

def increment (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (stage : Nat) (x : Ω) : SignedRatio :=
  SignedRatio.sub (chain.mean f (stage + 1) x) (chain.mean f stage x)

/-- Each increment has conditional mean zero at its previous observation.
The equality includes unsupported fibres, rather than choosing null values. -/
theorem increment_conditional_zero (chain : ObservationChain μ horizon) (f : Ω → SignedRatio)
    (stage : Nat) (within : stage < horizon) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation (chain.observe stage) (chain.increment f stage) x) SignedRatio.zero :=
  SignedRatio.equiv_trans (μ.conditionalExpectation_sub (chain.observe stage) (chain.mean f (stage + 1)) (chain.mean f stage) x)
    (SignedRatio.equiv_trans (ratio_sub_congr (chain.tower stage 1 (by omega) f x)
      (μ.conditionalExpectation_idempotent (chain.observe stage) f x))
      ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_refl _)))

theorem increment_mean_zero (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (stage : Nat) :
    SignedRatio.Equiv (μ.rationalExpectation (chain.increment f stage)) SignedRatio.zero :=
  SignedRatio.equiv_trans (μ.rationalExpectation_sub _ _)
    (SignedRatio.equiv_trans (ratio_sub_congr (μ.conditionalExpectation_total (chain.observe (stage + 1)) f)
      (μ.conditionalExpectation_total (chain.observe stage) f))
      ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_refl _)))

/-- Every earlier conditional mean is orthogonal to a later increment. -/
theorem mean_increment_orthogonal (chain : ObservationChain μ horizon) (f : Ω → SignedRatio)
    (start gap : Nat) (within : start + gap < horizon) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.mul
      (chain.mean f start x) (chain.increment f (start + gap) x))) SignedRatio.zero := by
  let h := fun label => chain.predictor f start (chain.mergeTo start gap label)
  have measurable : μ.AlmostSurely (fun x => SignedRatio.Equiv
      (chain.mean f start x) (h (chain.observe (start + gap) x))) := by
    intro atom member weight
    change SignedRatio.Equiv (chain.predictor f start (chain.observe start atom.1))
      (chain.predictor f start (chain.mergeTo start gap (chain.observe (start + gap) atom.1)))
    rw [chain.agreesTo start gap (by omega) atom member weight]
    exact SignedRatio.equiv_refl _
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr_positive _
    (fun x => SignedRatio.mul (h (chain.observe (start + gap) x))
      (SignedRatio.sub (chain.mean f (start + gap + 1) x)
        (μ.conditionalExpectation (chain.observe (start + gap)) (chain.mean f (start + gap + 1)) x))) ?_) ?_
  · intro atom member weight
    exact SignedRatio.mul_congr (measurable atom member weight)
      (ratio_sub_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_symm (chain.tower (start + gap) 1 (by omega) f atom.1)))
  · exact μ.conditionalExpectation_orthogonal (chain.observe (start + gap)) (chain.mean f (start + gap + 1)) h

/-- Distinct increments are orthogonal in the original weighted law.
The later index is written as early+1+gap, covering every strictly later stage. -/
theorem increments_orthogonal (chain : ObservationChain μ horizon) (f : Ω → SignedRatio)
    (early gap : Nat) (within : early + 1 + gap < horizon) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => SignedRatio.mul
      (chain.increment f early x) (chain.increment f (early + 1 + gap) x))) SignedRatio.zero := by
  have first := chain.mean_increment_orthogonal f (early + 1) gap within
  have second := chain.mean_increment_orthogonal f early (gap + 1) (by omega)
  have same : early + (gap + 1) = early + 1 + gap := by omega
  rw [same] at second
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _ (fun x => SignedRatio.sub_mul
    (chain.mean f (early + 1) x) (chain.mean f early x) (chain.increment f (early + 1 + gap) x))) ?_
  exact SignedRatio.equiv_trans (μ.rationalExpectation_sub _ _)
    (SignedRatio.equiv_trans (ratio_sub_congr first second) (SignedRatio.sub_zero SignedRatio.zero))

def energy (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (stage : Nat) : SignedRatio :=
  μ.rationalExpectation (fun x => SignedRatio.mul (chain.increment f stage x) (chain.increment f stage x))

def gain (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (start : Nat) : Nat → SignedRatio
  | 0 => SignedRatio.zero
  | steps + 1 => SignedRatio.add (chain.gain f start steps) (chain.energy f (start + steps))

theorem energy_nonnegative (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (stage : Nat) :
    SignedRatio.Nonnegative (chain.energy f stage) :=
  μ.rationalExpectation_nonnegative _ (fun _ _ _ => SignedRatio.nonnegative_square _)

theorem gain_nonnegative (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (start steps : Nat) :
    SignedRatio.Nonnegative (chain.gain f start steps) := by
  induction steps with
  | zero => exact SignedRatio.nonnegative_zero
  | succ steps ih => exact SignedRatio.nonnegative_add ih (chain.energy_nonnegative f (start + steps))

theorem gain_sum (chain : ObservationChain μ horizon) (f : Ω → SignedRatio) (start steps : Nat) :
    SignedRatio.Equiv (chain.gain f start steps)
      (SignedRatio.listSum ((List.range steps).map (fun step => chain.energy f (start + step)))) := by
  induction steps with
  | zero => exact SignedRatio.equiv_refl _
  | succ steps ih =>
      rw [List.range_succ, List.map_append]
      exact SignedRatio.equiv_trans (SignedRatio.add_congr ih (SignedRatio.equiv_refl _))
        (SignedRatio.equiv_symm (SignedRatio.equiv_trans (SignedRatio.listSum_append _ _)
          (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.add_zero _))))

/-- Cumulative prediction improvement is exactly the sum of increment
energies, plus the final prediction error. No independence hypothesis is used. -/
theorem prediction_error_decomposition (chain : ObservationChain μ horizon) (f : Ω → SignedRatio)
    (start steps : Nat) (within : start + steps ≤ horizon) :
    SignedRatio.Equiv (μ.rationalSquaredError f (chain.mean f start))
      (SignedRatio.add (μ.rationalSquaredError f (chain.mean f (start + steps))) (chain.gain f start steps)) := by
  induction steps with
  | zero => exact SignedRatio.equiv_symm (SignedRatio.add_zero _)
  | succ steps ih =>
      have previous := ih (by omega)
      have next : SignedRatio.Equiv (μ.rationalSquaredError f (chain.mean f (start + steps)))
          (SignedRatio.add (μ.rationalSquaredError f (chain.mean f (start + steps + 1))) (chain.energy f (start + steps))) :=
        μ.conditionalExpectation_refinement_gain_almostSurely (chain.observe (start + steps + 1))
          (chain.observe (start + steps)) (chain.merge (start + steps)) (chain.agrees (start + steps) (by omega)) f
      exact SignedRatio.equiv_trans previous (SignedRatio.equiv_trans (SignedRatio.add_congr next (SignedRatio.equiv_refl _))
        (SignedRatio.equiv_trans (SignedRatio.add_assoc _ _ _)
          (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _))))

/-- The same decomposition with the cumulative gain exposed as a finite sum. -/
theorem prediction_error_sum (chain : ObservationChain μ horizon) (f : Ω → SignedRatio)
    (start steps : Nat) (within : start + steps ≤ horizon) :
    SignedRatio.Equiv (μ.rationalSquaredError f (chain.mean f start))
      (SignedRatio.add (μ.rationalSquaredError f (chain.mean f (start + steps)))
        (SignedRatio.listSum ((List.range steps).map (fun step => chain.energy f (start + step))))) :=
  SignedRatio.equiv_trans (chain.prediction_error_decomposition f start steps within)
    (SignedRatio.add_congr (SignedRatio.equiv_refl _) (chain.gain_sum f start steps))

end ObservationChain
end Thesis.Probability.Distros
