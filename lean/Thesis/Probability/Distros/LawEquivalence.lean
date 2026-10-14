import Thesis.Probability.Distros.Moments

namespace Thesis.Probability.Distros

/-!
Equality of finite probability laws and its transport through maps,
independent products, positive conditioning, expectations, moments,
variance and PGFs.  Outcome types need neither decidable equality nor a
finite enumeration.  Observable bounds and common denominators are
constructed on the records' explicit finite supports.
-/

/-- Agreement of all Boolean event probabilities, independent of the
ordering, splitting, or denominator of the atom presentation. -/
def Distro.SameLaw (μ ν : Distro Ω) : Prop :=
  ∀ event : Event Ω, QProb.Equiv (μ.record.probVal event) (ν.record.probVal event)

namespace Distro.SameLaw

theorem refl (μ : Distro Ω) : μ.SameLaw μ := fun _ => QProb.equiv_refl _

theorem symm {μ ν : Distro Ω} (h : μ.SameLaw ν) : ν.SameLaw μ :=
  fun event => QProb.equiv_symm (h event)

theorem trans {μ ν ξ : Distro Ω} (h : μ.SameLaw ν) (h' : ν.SameLaw ξ) : μ.SameLaw ξ :=
  fun event => QProb.equiv_trans (h event) (h' event)

theorem map {μ ν : Distro Ω} (h : μ.SameLaw ν) (f : Ω → X) :
    (μ.map f).SameLaw (ν.map f) := fun event =>
  QProb.equiv_trans (μ.map_probVal f event)
    (QProb.equiv_trans (h (fun x => event (f x))) (QProb.equiv_symm (ν.map_probVal f event)))

end Distro.SameLaw

theorem natIntegral_congr_on_support (atoms : List (Ω × Nat)) (f g : Ω → Nat)
    (h : ∀ atom ∈ atoms, f atom.1 = g atom.1) :
    natIntegral atoms f = natIntegral atoms g := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      rw [natIntegral, natIntegral, h atom (List.mem_cons_self ..),
        ih (fun other member => h other (List.mem_cons_of_mem _ member))]

theorem natIntegral_indicator (atoms : List (Ω × Nat)) (event : Event Ω) :
    natIntegral atoms (fun x => if event x then 1 else 0) =
      FiniteProbRecord.eventMass atoms event := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      cases selected : event atom.1 <;>
        simp only [natIntegral, FiniteProbRecord.eventMass, selected, Bool.false_eq_true,
          if_false, if_true, Nat.mul_zero, Nat.mul_one, Nat.zero_add, ih]

def observableBound (atoms : List (Ω × Nat)) (f : Ω → Nat) : Nat :=
  atoms.foldr (fun atom bound => max (f atom.1) bound) 0

theorem observableBound_mem (atoms : List (Ω × Nat)) (f : Ω → Nat)
    (atom : Ω × Nat) (member : atom ∈ atoms) : f atom.1 ≤ observableBound atoms f := by
  induction atoms with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with eq | member
      · subst atom
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem Distro.expectNat_congr_on_support (μ : Distro Ω) (f g : Ω → Nat)
    (h : ∀ atom ∈ μ.record.atoms, f atom.1 = g atom.1) : μ.expectNat f = μ.expectNat g := by
  simp only [expectNat, natIntegral_congr_on_support _ _ _ h]

theorem Distro.SameLaw.expectNat_min {μ ν : Distro Ω} (h : μ.SameLaw ν)
    (f : Ω → Nat) (bound : Nat) :
    QProb.Equiv (μ.expectNat (fun x => min (f x) bound))
      (ν.expectNat (fun x => min (f x) bound)) := by
  induction bound with
  | zero => simp only [expectNat, Nat.min_zero, natIntegral_constant,
      Nat.mul_zero, QProb.Equiv, Nat.zero_mul]
  | succ bound ih =>
      have point : (fun x => min (f x) (bound + 1)) =
          (fun x => min (f x) bound + if decide (bound < f x) then 1 else 0) := by
        funext x
        split <;> simp_all only [decide_eq_true_eq] <;> omega
      rw [point]
      refine QProb.equiv_trans (expectNat_add μ _ _) ?_
      refine QProb.equiv_trans (QProb.add_congr ih ?_) (QProb.equiv_symm (expectNat_add ν _ _))
      simpa only [expectNat, natIntegral_indicator, FiniteProbRecord.probVal] using
        h (fun x => decide (bound < f x))

/-- Equality on Boolean events transports any natural expectation, even
when the outcome type has no finite enumeration or decidable equality. -/
theorem Distro.SameLaw.expectNat {μ ν : Distro Ω} (h : μ.SameLaw ν) (f : Ω → Nat) :
    QProb.Equiv (μ.expectNat f) (ν.expectNat f) := by
  let bound := max (observableBound μ.record.atoms f) (observableBound ν.record.atoms f)
  have left : μ.expectNat f = μ.expectNat (fun x => min (f x) bound) := by
    apply expectNat_congr_on_support
    intro atom member
    exact (Nat.min_eq_left (Nat.le_trans (observableBound_mem _ _ atom member)
      (Nat.le_max_left _ _))).symm
  have right : ν.expectNat f = ν.expectNat (fun x => min (f x) bound) := by
    apply expectNat_congr_on_support
    intro atom member
    exact (Nat.min_eq_left (Nat.le_trans (observableBound_mem _ _ atom member)
      (Nat.le_max_right _ _))).symm
  rw [left, right]
  exact h.expectNat_min f bound

theorem rationalIntegral_congr_on_support (atoms : List (Ω × Nat)) (f g : Ω → QProb)
    (h : ∀ atom ∈ atoms, QProb.Equiv (f atom.1) (g atom.1)) :
    QProb.Equiv (rationalIntegral atoms f) (rationalIntegral atoms g) := by
  induction atoms with
  | nil => exact QProb.equiv_refl _
  | cons atom rest ih =>
      simp only [rationalIntegral, List.map_cons, QProb.listSum] at ih ⊢
      exact QProb.add_congr (QProb.scale_congr _ (h atom (List.mem_cons_self ..)))
        (ih (fun other member => h other (List.mem_cons_of_mem _ member)))

def observableDenominator (atoms : List (Ω × Nat)) (f : Ω → QProb) : Nat :=
  atoms.foldr (fun atom den => (f atom.1).den * den) 1

theorem observableDenominator_pos (atoms : List (Ω × Nat)) (f : Ω → QProb) :
    0 < observableDenominator atoms f := by
  induction atoms with
  | nil => exact Nat.zero_lt_one
  | cons atom rest ih => exact Nat.mul_pos (f atom.1).den_pos ih

theorem observableDenominator_dvd (atoms : List (Ω × Nat)) (f : Ω → QProb)
    (atom : Ω × Nat) (member : atom ∈ atoms) :
    (f atom.1).den ∣ observableDenominator atoms f := by
  induction atoms with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with eq | member
      · subst atom
        exact Nat.dvd_mul_right _ _
      · exact Nat.dvd_mul_left_of_dvd (ih member) _

theorem rationalIntegral_commonDen (atoms : List (Ω × Nat)) (f : Ω → Nat)
    (den : Nat) (positive : 0 < den) :
    QProb.Equiv (rationalIntegral atoms (fun x => ⟨f x, den, positive⟩))
      ⟨natIntegral atoms f, den, positive⟩ := by
  induction atoms with
  | nil => exact QProb.equiv_zero_mk den positive
  | cons atom rest ih =>
      simp only [rationalIntegral, List.map_cons, QProb.listSum] at ih ⊢
      exact QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) ih)
        (QProb.add_mk_same_den den positive (atom.2 * f atom.1) (natIntegral rest f))

theorem Distro.expectation_commonDen (μ : Distro Ω) (f : Ω → Nat)
    (den : Nat) (positive : 0 < den) :
    QProb.Equiv (μ.expectation (fun x => ⟨f x, den, positive⟩))
      (QProb.div (μ.expectNat f) (QProb.ofNat den) positive) := by
  refine QProb.equiv_trans
    (QProb.div_congr (rationalIntegral_commonDen μ.record.atoms f den positive)
      (QProb.equiv_refl _) μ.record.den_pos μ.record.den_pos) ?_
  simp only [expectNat, QProb.Equiv, QProb.div, QProb.ofNat, Nat.mul_one]
  ac_rfl

theorem Distro.expectation_congr_on_support (μ : Distro Ω) (f g : Ω → QProb)
    (h : ∀ atom ∈ μ.record.atoms, QProb.Equiv (f atom.1) (g atom.1)) :
    QProb.Equiv (μ.expectation f) (μ.expectation g) :=
  QProb.div_congr (rationalIntegral_congr_on_support _ _ _ h)
    (QProb.equiv_refl _) μ.record.den_pos μ.record.den_pos

/-- Event-law equality transports every nonnegative rational expectation.
Common denominators are constructed only on the two finite supports. -/
theorem Distro.SameLaw.expectation {μ ν : Distro Ω} (h : μ.SameLaw ν) (f : Ω → QProb) :
    QProb.Equiv (μ.expectation f) (ν.expectation f) := by
  let atoms := μ.record.atoms ++ ν.record.atoms
  let den := observableDenominator atoms f
  have positive : 0 < den := observableDenominator_pos atoms f
  let g := fun x => (f x).num * (den / (f x).den)
  have value (atom : Ω × Nat) (member : atom ∈ atoms) :
      QProb.Equiv (f atom.1) (⟨g atom.1, den, positive⟩ : QProb) := by
    have dvd := observableDenominator_dvd atoms f atom member
    change (f atom.1).num * den =
      ((f atom.1).num * (den / (f atom.1).den)) * (f atom.1).den
    rw [Nat.mul_assoc, Nat.div_mul_cancel dvd]
  refine QProb.equiv_trans
    (expectation_congr_on_support μ f (fun x => ⟨g x, den, positive⟩) (fun atom member =>
      value atom (List.mem_append_left _ member))) ?_
  refine QProb.equiv_trans (expectation_commonDen μ g den positive) ?_
  refine QProb.equiv_trans
    (QProb.div_congr (h.expectNat g) (QProb.equiv_refl _) positive positive) ?_
  refine QProb.equiv_trans (QProb.equiv_symm (expectation_commonDen ν g den positive)) ?_
  exact QProb.equiv_symm (expectation_congr_on_support ν f (fun x => ⟨g x, den, positive⟩) (fun atom member =>
    value atom (List.mem_append_right _ member)))

theorem natIntegral_eq_sum (atoms : List (Ω × Nat)) (f : Ω → Nat) :
    natIntegral atoms f = (atoms.map (fun atom => atom.2 * f atom.1)).sum := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp only [natIntegral, List.map_cons, List.sum_cons, ih]

theorem Distro.SameLaw.product {μ μ' : Distro Ω} {ν ν' : Distro X}
    (left : μ.SameLaw μ') (right : ν.SameLaw ν') :
    (μ.product ν).SameLaw (μ'.product ν') := by
  intro event
  have leftSwap : QProb.Equiv ((μ.product ν).record.probVal event)
      ((μ'.product ν).record.probVal event) := by
    have integral := left.expectNat (fun x =>
      FiniteProbRecord.eventMass ν.record.atoms (fun y => event (x, y)))
    change natIntegral μ.record.atoms _ * μ'.record.den =
      natIntegral μ'.record.atoms _ * μ.record.den at integral
    rw [natIntegral_eq_sum, natIntegral_eq_sum] at integral
    change FiniteProbRecord.eventMass
        (FiniteProbRecord.weightedCartesian μ.record.atoms ν.record.atoms) event *
          (μ'.record.den * ν.record.den) =
      FiniteProbRecord.eventMass
        (FiniteProbRecord.weightedCartesian μ'.record.atoms ν.record.atoms) event *
          (μ.record.den * ν.record.den)
    rw [FiniteProbRecord.eventMass_weightedCartesian_bind,
      FiniteProbRecord.eventMass_weightedCartesian_bind]
    simpa only [Nat.mul_assoc] using congrArg (fun n => n * ν.record.den) integral
  exact QProb.equiv_trans leftSwap
    (FiniteProbRecord.product_probVal_equiv_of_slices μ'.record ν.record ν'.record
      event event (fun x => right (fun y => event (x, y))))

def Distro.conditionOn (μ : Distro Ω) (evidence : Event Ω)
    (positive : μ.record.EventPositive evidence) : Distro Ω :=
  ⟨μ.record.conditionOn evidence positive⟩

theorem Distro.SameLaw.eventPositive {μ ν : Distro Ω} (h : μ.SameLaw ν)
    (event : Event Ω) : μ.record.EventPositive event ↔ ν.record.EventPositive event :=
  QProb.equiv_num_pos_iff (h event)

theorem Distro.SameLaw.conditionOn {μ ν : Distro Ω} (h : μ.SameLaw ν)
    (evidence : Event Ω) (hμ : μ.record.EventPositive evidence)
    (hν : ν.record.EventPositive evidence) :
    (μ.conditionOn evidence hμ).SameLaw (ν.conditionOn evidence hν) := by
  intro event
  exact QProb.equiv_trans (μ.record.conditionOn_probVal evidence event hμ)
    (QProb.equiv_trans
      (QProb.div_congr (h (fun x => evidence x && event x)) (h evidence) hμ hν)
      (QProb.equiv_symm (ν.record.conditionOn_probVal evidence event hν)))

theorem Distro.sameLaw_of_singletons [DecidableEq Ω] (μ ν : Distro Ω)
    (values : List Ω) (nodup : values.Nodup) (complete : ∀ value, value ∈ values)
    (singletons : ∀ value, QProb.Equiv (μ.pmf value) (ν.pmf value)) : μ.SameLaw ν :=
  FiniteProbRecord.probVal_extensional_of_singletons μ.record ν.record
    values nodup complete singletons

theorem Distro.sameLaw_iff_expectNat (μ ν : Distro Ω) :
    μ.SameLaw ν ↔ ∀ f : Ω → Nat, QProb.Equiv (μ.expectNat f) (ν.expectNat f) := by
  constructor
  · exact fun h f => h.expectNat f
  · intro h event
    simpa only [expectNat, natIntegral_indicator, FiniteProbRecord.probVal] using
      h (fun x => if event x then 1 else 0)

theorem Distro.sameLaw_iff_expectation (μ ν : Distro Ω) :
    μ.SameLaw ν ↔ ∀ f : Ω → QProb, QProb.Equiv (μ.expectation f) (ν.expectation f) := by
  constructor
  · exact fun h f => h.expectation f
  · intro h
    apply (sameLaw_iff_expectNat μ ν).mpr
    intro f
    exact QProb.equiv_trans (QProb.equiv_symm (μ.expectation_nat f))
      (QProb.equiv_trans (h (fun x => QProb.ofNat (f x))) (ν.expectation_nat f))

/-- Multiply all weights and the denominator by a positive common factor. -/
def Distro.rescaleWeights (μ : Distro Ω) (factor : Nat) (positive : 0 < factor) : Distro Ω where
  record := {
    atoms := μ.record.atoms.map (fun atom => (atom.1, factor * atom.2))
    den := factor * μ.record.den
    den_pos := Nat.mul_pos positive μ.record.den_pos
    total_mass := by
      have h := FiniteProbRecord.totalMass_map_weight μ.record.atoms id factor
      simpa only [id, μ.record.total_mass] using h
  }

theorem Distro.rescaleWeights_sameLaw (μ : Distro Ω) (factor : Nat) (positive : 0 < factor) :
    (μ.rescaleWeights factor positive).SameLaw μ := by
  intro event
  change FiniteProbRecord.eventMass
      (μ.record.atoms.map (fun atom => (atom.1, factor * atom.2))) event * μ.record.den =
    FiniteProbRecord.eventMass μ.record.atoms event * (factor * μ.record.den)
  rw [FiniteProbRecord.eventMass_scale]
  ac_rfl

/-- Equality of the numeric laws permits different source outcome types. -/
def NatDistro.SameLaw (μ : NatDistro Ω) (ν : NatDistro X) : Prop :=
  (μ.distro.map μ.embed).SameLaw (ν.distro.map ν.embed)

theorem NatDistro.SameLaw.refl (μ : NatDistro Ω) : μ.SameLaw μ := Distro.SameLaw.refl _

theorem NatDistro.SameLaw.symm {μ : NatDistro Ω} {ν : NatDistro X}
    (h : μ.SameLaw ν) : ν.SameLaw μ := Distro.SameLaw.symm h

theorem NatDistro.SameLaw.trans {μ : NatDistro Ω} {ν : NatDistro X} {ξ : NatDistro Y}
    (h : μ.SameLaw ν) (h' : ν.SameLaw ξ) : μ.SameLaw ξ := Distro.SameLaw.trans h h'

theorem NatDistro.sameLaw_of_distro {μ ν : Distro Ω} (h : μ.SameLaw ν) (f : Ω → Nat) :
    (⟨μ, f⟩ : NatDistro Ω).SameLaw ⟨ν, f⟩ := h.map f

theorem NatDistro.sameLaw_iff_events (μ : NatDistro Ω) (ν : NatDistro X) :
    μ.SameLaw ν ↔ ∀ event : Event Nat,
      QProb.Equiv (μ.distro.record.probVal (fun x => event (μ.embed x)))
        (ν.distro.record.probVal (fun x => event (ν.embed x))) := by
  constructor
  · intro h event
    exact QProb.equiv_trans (QProb.equiv_symm (μ.distro.map_probVal μ.embed event))
      (QProb.equiv_trans (h event) (ν.distro.map_probVal ν.embed event))
  · intro h event
    exact QProb.equiv_trans (μ.distro.map_probVal μ.embed event)
      (QProb.equiv_trans (h event) (QProb.equiv_symm (ν.distro.map_probVal ν.embed event)))

theorem NatDistro.SameLaw.rawMoment {μ : NatDistro Ω} {ν : NatDistro X}
    (h : μ.SameLaw ν) (power : Nat) : QProb.Equiv (rawMoment μ power) (rawMoment ν power) := by
  rw [rawMoment_expectNat, rawMoment_expectNat]
  simpa only [Distro.expectNat_map] using Distro.SameLaw.expectNat h (fun n => n ^ power)

theorem NatDistro.SameLaw.mean {μ : NatDistro Ω} {ν : NatDistro X}
    (h : μ.SameLaw ν) : QProb.Equiv (mean μ) (mean ν) := h.rawMoment 1

theorem NatDistro.SameLaw.secondMoment {μ : NatDistro Ω} {ν : NatDistro X}
    (h : μ.SameLaw ν) : QProb.Equiv (secondMoment μ) (secondMoment ν) := h.rawMoment 2

theorem NatDistro.SameLaw.variance {μ : NatDistro Ω} {ν : NatDistro X}
    (h : μ.SameLaw ν) : QProb.Equiv (variance μ) (variance ν) := by
  apply variance_eq_of_balance
  exact QProb.equiv_trans
    (QProb.add_congr (QProb.equiv_refl _) (QProb.mul_congr h.mean h.mean))
    (QProb.equiv_trans (variance_balance ν) (QProb.equiv_symm h.secondMoment))

theorem NatDistro.SameLaw.pgf {μ : NatDistro Ω} {ν : NatDistro X}
    (h : μ.SameLaw ν) (s : QProb) : QProb.Equiv (pgf μ s) (pgf ν s) := by
  rw [pgf_expectation, pgf_expectation]
  simpa only [Distro.expectation_map] using Distro.SameLaw.expectation h (fun n => qpow s n)

end Thesis.Probability.Distros
