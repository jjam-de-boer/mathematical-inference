import Thesis.Probability.FiniteCellProduct

namespace Thesis
namespace Probability

/-!
Finite urn probability by direct cell counting.

`UrnProb` maps a positive finite number of equally weighted cells to outcome
labels.  Its probability of a Boolean event is the event-cell count divided by
the number of cells.  The qualitative reconstruction from finite urn events is
developed separately in `QualitativeUrn.lean`.
-/

/-- A nonempty finite urn whose cells may share outcome labels. -/
structure UrnProb (X : Type u) where
  n : Nat
  pos : 0 < n
  draw : Fin n → X

namespace UrnProb

/--
The ordered list of urn-cell labels.  It has one entry per cell, so distinct
cells that carry the same label remain distinct entries; this is not a
deduplicated set-theoretic support.
-/
def support (μ : UrnProb X) : List X :=
  List.ofFn μ.draw

theorem support_length (μ : UrnProb X) :
    μ.support.length = μ.n := by
  simp [support]

def ofList (xs : List X) (h : 0 < xs.length) : UrnProb X where
  n := xs.length
  pos := h
  draw := fun i => xs.get i

theorem support_ofList (xs : List X) (h : 0 < xs.length) :
    (ofList xs h).support = xs := by
  simp [ofList, support]

/-- Push an urn assignment forward by relabelling each cell. -/
def map (μ : UrnProb X) (f : X → Y) : UrnProb Y where
  n := μ.n
  pos := μ.pos
  draw := fun i => f (μ.draw i)

theorem support_map (μ : UrnProb X) (f : X → Y) :
    (μ.map f).support = μ.support.map f := by
  simp [map, support, Function.comp_def]

/-- The number of urn cells whose outcome satisfies the event. -/
def probNum (μ : UrnProb X) (E : Event X) : Nat :=
  count μ.support E

/-- The event-cell count as a finite rational probability. -/
def probVal (μ : UrnProb X) (E : Event X) : QProb where
  num := μ.probNum E
  den := μ.n
  den_pos := μ.pos

theorem probNum_map (μ : UrnProb X) (f : X → Y) (E : Event Y) :
    (μ.map f).probNum E = μ.probNum (fun x => E (f x)) := by
  simp [probNum, support_map, count, Function.comp_def]

theorem probVal_map (μ : UrnProb X) (f : X → Y) (E : Event Y) :
    QProb.Equiv ((μ.map f).probVal E)
      (μ.probVal (fun x => E (f x))) := by
  unfold QProb.Equiv probVal
  rw [probNum_map]
  rfl

/-- The rectangular product of two events on outcome labels. -/
def productEvent (E : Event X) (F : Event Y) : Event (X × Y) :=
  fun pair => E pair.1 && F pair.2

/-- The independent product urn, enumerated in row-major cell order. -/
def product (μ : UrnProb X) (ν : UrnProb Y) : UrnProb (X × Y) where
  n := μ.n * ν.n
  pos := Nat.mul_pos μ.pos ν.pos
  draw := fun index =>
    let cell := FiniteCellProduct.decode ν.pos index
    (μ.draw cell.1, ν.draw cell.2)

theorem probNum_eq_cellCount (μ : UrnProb X) (E : Event X) :
    μ.probNum E =
      count (FiniteCellProduct.cells μ.n) (fun i => E (μ.draw i)) := by
  change List.countP E (List.ofFn μ.draw) =
    List.countP (E ∘ μ.draw) (List.ofFn id)
  rw [← List.countP_map]
  simp [Function.comp_def]

theorem product_probNum (μ : UrnProb X) (ν : UrnProb Y)
    (E : Event X) (F : Event Y) :
    (μ.product ν).probNum (productEvent E F) =
      μ.probNum E * ν.probNum F := by
  rw [probNum_eq_cellCount, μ.probNum_eq_cellCount, ν.probNum_eq_cellCount]
  simpa [product, productEvent, FiniteCellProduct.encodedRectangularEvent,
    FiniteCellProduct.rectangularEvent] using
    (FiniteCellProduct.count_canonicalRectangularEvent ν.pos
      (fun i => E (μ.draw i)) (fun j => F (ν.draw j)))

theorem product_probVal (μ : UrnProb X) (ν : UrnProb Y)
    (E : Event X) (F : Event Y) :
    QProb.Equiv ((μ.product ν).probVal (productEvent E F))
      (QProb.mul (μ.probVal E) (ν.probVal F)) := by
  unfold QProb.Equiv probVal QProb.mul
  rw [product_probNum]
  rfl

/-- Conditional probability, defined only with a positive conditioning count. -/
def condVal (μ : UrnProb X) (E F : Event X)
    (hF : 0 < μ.probNum F) : QProb where
  num := μ.probNum (inter E F)
  den := μ.probNum F
  den_pos := hF

/--
Condition an urn on a positive Boolean event by retaining exactly the selected
cells. Repeated outcome labels remain repeated cells in the posterior urn.
-/
def conditionOn (μ : UrnProb X) (E : Event X)
    (hE : 0 < μ.probNum E) : UrnProb X :=
  ofList (μ.support.filter E) (by
    rw [← List.countP_eq_length_filter]
    simpa [probNum, count] using hE)

theorem conditionOn_support (μ : UrnProb X) (E : Event X)
    (hE : 0 < μ.probNum E) :
    (μ.conditionOn E hE).support = μ.support.filter E := by
  simp [conditionOn, support_ofList]

theorem conditionOn_probNum (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) :
    (μ.conditionOn E hE).probNum F = μ.probNum (inter E F) := by
  rw [probNum, conditionOn_support, probNum]
  unfold count
  rw [List.countP_filter]
  exact count_congr (fun x => Bool.and_comm (F x) (E x))

/-- The filtered posterior urn computes the corresponding conditional value. -/
theorem conditionOn_probVal (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv ((μ.conditionOn E hE).probVal F) (μ.condVal F E hE) := by
  have hn : (μ.conditionOn E hE).n = μ.probNum E := by
    change (μ.support.filter E).length = μ.probNum E
    rw [← List.countP_eq_length_filter]
    rfl
  have hcomm : μ.probNum (inter E F) = μ.probNum (inter F E) :=
    count_inter_comm μ.support E F
  simp [QProb.Equiv, probVal, condVal, conditionOn_probNum, hn, hcomm]

theorem probNum_nonneg (μ : UrnProb X) (E : Event X) :
    0 ≤ μ.probNum E := by
  exact Nat.zero_le _

theorem probNum_le_den (μ : UrnProb X) (E : Event X) :
    μ.probNum E ≤ μ.n := by
  rw [← μ.support_length]
  exact count_le_length μ.support E

/-- Every urn event has a nonnegative rational probability. -/
theorem probVal_nonneg (μ : UrnProb X) (E : Event X) :
    QProb.LE QProb.zero (μ.probVal E) :=
  QProb.zero_le _

/-- Every urn event has rational probability at most one. -/
theorem probVal_le_one (μ : UrnProb X) (E : Event X) :
    QProb.LE (μ.probVal E) QProb.one := by
  simp only [QProb.LE, probVal, QProb.one, Nat.mul_one, Nat.one_mul]
  exact μ.probNum_le_den E

/-- The usual closed-unit-interval bounds for an urn event probability. -/
theorem probVal_bounds (μ : UrnProb X) (E : Event X) :
    QProb.LE QProb.zero (μ.probVal E) ∧
      QProb.LE (μ.probVal E) QProb.one :=
  ⟨μ.probVal_nonneg E, μ.probVal_le_one E⟩

theorem probNum_top (μ : UrnProb X) :
    μ.probNum topEvent = μ.n := by
  rw [probNum, count_top, support_length]

theorem normalization (μ : UrnProb X) :
    QProb.Equiv (μ.probVal topEvent) QProb.one := by
  simp [QProb.Equiv, QProb.one, probVal, probNum_top]

/-- The empty event has probability zero. -/
theorem probVal_bottom (μ : UrnProb X) :
    QProb.Equiv (μ.probVal bottomEvent) QProb.zero := by
  simp [QProb.Equiv, probVal, probNum, count_bottom, QProb.zero]

/-- An event and its Boolean complement have probabilities summing to one. -/
theorem complement_rule (μ : UrnProb X) (E : Event X) :
    QProb.Equiv
      (QProb.add (μ.probVal E) (μ.probVal (complement E)))
      QProb.one := by
  have hcount := count_add_count_complement μ.support E
  rw [μ.support_length] at hcount
  change μ.probNum E + μ.probNum (complement E) = μ.n at hcount
  simp only [QProb.Equiv, QProb.add, probVal, QProb.one,
    Nat.mul_one, Nat.one_mul]
  rw [← Nat.add_mul, hcount]

theorem conditionOn_normalization (μ : UrnProb X) (E : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv ((μ.conditionOn E hE).probVal topEvent) QProb.one :=
  (μ.conditionOn E hE).normalization

theorem finite_additivity_num (μ : UrnProb X) (E F : Event X)
    (h : disjoint E F) :
    μ.probNum (union E F) = μ.probNum E + μ.probNum F := by
  exact count_union_disjoint μ.support E F h

theorem finite_additivity (μ : UrnProb X) (E F : Event X)
    (h : disjoint E F) :
    QProb.Equiv (μ.probVal (union E F))
      (QProb.add (μ.probVal E) (μ.probVal F)) := by
  have hcount := μ.finite_additivity_num E F h
  simp [QProb.Equiv, QProb.add, probVal, hcount,
    Nat.left_distrib, Nat.mul_assoc, Nat.mul_comm]

/-- Pairwise-disjoint finite families have additive selected-cell counts. -/
theorem finite_additivity_num_family (μ : UrnProb X)
    (events : List (Event X)) (pairwise : events.Pairwise disjoint) :
    μ.probNum (unionList events) =
      (events.map μ.probNum).sum := by
  exact count_unionList_pairwise μ.support pairwise

/--
Finite additivity for an arbitrary finite pairwise-disjoint family of Boolean
events.  The right side is the finite rational sum in list order.
-/
theorem finite_additivity_family (μ : UrnProb X) :
    ∀ (events : List (Event X)), events.Pairwise disjoint →
      QProb.Equiv (μ.probVal (unionList events))
        (QProb.listSum (events.map μ.probVal))
  | [], _ => μ.probVal_bottom
  | E :: events, pairwise => by
      have headDisjoint : disjoint E (unionList events) :=
        disjoint_unionList (List.pairwise_cons.mp pairwise).1
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      exact QProb.equiv_trans
        (μ.finite_additivity E (unionList events) headDisjoint)
        (QProb.add_congr (QProb.equiv_refl _)
          (μ.finite_additivity_family events tailPairwise))

theorem status_partition_num (μ : UrnProb S) (I : Inspection S A) :
    μ.probNum I.provedEvent +
      μ.probNum I.refutedEvent +
      μ.probNum I.unresolvedEvent =
      μ.n := by
  have h :=
    Inspection.status_count_partition μ.support I.status
  simpa [probNum, Inspection.provedEvent, Inspection.refutedEvent,
    Inspection.unresolvedEvent, support_length] using h

theorem status_partition (μ : UrnProb S) (I : Inspection S A) :
    QProb.Equiv
      (QProb.add
        (QProb.add (μ.probVal I.provedEvent) (μ.probVal I.refutedEvent))
        (μ.probVal I.unresolvedEvent))
      QProb.one := by
  have hsum := μ.status_partition_num I
  simp [QProb.Equiv, QProb.add, QProb.one, probVal]
  rw [← Nat.add_mul]
  calc
    (μ.probNum I.provedEvent + μ.probNum I.refutedEvent) * μ.n * μ.n +
        μ.probNum I.unresolvedEvent * (μ.n * μ.n)
        =
        (μ.probNum I.provedEvent + μ.probNum I.refutedEvent) *
            (μ.n * μ.n) +
          μ.probNum I.unresolvedEvent * (μ.n * μ.n) := by
          rw [Nat.mul_assoc]
    _ =
        (μ.probNum I.provedEvent + μ.probNum I.refutedEvent +
            μ.probNum I.unresolvedEvent) *
          (μ.n * μ.n) := by
          rw [← Nat.add_mul]
    _ = μ.n * (μ.n * μ.n) := by
          rw [hsum]
    _ = μ.n * μ.n * μ.n := by
          rw [← Nat.mul_assoc]

theorem product_rule_for_conditioning (μ : UrnProb X) (E F : Event X)
    (hF : 0 < μ.probNum F) :
    QProb.Equiv
      (QProb.mul (μ.condVal E F hF) (μ.probVal F))
      (μ.probVal (inter E F)) := by
  simp [QProb.Equiv, QProb.mul, condVal, probVal,
    Nat.mul_assoc, Nat.mul_comm]

/-- Under positive conditioning, the product and left-conditional forms of
unconditional independence are equivalent. -/
theorem independent_iff_condVal_left (μ : UrnProb X) (A B : Event X)
    (hB : 0 < μ.probNum B) :
    QProb.Equiv
        (μ.probVal (inter A B))
        (QProb.mul (μ.probVal A) (μ.probVal B)) ↔
      QProb.Equiv (μ.condVal A B hB) (μ.probVal A) := by
  simp only [QProb.Equiv, probVal, QProb.mul, condVal]
  constructor
  · intro h
    apply Nat.eq_of_mul_eq_mul_right μ.pos
    simpa [Nat.mul_assoc] using h
  · intro h
    simpa [Nat.mul_assoc] using congrArg (fun value => value * μ.n) h

/-- Under positive conditioning, the product and right-conditional forms of
unconditional independence are equivalent. -/
theorem independent_iff_condVal_right (μ : UrnProb X) (A B : Event X)
    (hA : 0 < μ.probNum A) :
    QProb.Equiv
        (μ.probVal (inter A B))
        (QProb.mul (μ.probVal A) (μ.probVal B)) ↔
      QProb.Equiv (μ.condVal B A hA) (μ.probVal B) := by
  have hInter : μ.probNum (inter B A) = μ.probNum (inter A B) :=
    (count_inter_comm μ.support A B).symm
  simp only [QProb.Equiv, probVal, QProb.mul, condVal]
  rw [hInter]
  constructor
  · intro h
    apply Nat.eq_of_mul_eq_mul_right μ.pos
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  · intro h
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      congrArg (fun value => value * μ.n) h

/-- Under positive conditioning, the denominator-free product equation for
conditional independence is equivalent to the product of conditional values. -/
theorem conditionalIndependent_iff_condProduct
    (μ : UrnProb X) (A B C : Event X)
    (hC : 0 < μ.probNum C) :
    QProb.Equiv
        (QProb.mul (μ.probVal (inter (inter A B) C)) (μ.probVal C))
        (QProb.mul (μ.probVal (inter A C)) (μ.probVal (inter B C))) ↔
      QProb.Equiv
        (μ.condVal (inter A B) C hC)
        (QProb.mul (μ.condVal A C hC) (μ.condVal B C hC)) := by
  simp only [QProb.Equiv, probVal, QProb.mul, condVal]
  constructor
  · intro h
    have hCore :
        μ.probNum (inter (inter A B) C) * μ.probNum C =
          μ.probNum (inter A C) * μ.probNum (inter B C) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos μ.pos μ.pos)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      congrArg (fun value => value * μ.probNum C) hCore
  · intro h
    have hCore :
        μ.probNum (inter (inter A B) C) * μ.probNum C =
          μ.probNum (inter A C) * μ.probNum (inter B C) := by
      apply Nat.eq_of_mul_eq_mul_right hC
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      congrArg (fun value => value * (μ.n * μ.n)) hCore

/-- Under positive conditioning, the denominator-free product equation for
conditional independence is equivalent to invariance after additionally
conditioning on `B`. -/
theorem conditionalIndependent_iff_condVal
    (μ : UrnProb X) (A B C : Event X)
    (hC : 0 < μ.probNum C) (hBC : 0 < μ.probNum (inter B C)) :
    QProb.Equiv
        (QProb.mul (μ.probVal (inter (inter A B) C)) (μ.probVal C))
        (QProb.mul (μ.probVal (inter A C)) (μ.probVal (inter B C))) ↔
      QProb.Equiv
        (μ.condVal A (inter B C) hBC)
        (μ.condVal A C hC) := by
  have hAssoc :
      μ.probNum (inter A (inter B C)) =
        μ.probNum (inter (inter A B) C) := by
    unfold probNum
    exact count_congr (fun x => (Bool.and_assoc (A x) (B x) (C x)).symm)
  simp only [QProb.Equiv, probVal, QProb.mul, condVal]
  rw [hAssoc]
  constructor
  · intro h
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos μ.pos μ.pos)
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  · intro h
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      congrArg (fun value => value * (μ.n * μ.n)) h

theorem bayes_product_rule (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) (hF : 0 < μ.probNum F) :
    QProb.Equiv
      (QProb.mul (μ.condVal E F hF) (μ.probVal F))
      (QProb.mul (μ.condVal F E hE) (μ.probVal E)) := by
  have hInter :
      μ.probNum (inter F E) = μ.probNum (inter E F) := by
    exact (count_inter_comm μ.support E F).symm
  simp [QProb.Equiv, QProb.mul, condVal, probVal, hInter,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem bayes_formula (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) (hF : 0 < μ.probNum F) :
    QProb.Equiv
      (μ.condVal E F hF)
      (QProb.div
        (QProb.mul (μ.condVal F E hE) (μ.probVal E))
        (μ.probVal F)
        hF) := by
  have hInter :
      μ.probNum (inter F E) = μ.probNum (inter E F) := by
    exact (count_inter_comm μ.support E F).symm
  simp [QProb.Equiv, QProb.div, QProb.mul, condVal, probVal, hInter,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/--
Monotonicity of finite urn probability: a sub-event has at most the same urn
count as the larger event. This is the integer counterpart of the standard
`E ⊆ F ⇒ P(E) ≤ P(F)` rule, used implicitly by inclusion–exclusion arguments.
-/
theorem monotonicity (μ : UrnProb X) {E F : Event X}
    (h : ∀ x, E x = true → F x = true) :
    μ.probNum E ≤ μ.probNum F :=
  count_mono h

/--
Rational monotonicity: a sub-event has rational probability at most that of
the larger event.  Both presentations use the same positive urn size as
denominator, so the selected-cell inequality of `monotonicity` is exactly
`QProb.le_of_same_den`.
-/
theorem monotonicity_probVal (μ : UrnProb X) {E F : Event X}
    (h : ∀ x, E x = true → F x = true) :
    QProb.LE (μ.probVal E) (μ.probVal F) := by
  have hnum := μ.monotonicity h
  have hden : (μ.probVal E).den = (μ.probVal F).den := rfl
  exact QProb.le_of_same_den hden hnum

/--
Two-event count form of inclusion–exclusion: the sum of cells in `E ∪ F` and in
`E ∩ F` equals the sum of cells in `E` and in `F`. This generalises
`finite_additivity_num` to events that need not be disjoint.
-/
theorem probNum_union_inter (μ : UrnProb X) (E F : Event X) :
    μ.probNum (union E F) + μ.probNum (inter E F) =
      μ.probNum E + μ.probNum F :=
  count_union_inter μ.support E F

/--
Two-event inclusion–exclusion as an equivalence of `QProb` values. The sum of
the `E ∪ F` and `E ∩ F` probabilities equals the sum of the `E` and `F`
probabilities. This is the form used implicitly by the tenure-track example
calculation in the main text.
-/
theorem inclusion_exclusion (μ : UrnProb X) (E F : Event X) :
    QProb.Equiv
      (QProb.add (μ.probVal (union E F)) (μ.probVal (inter E F)))
      (QProb.add (μ.probVal E) (μ.probVal F)) := by
  have hcount := μ.probNum_union_inter E F
  unfold QProb.Equiv QProb.add probVal
  simp only [← Nat.add_mul]
  rw [hcount]

/-- Evaluate an event in the posterior urn obtained by positive conditioning. -/
def bayesianUpdateProb (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) : QProb :=
  (μ.conditionOn E hE).probVal F

/--
Consistency of Bayesian update with conditional probability: when the
conditioning event has positive count, the update value `P_E(F)` equals
`P(F | E)`. This is the lemma the main text uses implicitly when treating
`P_E` and `P(- | E)` as interchangeable.
-/
theorem bayesian_update_consistency (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv (μ.bayesianUpdateProb E F hE) (μ.condVal F E hE) :=
  μ.conditionOn_probVal E F hE

/--
The Bayesian update induced by a positive event is normalized: the updated
probability of the total event is one.
-/
theorem bayesian_update_normalization (μ : UrnProb X) (E : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv (μ.bayesianUpdateProb E topEvent hE) QProb.one :=
  μ.conditionOn_normalization E hE

end UrnProb

end Probability
end Thesis
