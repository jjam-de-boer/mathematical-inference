import Thesis.Probability.FiniteCellProduct

namespace Thesis
namespace Probability

/-!
Finite urn probability and the qualitative urn-ratio reconstruction.

`UrnProb` is the direct counting presentation: a positive finite number of
equally weighted cells is mapped to outcome labels. Its probability of a
Boolean event is the event-cell count divided by the number of cells. The later
`UrnRatio` section records the rescaling assumptions used in the finite
Clayton--Waddington-style route described in the thesis.
-/

/-- A nonempty finite urn whose cells may share outcome labels. -/
structure UrnProb (X : Type u) where
  n : Nat
  pos : 0 < n
  draw : Fin n → X

namespace UrnProb

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

/-- The number of urn cells whose outcome satisfies the event. -/
def probNum (μ : UrnProb X) (E : Event X) : Nat :=
  count μ.support E

/-- The event-cell count as a finite rational probability. -/
def probVal (μ : UrnProb X) (E : Event X) : QProb where
  num := μ.probNum E
  den := μ.n
  den_pos := μ.pos

/-- Conditional probability, defined only with a positive conditioning count. -/
def condVal (μ : UrnProb X) (E F : Event X)
    (hF : 0 < μ.probNum F) : QProb where
  num := μ.probNum (inter E F)
  den := μ.probNum F
  den_pos := hF

theorem probNum_nonneg (μ : UrnProb X) (E : Event X) :
    0 ≤ μ.probNum E := by
  exact Nat.zero_le _

theorem probNum_le_den (μ : UrnProb X) (E : Event X) :
    μ.probNum E ≤ μ.n := by
  rw [← μ.support_length]
  exact count_le_length μ.support E

theorem probNum_top (μ : UrnProb X) :
    μ.probNum topEvent = μ.n := by
  rw [probNum, count_top, support_length]

theorem normalization (μ : UrnProb X) :
    QProb.Equiv (μ.probVal topEvent) QProb.one := by
  simp [QProb.Equiv, QProb.one, probVal, probNum_top]

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

/--
The Bayesian update probability of `F` given conditioning event `E`, computed
directly from the formula `p_E(ω) := 𝟙_E(ω)·p(ω) / P(E)` of the appendix
definition `def:bayesian-update`. In the urn presentation this is the count of
cells satisfying both `E` and `F`, divided by the count of cells satisfying `E`.
-/
def bayesianUpdateProb (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) : QProb where
  num := μ.probNum (inter E F)
  den := μ.probNum E
  den_pos := hE

/--
Consistency of Bayesian update with conditional probability: when the
conditioning event has positive count, the update value `P_E(F)` equals
`P(F | E)`. This is the lemma the main text uses implicitly when treating
`P_E` and `P(- | E)` as interchangeable.
-/
theorem bayesian_update_consistency (μ : UrnProb X) (E F : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv (μ.bayesianUpdateProb E F hE) (μ.condVal F E hE) := by
  have hcomm : μ.probNum (inter E F) = μ.probNum (inter F E) :=
    count_inter_comm μ.support E F
  simp [QProb.Equiv, bayesianUpdateProb, condVal, hcomm]

/--
The Bayesian update induced by a positive event is normalized: the updated
probability of the total event is one.
-/
theorem bayesian_update_normalization (μ : UrnProb X) (E : Event X)
    (hE : 0 < μ.probNum E) :
    QProb.Equiv (μ.bayesianUpdateProb E topEvent hE) QProb.one := by
  have htop : μ.probNum (inter E topEvent) = μ.probNum E := by
    unfold probNum
    apply count_congr
    intro x
    cases h : E x <;> simp [inter, topEvent, h]
  simp [QProb.Equiv, bayesianUpdateProb, QProb.one, htop]

end UrnProb
namespace ClaytonWaddington

/-!
Finite urn events as the Lean counterpart of the Clayton--Waddington-style
appendix argument.  An event in a symmetric urn is represented only by the
number of selected cells `k` in an urn of positive size `N`; relabelling
invariance is therefore built into the representation.
-/

structure UrnRatio where
  N : Nat
  k : Nat
  pos : 0 < N
  le : k ≤ N

namespace UrnRatio

def toQProb (u : UrnRatio) : QProb where
  num := u.k
  den := u.N
  den_pos := u.pos

def sameRatio (u v : UrnRatio) : Prop :=
  u.k * v.N = v.k * u.N

theorem sameRatio_toQProb {u v : UrnRatio}
    (h : sameRatio u v) :
    QProb.Equiv u.toQProb v.toQProb := by
  exact h

def refine (u : UrnRatio) (c : Nat) (hc : 0 < c) : UrnRatio where
  N := c * u.N
  k := c * u.k
  pos := Nat.mul_pos hc u.pos
  le := Nat.mul_le_mul_left c u.le

theorem refinement_preserves_ratio (u : UrnRatio)
    (c : Nat) (hc : 0 < c) :
    QProb.Equiv (u.refine c hc).toQProb u.toQProb := by
  simp [QProb.Equiv, toQProb, refine, Nat.mul_comm, Nat.mul_left_comm]

def complement (u : UrnRatio) : UrnRatio where
  N := u.N
  k := u.N - u.k
  pos := u.pos
  le := Nat.sub_le u.N u.k

theorem complement_rule (u : UrnRatio) :
    QProb.Equiv (QProb.add u.toQProb u.complement.toQProb) QProb.one := by
  have hsum : u.k + (u.N - u.k) = u.N := by
    rw [Nat.add_comm, Nat.sub_add_cancel u.le]
  simp [QProb.Equiv, QProb.add, QProb.one, toQProb, complement]
  rw [← Nat.add_mul, hsum]

def product (u v : UrnRatio) : UrnRatio where
  N := u.N * v.N
  k := u.k * v.k
  pos := Nat.mul_pos u.pos v.pos
  le := Nat.mul_le_mul u.le v.le

theorem product_rule (u v : UrnRatio) :
    QProb.Equiv (u.product v).toQProb
      (QProb.mul u.toQProb v.toQProb) := by
  simp [QProb.Equiv, QProb.mul, toQProb, product,
    Nat.mul_comm, Nat.mul_left_comm]

/-- The selected-cell field of the ratio product is realized by the encoded
rectangular event on the explicitly constructed product cell type. -/
theorem product_selectedCells (u v : UrnRatio)
    (E : Event (Fin u.N)) (F : Event (Fin v.N))
    (hE : count (FiniteCellProduct.cells u.N) E = u.k)
    (hF : count (FiniteCellProduct.cells v.N) F = v.k) :
    count (FiniteCellProduct.cells (u.N * v.N))
        (FiniteCellProduct.encodedRectangularEvent v.pos E F) =
      (u.product v).k := by
  simpa [product] using
    FiniteCellProduct.selectedCells_product v.pos E F hE hF

theorem rescaling_is_k_over_N (u : UrnRatio) :
    QProb.Equiv u.toQProb
      { num := u.k, den := u.N, den_pos := u.pos } := by
  rfl

/--
A primitive qualitative plausibility scale for finite symmetric urn events.

The scale does not start with numerical probabilities.  It starts with a type
of plausibility values, an equivalence relation on those values, and a strict
comparison.  The assumptions say that only the number of selected cells matters,
refining every cell into the same positive number of subcells preserves
plausibility, and larger selected subsets in a fixed urn are strictly more
plausible.
-/
structure QualitativeUrnScale where
  Plaus : Type u
  plaus : UrnRatio → Plaus
  eqv : Plaus → Plaus → Prop
  lt : Plaus → Plaus → Prop
  eqv_refl : ∀ a, eqv a a
  eqv_symm : ∀ {a b}, eqv a b → eqv b a
  eqv_trans : ∀ {a b c}, eqv a b → eqv b c → eqv a c
  lt_irrefl : ∀ a, lt a a → False
  lt_trans : ∀ {a b c}, lt a b → lt b c → lt a c
  same_counts_eqv :
    ∀ u v, u.N = v.N → u.k = v.k → eqv (plaus u) (plaus v)
  refinement_eqv :
    ∀ u (c : Nat) (hc : 0 < c),
      eqv (plaus (u.refine c hc)) (plaus u)
  strict_mono_same_urn :
    ∀ (N : Nat) (hN : 0 < N) {k l : Nat}
      (hk : k ≤ N) (hl : l ≤ N),
      k < l →
      lt
        (plaus { N := N, k := k, pos := hN, le := hk })
        (plaus { N := N, k := l, pos := hN, le := hl })
  lt_respects_eqv :
    ∀ {a b c d}, eqv a c → eqv b d → lt a b → lt c d

namespace QualitativeUrnScale

theorem lt_asymm (Q : QualitativeUrnScale)
    {a b : Q.Plaus} (hab : Q.lt a b) (hba : Q.lt b a) :
    False := by
  exact Q.lt_irrefl a (Q.lt_trans hab hba)

theorem eqv_lt_false (Q : QualitativeUrnScale)
    {a b : Q.Plaus} (hab : Q.eqv a b) (hlt : Q.lt a b) :
    False := by
  have haa : Q.lt a a :=
    Q.lt_respects_eqv (Q.eqv_refl a) (Q.eqv_symm hab) hlt
  exact Q.lt_irrefl a haa

def commonLeft (u v : UrnRatio) : UrnRatio where
  N := v.N * u.N
  k := v.N * u.k
  pos := Nat.mul_pos v.pos u.pos
  le := Nat.mul_le_mul_left v.N u.le

def commonRight (u v : UrnRatio) : UrnRatio where
  N := v.N * u.N
  k := v.k * u.N
  pos := Nat.mul_pos v.pos u.pos
  le := Nat.mul_le_mul_right u.N v.le

theorem commonLeft_eqv (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.plaus (commonLeft u v)) (Q.plaus u) := by
  let refined := u.refine v.N v.pos
  have hsame :
      Q.eqv (Q.plaus (commonLeft u v)) (Q.plaus refined) := by
    apply Q.same_counts_eqv
    · rfl
    · rfl
  exact Q.eqv_trans hsame (Q.refinement_eqv u v.N v.pos)

theorem commonRight_eqv (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.plaus (commonRight u v)) (Q.plaus v) := by
  let refined := v.refine u.N u.pos
  have hsame :
      Q.eqv (Q.plaus (commonRight u v)) (Q.plaus refined) := by
    apply Q.same_counts_eqv
    · simp [commonRight, refined, refine, Nat.mul_comm]
    · simp [commonRight, refined, refine, Nat.mul_comm]
  exact Q.eqv_trans hsame (Q.refinement_eqv v u.N u.pos)

theorem sameRatio_implies_eqv (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : sameRatio u v) :
    Q.eqv (Q.plaus u) (Q.plaus v) := by
  have hcommon :
      Q.eqv (Q.plaus (commonLeft u v)) (Q.plaus (commonRight u v)) := by
    apply Q.same_counts_eqv
    · rfl
    · simp [commonLeft, commonRight, sameRatio] at h ⊢
      calc
        v.N * u.k = u.k * v.N := by
          exact Nat.mul_comm v.N u.k
        _ = v.k * u.N := h
  exact Q.eqv_trans
    (Q.eqv_symm (Q.commonLeft_eqv u v))
    (Q.eqv_trans hcommon (Q.commonRight_eqv u v))

theorem ratio_lt_implies_lt (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : u.k * v.N < v.k * u.N) :
    Q.lt (Q.plaus u) (Q.plaus v) := by
  have hcommon :
      Q.lt (Q.plaus (commonLeft u v)) (Q.plaus (commonRight u v)) := by
    apply Q.strict_mono_same_urn (v.N * u.N)
      (Nat.mul_pos v.pos u.pos)
      (commonLeft u v).le
      (commonRight u v).le
    simpa [commonLeft, commonRight, Nat.mul_comm] using h
  exact Q.lt_respects_eqv
    (Q.commonLeft_eqv u v)
    (Q.commonRight_eqv u v)
    hcommon

theorem eqv_implies_sameRatio (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.eqv (Q.plaus u) (Q.plaus v)) :
    sameRatio u v := by
  by_cases heq : u.k * v.N = v.k * u.N
  · exact heq
  · by_cases hlt : u.k * v.N < v.k * u.N
    · exact False.elim (Q.eqv_lt_false h (Q.ratio_lt_implies_lt hlt))
    · have hgt : v.k * u.N < u.k * v.N := by
        omega
      have hvu : Q.lt (Q.plaus v) (Q.plaus u) :=
        Q.ratio_lt_implies_lt hgt
      exact False.elim (Q.eqv_lt_false (Q.eqv_symm h) hvu)

theorem eqv_iff_sameRatio (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.plaus u) (Q.plaus v) ↔ sameRatio u v :=
  ⟨Q.eqv_implies_sameRatio, Q.sameRatio_implies_eqv⟩

theorem lt_implies_ratio_lt (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.lt (Q.plaus u) (Q.plaus v)) :
    u.k * v.N < v.k * u.N := by
  rcases Nat.lt_trichotomy (u.k * v.N) (v.k * u.N) with hlt | heq | hgt
  · exact hlt
  · exact False.elim (Q.eqv_lt_false (Q.sameRatio_implies_eqv heq) h)
  · have hrev : Q.lt (Q.plaus v) (Q.plaus u) :=
      Q.ratio_lt_implies_lt hgt
    exact False.elim (Q.lt_asymm h hrev)

theorem lt_iff_ratio_lt (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.lt (Q.plaus u) (Q.plaus v) ↔
      u.k * v.N < v.k * u.N :=
  ⟨Q.lt_implies_ratio_lt, Q.ratio_lt_implies_lt⟩

/--
The qualitative representation theorem: the rational value `k/N` is a
well-defined rescaling of primitive qualitative plausibility classes.
-/
theorem rational_rescaling_well_defined (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.eqv (Q.plaus u) (Q.plaus v)) :
    QProb.Equiv u.toQProb v.toQProb := by
  exact sameRatio_toQProb (Q.eqv_implies_sameRatio h)

/--
The rational rescaling is order-preserving on represented qualitative values:
strict qualitative increase implies strict increase of the represented ratio.
-/
theorem rational_rescaling_order_preserving (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.lt (Q.plaus u) (Q.plaus v)) :
    u.k * v.N < v.k * u.N := by
  exact Q.lt_implies_ratio_lt h

/--
The rational rescaling also reflects strict order: strict increase of the
represented ratio implies strict qualitative increase.
-/
theorem rational_rescaling_order_reflecting (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : u.k * v.N < v.k * u.N) :
    Q.lt (Q.plaus u) (Q.plaus v) := by
  exact Q.ratio_lt_implies_lt h

theorem rational_rescaling_order_iff (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.lt (Q.plaus u) (Q.plaus v) ↔
      u.k * v.N < v.k * u.N :=
  Q.lt_iff_ratio_lt u v

end QualitativeUrnScale

/--
The primitive finite-urn representation step.

Read `cell` as the common value of one equipossible cell.  Finite additivity
says that an event with `k` such cells has value `scale k cell`, while
normalization says that all `N` cells together have value one.  Under those
assumptions, the value forced for the event is `k/N`.
-/
theorem equal_cells_force_ratio (u : UrnRatio) (cell : QProb)
    (hwhole : QProb.Equiv (QProb.scale u.N cell) QProb.one) :
    QProb.Equiv (QProb.scale u.k cell) u.toQProb := by
  exact QProb.scale_forced_ratio u.pos cell hwhole

/--
An explicit packaging of the primitive assumptions used by the finite
Clayton--Waddington urn argument.

`whole_is_all_cells` is normalization plus equipossibility of the `N` cells.
`event_is_selected_cells` is the finite-additivity consequence that the event
made of `k` selected cells has the sum of `k` equal cell-values.
-/
structure PrimitiveUrnAssignment (u : UrnRatio) where
  cell : QProb
  value : QProb
  whole_is_all_cells :
    QProb.Equiv (QProb.scale u.N cell) QProb.one
  event_is_selected_cells :
    QProb.Equiv value (QProb.scale u.k cell)

theorem PrimitiveUrnAssignment.forces_ratio
    {u : UrnRatio} (A : PrimitiveUrnAssignment u) :
    QProb.Equiv A.value u.toQProb := by
  exact QProb.equiv_trans A.event_is_selected_cells
    (equal_cells_force_ratio u A.cell A.whole_is_all_cells)

end UrnRatio

end ClaytonWaddington

end Probability
end Thesis
