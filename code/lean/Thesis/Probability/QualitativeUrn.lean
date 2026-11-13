import Thesis.Probability.Urn
import Thesis.Probability.Reindexing

namespace Thesis
namespace Probability

namespace ClaytonWaddington

/-!
Finite urn events as the Lean counterpart of the Clayton--Waddington-style
appendix argument.  The primitive qualitative scale evaluates Boolean events
on finite cell types.  Canonical events with `k` selected cells then connect
that event-level interface to the ratio presentation `k/N` used by the
representation theorem.
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

/-- The canonical `k`-cell event in an `N`-cell urn. -/
def canonicalEvent (u : UrnRatio) : Event (Fin u.N) :=
  fun index => decide (index.val < u.k)

private theorem count_initialSegment : ∀ (N k : Nat), k ≤ N →
    count (List.finRange N) (fun index => decide (index.val < k)) = k := by
  intro N
  induction N with
  | zero =>
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      rfl
  | succ N ih =>
      intro k hk
      cases k with
      | zero =>
          calc
            count (List.finRange (N + 1))
                (fun index => decide (index.val < 0)) =
                count (List.finRange (N + 1)) bottomEvent := by
              apply count_congr
              intro index
              simp [bottomEvent]
            _ = 0 := count_bottom _
      | succ k =>
          rw [List.finRange_succ]
          unfold count
          rw [List.countP_cons, List.countP_map]
          simp only [Fin.val_zero, Nat.zero_lt_succ, decide_true, if_true]
          have hkN : k ≤ N := Nat.succ_le_succ_iff.mp hk
          have htail :
              (List.finRange N).countP
                  ((fun index : Fin (N + 1) =>
                    decide (index.val < k + 1)) ∘ Fin.succ) = k := by
            calc
              count (List.finRange N)
                    ((fun index : Fin (N + 1) =>
                      decide (index.val < k + 1)) ∘ Fin.succ) =
                  count (List.finRange N)
                    (fun index : Fin N => decide (index.val < k)) := by
                apply count_congr
                intro index
                simp
              _ = k := ih k hkN
          rw [htail]

/-- The canonical event selects exactly the numerator's number of cells. -/
theorem canonicalEvent_count (u : UrnRatio) :
    count (FiniteCellProduct.cells u.N) u.canonicalEvent = u.k := by
  change count (List.finRange u.N)
    (fun index => decide (index.val < u.k)) = u.k
  exact count_initialSegment u.N u.k u.le

/-- The ratio presentation obtained by counting an event on a positive cell type. -/
def ofCellEvent (N : Nat) (hN : 0 < N) (E : Event (Fin N)) : UrnRatio where
  N := N
  k := count (FiniteCellProduct.cells N) E
  pos := hN
  le := by
    simpa [FiniteCellProduct.cells] using
      count_le_length (FiniteCellProduct.cells N) E

/-- Pull a labelled urn event back to the urn's finite cell type. -/
def inducedCellEvent (μ : UrnProb X) (E : Event X) : Event (Fin μ.n) :=
  fun cell => E (μ.draw cell)

/-- The ratio presentation determined by an arbitrary labelled urn event. -/
def ofUrnEvent (μ : UrnProb X) (E : Event X) : UrnRatio where
  N := μ.n
  k := μ.probNum E
  pos := μ.pos
  le := μ.probNum_le_den E

/-- The induced cell event selects the numerator of its associated ratio. -/
theorem inducedCellEvent_count (μ : UrnProb X) (E : Event X) :
    count (FiniteCellProduct.cells μ.n) (inducedCellEvent μ E) =
      (ofUrnEvent μ E).k := by
  exact (μ.probNum_eq_cellCount E).symm

/-- The labelled-event probability is the rational value of its cell ratio. -/
theorem urnEvent_toQProb (μ : UrnProb X) (E : Event X) :
    QProb.Equiv (μ.probVal E) (ofUrnEvent μ E).toQProb := by
  rfl

/-- Evaluate the canonical event associated with a ratio presentation. -/
def canonicalPlaus {Plaus : Type u}
    (plaus : (N : Nat) → Event (Fin N) → Plaus)
    (ratio : UrnRatio) : Plaus :=
  plaus ratio.N ratio.canonicalEvent

end UrnRatio

open UrnRatio

/--
A primitive qualitative plausibility scale for finite symmetric urn events.

The scale does not start with numerical probabilities.  It assigns
plausibility values to arbitrary Boolean events on each finite cell type.  Its
count-invariance field makes cell relabelling explicit at event level.  The
remaining assumptions say that uniform positive refinement preserves the
canonical event's plausibility and that larger canonical subsets of a fixed
urn are strictly more plausible.
-/
structure QualitativeUrnScale where
  Plaus : Type u
  plaus : (N : Nat) → Event (Fin N) → Plaus
  eqv : Plaus → Plaus → Prop
  lt : Plaus → Plaus → Prop
  eqv_refl : ∀ a, eqv a a
  eqv_symm : ∀ {a b}, eqv a b → eqv b a
  eqv_trans : ∀ {a b c}, eqv a b → eqv b c → eqv a c
  lt_irrefl : ∀ a, lt a a → False
  lt_trans : ∀ {a b c}, lt a b → lt b c → lt a c
  count_invariant :
    ∀ (N : Nat) (E F : Event (Fin N)),
      count (FiniteCellProduct.cells N) E =
          count (FiniteCellProduct.cells N) F →
        eqv (plaus N E) (plaus N F)
  refinement_eqv :
    ∀ u (c : Nat) (hc : 0 < c),
      eqv (canonicalPlaus plaus (u.refine c hc)) (canonicalPlaus plaus u)
  strict_mono_same_urn :
    ∀ (N : Nat) (hN : 0 < N) {k l : Nat}
      (hk : k ≤ N) (hl : l ≤ N),
      k < l →
      lt
        (canonicalPlaus plaus { N := N, k := k, pos := hN, le := hk })
        (canonicalPlaus plaus { N := N, k := l, pos := hN, le := hl })
  lt_respects_eqv :
    ∀ {a b c d}, eqv a c → eqv b d → lt a b → lt c d

/-! ## A canonical jointly satisfying scale -/

/--
The rational plausibility assigned to an event by counting selected cells.
The empty cell type is assigned zero because `QProb` presentations require a
positive denominator; every qualitative urn axiom involving a ratio already
carries a positive-size witness.
-/
def rationalEventPlaus (N : Nat) (event : Event (Fin N)) : QProb :=
  if hN : 0 < N then
    { num := count (FiniteCellProduct.cells N) event
      den := N
      den_pos := hN }
  else
    QProb.zero

/-- On a positive cell type, the rational event assignment is its count ratio. -/
theorem rationalEventPlaus_of_pos (N : Nat) (hN : 0 < N)
    (event : Event (Fin N)) :
    rationalEventPlaus N event =
      { num := count (FiniteCellProduct.cells N) event
        den := N
        den_pos := hN } := by
  simp [rationalEventPlaus, hN]

/--
The cell-count rational scale is an explicit model of all qualitative urn
assumptions.  It supplies a non-vacuity witness for the assumptions of the
representation theorem: equivalence and strict comparison are ordinary cross
multiplication.
-/
def rationalScale : QualitativeUrnScale where
  Plaus := QProb
  plaus := rationalEventPlaus
  eqv := QProb.Equiv
  lt := QProb.LT
  eqv_refl := QProb.equiv_refl
  eqv_symm := QProb.equiv_symm
  eqv_trans := QProb.equiv_trans
  lt_irrefl := QProb.lt_irrefl
  lt_trans := QProb.lt_trans
  count_invariant := by
    intro N E F sameCount
    by_cases hN : 0 < N
    · simp only [rationalEventPlaus, hN, dif_pos, QProb.Equiv]
      rw [sameCount]
    · simp [rationalEventPlaus, hN, QProb.equiv_refl]
  refinement_eqv := by
    intro ratio c hc
    have hrefined : 0 < (ratio.refine c hc).N :=
      (ratio.refine c hc).pos
    change QProb.Equiv
      (rationalEventPlaus (ratio.refine c hc).N
        (ratio.refine c hc).canonicalEvent)
      (rationalEventPlaus ratio.N ratio.canonicalEvent)
    rw [rationalEventPlaus_of_pos _ hrefined,
      rationalEventPlaus_of_pos _ ratio.pos]
    have refinedCount := canonicalEvent_count (ratio.refine c hc)
    have originalCount := canonicalEvent_count ratio
    simp only [QProb.Equiv]
    rw [refinedCount, originalCount]
    simp only [refine]
    ac_rfl
  strict_mono_same_urn := by
    intro N hN k l hk hl hkl
    let lower : UrnRatio := { N := N, k := k, pos := hN, le := hk }
    let upper : UrnRatio := { N := N, k := l, pos := hN, le := hl }
    change QProb.LT
      (rationalEventPlaus N lower.canonicalEvent)
      (rationalEventPlaus N upper.canonicalEvent)
    rw [rationalEventPlaus_of_pos _ hN,
      rationalEventPlaus_of_pos _ hN]
    unfold QProb.LT
    rw [canonicalEvent_count lower, canonicalEvent_count upper]
    exact Nat.mul_lt_mul_of_pos_right hkl hN
  lt_respects_eqv := by
    intro a b c d hac hbd hab
    exact QProb.lt_congr hac hbd hab

/-- The four qualitative urn assumptions are jointly satisfiable. -/
theorem qualitativeUrnScale_nonempty :
    Nonempty (QualitativeUrnScale.{0}) :=
  ⟨rationalScale⟩

namespace QualitativeUrnScale

/-- The plausibility of the canonical event represented by `k/N`. -/
def ratioPlaus (Q : QualitativeUrnScale) (ratio : UrnRatio) : Q.Plaus :=
  canonicalPlaus Q.plaus ratio

/-- Pointwise-equal events have equivalent qualitative plausibility. -/
theorem plaus_eqv_of_pointwise (Q : QualitativeUrnScale) (N : Nat)
    (E F : Event (Fin N)) (pointwise : ∀ index, E index = F index) :
    Q.eqv (Q.plaus N E) (Q.plaus N F) :=
  Q.count_invariant N E F (count_congr pointwise)

/--
An explicitly inverted permutation of the cells preserves qualitative
plausibility.  This is derived from event-count invariance rather than assumed
as a separate numerical principle.
-/
theorem plaus_reindex_eqv (Q : QualitativeUrnScale) (N : Nat)
    (E : Event (Fin N)) (σ τ : Fin N → Fin N)
    (left_inv : ∀ index, τ (σ index) = index)
    (right_inv : ∀ index, σ (τ index) = index) :
    Q.eqv (Q.plaus N (E ∘ σ)) (Q.plaus N E) := by
  apply Q.count_invariant
  change count (List.finRange N) (E ∘ σ) =
    count (List.finRange N) E
  calc
    count (List.finRange N) (E ∘ σ) =
        count ((List.finRange N).map σ) E := by
      unfold count
      rw [List.countP_map]
    _ = count (List.finRange N) E :=
      count_reindex
        (AdditiveCarrier.finRange_map_bijective_perm σ τ
          left_inv right_inv) E

/-- Any event with the represented count is equivalent to its canonical event. -/
theorem event_eqv_ratio (Q : QualitativeUrnScale) (ratio : UrnRatio)
    (E : Event (Fin ratio.N))
    (selected : count (FiniteCellProduct.cells ratio.N) E = ratio.k) :
    Q.eqv (Q.plaus ratio.N E) (Q.ratioPlaus ratio) := by
  apply Q.count_invariant
  exact selected.trans ratio.canonicalEvent_count.symm

/--
Every labelled urn event is qualitatively equivalent, at cell level, to the
canonical event for the ratio computed by its ordinary urn probability.
-/
theorem urnEvent_eqv_ratio (Q : QualitativeUrnScale)
    (μ : UrnProb X) (E : Event X) :
    Q.eqv (Q.plaus μ.n (inducedCellEvent μ E))
      (Q.ratioPlaus (ofUrnEvent μ E)) :=
  Q.event_eqv_ratio (ofUrnEvent μ E) (inducedCellEvent μ E)
    (inducedCellEvent_count μ E)

/-- Equal total and selected-cell counts give equal canonical plausibility. -/
theorem same_counts_eqv (Q : QualitativeUrnScale)
    (u v : UrnRatio) (sameTotal : u.N = v.N)
    (sameSelected : u.k = v.k) :
    Q.eqv (Q.ratioPlaus u) (Q.ratioPlaus v) := by
  cases u with
  | mk N k pos le =>
      cases v with
      | mk N' k' pos' le' =>
          simp only at sameTotal sameSelected
          subst N'
          subst k'
          apply Q.count_invariant
          rfl

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
    Q.eqv (Q.ratioPlaus (commonLeft u v)) (Q.ratioPlaus u) := by
  let refined := u.refine v.N v.pos
  have hsame :
      Q.eqv (Q.ratioPlaus (commonLeft u v)) (Q.ratioPlaus refined) := by
    apply Q.same_counts_eqv
    · rfl
    · rfl
  exact Q.eqv_trans hsame (Q.refinement_eqv u v.N v.pos)

theorem commonRight_eqv (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.ratioPlaus (commonRight u v)) (Q.ratioPlaus v) := by
  let refined := v.refine u.N u.pos
  have hsame :
      Q.eqv (Q.ratioPlaus (commonRight u v)) (Q.ratioPlaus refined) := by
    apply Q.same_counts_eqv
    · simp [commonRight, refined, refine, Nat.mul_comm]
    · simp [commonRight, refined, refine, Nat.mul_comm]
  exact Q.eqv_trans hsame (Q.refinement_eqv v u.N u.pos)

theorem sameRatio_implies_eqv (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : sameRatio u v) :
    Q.eqv (Q.ratioPlaus u) (Q.ratioPlaus v) := by
  have hcommon :
      Q.eqv (Q.ratioPlaus (commonLeft u v)) (Q.ratioPlaus (commonRight u v)) := by
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
    Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v) := by
  have hcommon :
      Q.lt (Q.ratioPlaus (commonLeft u v)) (Q.ratioPlaus (commonRight u v)) := by
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
    {u v : UrnRatio} (h : Q.eqv (Q.ratioPlaus u) (Q.ratioPlaus v)) :
    sameRatio u v := by
  by_cases heq : u.k * v.N = v.k * u.N
  · exact heq
  · by_cases hlt : u.k * v.N < v.k * u.N
    · exact False.elim (Q.eqv_lt_false h (Q.ratio_lt_implies_lt hlt))
    · have hgt : v.k * u.N < u.k * v.N := by
        omega
      have hvu : Q.lt (Q.ratioPlaus v) (Q.ratioPlaus u) :=
        Q.ratio_lt_implies_lt hgt
      exact False.elim (Q.eqv_lt_false (Q.eqv_symm h) hvu)

theorem eqv_iff_sameRatio (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.eqv (Q.ratioPlaus u) (Q.ratioPlaus v) ↔ sameRatio u v :=
  ⟨Q.eqv_implies_sameRatio, Q.sameRatio_implies_eqv⟩

theorem lt_implies_ratio_lt (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v)) :
    u.k * v.N < v.k * u.N := by
  rcases Nat.lt_trichotomy (u.k * v.N) (v.k * u.N) with hlt | heq | hgt
  · exact hlt
  · exact False.elim (Q.eqv_lt_false (Q.sameRatio_implies_eqv heq) h)
  · have hrev : Q.lt (Q.ratioPlaus v) (Q.ratioPlaus u) :=
      Q.ratio_lt_implies_lt hgt
    exact False.elim (Q.lt_asymm h hrev)

theorem lt_iff_ratio_lt (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v) ↔
      u.k * v.N < v.k * u.N :=
  ⟨Q.lt_implies_ratio_lt, Q.ratio_lt_implies_lt⟩

/--
On a positive fixed urn, qualitative equivalence of arbitrary events is
exactly equality of their selected-cell counts.
-/
theorem event_eqv_iff_count_eq (Q : QualitativeUrnScale)
    (N : Nat) (hN : 0 < N) (E F : Event (Fin N)) :
    Q.eqv (Q.plaus N E) (Q.plaus N F) ↔
      count (FiniteCellProduct.cells N) E =
        count (FiniteCellProduct.cells N) F := by
  let u := ofCellEvent N hN E
  let v := ofCellEvent N hN F
  have hE : Q.eqv (Q.plaus N E) (Q.ratioPlaus u) := by
    exact Q.event_eqv_ratio (ofCellEvent N hN E) E rfl
  have hF : Q.eqv (Q.plaus N F) (Q.ratioPlaus v) := by
    exact Q.event_eqv_ratio (ofCellEvent N hN F) F rfl
  constructor
  · intro h
    have huv : Q.eqv (Q.ratioPlaus u) (Q.ratioPlaus v) :=
      Q.eqv_trans (Q.eqv_symm hE) (Q.eqv_trans h hF)
    have hratio := Q.eqv_implies_sameRatio huv
    apply Nat.eq_of_mul_eq_mul_right hN
    exact hratio
  · exact Q.count_invariant N E F

private theorem lt_of_mul_lt_mul_right_constructive {a b c : Nat}
    (h : a * c < b * c) : a < b := by
  rcases Nat.lt_or_ge a b with hab | hba
  · exact hab
  · exact False.elim
      ((Nat.not_lt_of_ge (Nat.mul_le_mul_right c hba)) h)

/--
On a positive fixed urn, strict qualitative comparison of arbitrary events is
exactly strict comparison of their selected-cell counts.
-/
theorem event_lt_iff_count_lt (Q : QualitativeUrnScale)
    (N : Nat) (hN : 0 < N) (E F : Event (Fin N)) :
    Q.lt (Q.plaus N E) (Q.plaus N F) ↔
      count (FiniteCellProduct.cells N) E <
        count (FiniteCellProduct.cells N) F := by
  let u := ofCellEvent N hN E
  let v := ofCellEvent N hN F
  have hE : Q.eqv (Q.plaus N E) (Q.ratioPlaus u) := by
    exact Q.event_eqv_ratio (ofCellEvent N hN E) E rfl
  have hF : Q.eqv (Q.plaus N F) (Q.ratioPlaus v) := by
    exact Q.event_eqv_ratio (ofCellEvent N hN F) F rfl
  constructor
  · intro h
    have huv : Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v) :=
      Q.lt_respects_eqv hE hF h
    have hratio := Q.lt_implies_ratio_lt huv
    dsimp [u, v, ofCellEvent] at hratio
    exact lt_of_mul_lt_mul_right_constructive hratio
  · intro h
    have huv : Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v) := by
      apply Q.ratio_lt_implies_lt
      dsimp [u, v, ofCellEvent]
      exact Nat.mul_lt_mul_of_pos_right h hN
    exact Q.lt_respects_eqv (Q.eqv_symm hE) (Q.eqv_symm hF) huv

/--
The qualitative representation theorem: the rational value `k/N` is a
well-defined rescaling of primitive qualitative plausibility classes.
-/
theorem rational_rescaling_well_defined (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.eqv (Q.ratioPlaus u) (Q.ratioPlaus v)) :
    QProb.Equiv u.toQProb v.toQProb := by
  exact sameRatio_toQProb (Q.eqv_implies_sameRatio h)

/--
The rational rescaling is order-preserving on represented qualitative values:
strict qualitative increase implies strict increase of the represented ratio.
-/
theorem rational_rescaling_order_preserving (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v)) :
    u.k * v.N < v.k * u.N := by
  exact Q.lt_implies_ratio_lt h

/--
The rational rescaling also reflects strict order: strict increase of the
represented ratio implies strict qualitative increase.
-/
theorem rational_rescaling_order_reflecting (Q : QualitativeUrnScale)
    {u v : UrnRatio} (h : u.k * v.N < v.k * u.N) :
    Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v) := by
  exact Q.ratio_lt_implies_lt h

theorem rational_rescaling_order_iff (Q : QualitativeUrnScale)
    (u v : UrnRatio) :
    Q.lt (Q.ratioPlaus u) (Q.ratioPlaus v) ↔
      u.k * v.N < v.k * u.N :=
  Q.lt_iff_ratio_lt u v

end QualitativeUrnScale

namespace UrnRatio

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
