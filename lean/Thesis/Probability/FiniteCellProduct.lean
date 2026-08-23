import Thesis.Probability.ConstructivePermutation

namespace Thesis
namespace Probability

/-!
Constructive cell-level products for finite urns.

The product of an `M`-cell urn and an `N`-cell urn is first enumerated as
`Fin M × Fin N`.  Row-major encoding then identifies those pairs with the
`M * N` cells of `Fin (M * N)`.  The counting theorem below verifies that a
rectangular Boolean event selects the product of the two component counts.
-/

namespace FiniteCellProduct

/-- Explicit two-sided data witnessing an equivalence of types. -/
structure ConstructiveEquivalence (A : Type u) (B : Type v) where
  forward : A -> B
  backward : B -> A
  backward_forward : forall value, backward (forward value) = value
  forward_backward : forall value, forward (backward value) = value

/-- Row-major encoding of a pair of finite cell indices. -/
def encode {M N : Nat} (cell : Fin M × Fin N) : Fin (M * N) :=
  ⟨cell.1.val * N + cell.2.val, by
    calc
      cell.1.val * N + cell.2.val < cell.1.val * N + N :=
        Nat.add_lt_add_left cell.2.isLt _
      _ = Nat.succ cell.1.val * N := (Nat.succ_mul _ _).symm
      _ <= M * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt cell.1.isLt)⟩

/-- Decode a row-major index into its quotient and remainder coordinates. -/
def decode {M N : Nat} (hN : 0 < N) (index : Fin (M * N)) :
    Fin M × Fin N :=
  (⟨index.val / N, (Nat.div_lt_iff_lt_mul hN).2 index.isLt⟩,
    ⟨index.val % N, Nat.mod_lt _ hN⟩)

@[simp] theorem decode_encode {M N : Nat} (hN : 0 < N)
    (cell : Fin M × Fin N) :
    decode hN (encode cell) = cell := by
  apply Prod.ext
  · apply Fin.ext
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        cell.1.val * N + cell.2.val < cell.1.val * N + N :=
          Nat.add_lt_add_left cell.2.isLt _
        _ = Nat.succ cell.1.val * N := (Nat.succ_mul _ _).symm
  · apply Fin.ext
    change (cell.1.val * N + cell.2.val) % N = cell.2.val
    rw [Nat.add_comm, Nat.mul_comm cell.1.val N,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt cell.2.isLt

@[simp] theorem encode_decode {M N : Nat} (hN : 0 < N)
    (index : Fin (M * N)) :
    encode (decode hN index) = index := by
  apply Fin.ext
  simp only [encode, decode]
  change (index.val / N) * N + index.val % N = index.val
  rw [Nat.mul_comm]
  exact Nat.div_add_mod index.val N

/-- The explicit constructive equivalence between product cells and `M * N` cells. -/
def equivalence (M N : Nat) (hN : 0 < N) :
    ConstructiveEquivalence (Fin M × Fin N) (Fin (M * N)) where
  forward := encode
  backward := decode hN
  backward_forward := decode_encode hN
  forward_backward := encode_decode hN

/-- The canonical list of all cells of a finite index type. -/
def cells (N : Nat) : List (Fin N) :=
  List.ofFn id

/-- The canonical finite-cell enumeration contains no repeated indices. -/
theorem cells_nodup : forall N, (cells N).Nodup := by
  intro N
  change (List.finRange N).Nodup
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.finRange_succ]
      exact List.nodup_cons.mpr ⟨by
        intro member
        rcases List.mem_map.mp member with ⟨value, _, equal⟩
        exact Fin.succ_ne_zero value equal,
        List.Pairwise.map Fin.succ (fun left right different equal =>
          different ((Fin.succ_inj).mp equal)) ih⟩

private theorem count_cells_singleton (index : Fin N) :
    count (cells N) (fun value => value == index) = 1 := by
  change List.count index (cells N) = 1
  rw [(cells_nodup N).count]
  simp [cells]

/-- Row-major enumeration of all pairs of cells. -/
def productCells (M N : Nat) : List (Fin M × Fin N) :=
  (cells M).flatMap (fun left =>
    (cells N).map (fun right => (left, right)))

/-- The rectangular product of two Boolean cell events. -/
def rectangularEvent (E : Event (Fin M)) (F : Event (Fin N)) :
    Event (Fin M × Fin N) :=
  fun cell => E cell.1 && F cell.2

private theorem count_row (left : Fin M) (rightCells : List (Fin N))
    (E : Event (Fin M)) (F : Event (Fin N)) :
    count (rightCells.map (fun right => (left, right)))
        (rectangularEvent E F) =
      if E left = true then count rightCells F else 0 := by
  induction rightCells with
  | nil =>
      cases hE : E left <;> simp [count]
  | cons right rest ih =>
      change
        List.countP (rectangularEvent E F)
            ((left, right) :: rest.map (fun value => (left, value))) =
          if E left = true then List.countP F (right :: rest) else 0
      rw [List.countP_cons]
      have ih' :
          List.countP (rectangularEvent E F)
              (rest.map (fun value => (left, value))) =
            if E left = true then List.countP F rest else 0 := by
        simpa [count] using ih
      rw [ih', List.countP_cons]
      cases hE : E left <;> cases hF : F right <;>
        simp [rectangularEvent, hE, hF]

private theorem count_rectangular_lists (leftCells : List (Fin M))
    (rightCells : List (Fin N)) (E : Event (Fin M))
    (F : Event (Fin N)) :
    count
        (leftCells.flatMap (fun left =>
          rightCells.map (fun right => (left, right))))
        (rectangularEvent E F) =
      count leftCells E * count rightCells F := by
  induction leftCells with
  | nil =>
      simp [count]
  | cons left rest ih =>
      rw [List.flatMap_cons, count, List.countP_append]
      change
        List.countP (rectangularEvent E F)
            (rightCells.map (fun right => (left, right))) +
            count
              (rest.flatMap (fun value =>
                rightCells.map (fun right => (value, right))))
              (rectangularEvent E F) =
          List.countP E (left :: rest) * count rightCells F
      have hrow := count_row left rightCells E F
      rw [show
        List.countP (rectangularEvent E F)
            (rightCells.map (fun right => (left, right))) =
          (if E left = true then count rightCells F else 0) by
            simpa [count] using hrow]
      rw [ih, List.countP_cons]
      cases hE : E left with
      | false => simp [count]
      | true => simp [count, Nat.add_mul, Nat.add_comm]

/-- A rectangular event selects the product of its two component counts. -/
theorem count_rectangularEvent (E : Event (Fin M)) (F : Event (Fin N)) :
    count (productCells M N) (rectangularEvent E F) =
      count (cells M) E * count (cells N) F := by
  exact count_rectangular_lists (cells M) (cells N) E F

/-- The row-major enumeration transported to `Fin (M * N)`. -/
def encodedCells (M N : Nat) : List (Fin (M * N)) :=
  (productCells M N).map encode

/-- The rectangular event transported to the `M * N`-cell index type. -/
def encodedRectangularEvent (hN : 0 < N)
    (E : Event (Fin M)) (F : Event (Fin N)) : Event (Fin (M * N)) :=
  fun index => rectangularEvent E F (decode hN index)

private theorem encoded_singleton_event (hN : 0 < N)
    (target index : Fin (M * N)) :
    encodedRectangularEvent hN
        (fun left => left == (decode hN target).1)
        (fun right => right == (decode hN target).2) index =
      (index == target) := by
  apply Bool.eq_iff_iff.mpr
  simp only [encodedRectangularEvent, rectangularEvent, Bool.and_eq_true_iff,
    beq_iff_eq]
  constructor
  · rintro ⟨leftEqual, rightEqual⟩
    have decodedEqual : decode hN index = decode hN target :=
      Prod.ext leftEqual rightEqual
    calc
      index = encode (decode hN index) := (encode_decode hN index).symm
      _ = encode (decode hN target) := congrArg encode decodedEqual
      _ = target := encode_decode hN target
  · intro equal
    cases equal
    exact ⟨rfl, rfl⟩

/-- Transport along the explicit equivalence preserves the rectangular count. -/
theorem count_encodedRectangularEvent (hN : 0 < N)
    (E : Event (Fin M)) (F : Event (Fin N)) :
    count (encodedCells M N) (encodedRectangularEvent hN E F) =
      count (cells M) E * count (cells N) F := by
  rw [encodedCells, count, List.countP_map]
  change
    count (productCells M N)
        (fun cell => encodedRectangularEvent hN E F (encode cell)) = _
  simpa [encodedRectangularEvent] using count_rectangularEvent E F

private theorem count_encodedCells_singleton (hN : 0 < N)
    (index : Fin (M * N)) :
    count (encodedCells M N) (fun value => value == index) = 1 := by
  rw [← count_congr (xs := encodedCells M N)
    (E := encodedRectangularEvent hN
      (fun left => left == (decode hN index).1)
      (fun right => right == (decode hN index).2))
    (F := fun value => value == index) (encoded_singleton_event hN index)]
  rw [count_encodedRectangularEvent, count_cells_singleton,
    count_cells_singleton]

/-- Row-major encoding enumerates the same product cells as the canonical
enumeration of `Fin (M * N)`, possibly in a different order. -/
theorem encodedCells_perm_cells :
    (encodedCells M N).Perm (cells (M * N)) := by
  cases N with
  | zero => simp [encodedCells, productCells, cells]
  | succ N =>
      apply ConstructivePermutation.perm_of_count_eq
      intro index
      rw [List.count_eq_countP, List.count_eq_countP]
      change count (encodedCells M (N + 1)) (fun value => value == index) =
        count (cells (M * (N + 1))) (fun value => value == index)
      rw [count_encodedCells_singleton (Nat.zero_lt_succ N) index,
        count_cells_singleton index]

/-- The rectangular count transported to the canonical enumeration of the
`M * N`-cell urn. -/
theorem count_canonicalRectangularEvent (hN : 0 < N)
    (E : Event (Fin M)) (F : Event (Fin N)) :
    count (cells (M * N)) (encodedRectangularEvent hN E F) =
      count (cells M) E * count (cells N) F := by
  rw [← count_reindex encodedCells_perm_cells]
  exact count_encodedRectangularEvent hN E F

/-- If the component events select `k` and `l` cells, their encoded rectangle
selects exactly `k * l` cells in the product urn. -/
theorem selectedCells_product {k l : Nat} (hN : 0 < N)
    (E : Event (Fin M)) (F : Event (Fin N))
    (hE : count (cells M) E = k) (hF : count (cells N) F = l) :
    count (cells (M * N)) (encodedRectangularEvent hN E F) = k * l := by
  rw [count_canonicalRectangularEvent, hE, hF]

end FiniteCellProduct
end Probability
end Thesis
