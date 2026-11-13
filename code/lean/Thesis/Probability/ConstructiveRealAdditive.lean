import Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.ConstructiveReal

theorem add_comm (x y : ConstructiveReal) : Equiv (add x y) (add y x) := by
  constructor
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _)).mpr
      (SignedRatio.add_le_add (x.coherent _ _) (y.coherent _ _))
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _)).mpr
      (SignedRatio.add_le_add (y.coherent _ _) (x.coherent _ _))

theorem add_assoc (x y z : ConstructiveReal) : Equiv (add (add x y) z) (add x (add y z)) := by
  constructor
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_assoc _ _ _)).mp
      (SignedRatio.add_le_add (SignedRatio.add_le_add (x.coherent _ _) (y.coherent _ _)) (z.coherent _ _))
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.add_assoc _ _ _) (SignedRatio.equiv_refl _)).mp
      (SignedRatio.add_le_add (SignedRatio.add_le_add (x.coherent _ _) (y.coherent _ _)) (z.coherent _ _))

theorem add_zero (x : ConstructiveReal) : Equiv (add x zero) x := by
  constructor
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.add_zero _) (SignedRatio.equiv_refl _)).mpr (x.coherent _ _)
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_zero _)).mpr (x.coherent _ _)

theorem zero_add (x : ConstructiveReal) : Equiv (add zero x) x := equiv_trans (add_comm _ _) (add_zero _)

theorem add_neg (x : ConstructiveReal) : Equiv (add x (neg x)) zero := by
  constructor
  · intro first second
    exact (SignedRatio.sub_le_zero_iff _ _).mpr (x.enclose first.half).ordered
  · intro first second
    exact (SignedRatio.zero_le_sub_iff _ _).mpr (x.enclose second.half).ordered

theorem neg_neg (x : ConstructiveReal) : Equiv (neg (neg x)) x := by
  constructor
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.neg_neg _) (SignedRatio.equiv_refl _)).mpr (x.coherent _ _)
  · intro first second
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.neg_neg _)).mpr (x.coherent _ _)

theorem ofSignedRatio_add (a b : SignedRatio) :
    Equiv (add (ofSignedRatio a) (ofSignedRatio b)) (ofSignedRatio (SignedRatio.add a b)) :=
  ⟨fun _ _ => SignedRatio.le_refl _, fun _ _ => SignedRatio.le_refl _⟩

theorem ofSignedRatio_neg (a : SignedRatio) : Equiv (ofSignedRatio (SignedRatio.neg a)) (neg (ofSignedRatio a)) :=
  ⟨fun _ _ => SignedRatio.le_refl _, fun _ _ => SignedRatio.le_refl _⟩

/-- Closed real order can be cancelled under a common translation, without
requiring a decision procedure for that order. -/
theorem add_le_add_right_iff (a b c : ConstructiveReal) : LE (add a c) (add b c) ↔ LE a b := by
  constructor
  · intro bounded
    have shifted := add_le_add bounded (le_refl (neg c))
    have reduce (x : ConstructiveReal) : Equiv (add (add x c) (neg c)) x :=
      equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg c)) (add_zero x))
    exact (le_congr (reduce a) (reduce b)).mp shifted
  · intro bounded
    exact add_le_add bounded (le_refl c)

/-- Finite sums use the same computable enclosure arithmetic. -/
def listSum : List ConstructiveReal → ConstructiveReal
  | [] => zero
  | value :: rest => add value (listSum rest)

theorem listSum_map_congr (values : List A) (first second : A → ConstructiveReal)
    (same : ∀ value ∈ values, Equiv (first value) (second value)) :
    Equiv (listSum (values.map first)) (listSum (values.map second)) := by
  induction values with
  | nil => exact equiv_refl _
  | cons value rest ih =>
      exact add_congr (same value (List.mem_cons_self ..))
        (ih (fun other member => same other (List.mem_cons_of_mem _ member)))

end Thesis.Probability.ConstructiveReal
