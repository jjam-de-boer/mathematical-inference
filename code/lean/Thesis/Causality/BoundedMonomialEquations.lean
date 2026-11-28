import Thesis.Causality.BoundedArithmeticTies
import Thesis.Probability.QProbOrder

namespace Thesis.Causality.QualitativeTies
open Probability

/-!
# Compare sums of three monomials using bounded arithmetic

A signed elementary equation becomes an equality between two sums of
at most three nonnegative monomials after clearing denominators. A term
in each monomial is a declared unit-interval rate; absent terms can be
encoded by the supplied zero rate. The mathematical sums can reach
three. In the compiled constraints each monomial is scaled by one quarter
before addition, so every computed slot is still in the unit interval.
Scaling is by the same positive constant on both sides.
-/

abbrev BoundedRate := {p : QProb // p.LE .one}
abbrev Monomial (n : Nat) := Fin n × Fin n
abbrev MonomialSide (n : Nat) := Fin 3 → Monomial n

def MonomialSide.evaluate (side : MonomialSide n) (values : Fin n → QProb) : QProb :=
  let term := fun i => (values (side i).1).mul (values (side i).2)
  ((term 0).add (term 1)).add (term 2)

structure MonomialEquation (n : Nat) where
  left : MonomialSide n
  right : MonomialSide n

structure MonomialSystem where
  count : Nat
  requirements : List (BoundedConstraint count)
  equations : List (MonomialEquation count)

def MonomialSystem.Solvable (system : MonomialSystem) : Prop :=
  ∃ values : Fin system.count → BoundedRate,
    (∀ req ∈ system.requirements, req.holds (fun i => (values i).val)) ∧
    (∀ eq ∈ system.equations, (eq.left.evaluate (fun i => (values i).val)).Equiv
      (eq.right.evaluate (fun i => (values i).val)))

namespace BoundedMonomialEquations

private def width (n equations : Nat) : Nat := n + 2 + 16 * equations
private def base (m : Nat) (i : Fin n) : Fin (width n m) :=
  ⟨i.val, by unfold width; have h := i.isLt; omega⟩
private def halfIndex (n m : Nat) : Fin (width n m) := ⟨n, by unfold width; omega⟩
private def quarterIndex (n m : Nat) : Fin (width n m) := ⟨n+1, by unfold width; omega⟩

/-- Eight results per side, in separate blocks. Six results implement
products and scaling, and two implement the successive additions. -/
private def slot (n : Nat) (i : Fin m) (side : Bool) (offset : Fin 8) : Fin (width n m) :=
  ⟨n + 2 + 16 * i.val + (if side then 8 else 0) + offset.val, by
    unfold width
    have block := i.isLt
    have entry := offset.isLt
    cases side <;> dsimp <;> omega⟩

private def rename (f : Fin n → Fin m) : BoundedConstraint n → BoundedConstraint m
  | .equal a b => .equal (f a) (f b)
  | .zero a => .zero (f a)
  | .one a => .one (f a)
  | .half a => .half (f a)
  | .multiply a b c => .multiply (f a) (f b) (f c)
  | .add a b c => .add (f a) (f b) (f c)

private theorem holds_rename (f : Fin n → Fin m) (values : Fin m → QProb) (req : BoundedConstraint n) :
    (rename f req).holds values ↔ req.holds (values ∘ f) := by cases req <;> rfl

private def sideProgram (i : Fin m) (direction : Bool) (side : MonomialSide n) :
    List (BoundedConstraint (width n m)) :=
  let v := slot n i direction
  let q := quarterIndex n m
  [ .multiply (base m (side 0).1) (base m (side 0).2) (v 0), .multiply q (v 0) (v 1),
    .multiply (base m (side 1).1) (base m (side 1).2) (v 2), .multiply q (v 2) (v 3),
    .multiply (base m (side 2).1) (base m (side 2).2) (v 4), .multiply q (v 4) (v 5),
    .add (v 1) (v 3) (v 6), .add (v 6) (v 5) (v 7) ]

private def equationProgram (i : Fin m) (equation : MonomialEquation n) : List (BoundedConstraint (width n m)) :=
  sideProgram i false equation.left ++ sideProgram i true equation.right ++ [.equal (slot n i false 7) (slot n i true 7)]

/-- Translate the entire system using one shared scale and fresh result
slots for each sum on each side. -/
def compile (system : MonomialSystem) : List (BoundedConstraint (width system.count system.equations.length)) :=
  let n := system.count
  let m := system.equations.length
  [.half (halfIndex n m), .multiply (halfIndex n m) (halfIndex n m) (quarterIndex n m)] ++
    system.requirements.map (rename (base m)) ++
    (List.finRange m).flatMap fun i => equationProgram i system.equations[i]

private def half : QProb := ⟨1, 2, by decide⟩
private def quarter : QProb := ⟨1, 4, by decide⟩

private theorem mul_le {a b a' b' : QProb} (ha : a.LE a') (hb : b.LE b') :
    (a.mul b).LE (a'.mul b') := by
  change (a.num * b.num) * (a'.den * b'.den) ≤ (a'.num * b'.num) * (a.den * b.den)
  rw [QProb.mul_reorder_four a.num b.num a'.den b'.den, QProb.mul_reorder_four a'.num b'.num a.den b.den]
  exact Nat.mul_le_mul ha hb

private theorem mul_quarter_cancel {a b : QProb} (same : (quarter.mul a).Equiv (quarter.mul b)) : a.Equiv b := by
  change (1 * a.num) * (4 * b.den) = (1 * b.num) * (4 * a.den) at same
  simp only [Nat.one_mul] at same
  apply Nat.eq_of_mul_eq_mul_right (m := 4) (by decide)
  calc
    _ = a.num * (4 * b.den) := by ac_rfl
    _ = b.num * (4 * a.den) := same
    _ = _ := by ac_rfl

private theorem side_correct (i : Fin m) (direction : Bool) (side : MonomialSide n)
    (chosen : Fin (width n m) → QProb)
    (valid : ∀ clause ∈ sideProgram i direction side, clause.holds chosen) :
    ((chosen (quarterIndex n m)).mul (side.evaluate (fun j => chosen (base m j)))).Equiv
      (chosen (slot n i direction 7)) := by
  unfold sideProgram at valid
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    BoundedConstraint.holds] at valid
  obtain ⟨term₀, scale₀, term₁, scale₁, term₂, scale₂, firstSum, totalSum⟩ := valid
  unfold MonomialSide.evaluate
  refine QProb.equiv_trans (QProb.mul_add_distrib _ _ _) ?_
  apply QProb.equiv_trans ?_ totalSum
  apply QProb.add_congr
  · refine QProb.equiv_trans (QProb.mul_add_distrib _ _ _) ?_
    apply QProb.equiv_trans ?_ firstSum
    exact QProb.add_congr (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) term₀) scale₀)
      (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) term₁) scale₁)
  · exact QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) term₂) scale₂

private theorem scale_certifies (system : MonomialSystem) (chosen : Fin (width system.count system.equations.length) → QProb)
    (obeys : ∀ req ∈ compile system, req.holds chosen) :
    (chosen (quarterIndex system.count system.equations.length)).Equiv quarter := by
  have first := obeys (.half _) (List.mem_append_left _ (List.mem_cons_self))
  have second := obeys (.multiply _ _ _) (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact QProb.equiv_trans (QProb.equiv_symm second) (QProb.mul_congr first first)

private theorem unscaled_of_bounded (system : MonomialSystem)
    (chosen : Fin (width system.count system.equations.length) → BoundedRate)
    (obeys : ∀ req ∈ compile system, req.holds (fun i => (chosen i).val)) : system.Solvable := by
  let values := fun i => (chosen i).val
  refine ⟨fun i => chosen (base system.equations.length i), ?_, ?_⟩
  · intro req member
    apply (holds_rename _ values req).mp
    exact obeys _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨req, member, rfl⟩)))
  · intro equation member
    obtain ⟨k, bound, given⟩ := List.getElem_of_mem member
    let i : Fin system.equations.length := ⟨k, bound⟩
    have fromProgram : ∀ req ∈ equationProgram i equation, req.holds values := by
      intro req present
      apply obeys
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨i, List.mem_finRange i, given.symm ▸ present⟩
    have lhs := side_correct i false equation.left values (fun req h => fromProgram req (List.mem_append_left _ (List.mem_append_left _ h)))
    have rhs := side_correct i true equation.right values (fun req h => fromProgram req (List.mem_append_left _ (List.mem_append_right _ h)))
    have final := fromProgram _ (List.mem_append_right _ List.mem_cons_self)
    have scale := scale_certifies system values obeys
    apply mul_quarter_cancel
    exact QProb.equiv_trans (QProb.mul_congr (QProb.equiv_symm scale) (QProb.equiv_refl _))
      (QProb.equiv_trans lhs (QProb.equiv_trans final (QProb.equiv_trans (QProb.equiv_symm rhs)
        (QProb.mul_congr scale (QProb.equiv_refl _)))))

private def halfRate : BoundedRate := ⟨half, by change 1 ≤ 2; decide⟩
private def quarterRate : BoundedRate := ⟨quarter, by change 1 ≤ 4; decide⟩

private def sideValues (side : MonomialSide n) (values : Fin n → BoundedRate) (position : Nat) : BoundedRate :=
  let raw (j : Fin 3) : BoundedRate :=
    let a := values (side j).1
    let b := values (side j).2
    ⟨a.val.mul b.val, (QProb.le_congr (QProb.equiv_refl _) (QProb.mul_one _)) (mul_le a.property b.property)⟩
  let scaled (j : Fin 3) : QProb := quarter.mul (raw j).val
  have scaledBound (j : Fin 3) : (scaled j).LE quarter :=
    (QProb.le_congr (QProb.equiv_refl _) (QProb.mul_one _)) (mul_le (QProb.le_refl _) (raw j).property)
  let firstSum := (scaled 0).add (scaled 1)
  have firstBound : firstSum.LE (quarter.add quarter) := QProb.add_le_add (scaledBound 0) (scaledBound 1)
  let total := firstSum.add (scaled 2)
  have totalBound : total.LE ((quarter.add quarter).add quarter) := QProb.add_le_add firstBound (scaledBound 2)
  match position with
  | 0 => raw 0
  | 1 => ⟨scaled 0, QProb.le_trans (scaledBound 0) quarterRate.property⟩
  | 2 => raw 1
  | 3 => ⟨scaled 1, QProb.le_trans (scaledBound 1) quarterRate.property⟩
  | 4 => raw 2
  | 5 => ⟨scaled 2, QProb.le_trans (scaledBound 2) quarterRate.property⟩
  | 6 => ⟨firstSum, QProb.le_trans firstBound (by change 8 ≤ 16; decide)⟩
  | _ => ⟨total, QProb.le_trans totalBound (by change 48 ≤ 64; decide)⟩

private def directionSide (equation : MonomialEquation n) (side : Bool) : MonomialSide n :=
  if side then equation.right else equation.left

private def liftedValues (system : MonomialSystem) (values : Fin system.count → BoundedRate)
    (index : Fin (width system.count system.equations.length)) : BoundedRate :=
  if original : index.val < system.count then values ⟨index.val, original⟩
  else if atHalf : index.val = system.count then halfRate
  else if atQuarter : index.val = system.count + 1 then quarterRate
  else
    let relative := index.val - (system.count + 2)
    let k : Fin system.equations.length := ⟨relative / 16, by
      have bound := index.isLt
      unfold width at bound
      dsimp [relative]
      omega⟩
    sideValues (directionSide system.equations[k] (decide (8 ≤ relative % 16))) values (relative % 8)

private theorem liftedValues_base (system : MonomialSystem) (values : Fin system.count → BoundedRate) (i : Fin system.count) :
    liftedValues system values (base system.equations.length i) = values i := by
  unfold liftedValues
  have within : (base system.equations.length i).val < system.count := i.isLt
  rw [dif_pos within]
  rfl

private theorem liftedValues_half (system : MonomialSystem) (values : Fin system.count → BoundedRate) :
    liftedValues system values (halfIndex system.count system.equations.length) = halfRate := by
  unfold liftedValues
  have before : ¬(halfIndex system.count system.equations.length).val < system.count := Nat.lt_irrefl _
  have here : (halfIndex system.count system.equations.length).val = system.count := rfl
  rw [dif_neg before, dif_pos here]

private theorem liftedValues_quarter (system : MonomialSystem) (values : Fin system.count → BoundedRate) :
    liftedValues system values (quarterIndex system.count system.equations.length) = quarterRate := by
  unfold liftedValues
  rw [dif_neg (by change ¬system.count + 1 < system.count; omega),
      dif_neg (by change system.count + 1 ≠ system.count; omega)]
  have here : (quarterIndex system.count system.equations.length).val = system.count + 1 := rfl
  rw [dif_pos here]

private theorem liftedValues_slot (system : MonomialSystem) (values : Fin system.count → BoundedRate)
    (i : Fin system.equations.length) (direction : Bool) (offset : Fin 8) :
    liftedValues system values (slot system.count i direction offset) =
      sideValues (directionSide system.equations[i] direction) values offset.val := by
  let index := slot system.count i direction offset
  have formula : index.val = system.count + 2 + 16 * i.val + (if direction then 8 else 0) + offset.val := rfl
  have bound := offset.isLt
  change liftedValues system values index = _
  unfold liftedValues
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
  have picked : (index.val - (system.count + 2)) / 16 = i.val := by cases direction <;> simp_all <;> omega
  have final : (index.val - (system.count + 2)) % 8 = offset.val := by cases direction <;> simp_all <;> omega
  have side : decide (8 ≤ (index.val - (system.count + 2)) % 16) = direction := by
    cases direction
    · apply decide_eq_false; simp only [Bool.false_eq_true, if_false] at formula; omega
    · apply decide_eq_true; simp only [if_true] at formula; omega
  simp only [picked, final, side]

private theorem sideProgram_realized (system : MonomialSystem) (values : Fin system.count → BoundedRate)
    (i : Fin system.equations.length) (direction : Bool) :
    ∀ req ∈ sideProgram i direction (directionSide system.equations[i] direction),
      req.holds (fun j => (liftedValues system values j).val) := by
  unfold sideProgram
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, BoundedConstraint.holds,
    liftedValues_base, liftedValues_quarter, liftedValues_slot, quarterRate]
  exact ⟨QProb.equiv_refl _, QProb.equiv_refl _, QProb.equiv_refl _, QProb.equiv_refl _,
    QProb.equiv_refl _, QProb.equiv_refl _, QProb.equiv_refl _, QProb.equiv_refl _⟩

private theorem equationProgram_realized (system : MonomialSystem) (values : Fin system.count → BoundedRate)
    (i : Fin system.equations.length)
    (holds : (system.equations[i].left.evaluate (fun j => (values j).val)).Equiv
      (system.equations[i].right.evaluate (fun j => (values j).val))) :
    ∀ req ∈ equationProgram i system.equations[i], req.holds (fun j => (liftedValues system values j).val) := by
  intro req member
  rcases List.mem_append.mp member with fromSide | final
  · rcases List.mem_append.mp fromSide with left | right
    · exact sideProgram_realized system values i false req left
    · exact sideProgram_realized system values i true req right
  · rcases List.mem_cons.mp final with tie | absent
    · subst req
      let f := fun j => (liftedValues system values j).val
      have left := side_correct i false (system.equations[i].left) f (sideProgram_realized system values i false)
      have right := side_correct i true (system.equations[i].right) f (sideProgram_realized system values i true)
      unfold f at left right
      simp only [liftedValues_quarter, liftedValues_base, quarterRate] at left right
      exact QProb.equiv_trans (QProb.equiv_symm left) (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) holds) right)
    · cases absent

private theorem bounded_of_unscaled (system : MonomialSystem) (solved : system.Solvable) :
    ∃ values : Fin (width system.count system.equations.length) → BoundedRate,
      ∀ req ∈ compile system, req.holds (fun i => (values i).val) := by
  obtain ⟨values, requirements, equations⟩ := solved
  refine ⟨liftedValues system values, ?_⟩
  intro req member
  rcases List.mem_append.mp member with prefixOrOriginal | generated
  · rcases List.mem_append.mp prefixOrOriginal with scaleRequirements | original
    · rcases List.mem_cons.mp scaleRequirements with first | rest
      · subst req
        simp only [BoundedConstraint.holds, liftedValues_half, halfRate]
        exact QProb.equiv_refl _
      · rcases List.mem_cons.mp rest with second | absent
        · subst req
          simp only [BoundedConstraint.holds, liftedValues_half, liftedValues_quarter, halfRate, quarterRate]
          exact QProb.equiv_refl _
        · cases absent
    · obtain ⟨named, appears, rfl⟩ := List.mem_map.mp original
      apply (holds_rename _ _ _).mpr
      simpa only [Function.comp_def, liftedValues_base] using requirements named appears
  · obtain ⟨i, _, localRequirement⟩ := List.mem_flatMap.mp generated
    exact equationProgram_realized system values i (equations _ (List.getElem_mem _)) req localRequirement

/-- Clearing the arithmetic equation and building its bounded gates
preserves and reflects all solvability, with the scale certified positive. -/
theorem compile_correct (system : MonomialSystem) :
    (∃ values : Fin (width system.count system.equations.length) → BoundedRate,
      ∀ req ∈ compile system, req.holds (fun i => (values i).val)) ↔ system.Solvable :=
  ⟨fun ⟨values, correct⟩ => unscaled_of_bounded system values correct, bounded_of_unscaled system⟩

end BoundedMonomialEquations
end Thesis.Causality.QualitativeTies
