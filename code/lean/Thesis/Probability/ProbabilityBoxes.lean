import Thesis.Probability.QProbOrder
import Thesis.Probability.Construction

namespace Thesis.Probability.ProbabilityBoxes

/-- Every finite coordinate assignment of box indices is enumerated. The
indices select intervals, never a cap on a feasible law's denominator. -/
def enumerate : (dimension size : Nat) → List (Fin dimension → Fin (size + 1))
  | 0, _ => [fun index => Fin.elim0 index]
  | dimension + 1, size => (List.finRange (size + 1)).flatMap (fun head =>
      (enumerate dimension size).map (fun tail => Fin.cases head tail))

theorem enumerate_complete : (dimension size : Nat) → (values : Fin dimension → Fin (size + 1)) → values ∈ enumerate dimension size
  | 0, _, values => by
      have equal : values = fun index => Fin.elim0 index := by funext index; exact Fin.elim0 index
      rw [equal]
      exact List.mem_singleton_self _
  | dimension + 1, size, values => by
      apply List.mem_flatMap.mpr
      refine ⟨values 0, List.mem_finRange _, List.mem_map.mpr ?_⟩
      refine ⟨(fun index => values index.succ), enumerate_complete dimension size _, ?_⟩
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

/-- The floor index of an arbitrary rational probability. -/
def locate (p : QProb) (bounded : p.num ≤ p.den) (size : Nat) : Fin (size + 1) :=
  ⟨p.num * size / p.den, Nat.lt_succ_of_le (Nat.div_le_of_le_mul (Nat.mul_le_mul_right size bounded))⟩

def lower {size : Nat} (index : Fin (size + 1)) (positive : 0 < size) : QProb := ⟨index.val, size, positive⟩
def upper {size : Nat} (index : Fin (size + 1)) (positive : 0 < size) : QProb := ⟨index.val + 1, size, positive⟩
def width (size : Nat) (positive : 0 < size) : QProb := ⟨1, size, positive⟩

theorem locate_bounds (p : QProb) (bounded : p.num ≤ p.den) (size : Nat) (positive : 0 < size) :
    QProb.LE (lower (locate p bounded size) positive) p ∧ QProb.LE p (upper (locate p bounded size) positive) := by
  constructor
  · simpa only [lower, locate, QProb.LE, Nat.mul_comm] using Nat.mul_div_le (p.num * size) p.den
  · simpa only [upper, locate, QProb.LE, Nat.mul_comm] using
      Nat.le_of_lt (Nat.lt_mul_div_succ (p.num * size) p.den_pos)

theorem upper_eq_lower_add_width {size : Nat} (index : Fin (size + 1)) (positive : 0 < size) :
    QProb.Equiv (QProb.add (lower index positive) (width size positive)) (upper index positive) :=
  QProb.add_mk_same_den size positive index.val 1

/-- Any two rational points in one box differ by at most its width. They
need not be endpoints, grid points, or share the box's denominator. -/
theorem same_box_close {size : Nat} (index : Fin (size + 1)) (positive : 0 < size) (p q : QProb)
    (pBounds : QProb.LE (lower index positive) p ∧ QProb.LE p (upper index positive))
    (qBounds : QProb.LE (lower index positive) q ∧ QProb.LE q (upper index positive)) :
    QProb.LE p (QProb.add q (width size positive)) ∧ QProb.LE q (QProb.add p (width size positive)) := by
  have bound (x y : QProb) (above : QProb.LE x (upper index positive)) (below : QProb.LE (lower index positive) y) :
      QProb.LE x (QProb.add y (width size positive)) := by
    have moved := QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm (upper_eq_lower_add_width index positive)) above
    exact QProb.le_trans moved (QProb.add_le_add below (QProb.le_refl _))
  exact ⟨bound p q pBounds.2 qBounds.1, bound q p qBounds.2 pBounds.1⟩

end Thesis.Probability.ProbabilityBoxes
