import Thesis.Probability.Distros.Gaussian
import Thesis.Probability.Distros.IndependentSums

namespace Thesis.Probability.Distros

open Combinatorics

/-! Additivity and moments of the finite squared-coordinate construction. -/

/-- One squared centred coordinate, on natural outcomes. -/
def gaussianSquareRecord (radius : Nat) (q : QProb) (bounded : QProb.LE q QProb.one) :
    FiniteProbRecord Nat :=
  (discreteGaussianDistro radius q bounded).record.map
    (fun value => natSqDiff value.val radius)

/-- The existing finite χ² record is literally a repeated independent sum
after exposing its natural-valued outcomes. -/
theorem chiSquared_numeric_record (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    (chiSquaredRecord df radius q bounded).map Fin.val =
      iteratedSumRecord (gaussianSquareRecord radius q bounded) df := by
  induction df with
  | zero => rfl
  | succ df ih =>
      change (((chiSquaredRecord df radius q bounded).product
        (discreteGaussianDistro radius q bounded).record).map _).map Fin.val = _
      rw [FiniteProbRecord.map_comp]
      change ((chiSquaredRecord df radius q bounded).product
        (discreteGaussianDistro radius q bounded).record).map
          (fun pair => pair.1.val + natSqDiff pair.2.val radius) = _
      rw [← sumRecord_map (chiSquaredRecord df radius q bounded)
        (discreteGaussianDistro radius q bounded).record Fin.val
        (fun value => natSqDiff value.val radius), ih]
      rfl

/-- Independent blocks of squared coordinates combine their degrees of freedom. -/
theorem chiSquared_additive_record (df df' radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    sumRecord ((chiSquaredRecord df radius q bounded).map Fin.val)
        ((chiSquaredRecord df' radius q bounded).map Fin.val) =
      (chiSquaredRecord (df + df') radius q bounded).map Fin.val := by
  rw [chiSquared_numeric_record, chiSquared_numeric_record,
    chiSquared_numeric_record, iteratedSumRecord_add]

/-- Additivity holds on every Boolean event of the summed numeric outcome. -/
theorem chiSquared_additivity (df df' radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) (event : Event Nat) :
    QProb.Equiv
      ((independentSum (chiSquaredDistro df radius q bounded)
        (chiSquaredDistro df' radius q bounded)).distro.record.probVal
          (fun pair => event (pair.1.val + pair.2.val)))
      ((chiSquaredDistro (df + df') radius q bounded).distro.record.probVal
        (fun value => event value.val)) := by
  have h := congrArg (fun record => record.probVal event)
    (chiSquared_additive_record df df' radius q bounded)
  rw [sumRecord_map] at h
  dsimp only at h
  have he : QProb.Equiv
      ((((chiSquaredRecord df radius q bounded).product
        (chiSquaredRecord df' radius q bounded)).map
          (fun pair => pair.1.val + pair.2.val)).probVal event)
      (((chiSquaredRecord (df + df') radius q bounded).map Fin.val).probVal event) := by
    rw [h]
    exact QProb.equiv_refl _
  exact QProb.equiv_trans
    (QProb.equiv_symm (FiniteProbRecord.map_probVal _ _ event))
    (QProb.equiv_trans he
      (FiniteProbRecord.map_probVal _ _ event))

theorem chiSquared_mean (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (mean (chiSquaredDistro df radius q bounded))
      (QProb.scale df (mean (naturalDistro (gaussianSquareRecord radius q bounded)))) := by
  have transport := NatDistro.mean_map (chiSquaredDistro df radius q bounded) Fin.val id
  change mean (naturalDistro ((chiSquaredRecord df radius q bounded).map Fin.val)) =
    mean (chiSquaredDistro df radius q bounded) at transport
  rw [← transport, chiSquared_numeric_record]
  exact iteratedSumRecord_mean _ _

theorem chiSquared_variance (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv (variance (chiSquaredDistro df radius q bounded))
      (QProb.scale df (variance (naturalDistro (gaussianSquareRecord radius q bounded)))) := by
  have transport := NatDistro.variance_map (chiSquaredDistro df radius q bounded) Fin.val id
  change variance (naturalDistro ((chiSquaredRecord df radius q bounded).map Fin.val)) =
    variance (chiSquaredDistro df radius q bounded) at transport
  rw [← transport, chiSquared_numeric_record]
  exact iteratedSumRecord_variance _ _

theorem chiSquared_pgf (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) (s : QProb) :
    QProb.Equiv (pgf (chiSquaredDistro df radius q bounded) s)
      (qpow (pgf (naturalDistro (gaussianSquareRecord radius q bounded)) s) df) := by
  have transport := NatDistro.pgf_map (chiSquaredDistro df radius q bounded) Fin.val id s
  change pgf (naturalDistro ((chiSquaredRecord df radius q bounded).map Fin.val)) s =
    pgf (chiSquaredDistro df radius q bounded) s at transport
  rw [← transport, chiSquared_numeric_record]
  exact iteratedSumRecord_pgf _ _ _

end Thesis.Probability.Distros
