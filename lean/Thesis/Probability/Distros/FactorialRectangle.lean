import Thesis.Probability.Distros.MultivariateFactorialInversion
import Thesis.Probability.Distros.DepletingSupport

namespace Thesis.Probability.Distros
open Combinatorics

/-- Exact coordinatewise bounds, including matching dimensions. This reuses
the existing finite coordinate comparison; bounds need not describe an urn. -/
abbrev CoordinateBounds (counts bounds : List Nat) : Prop := depletingCountsWithin counts bounds

theorem coordinateBounds_length (counts bounds : List Nat) (within : CoordinateBounds counts bounds) :
    counts.length = bounds.length := ((depletingCountsWithin_iff_coordinates counts bounds).mp within).1

/-- The actual rectangle, with a separate bound for each coordinate. A zero
bound retains its zero coordinate; the zero-dimensional rectangle is `[[]]`. -/
def factorialRectangle : List Nat → List (List Nat)
  | [] => [[]]
  | bound :: bounds => (List.range (bound + 1)).flatMap (fun order =>
      (factorialRectangle bounds).map (fun orders => order :: orders))

theorem factorialRectangle_mem (bounds orders : List Nat) (member : orders ∈ factorialRectangle bounds) :
    CoordinateBounds orders bounds := by
  induction bounds generalizing orders with
  | nil =>
      have same := List.mem_singleton.mp member
      cases same
      exact True.intro
  | cons bound bounds ih =>
      rcases List.mem_flatMap.mp member with ⟨order, within, tail⟩
      rcases List.mem_map.mp tail with ⟨orders, listed, same⟩
      cases same
      exact ⟨by have upper := List.mem_range.mp within; omega, ih orders listed⟩

theorem factorialRectangle_listSum (bound : Nat) (bounds : List Nat) (f : List Nat → QProb) :
    QProb.Equiv (QProb.listSum ((factorialRectangle (bound :: bounds)).map f))
      (QProb.listSum ((List.range (bound + 1)).map (fun order =>
        QProb.listSum ((factorialRectangle bounds).map (fun orders => f (order :: orders)))))) := by
  rw [factorialRectangle, List.map_flatMap]
  simpa only [List.map_map, Function.comp_def] using
    QProb.listSum_flatMap (List.range (bound + 1))
      (fun order => (factorialRectangle bounds).map (fun orders => f (order :: orders)))

private theorem rectangle_scale_product (a b : Nat) (p q : QProb) :
    QProb.Equiv (QProb.mul (QProb.scale a p) (QProb.scale b q)) (QProb.scale (a * b) (QProb.mul p q)) := by
  simp only [QProb.Equiv, QProb.mul, QProb.scale]
  ac_rfl

theorem multivariateMonomial_add_one_rectangle (args : List QProb) (counts bounds : List Nat)
    (dimension : counts.length = args.length) (bounded : CoordinateBounds counts bounds) :
    QProb.Equiv (multivariateMonomial (args.map (fun t => QProb.add t QProb.one)) counts)
      (QProb.listSum ((factorialRectangle bounds).map (fun orders =>
        QProb.scale (jointChoose orders counts) (multivariateMonomial args orders)))) := by
  induction args generalizing counts bounds with
  | nil => cases counts with
      | nil => cases bounds with
          | nil => exact QProb.equiv_refl _
          | cons bound bounds => exact False.elim bounded
      | cons count counts => simp only [List.length_cons, List.length_nil] at dimension; omega
  | cons arg args ih => cases counts with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons count counts => cases bounds with
          | nil => exact False.elim bounded
          | cons bound bounds =>
              simp only [List.map_cons, multivariateMonomial]
              refine QProb.equiv_trans (QProb.mul_congr
                (qpow_add_one_bounded count bound bounded.1 arg)
                (ih counts bounds (Nat.succ.inj dimension) bounded.2)) ?_
              have product := QProb.listSum_mul_listSum
                ((List.range (bound + 1)).map (fun order => QProb.scale (binom count order) (qpow arg order)))
                ((factorialRectangle bounds).map (fun orders => QProb.scale (jointChoose orders counts) (multivariateMonomial args orders)))
              simp only [List.map_map, Function.comp_def] at product
              refine QProb.equiv_trans product ?_
              refine QProb.equiv_trans (QProb.listSum_map_congr (List.range (bound + 1)) _ _ (fun order =>
                QProb.listSum_map_congr (factorialRectangle bounds) _ _ (fun orders => rectangle_scale_product _ _ _ _))) ?_
              exact QProb.equiv_symm (factorialRectangle_listSum bound bounds
                (fun orders => QProb.scale (jointChoose orders (count :: counts)) (multivariateMonomial (arg :: args) orders)))

/-- Mixed factorial expansion over the supplied coordinate-specific rectangle.
All bounds and dimensions are required only on positive-weight occurrences. -/
theorem multivariatePGF_factorial_expansion_rectangle (μ : Distro (List Nat)) (args : List QProb) (bounds : List Nat)
    (dimension : bounds.length = args.length) (support : μ.AlmostSurely (fun counts => CoordinateBounds counts bounds)) :
    QProb.Equiv (multivariatePGF μ (args.map (fun t => QProb.add t QProb.one)))
      (QProb.listSum ((factorialRectangle bounds).map (fun orders =>
        QProb.mul (multivariateFactorialCoefficient μ orders) (multivariateMonomial args orders)))) := by
  refine QProb.equiv_trans (μ.expectation_congr_positive
    (multivariateMonomial (args.map (fun t => QProb.add t QProb.one)))
    (fun counts => QProb.listSum ((factorialRectangle bounds).map (fun orders =>
      QProb.scale (jointChoose orders counts) (multivariateMonomial args orders))))
    (fun atom member weight => multivariateMonomial_add_one_rectangle args atom.1 bounds
      ((coordinateBounds_length _ _ (support atom member weight)).trans dimension) (support atom member weight))) ?_
  refine QProb.equiv_trans (μ.expectation_listSum (factorialRectangle bounds)
    (fun orders counts => QProb.scale (jointChoose orders counts) (multivariateMonomial args orders))) ?_
  apply QProb.listSum_map_congr
  intro orders
  refine QProb.equiv_trans (μ.expectation_congr _
    (fun counts => QProb.mul (multivariateMonomial args orders) (QProb.ofNat (jointChoose orders counts))) (fun counts => ?_)) ?_
  · simp only [QProb.Equiv, QProb.scale, QProb.mul, QProb.ofNat, Nat.mul_one]
    ac_rfl
  · exact QProb.equiv_trans (μ.expectation_scale _ _)
      (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) (μ.expectation_nat _))
        (QProb.equiv_trans (QProb.mul_comm _ _)
          (QProb.mul_congr (QProb.equiv_symm (multivariateFactorialCoefficient_choose μ orders)) (QProb.equiv_refl _))))

/-- The tensor inverse Pascal kernel with coordinate-specific padding. -/
theorem jointInverseBinomial_rectangle_kernel (counts target bounds : List Nat)
    (dimension : target.length = counts.length) (bounded : CoordinateBounds counts bounds) :
    SignedRatio.Equiv (SignedRatio.listSum ((factorialRectangle bounds).map (fun orders =>
      SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
        (QProb.ofNat (jointChoose orders counts)).toSignedRatio)))
      (if counts = target then SignedRatio.one else SignedRatio.zero) := by
  induction counts generalizing target bounds with
  | nil => cases target with
      | nil => cases bounds with
          | nil => rfl
          | cons bound bounds => exact False.elim bounded
      | cons value target => simp only [List.length_cons, List.length_nil] at dimension; omega
  | cons count counts ih => cases target with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons value target => cases bounds with
          | nil => exact False.elim bounded
          | cons bound bounds =>
              let head := fun order => SignedRatio.mul ⟨inverseBinomial order value, 1, Nat.zero_lt_one⟩
                (QProb.ofNat (binom count order)).toSignedRatio
              let tail := fun orders => SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
                (QProb.ofNat (jointChoose orders counts)).toSignedRatio
              let term := fun order orders => SignedRatio.mul
                ⟨jointInverseBinomial (order :: orders) (value :: target), 1, Nat.zero_lt_one⟩
                (QProb.ofNat (jointChoose (order :: orders) (count :: counts))).toSignedRatio
              have separated (order : Nat) (orders : List Nat) :
                  SignedRatio.Equiv (term order orders) (SignedRatio.mul (head order) (tail orders)) := by
                simp only [term, head, tail, jointInverseBinomial, jointChoose, SignedRatio.Equiv,
                  SignedRatio.mul, QProb.ofNat, QProb.toSignedRatio, Nat.mul_one,
                  Int.natCast_one, Int.natCast_mul, Int.mul_one]
                ac_rfl
              have tailKernel := ih target bounds (Nat.succ.inj dimension) bounded.2
              have rows (order : Nat) : SignedRatio.Equiv
                  (SignedRatio.listSum ((factorialRectangle bounds).map (term order)))
                  (SignedRatio.mul (head order) (if counts = target then SignedRatio.one else SignedRatio.zero)) := by
                refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ (separated order)) ?_
                refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
                  simpa only [List.map_map, Function.comp_def] using
                    (SignedRatio.mul_listSum (head order) ((factorialRectangle bounds).map tail)))) ?_
                exact SignedRatio.mul_congr (SignedRatio.equiv_refl _) tailKernel
              have grouped := SignedRatio.listSum_flatMap (List.range (bound + 1))
                (fun order => (factorialRectangle bounds).map (term order))
              refine SignedRatio.equiv_trans (by
                simpa only [List.length_cons, factorialRectangle, List.map_flatMap, List.map_map, Function.comp_def, term] using grouped) ?_
              refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ rows) ?_
              refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
                simpa only [List.map_map, Function.comp_def] using
                  (SignedRatio.listSum_mul ((List.range (bound + 1)).map head)
                    (if counts = target then SignedRatio.one else SignedRatio.zero)))) ?_
              refine SignedRatio.equiv_trans (SignedRatio.mul_congr
                (inverseBinomial_ratio_kernel count value bound bounded.1)
                (SignedRatio.equiv_refl _)) ?_
              by_cases first : count = value <;> by_cases rest : counts = target
              · simp only [first, rest, if_true]
                exact SignedRatio.one_mul _
              · simp only [List.cons.injEq, first, rest, true_and, false_and, if_false, if_true]
                exact SignedRatio.mul_zero _
              · simp only [List.cons.injEq, first, rest, false_and, if_false, if_true]
                exact SignedRatio.zero_mul _
              · simp only [List.cons.injEq, first, rest, false_and, if_false]
                exact SignedRatio.zero_mul _

/-- Explicit inversion enumerates only the supplied rectangle. -/
def inverseRectangleFactorialPMF (μ : Distro (List Nat)) (bounds target : List Nat) : SignedRatio :=
  SignedRatio.listSum ((factorialRectangle bounds).map (fun orders =>
    SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
      (multivariateFactorialCoefficient μ orders).toSignedRatio))

theorem Distro.pmf_rectangleFactorial_inversion (μ : Distro (List Nat)) (bounds target : List Nat)
    (dimension : target.length = bounds.length) (support : μ.AlmostSurely (fun counts => CoordinateBounds counts bounds)) :
    SignedRatio.Equiv (μ.pmf target).toSignedRatio (inverseRectangleFactorialPMF μ bounds target) := by
  let terms := fun orders counts => SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
    (QProb.ofNat (jointChoose orders counts)).toSignedRatio
  let kernel := fun counts => SignedRatio.listSum ((factorialRectangle bounds).map (fun orders => terms orders counts))
  let event := FiniteProbRecord.singletonEvent target
  have indicator : SignedRatio.Equiv (μ.rationalExpectation (fun counts =>
      if counts = target then SignedRatio.one else SignedRatio.zero)) (μ.pmf target).toSignedRatio := by
    refine SignedRatio.equiv_trans (μ.rationalExpectation_congr _
      (fun counts => (QProb.ofNat (if event counts then 1 else 0)).toSignedRatio) ?_) ?_
    · intro counts
      by_cases same : counts = target
      · simp only [event, FiniteProbRecord.singletonEvent, same, if_true, decide_true]
        exact SignedRatio.equiv_refl _
      · simp only [event, FiniteProbRecord.singletonEvent, same, if_false, decide_false, Bool.false_eq_true]
        exact SignedRatio.equiv_refl _
    · have result := μ.rationalExpectation_ofNat (fun counts => if event counts then 1 else 0)
      simpa only [Distro.expectNat, natIntegral_indicator, Distro.pmf, FiniteProbRecord.probVal] using result
  have singleton : SignedRatio.Equiv (μ.rationalExpectation kernel) (μ.pmf target).toSignedRatio := by
    refine SignedRatio.equiv_trans (μ.rationalExpectation_congr_positive kernel _ ?_) indicator
    intro atom member weight
    have data := support atom member weight
    exact jointInverseBinomial_rectangle_kernel atom.1 target bounds
      (dimension.trans (coordinateBounds_length _ _ data).symm) data
  have expansion := μ.rationalExpectation_listSum (factorialRectangle bounds) terms
  have moments := SignedRatio.listSum_map_congr (factorialRectangle bounds)
    (fun orders => μ.rationalExpectation (terms orders))
    (fun orders => SignedRatio.mul ⟨jointInverseBinomial orders target, 1, Nat.zero_lt_one⟩
      (multivariateFactorialCoefficient μ orders).toSignedRatio)
    (fun orders => SignedRatio.equiv_trans (μ.rationalExpectation_mul_left _ _)
      (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_trans (μ.rationalExpectation_ofNat _)
          (QProb.toSignedRatio_congr (QProb.equiv_symm (multivariateFactorialCoefficient_choose μ orders))))))
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm singleton) (SignedRatio.equiv_trans expansion moments)

private theorem ratio_sum_congr_on_mem (values : List A) (f g : A → SignedRatio)
    (same : ∀ value ∈ values, SignedRatio.Equiv (f value) (g value)) :
    SignedRatio.Equiv (SignedRatio.listSum (values.map f)) (SignedRatio.listSum (values.map g)) := by
  induction values with
  | nil => exact SignedRatio.equiv_refl _
  | cons value values ih =>
      exact SignedRatio.add_congr (same value (List.mem_cons_self ..))
        (ih (fun other member => same other (List.mem_cons_of_mem _ member)))

/-- Only moments in the actual rectangle are needed for reconstruction.
Wrong-shaped or out-of-bounds zero-weight atoms are retained on both sides. -/
theorem Distro.sameLaw_of_rectangleFactorialMoments (μ ν : Distro (List Nat)) (bounds : List Nat)
    (hμ : μ.AlmostSurely (fun counts => CoordinateBounds counts bounds))
    (hν : ν.AlmostSurely (fun counts => CoordinateBounds counts bounds))
    (same : ∀ orders, CoordinateBounds orders bounds →
      QProb.Equiv (jointFactorialMoment μ orders) (jointFactorialMoment ν orders)) : μ.SameLaw ν := by
  apply Distro.sameLaw_of_pmf
  intro target
  by_cases dimension : target.length = bounds.length
  · apply (QProb.toSignedRatio_equiv_iff _ _).mp
    refine SignedRatio.equiv_trans (μ.pmf_rectangleFactorial_inversion bounds target dimension hμ) ?_
    refine SignedRatio.equiv_trans ?_ (SignedRatio.equiv_symm (ν.pmf_rectangleFactorial_inversion bounds target dimension hν))
    apply ratio_sum_congr_on_mem
    intro orders member
    exact SignedRatio.mul_congr (SignedRatio.equiv_refl _)
      (QProb.toSignedRatio_congr (QProb.div_congr (same orders (factorialRectangle_mem bounds orders member))
        (QProb.equiv_refl _) _ _))
  · have left := μ.pmf_zero_of_almostSure_ne target (fun atom member weight equal =>
      dimension (equal ▸ coordinateBounds_length atom.1 bounds (hμ atom member weight)))
    have right := ν.pmf_zero_of_almostSure_ne target (fun atom member weight equal =>
      dimension (equal ▸ coordinateBounds_length atom.1 bounds (hν atom member weight)))
    exact QProb.equiv_trans left (QProb.equiv_symm right)

end Thesis.Probability.Distros
