import Thesis.Probability.ConstructiveRealFaceKKT

namespace Thesis.Examples.EntropySupportFace
open Probability Probability.Distros ConstructiveReal
open RationalLinear PartialMomentProblem

private def constraint : MomentInterval (Fin 3) := .exact (eventResponse (FiniteProbRecord.singletonEvent 2)) SignedRatio.zero
private def problem : PartialMomentProblem (Fin 3) :=
  ⟨List.finRange 3, 0, by decide, finRange_nodup 3, [constraint, constraint]⟩
private instance : NeZero problem.cells.length := ⟨Nat.ne_of_gt problem.nonempty⟩
private def vector : Fin 3 → SignedRatio := fun i => if i = 0 then ⟨1, 4, by decide⟩ else if i = 1 then ⟨3, 4, by decide⟩ else SignedRatio.zero
private def seed : problem.CompatibleLaw := problem.lawOfVector vector ⟨⟨by decide +kernel, by decide +kernel⟩, by
  intro row member
  change row ∈ [constraint, constraint] at member
  rcases List.mem_cons.mp member with rfl | later
  · constructor <;> decide +kernel
  · have same := List.mem_singleton.mp later
    cases same
    constructor <;> decide +kernel⟩

private def boundarySeed : problem.CompatibleLaw :=
  problem.lawOfVector (fun i : Fin 3 => if i = 0 then SignedRatio.one else SignedRatio.zero)
    ⟨⟨by decide +kernel, by decide +kernel⟩, by
      intro row member
      change row ∈ [constraint, constraint] at member
      rcases List.mem_cons.mp member with rfl | later
      · constructor <;> decide +kernel
      · have same := List.mem_singleton.mp later
        cases same
        constructor <;> decide +kernel⟩

private theorem coefficients : constraint.coefficients problem.cells problem.default = (fun i : Fin 3 => if i = 2 then 1 else 0) := by
  apply funext
  change ∀ i : Fin 3, constraint.coefficients problem.cells problem.default i = if i = 2 then 1 else 0
  decide +kernel

private theorem forced_zero (law : problem.RealCompatibleLaw) : Equiv (law.mass 2).value zero := by
  have bound := (law.moment_bounds constraint (List.mem_cons_self ..)).2
  rw [coefficients] at bound
  exact ⟨(le_congr (realDot_unit 3 2 _) (equiv_refl _)).mp bound, (law.mass 2).nonnegative⟩

private theorem hull_absent : ¬ 0 < (seed.supportHull.distro.pmf 2).num := by
  have vanished := forced_zero seed.supportHull.toReal
  have rational := (ofSignedRatio_equiv_iff _ _).mp vanished
  change ((seed.supportHull.distro.pmf 2).num : Int) * 1 = 0 * ((seed.supportHull.distro.pmf 2).den : Int) at rational
  simp only [Int.mul_one, Int.zero_mul] at rational
  omega

/-- A recorded null coordinate does not count as a positive support state. -/
example : ∃ weight, ((2 : Fin 3), weight) ∈ seed.distro.record.atoms := seed.retains 2 (List.mem_finRange 2)
example : (seed.distro.pmf 2).num = 0 := by decide +kernel

example : (2 : Fin 3) ∉ seed.supportFace.cells := by
  intro listed
  exact hull_absent (of_decide_eq_true (List.mem_filter.mp listed).2)

example : (0 : Fin 3) ∈ seed.supportFace.cells :=
  List.mem_filter.mpr ⟨List.mem_finRange 0, decide_eq_true
    (seed.supportHull_dominates seed 0 (List.mem_finRange 0) (by decide +kernel))⟩

/-- A boundary starting law omits a possible state. The automatic hull
recovers it, and gives exactly the same face as the positive-on-face seed. -/
example : (boundarySeed.distro.pmf 1).num = 0 := by decide +kernel
example : (1 : Fin 3) ∈ boundarySeed.supportFace.cells :=
  List.mem_filter.mpr ⟨List.mem_finRange 1, decide_eq_true
    (boundarySeed.supportHull_dominates seed 1 (List.mem_finRange 1) (by decide +kernel))⟩
example : boundarySeed.supportFaceCells = seed.supportFaceCells := boundarySeed.supportFaceCells_eq seed

/-- The solver's forced-zero certificate applies to every analytic feasible
law, not only the rational starting law or the constructed support witness. -/
example (law : problem.RealCompatibleLaw) : Equiv (law.mass 2).value zero := seed.supportHull_null law 2 hull_absent

example (law : problem.RealCompatibleLaw) : Equiv (law.toSupportFace seed).entropy law.entropy := law.toSupportFace_entropy seed
example (law : seed.supportFace.RealCompatibleLaw) : Equiv (law.fromSupportFace seed).entropy law.entropy := law.fromSupportFace_entropy seed

/-- Only the two declared exact expectation constraints and their reverse
rows reach the multiplier problem; no per-state simplex inequalities do. -/
example : seed.supportFace.analyticProblem.rows.length = 4 := rfl

/-- No positive feasible starting law on the original three-state grid is
assumed: the face and its positive witness are computed from `seed`. -/
example : seed.faceIdeal.Maximal := seed.faceIdeal_maximal

example (index : Fin seed.supportFace.cells.length) : Equiv (seed.faceSeed.maximize.mass index).value
    (mul (neg (seed.faceMultipliers.score index)).exp seed.faceMultipliers.partitionInverse) := seed.face_gibbsForm index

/-- Any finite coefficient proposal on the full grid fails at its forced
zero, even though finite fitted coefficients exist on the computed face. -/
example (gradient : Fin 3 → ConstructiveReal) (certificate : problem.analyticProblem.LagrangeCoefficients gradient)
    (law : problem.RealCompatibleLaw) :
    ¬ Equiv (law.mass 2).value (mul (neg (certificate.score 2)).exp certificate.partitionInverse) := by
  intro represented
  exact certificate.gibbs_not_zero 2 (equiv_trans (equiv_symm represented) (forced_zero law))

/-- A boundary seed still yields signed natural multipliers on its computed
face, including the duplicated exact constraints and their reversed rows. -/
example (row : Fin boundarySeed.supportFace.analyticProblem.rows.length) :
    LE zero (boundarySeed.faceKKTMultipliers.val.coefficient row) :=
  boundarySeed.faceKKTMultipliers.property.nonnegative row

example (row : Fin boundarySeed.supportFace.analyticProblem.rows.length) :
    Equiv (mul (boundarySeed.faceKKTMultipliers.val.coefficient row) (boundarySeed.faceSeed.maximize.rowSlack row)) zero :=
  boundarySeed.faceKKTMultipliers.property.complementary row

example (index : Fin boundarySeed.supportFace.cells.length) :
    let fitted := boundarySeed.faceKKTMultipliers.val
    Equiv (boundarySeed.faceSeed.maximize.mass index).value (mul (neg (fitted.score index)).exp fitted.partitionInverse) :=
  boundarySeed.faceKKT_gibbsForm index

end Thesis.Examples.EntropySupportFace
