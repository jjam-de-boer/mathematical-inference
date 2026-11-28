import Thesis.Causality.FiniteSymmetry
import Thesis.Probability.Distros.PartialMomentConditionalBounds
import Thesis.Probability.Distros.RationalCovarianceAlgebra

/-!
# Response-table orbit masses for a verified stabilizer

The action is supplied on the complete response-table carrier. A finite
test retains precisely the elements that fix each measurement response
and each requested event pointwise. The conditioner and the joint numerator
event are registered for a conditional query. This subgroup can be smaller than
one that permutes equally measured rows as a family.

Within a retained orbit all registered responses agree. Moving its total
mass to a representative preserves every constraint and query used here.
The inverse sends a representative law to the original shared-response
class. Uniform averaging over the retained action also preserves those
measurements and events. These operations use arbitrary rational laws on
the full carrier, as in the shared latent response model class.
-/

namespace Thesis.Causality.ResponseOrbitReduction

open Probability Probability.Distros FiniteSymmetry

/-- The full carrier is required for the finite tests and the orbit search.
Events are the declared objectives, including any evidence events. -/
structure Reduction (G : Group) (full : PartialMomentProblem A) where
  action : Action G A
  complete : ∀ table, table ∈ full.cells
  events : List (Event A)

variable {G : Group} {full : PartialMomentProblem A}

def Reduction.Fixes (reduction : Reduction G full) (g : G.Carrier) : Prop :=
  (∀ row ∈ full.intervals, ∀ table ∈ full.cells,
    row.response (reduction.action.act g table) = row.response table) ∧
  (∀ event ∈ reduction.events, ∀ table ∈ full.cells,
    event (reduction.action.act g table) = event table)

instance (reduction : Reduction G full) (g : G.Carrier) : Decidable (reduction.Fixes g) := by
  unfold Reduction.Fixes
  infer_instance

theorem Reduction.one_fixes (reduction : Reduction G full) : reduction.Fixes G.one :=
  ⟨fun row _ table _ => congrArg row.response (reduction.action.one_act table),
    fun event _ table _ => congrArg event (reduction.action.one_act table)⟩

theorem Reduction.mul_fixes (reduction : Reduction G full) {g h : G.Carrier}
    (gFixes : reduction.Fixes g) (hFixes : reduction.Fixes h) : reduction.Fixes (G.mul g h) := by
  constructor
  · intro row listed table member
    rw [reduction.action.mul_act, gFixes.1 row listed _ (reduction.complete _),
      hFixes.1 row listed _ member]
  · intro event listed table member
    rw [reduction.action.mul_act, gFixes.2 event listed _ (reduction.complete _),
      hFixes.2 event listed _ member]

theorem Reduction.inv_fixes (reduction : Reduction G full) {g : G.Carrier}
    (fixed : reduction.Fixes g) : reduction.Fixes (G.inv g) := by
  constructor
  · intro row listed table _
    have same := fixed.1 row listed (reduction.action.act (G.inv g) table) (reduction.complete _)
    simpa only [reduction.action.act_inv] using same.symm
  · intro event listed table _
    have same := fixed.2 event listed (reduction.action.act (G.inv g) table) (reduction.complete _)
    simpa only [reduction.action.act_inv] using same.symm

def Reduction.elements (reduction : Reduction G full) : List {g : G.Carrier // reduction.Fixes g} :=
  (deduplicate G.elements).filterMap fun g =>
    if fixed : reduction.Fixes g then some ⟨g, fixed⟩ else none

theorem Reduction.elements_complete (reduction : Reduction G full)
    (g : {g : G.Carrier // reduction.Fixes g}) : g ∈ reduction.elements := by
  apply List.mem_filterMap.mpr
  refine ⟨g.val, (mem_deduplicate _ _).mpr (G.complete _), ?_⟩
  simp only [dif_pos g.property]

private def Reduction.uniform (reduction : Reduction G full) :
    Distro {g : G.Carrier // reduction.Fixes g} :=
  let elements := reduction.elements
  ⟨{ atoms := elements.map (fun g => (g, 1))
     den := elements.length
     den_pos := List.length_pos_of_mem (reduction.elements_complete ⟨G.one, reduction.one_fixes⟩)
     total_mass := by
       change FiniteProbRecord.totalMass (elements.map (fun g => (g, 1))) = elements.length
       generalize elements = groupList
       induction groupList with
       | nil => rfl
       | cons _ _ ih => simp only [List.map_cons, FiniteProbRecord.totalMass, ih, List.length_cons,
           Nat.add_comm] }⟩

/-- Uniform averaging is a finite rational draw of an action, independent
of the original table, followed by evaluation of that action. -/
def Reduction.average (reduction : Reduction G full) (law : Distro A) : Distro A :=
  (law.product reduction.uniform).map fun pair => reduction.action.act pair.2.val pair.1

theorem Reduction.average_expectation (reduction : Reduction G full) (law : Distro A)
    (value : A → SignedRatio)
    (fixed : ∀ g : {g : G.Carrier // reduction.Fixes g}, ∀ table,
      value (reduction.action.act g.val table) = value table) :
    SignedRatio.Equiv ((reduction.average law).rationalExpectation value)
      (law.rationalExpectation value) := by
  unfold Reduction.average
  rw [Distro.rationalExpectation_map]
  exact SignedRatio.equiv_trans ((law.product reduction.uniform).rationalExpectation_congr _ _
      (fun pair => by rw [fixed]; exact SignedRatio.equiv_refl _))
    (law.rationalExpectation_product_left reduction.uniform value)

theorem Reduction.average_moments (reduction : Reduction G full) (law : full.CompatibleLaw)
    (row : MomentInterval A) (listed : row ∈ full.intervals) :
    row.LawHolds (reduction.average law.distro) := by
  have unchanged := reduction.average_expectation law.distro (integerResponse row.response)
    (fun g table => congrArg (fun i : Int => (⟨i, 1, Nat.zero_lt_one⟩ : SignedRatio))
      (g.property.1 row listed table (reduction.complete _)))
  have holds := law.moments row listed
  exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) unchanged).mpr holds.1,
    (SignedRatio.le_congr unchanged (SignedRatio.equiv_refl _)).mpr holds.2⟩

theorem Reduction.average_event (reduction : Reduction G full) (law : Distro A)
    (event : Event A) (registered : event ∈ reduction.events) :
    QProb.Equiv ((reduction.average law).record.probVal event) (law.record.probVal event) := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  exact SignedRatio.equiv_trans
    (SignedRatio.equiv_symm (eventResponse_expectation (reduction.average law) event))
    (SignedRatio.equiv_trans (reduction.average_expectation law (integerResponse (eventResponse event))
      (fun g table => by
        unfold integerResponse eventResponse
        rw [g.property.2 event registered table (reduction.complete table)]))
      (eventResponse_expectation law event))

def Reduction.SameOrbit (reduction : Reduction G full) (left right : A) : Prop :=
  ∃ g ∈ G.elements, reduction.Fixes g ∧ reduction.action.act g left = right

instance [DecidableEq A] (reduction : Reduction G full) (left right : A) :
    Decidable (reduction.SameOrbit left right) := by
  unfold Reduction.SameOrbit
  infer_instance

theorem Reduction.SameOrbit.refl (reduction : Reduction G full) (table : A) :
    reduction.SameOrbit table table :=
  ⟨G.one, G.complete _, reduction.one_fixes, reduction.action.one_act _⟩

theorem Reduction.SameOrbit.symm {reduction : Reduction G full} {x y : A}
    (same : reduction.SameOrbit x y) : reduction.SameOrbit y x := by
  obtain ⟨g, _, fixed, moves⟩ := same
  exact ⟨G.inv g, G.complete _, reduction.inv_fixes fixed, by rw [← moves, reduction.action.inv_act]⟩

theorem Reduction.SameOrbit.trans {reduction : Reduction G full} {x y z : A}
    (first : reduction.SameOrbit x y) (second : reduction.SameOrbit y z) :
    reduction.SameOrbit x z := by
  obtain ⟨g, _, firstFixed, firstMoves⟩ := first
  obtain ⟨h, _, secondFixed, secondMoves⟩ := second
  exact ⟨G.mul h g, G.complete _, reduction.mul_fixes secondFixed firstFixed,
    by rw [reduction.action.mul_act, firstMoves, secondMoves]⟩

variable [DecidableEq A]

/-- The first table in the declared order belonging to the orbit. The
identity element makes the fallback unreachable. -/
def Reduction.representative (reduction : Reduction G full) (table : A) : A :=
  (full.cells.find? (fun other => decide (reduction.SameOrbit table other))).getD table

theorem Reduction.representative_in_orbit (reduction : Reduction G full) (table : A) :
    reduction.SameOrbit table (reduction.representative table) := by
  unfold Reduction.representative
  generalize found : full.cells.find? (fun other => decide (reduction.SameOrbit table other)) = result
  cases result with
  | none => exact Reduction.SameOrbit.refl reduction table
  | some other =>
    have matchFound : decide (reduction.SameOrbit table other) = true :=
      List.find?_some (p := fun candidate => decide (reduction.SameOrbit table candidate)) found
    exact of_decide_eq_true matchFound

theorem Reduction.representative_eq_of_sameOrbit (reduction : Reduction G full) {left right : A}
    (same : reduction.SameOrbit left right) : reduction.representative left = reduction.representative right := by
  have equivalent : (fun other => decide (reduction.SameOrbit left other)) =
      (fun other => decide (reduction.SameOrbit right other)) := by
    funext other
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact ⟨fun next => same.symm.trans next, fun next => same.trans next⟩
  have existsRep : ∃ other, full.cells.find? (fun other => decide (reduction.SameOrbit right other)) = some other := by
    cases found : full.cells.find? (fun other => decide (reduction.SameOrbit right other)) with
    | none => exact False.elim (List.find?_eq_none.mp found right (reduction.complete right)
        (decide_eq_true (Reduction.SameOrbit.refl reduction right)))
    | some other => exact ⟨other, rfl⟩
  obtain ⟨other, found⟩ := existsRep
  simp only [Reduction.representative, equivalent, found, Option.getD_some]

theorem Reduction.rep_idempotent (reduction : Reduction G full) (table : A) :
    reduction.representative (reduction.representative table) = reduction.representative table :=
  (reduction.representative_eq_of_sameOrbit (reduction.representative_in_orbit table)).symm

def Reduction.cells (reduction : Reduction G full) : List A :=
  full.cells.filter fun table => decide (reduction.representative table = table)

theorem Reduction.representative_mem (reduction : Reduction G full) (table : A) :
    reduction.representative table ∈ reduction.cells :=
  List.mem_filter.mpr ⟨reduction.complete _, decide_eq_true (reduction.rep_idempotent table)⟩

/-- Only one unknown mass per orbit is sent to the linear solver. The
finite checking and representative selection still enumerate the full
carrier. -/
def Reduction.problem (reduction : Reduction G full) : PartialMomentProblem A where
  cells := reduction.cells
  default := reduction.representative full.default
  nonempty := List.length_pos_of_mem (reduction.representative_mem full.default)
  distinct := List.Sublist.nodup List.filter_sublist full.distinct
  intervals := full.intervals

theorem Reduction.representative_event (reduction : Reduction G full)
    (event : Event A) (listed : event ∈ reduction.events) (table : A) :
    event (reduction.representative table) = event table := by
  obtain ⟨g, _, good, moves⟩ := reduction.representative_in_orbit table
  rw [← moves]
  exact good.2 event listed table (reduction.complete _)

theorem Reduction.representative_response (reduction : Reduction G full)
    (row : MomentInterval A) (listed : row ∈ full.intervals) (table : A) :
    row.response (reduction.representative table) = row.response table := by
  obtain ⟨g, _, good, moves⟩ := reduction.representative_in_orbit table
  rw [← moves]
  exact good.1 row listed table (reduction.complete _)

theorem Reduction.mapExpectation (reduction : Reduction G full) (law : Distro A)
    (value : A → SignedRatio) (fixed : ∀ table, value (reduction.representative table) = value table) :
    SignedRatio.Equiv ((law.map reduction.representative).rationalExpectation value)
      (law.rationalExpectation value) := by
  rw [Distro.rationalExpectation_map]
  exact law.rationalExpectation_congr _ _ (fun table => by rw [fixed]; exact SignedRatio.equiv_refl _)

theorem Reduction.mapEvent (reduction : Reduction G full) (law : Distro A) (event : Event A)
    (fixed : ∀ table, event (reduction.representative table) = event table) :
    QProb.Equiv ((law.map reduction.representative).record.probVal event) (law.record.probVal event) :=
  QProb.equiv_trans (law.map_probVal _ _) (law.record.probVal_congr _ _ fixed)

omit [DecidableEq A] in
private def zeroAtoms (cells : List A) : List (A × Nat) := cells.map fun cell => (cell, 0)

omit [DecidableEq A] in
private theorem zeroAtoms_mass (cells : List A) : FiniteProbRecord.totalMass (zeroAtoms cells) = 0 := by
  induction cells with
  | nil => rfl
  | cons _ _ ih =>
    simp only [zeroAtoms, List.map_cons, FiniteProbRecord.totalMass, Nat.zero_add]
    exact ih

omit [DecidableEq A] in
private theorem zeroAtoms_event (cells : List A) (event : Event A) :
    FiniteProbRecord.eventMass (zeroAtoms cells) event = 0 := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    change (if event cell then 0 + FiniteProbRecord.eventMass (zeroAtoms rest) event
      else FiniteProbRecord.eventMass (zeroAtoms rest) event) = 0
    rw [ih]
    split <;> rfl

/-- The partial-moment interface retains a zero occurrence for missing
alphabet cells as bookkeeping. This padding changes no event mass. -/
private def pad (law : Distro A) (cells : List A) : Distro A :=
  ⟨{ law.record with
      atoms := law.record.atoms ++ zeroAtoms cells
      total_mass := by
        rw [FiniteProbRecord.totalMass_append, zeroAtoms_mass, Nat.add_zero, law.record.total_mass] }⟩

private theorem pad_sameLaw (law : Distro A) (cells : List A) : (pad law cells).SameLaw law := by
  intro event
  unfold pad FiniteProbRecord.probVal QProb.Equiv
  simp only [FiniteProbRecord.eventMass_append, zeroAtoms_event, Nat.add_zero]

private theorem pad_retains (law : Distro A) (cells : List A) (cell : A) (listed : cell ∈ cells) :
    ∃ weight, (cell, weight) ∈ (pad law cells).record.atoms :=
  ⟨0, List.mem_append_right _ (List.mem_map_of_mem listed)⟩

private theorem pad_support {law : Distro A} {cells : List A}
    (support : law.AlmostSurely (fun cell => cell ∈ cells)) :
    (pad law cells).AlmostSurely (fun cell => cell ∈ cells) := by
  intro atom listed positive
  rcases List.mem_append.mp listed with old | extra
  · exact support atom old positive
  · obtain ⟨cell, member, same⟩ := List.mem_map.mp extra
    subst atom
    exact member

omit [DecidableEq A] in
private theorem holds_of_sameLaw {left right : Distro A} (same : left.SameLaw right)
    {row : MomentInterval A} (holds : row.LawHolds right) : row.LawHolds left := by
  have unchanged := same.rationalExpectation (integerResponse row.response)
  exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) unchanged).mpr holds.1,
    (SignedRatio.le_congr unchanged (SignedRatio.equiv_refl _)).mpr holds.2⟩

theorem Reduction.compressed_support (reduction : Reduction G full) (law : Distro A) :
    (law.map reduction.representative).AlmostSurely (fun table => table ∈ reduction.problem.cells) := by
  intro atom listed _
  obtain ⟨previous, _, same⟩ := List.mem_map.mp listed
  subst atom
  exact reduction.representative_mem previous.1

theorem Reduction.compressed_moments (reduction : Reduction G full) (law : Distro A)
    (moments : ∀ row ∈ full.intervals, row.LawHolds law) :
    ∀ row ∈ reduction.problem.intervals, row.LawHolds (law.map reduction.representative) := by
  intro row listed
  have unchanged := reduction.mapExpectation law (integerResponse row.response)
    (fun table => congrArg (fun i : Int => (⟨i, 1, Nat.zero_lt_one⟩ : SignedRatio))
      (reduction.representative_response row listed table))
  have holds := moments row listed
  exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) unchanged).mpr holds.1,
    (SignedRatio.le_congr unchanged (SignedRatio.equiv_refl _)).mpr holds.2⟩

/-- Compress by adding the mass of all tables assigned to one orbit. -/
def Reduction.compress (reduction : Reduction G full) (law : Distro A)
    (moments : ∀ row ∈ full.intervals, row.LawHolds law) : reduction.problem.CompatibleLaw where
  distro := pad (law.map reduction.representative) reduction.cells
  support := pad_support (reduction.compressed_support law)
  moments row listed := holds_of_sameLaw (pad_sameLaw _ _)
    (reduction.compressed_moments law moments row listed)
  retains := pad_retains _ _

/-- Each representative is itself a real response table. A law supported
on representatives embeds directly as a fine response law. -/
def Reduction.restore (reduction : Reduction G full) (law : reduction.problem.CompatibleLaw) :
    full.CompatibleLaw where
  distro := pad law.distro full.cells
  support := pad_support (fun atom _ _ => reduction.complete atom.1)
  moments row listed := holds_of_sameLaw (pad_sameLaw _ _) (law.moments row listed)
  retains := pad_retains _ _

theorem Reduction.infeasible_not_compatible (reduction : Reduction G full)
    (certificate : RationalLinear.Infeasibility reduction.problem.cells.length reduction.problem.rows) :
    ¬ ∃ μ : Distro A, ∀ row ∈ full.intervals, row.LawHolds μ := by
  rintro ⟨law, moments⟩
  exact reduction.problem.refutation_not_realizable certificate
    ⟨law.map reduction.representative, reduction.compressed_support law, reduction.compressed_moments law moments⟩

/-- The reduced and full problems have the same sharp range for every
registered event. Restoring a reduced endpoint keeps an attaining law. -/
def Reduction.restoreBounds (reduction : Reduction G full) (event : Event A)
    (registered : event ∈ reduction.events) (sharp : reduction.problem.SharpBounds (eventResponse event)) :
    full.SharpBounds (eventResponse event) where
  lower := sharp.lower
  upper := sharp.upper
  lowerLaw := reduction.restore sharp.lowerLaw
  upperLaw := reduction.restore sharp.upperLaw
  lower_attained := SignedRatio.equiv_trans ((pad_sameLaw _ _).rationalExpectation _) sharp.lower_attained
  upper_attained := SignedRatio.equiv_trans ((pad_sameLaw _ _).rationalExpectation _) sharp.upper_attained
  bounds := by
    intro law _ moments
    let compressed := law.map reduction.representative
    have bounded := sharp.bounds compressed (reduction.compressed_support law)
      (reduction.compressed_moments law moments)
    have unchanged := reduction.mapExpectation law (integerResponse (eventResponse event))
      (fun table => by
        unfold integerResponse eventResponse
        rw [reduction.representative_event event registered table])
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) unchanged).mp bounded.1,
      (SignedRatio.le_congr unchanged (SignedRatio.equiv_refl _)).mp bounded.2⟩

def Reduction.compressConditional (reduction : Reduction G full) (evidence : Event A)
    (registered : evidence ∈ reduction.events) (law : full.ConditionalLaw evidence) :
    reduction.problem.ConditionalLaw evidence where
  distro := law.distro.map reduction.representative
  support := reduction.compressed_support law.distro
  moments := reduction.compressed_moments law.distro law.moments
  positive := (QProb.equiv_num_pos_iff (reduction.mapEvent law.distro evidence
    (reduction.representative_event evidence registered))).mpr law.positive

def Reduction.restoreConditional (reduction : Reduction G full) (evidence : Event A)
    (law : reduction.problem.ConditionalLaw evidence) : full.ConditionalLaw evidence :=
  ⟨law.distro, fun atom _ _ => reduction.complete atom.1, law.moments, law.positive⟩

theorem Reduction.compressConditional_value (reduction : Reduction G full) (evidence event : Event A)
    (hasEvidence : evidence ∈ reduction.events)
    (hasNumerator : (fun table => evidence table && event table) ∈ reduction.events)
    (law : full.ConditionalLaw evidence) :
    QProb.Equiv ((reduction.compressConditional evidence hasEvidence law).value event) (law.value event) := by
  let compressed := reduction.compressConditional evidence hasEvidence law
  have denominator := reduction.mapEvent law.distro evidence
    (reduction.representative_event evidence hasEvidence)
  have numerator := reduction.mapEvent law.distro (fun table => evidence table && event table)
    (reduction.representative_event _ hasNumerator)
  exact QProb.equiv_trans (compressed.distro.record.conditionOn_probVal evidence event compressed.positive)
    (QProb.equiv_trans (QProb.div_congr numerator denominator compressed.positive law.positive)
      (QProb.equiv_symm (law.distro.record.conditionOn_probVal evidence event law.positive)))

/-- Compression preserves both the joint numerator and evidence mass.
Supported endpoints and every attainable intermediate value lift. -/
def Reduction.restoreConditionalRange (reduction : Reduction G full) (evidence event : Event A)
    (hasEvidence : evidence ∈ reduction.events)
    (hasNumerator : (fun table => evidence table && event table) ∈ reduction.events)
    (sharp : reduction.problem.ConditionalRange evidence event) : full.ConditionalRange evidence event where
  lower := reduction.restoreConditional evidence sharp.lower
  upper := reduction.restoreConditional evidence sharp.upper
  bounds := by
    intro source
    have bounded := sharp.bounds (reduction.compressConditional evidence hasEvidence source)
    have unchanged := reduction.compressConditional_value evidence event hasEvidence hasNumerator source
    exact ⟨QProb.le_congr (QProb.equiv_refl _) unchanged bounded.1,
      QProb.le_congr unchanged (QProb.equiv_refl _) bounded.2⟩
  pointBetween value lower upper :=
    let witness := sharp.pointBetween value lower upper
    ⟨reduction.restoreConditional evidence witness.val, witness.property⟩

end Thesis.Causality.ResponseOrbitReduction
