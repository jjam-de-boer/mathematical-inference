import Thesis.Causality.LatentRationalCPT
import Thesis.CausalTransport.ValueRefinementCounterexample
import Thesis.Examples.HedgeObstructionLikelihood
import Thesis.Examples.HedgeCarrierRouteObstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeObstructionModel

open Probability
open HedgeObstructionLikelihood

/-!
# Functional realization of the outer-reentry table pair

The likelihood regression supplies rational rows on the seven-node graph
`A,R,U,V,B,Q,Y`.  Here those rows become actual structural mechanisms with
independent finite latent sources.  The four shared coordinates retain
exactly the pairs `A,R`, `R,Q`, `A,B`, and `V,B`; a separate private response
table at each node supplies its conditional randomness.

Local configurations contain only declared observed parents and incident
shared sources.  In particular, `B` may read `V,J,K`, but cannot see `H,L`
or any other observed coordinate.  The configuration counts below are the
small local products, not an enumeration of whole observed assignments.

Likelihoods must be related to evaluation of these same SCMs before the
algebraic table equality can imply observational equivalence.  Private
response spaces are integrated by the general rational-table theorem;
concrete checks concern only the 72 shared assignments and 128 observations.
This construction addresses the carrier family's outer-reentry obstruction,
not the still-open universal hedge-countermodel theorem.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev originalSignature := HedgeCarrierRouteObstruction.signature
abbrev signature := originalSignature.binary
abbrev graph := HedgeCarrierRouteObstruction.graph.binary

/-- The original topological indices are retained throughout. -/
def a : Fin signature.count := ⟨0, by decide⟩
def r : Fin signature.count := ⟨1, by decide⟩
def u : Fin signature.count := ⟨2, by decide⟩
def v : Fin signature.count := ⟨3, by decide⟩
def b : Fin signature.count := ⟨4, by decide⟩
def q : Fin signature.count := ⟨5, by decide⟩
def y : Fin signature.count := ⟨6, by decide⟩

def observationAssignment (sample : Observation) : signature.Assignment :=
  fun node => match node.val with
    | 0 => sample.a
    | 1 => sample.r
    | 2 => sample.u
    | 3 => sample.v
    | 4 => sample.b
    | 5 => sample.q
    | _ => sample.y

def observationOfAssignment (sample : signature.Assignment) : Observation :=
  ⟨sample a, sample r, sample u, sample v, sample b, sample q, sample y⟩

theorem observationOfAssignment_assignment (sample : Observation) :
    observationOfAssignment (observationAssignment sample) = sample := by
  cases sample
  rfl

theorem observationAssignment_ofAssignment (sample : signature.Assignment) :
    observationAssignment (observationOfAssignment sample) = sample := by
  funext node
  rcases node with ⟨index, bound⟩
  change index < 7 at bound
  match index with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | _ + 7 => omega

def sampleEnumeration : List signature.Assignment := observations.map observationAssignment

theorem sampleEnumeration_complete (sample : signature.Assignment) :
    sample ∈ sampleEnumeration :=
  List.mem_map.mpr ⟨observationOfAssignment sample,
    observations_complete _, observationAssignment_ofAssignment sample⟩

theorem sampleEnumeration_nodup : sampleEnumeration.Nodup := by
  apply observations_nodup.map
  intro first second different same
  apply different
  simpa only [observationOfAssignment_assignment] using congrArg observationOfAssignment same

/-! ## The four genuinely independent pair sources -/

abbrev sharedValue (root : Fin 4) : Type := match root.val with
  | 0 => Bool
  | 1 => Bool
  | 2 => Fin 6
  | _ => Fin 3

def sharedEnumeration (root : Fin 4) : List (sharedValue root) := match root with
  | ⟨0, _⟩ => [false, true]
  | ⟨1, _⟩ => [false, true]
  | ⟨2, _⟩ => List.finRange 6
  | ⟨_ + 3, _⟩ => List.finRange 3

theorem sharedEnumeration_complete (root : Fin 4) (value : sharedValue root) :
    value ∈ sharedEnumeration root := by
  rcases root with ⟨index, bound⟩
  match index with
  | 0 => change value ∈ ([false, true] : List Bool); cases value <;> simp
  | 1 => change value ∈ ([false, true] : List Bool); cases value <;> simp
  | 2 => exact List.mem_finRange value
  | _ + 3 => exact List.mem_finRange value

def sharedDecidableEq (root : Fin 4) : DecidableEq (sharedValue root) := match root with
  | ⟨0, _⟩ => (inferInstance : DecidableEq Bool)
  | ⟨1, _⟩ => (inferInstance : DecidableEq Bool)
  | ⟨2, _⟩ => (inferInstance : DecidableEq (Fin 6))
  | ⟨_ + 3, _⟩ => (inferInstance : DecidableEq (Fin 3))

/-- Each source has exactly its advertised two children.  These incidence
tests are Nat decisions, never proposition-level excluded middle. -/
def sharedIncident (root : Fin 4) (child : Fin signature.count) : Bool :=
  match root.val with
  | 0 => decide (child.val = 0 ∨ child.val = 1)
  | 1 => decide (child.val = 1 ∨ child.val = 5)
  | 2 => decide (child.val = 0 ∨ child.val = 4)
  | _ => decide (child.val = 3 ∨ child.val = 4)

abbrev shared : LatentExtension signature where
  count := 4
  Value := sharedValue
  valueEnumeration := sharedEnumeration
  value_complete := sharedEnumeration_complete
  valueDecidableEq := sharedDecidableEq
  incident := sharedIncident

def hiddenAssignment (unit : Hidden) : shared.Assignment := fun root => match root with
  | ⟨0, _⟩ => unit.h
  | ⟨1, _⟩ => unit.l
  | ⟨2, _⟩ => unit.j
  | ⟨_ + 3, _⟩ => unit.k

def hiddenOfAssignment (unit : shared.Assignment) : Hidden :=
  ⟨unit ⟨0, by decide⟩, unit ⟨1, by decide⟩, unit ⟨2, by decide⟩, unit ⟨3, by decide⟩⟩

theorem hiddenOfAssignment_assignment (unit : Hidden) :
    hiddenOfAssignment (hiddenAssignment unit) = unit := by cases unit; rfl

theorem hiddenAssignment_ofAssignment (unit : shared.Assignment) :
    hiddenAssignment (hiddenOfAssignment unit) = unit := by
  funext root
  rcases root with ⟨index, bound⟩
  change index < 4 at bound
  match index with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 =>
    -- Eliminate the impossible index through `False` explicitly.  Asking
    -- an arithmetic tactic to prove this dependent value equality directly
    -- can insert classical contradiction when it cannot infer its decider.
    exact False.elim (by omega)

def hiddenEnumeration : List shared.Assignment := hiddenAssignments.map hiddenAssignment

theorem hiddenEnumeration_complete (unit : shared.Assignment) : unit ∈ hiddenEnumeration :=
  List.mem_map.mpr ⟨hiddenOfAssignment unit, hiddenAssignments_complete _,
    hiddenAssignment_ofAssignment unit⟩

theorem hiddenEnumeration_nodup : hiddenEnumeration.Nodup := by
  apply hiddenAssignments_nodup.map
  intro first second different same
  apply different
  simpa only [hiddenOfAssignment_assignment] using congrArg hiddenOfAssignment same

/-- The two weights really form a normalized Bernoulli record.  Keeping the
row denominator literal makes the later table-to-likelihood bridge exact. -/
def bernoulli (den numerator : Nat) (positive : 0 < den) (bounded : numerator ≤ den) :
    FiniteProbRecord Bool where
  atoms := [(false, den - numerator), (true, numerator)]
  den := den
  den_pos := positive
  total_mass := by
    change (den - numerator) + (numerator + 0) = den
    omega

def fair : FiniteProbRecord Bool := bernoulli 2 1 (by decide) (by decide)
def uniformSix : FiniteProbRecord (Fin 6) :=
  ⟨(List.finRange 6).map (fun value => (value, 1)), 6, by decide, by decide⟩
def uniformThree : FiniteProbRecord (Fin 3) :=
  ⟨(List.finRange 3).map (fun value => (value, 1)), 3, by decide, by decide⟩

def sharedFactor (root : Fin shared.count) : FiniteProbRecord (shared.Value root) :=
  match root with
  | ⟨0, _⟩ => fair
  | ⟨1, _⟩ => fair
  | ⟨2, _⟩ => uniformSix
  | ⟨_ + 3, _⟩ => uniformThree

theorem shared_canonical : shared.CanonicalSemiMarkovian := by
  intro root first second third one two three
  change sharedIncident root first = true at one
  change sharedIncident root second = true at two
  change sharedIncident root third = true at three
  unfold sharedIncident at one two three
  split at one <;> simp_all only <;>
    have one' := of_decide_eq_true one <;>
    have two' := of_decide_eq_true two <;>
    have three' := of_decide_eq_true three <;>
    apply Or.imp Fin.ext (Or.imp Fin.ext Fin.ext) <;> omega

private theorem shared_projected_check :
    finAll 7 (fun first => finAll 7 (fun second =>
      decide (shared.projectedBidirected first second = graph.bidirected first second))) = true :=
  by decide +kernel

theorem shared_projected (first second : Fin signature.count) :
    shared.projectedBidirected first second = graph.bidirected first second :=
  of_decide_eq_true ((finAll_eq_true_iff _).mp
    ((finAll_eq_true_iff _).mp shared_projected_check first) second)

/-! ## Small local contexts, with access checked by the graph types -/

private def parentBit (child parent : Fin signature.count)
    (parents : signature.ParentValues child) : Bool :=
  if edge : signature.directed parent child = true then parents parent edge else false

private def parentContext (child : Fin signature.count)
    (parents : signature.ParentValues child) : Observation :=
  ⟨parentBit child a parents, parentBit child r parents, parentBit child u parents,
    parentBit child v parents, parentBit child b parents, parentBit child q parents,
    parentBit child y parents⟩

/-- Unavailable shared inputs get harmless defaults in this intermediate
record.  Only the incident-input branch can read an actual latent value;
the local encoder subsequently ignores every irrelevant record field. -/
private def hiddenContext (child : Fin signature.count) (inputs : shared.Inputs child) : Hidden :=
  ⟨if selected : shared.incident ⟨0, by decide⟩ child = true then inputs _ selected else false,
   if selected : shared.incident ⟨1, by decide⟩ child = true then inputs _ selected else false,
   if selected : shared.incident ⟨2, by decide⟩ child = true then inputs _ selected else ⟨0, by decide⟩,
   if selected : shared.incident ⟨3, by decide⟩ child = true then inputs _ selected else ⟨0, by decide⟩⟩

def boolNat (value : Bool) : Nat := if value then 1 else 0
private theorem boolNat_lt (value : Bool) : boolNat value < 2 := by cases value <;> decide

/-- The counts are respectively `H×J`, `H×L`, `R`, `A×U×K`,
`V×J×K`, `B×L`, and `V×Q`.  No globally visible context is used. -/
def configCount (child : Fin signature.count) : Nat := match child.val with
  | 0 => 12
  | 1 => 4
  | 2 => 2
  | 3 => 12
  | 4 => 36
  | _ => 4

private def contextIndex (child : Fin signature.count) (sample : Observation) (unit : Hidden) : Nat :=
  match child.val with
  | 0 => 6 * boolNat unit.h + unit.j.val
  | 1 => 2 * boolNat unit.h + boolNat unit.l
  | 2 => boolNat sample.r
  | 3 => 6 * boolNat sample.a + 3 * boolNat sample.u + unit.k.val
  | 4 => 18 * boolNat sample.v + 3 * unit.j.val + unit.k.val
  | 5 => 2 * boolNat sample.b + boolNat unit.l
  | _ => 2 * boolNat sample.v + boolNat sample.q

private theorem contextIndex_lt (child : Fin signature.count) (sample : Observation) (unit : Hidden) :
    contextIndex child sample unit < configCount child := by
  have := boolNat_lt unit.h
  have := boolNat_lt unit.l
  have := boolNat_lt sample.a
  have := boolNat_lt sample.r
  have := boolNat_lt sample.u
  have := boolNat_lt sample.v
  have := boolNat_lt sample.b
  have := boolNat_lt sample.q
  have := unit.j.isLt
  have := unit.k.isLt
  rcases child with ⟨index, bound⟩
  match index with
  | 0 => simp only [contextIndex, configCount]; omega
  | 1 => simp only [contextIndex, configCount]; omega
  | 2 => simp only [contextIndex, configCount]; omega
  | 3 => simp only [contextIndex, configCount]; omega
  | 4 => simp only [contextIndex, configCount]; omega
  | 5 => simp only [contextIndex, configCount]; omega
  | _ + 6 => simp only [contextIndex, configCount]; omega

def encode (child : Fin signature.count) (parents : signature.ParentValues child)
    (inputs : shared.Inputs child) : Fin (configCount child) :=
  ⟨contextIndex child (parentContext child parents) (hiddenContext child inputs), contextIndex_lt _ _ _⟩

def rowDenominator (child : Fin signature.count) : Nat := match child.val with
  | 0 => 1536
  | 1 => 1024
  | _ => 6

/-- Decode only the small configuration index.  The tables are literally
the likelihood regression's rows, with ordinary mixed-radix decoding. -/
def rowTrueWeight (perturbed : Bool) (child : Fin signature.count) (index : Nat) : Nat :=
  match child.val with
  | 0 => aTrueWeight ⟨decide (index / 6 = 1), false, ⟨index % 6, Nat.mod_lt _ (by decide)⟩, ⟨0, by decide⟩⟩
  | 1 => rTrueWeight perturbed ⟨decide (index / 2 = 1), decide (index % 2 = 1), ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  | 2 => if index = 1 then 5 else 1
  | 3 => if index / 6 = 1 then 3 else
      if (index / 3) % 2 = 1 then match index % 3 with
        | 0 => 4
        | 1 => 1
        | _ => 3
      else match index % 3 with
        | 0 => 1
        | 1 => 4
        | _ => 5
  | 4 => if (index / 3) % 6 = (if index / 18 = 1 then 3 else 0) + index % 3 then 2 else 3
  | 5 => if index / 2 = 1 then 3 else if index % 2 = 1 then 5 else 1
  | _ => if Bool.xor (decide (index / 2 = 1)) (decide (index % 2 = 1)) then 5 else 1

private theorem row_bounds (perturbed : Bool) (child : Fin signature.count) (index : Nat) :
    0 < rowTrueWeight perturbed child index ∧ rowTrueWeight perturbed child index < rowDenominator child := by
  rcases child with ⟨node, bound⟩
  match node with
  | 0 =>
    simp only [rowTrueWeight, rowDenominator]
    unfold aTrueWeight
    split
    · decide
    · split <;> decide
  | 1 =>
    simp only [rowTrueWeight, rowDenominator]
    unfold rTrueWeight
    split
    · split <;> split <;> decide
    · decide
  | 2 => simp only [rowTrueWeight, rowDenominator]; split <;> decide
  | 3 =>
    simp only [rowTrueWeight, rowDenominator]
    split
    · decide
    · split <;> split <;> decide
  | 4 => simp only [rowTrueWeight, rowDenominator]; split <;> split <;> decide
  | 5 =>
    simp only [rowTrueWeight, rowDenominator]
    split
    · decide
    · split <;> decide
  | _ + 6 => simp only [rowTrueWeight, rowDenominator]; split <;> decide

def row (perturbed : Bool) (child : Fin signature.count) (configuration : Fin (configCount child)) :
    FiniteProbRecord Bool :=
  bernoulli (rowDenominator child) (rowTrueWeight perturbed child configuration.val)
    (Nat.lt_trans (row_bounds perturbed child configuration.val).1
      (row_bounds perturbed child configuration.val).2)
    (Nat.le_of_lt (row_bounds perturbed child configuration.val).2)

def tables (perturbed : Bool) : FiniteLatentRationalCPT signature where
  shared := shared
  sharedFactor := sharedFactor
  configCount := configCount
  encode := encode
  row := row perturbed

/-- These are actual SCMs, with the product prior and private response
mechanisms of the generic realization—not records merely labelled as SCMs. -/
def model (perturbed : Bool) : ExactModel signature := (tables perturbed).toSCM

theorem model_compatible (perturbed : Bool) : Compatible (model perturbed) graph :=
  (tables perturbed).toSCM_compatible graph shared_canonical shared_projected

/-- Reindex the generic likelihood by the named four-source tuples.  The
dependent shared assignment type is reduced explicitly at this boundary;
the complete enumeration and all weights remain unchanged. -/
theorem likelihoodWith_hiddenEnumeration (perturbed : Bool)
    (target : Fin signature.count → Option Bool) (sample : signature.Assignment) :
    (tables perturbed).likelihoodWith hiddenEnumeration target sample =
      QProb.listSum (hiddenAssignments.map fun unit =>
        FiniteProduct.qProduct (tables perturbed).extension.count
          ((tables perturbed).sliceFactors target (hiddenAssignment unit) sample)) := by
  unfold FiniteLatentRationalCPT.likelihoodWith hiddenEnumeration
  exact congrArg QProb.listSum (List.map_map (f := hiddenAssignment))

/-! ## Literal table products are likelihoods of these same models -/

private def factualSlice (perturbed : Bool) (sample : Observation) (unit : Hidden) : QProb :=
  FiniteProduct.qProduct (tables perturbed).extension.count
    ((tables perturbed).sliceFactors (FiniteLatentSCM.noIntervention signature)
      (hiddenAssignment unit) (observationAssignment sample))

private def factualWeight (perturbed : Bool) (sample : Observation) (unit : Hidden) : QProb :=
  ⟨(rowWeights perturbed sample unit).foldl Nat.mul 1, observationalDenominator, by decide⟩

/-- This finite check bridges the actual local-input encoder and actual row
records to the original seven table factors.  It does not evaluate a huge
private response prior: that integration is already a general theorem.
Every observed assignment, shared tuple, and member of the pair is checked. -/
private theorem factual_slice_checks (perturbed : Bool) (sample : Observation) :
    hiddenAssignments.all (fun unit => decide
      (QProb.Equiv (factualSlice perturbed sample unit) (factualWeight perturbed sample unit))) = true := by
  -- Keep each kernel reduction bounded to 72 shared tuples.  A single
  -- nested check of all observations creates a needlessly large reduction
  -- cache; structural Boolean cases establish precisely the same coverage.
  rcases sample with ⟨sa, sr, su, sv, sb, sq, sy⟩
  cases perturbed <;> cases sa <;> cases sr <;> cases su <;>
    cases sv <;> cases sb <;> cases sq <;> cases sy <;> decide +kernel

private theorem factualSlice_equiv (perturbed : Bool) (sample : Observation) (unit : Hidden) :
    QProb.Equiv (factualSlice perturbed sample unit) (factualWeight perturbed sample unit) := by
  exact of_decide_eq_true (List.all_eq_true.mp (factual_slice_checks perturbed sample)
    unit (hiddenAssignments_complete unit))

private theorem factualLikelihood_equiv (perturbed : Bool) (sample : Observation) :
    QProb.Equiv
      ((tables perturbed).likelihoodWith hiddenEnumeration
        (FiniteLatentSCM.noIntervention signature) (observationAssignment sample))
      ⟨observationalNumerator perturbed sample, observationalDenominator, by decide⟩ := by
  rw [likelihoodWith_hiddenEnumeration]
  refine QProb.equiv_trans
    (QProb.listSum_map_congr hiddenAssignments _ _ (factualSlice_equiv perturbed sample)) ?_
  simpa only [List.map_map, factualWeight, observationalNumerator] using
    (QProb.listSum_mk_same_den observationalDenominator (by decide)
      (hiddenAssignments.map fun unit => (rowWeights perturbed sample unit).foldl Nat.mul 1))

/-- The exact full-assignment likelihood is now a theorem of the SCM's
factual evaluation, rather than a property of a separate probability record. -/
theorem model_observational_singleton (perturbed : Bool) (sample : signature.Assignment) :
    QProb.Equiv ((model perturbed).observationalValue (FiniteProbRecord.singletonEvent sample))
      ⟨observationalNumerator perturbed (observationOfAssignment sample),
        observationalDenominator, by decide⟩ := by
  have semantics := (tables perturbed).toSCM_observational_singleton_likelihoodWith
    hiddenEnumeration hiddenEnumeration_nodup hiddenEnumeration_complete sample
  have likelihood := factualLikelihood_equiv perturbed (observationOfAssignment sample)
  rw [observationAssignment_ofAssignment] at likelihood
  exact QProb.equiv_trans semantics likelihood

/-- Strict support belongs to the realized model on every Boolean observed
assignment.  It is transported from its exact singleton likelihood. -/
theorem model_positive (perturbed : Bool) : ObservationallyPositive (model perturbed) := by
  intro sample
  exact (QProb.equiv_num_pos_iff (model_observational_singleton perturbed sample)).mpr
    (observationalNumerator_positive perturbed (observationOfAssignment sample))

/-- Equality of all 128 realized singleton likelihoods determines the
entire observed law, including events that couple arbitrary coordinates. -/
theorem models_observationally_equivalent : ObservationallyEquivalent (model false) (model true) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons
    (model false).observationalDist (model true).observationalDist sampleEnumeration
    sampleEnumeration_nodup sampleEnumeration_complete
  intro sample
  have left := model_observational_singleton false sample
  have right := model_observational_singleton true sample
  have scalar : QProb.Equiv
      ⟨observationalNumerator false (observationOfAssignment sample), observationalDenominator, by decide⟩
      ⟨observationalNumerator true (observationOfAssignment sample), observationalDenominator, by decide⟩ := by
    unfold QProb.Equiv
    rw [observationalNumerator_equal]
  exact QProb.equiv_trans left (QProb.equiv_trans scalar (QProb.equiv_symm right))

end HedgeObstructionModel
end Examples
end Causality
end Thesis
