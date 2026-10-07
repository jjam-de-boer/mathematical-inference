import Thesis.CausalTransport.ValueRefinementCounterexample

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryLabelRefinement

open Probability ObservedValueRefinement

/-!
# A binary bow countermodel with genuinely positive three-valued labels

The declared graph is `X → Y` and `X ↔ Y`, with three supplied labels at
both nodes.  The binary core emits only zero and one.  A fair shared bit
sets `X`; a private two-to-one coin sets `Y` observationally.  In the large
model `Y = shared XOR X XOR private`, while in the other model it is simply
the private bit.  Thus their complete observed laws agree, but under
`do(X = 0)` the probability of the bit-one outcome is `1/2` versus `1/3`.

The core is positive on its decoded assignments, not on the full alphabet:
label two is impossible.  The general label sweep supplies that missing
support without changing the bit, graph, query, or causal gap.  Each node's
two bit-zero candidate labels have independent private inputs, so repeated
pivots occur in this small regression too.  No hedge-specific background
carrier, route, sink condition, or latent recoding is used by the refinement.
-/

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => by decide
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by intro parent child selected; have := of_decide_eq_true selected; omega

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right)
  bidirected_symmetric := by intro left right selected; exact decide_eq_true (Ne.symm (of_decide_eq_true selected))
  bidirected_irreflexive := fun node => decide_eq_false (fun different => different rfl)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

def shared : Fin 2 := ⟨0, by decide⟩
def privateRoot : Fin 2 := ⟨1, by decide⟩

def latent : LatentExtension signature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> decide
  valueDecidableEq := fun _ => inferInstance
  incident := fun root child => if root.val = 0 then true else decide (child.val = 1)

def fair : FiniteProbRecord Bool := ⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩
def biased : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩
def factors (root : Fin latent.count) : FiniteProbRecord Bool := if root.val = 0 then fair else biased

def encode (value : Bool) : Fin 3 := if value then ⟨1, by decide⟩ else ⟨0, by decide⟩

private theorem edge_to_second (child : Fin signature.count) (notFirst : child.val ≠ 0) :
    signature.directed x child = true := by
  have bound : child.val < 2 := child.isLt
  have second : child.val = 1 := by omega
  -- Fix the numeral's type before elaborating the Boolean decision.  An
  -- unconstrained `0 = 0` can otherwise synthesize a classical decider;
  -- the declared edge is the constructive conjunction of two Nat equalities.
  change decide ((0 : Nat) = 0 ∧ child.val = 1) = true
  exact decide_eq_true ⟨rfl, second⟩

private theorem private_incident_at_second (child : Fin signature.count) (notFirst : child.val ≠ 0) :
    latent.incident privateRoot child = true := by
  have bound : child.val < 2 := child.isLt
  change (if (1 : Nat) = 0 then true else decide (child.val = 1)) = true
  simp only [Nat.one_ne_zero, if_false]
  apply decide_eq_true
  omega

/-- The private coin is read only at `Y`; the shared source may feed both
nodes.  Mechanisms have no access to any other observed or latent input. -/
def mechanism (large : Bool) (child : Fin signature.count) (parents : signature.ParentValues child)
    (inputs : latent.Inputs child) : signature.Value child :=
  if selected : child.val = 0 then encode (inputs shared (by simp only [latent, shared, if_true]))
  else encode (Bool.xor
    (if large then Bool.xor (inputs shared (by simp only [latent, shared, if_true]))
      (bit rich x (parents x (edge_to_second child selected)))
    else false)
    (inputs privateRoot (private_incident_at_second child selected)))

def core (large : Bool) : ExactModel signature where
  latent := latent
  factor := factors
  prior := FiniteProduct.record 2 (fun _ => Bool) factors
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool) factors
  mechanism := mechanism large

theorem core_compatible (large : Bool) : Compatible (core large) graph := by
  constructor
  · intro root first second third _one _two _three
    by_cases same : first = second
    · exact Or.inl same
    · have either : first = third ∨ second = third := by
        apply Or.imp (Fin.ext) (Fin.ext)
        have firstBound : first.val < 2 := first.isLt
        have secondBound : second.val < 2 := second.isLt
        have thirdBound : third.val < 2 := third.isLt
        have different : first.val ≠ second.val := fun equal => same (Fin.ext equal)
        omega
      cases either with
      | inl equal => exact Or.inr (Or.inl equal)
      | inr equal => exact Or.inr (Or.inr equal)
  · intro first second
    change latent.projectedBidirected first second = graph.bidirected first second
    have finite : first = x ∨ first = y := by
      apply Or.imp Fin.ext Fin.ext
      have bound : first.val < 2 := first.isLt
      change first.val = 0 ∨ first.val = 1
      omega
    have finiteSecond : second = x ∨ second = y := by
      apply Or.imp Fin.ext Fin.ext
      have bound : second.val < 2 := second.isLt
      change second.val = 0 ∨ second.val = 1
      omega
    rcases finite with same | same <;> subst first <;>
      rcases finiteSecond with same | same <;> subst second <;> decide +kernel

theorem core_respects (large : Bool) : RespectsParentBits (core large) rich := by
  intro child first second inputs agree
  change mechanism large child first inputs = mechanism large child second inputs
  unfold mechanism
  split
  · rfl
  · rw [agree x]

/-- Whole observed atom lists agree.  This finite check includes the actual
dependent-product prior and mechanisms, not just a selected parity event. -/
theorem core_observationally_equivalent : ObservationallyEquivalent (core false) (core true) := by
  have same : (core false).observationalDist.atoms = (core true).observationalDist.atoms := by decide +kernel
  intro event
  change FiniteProbRecord.eventMass (core false).observationalDist.atoms event * 6 =
    FiniteProbRecord.eventMass (core true).observationalDist.atoms event * 6
  rw [same]

private theorem two_bits_positive (large first second : Bool) :
    (core large).observationalDist.EventPositive
      (fun sample => decide (bit rich x (sample x) = first) && decide (bit rich y (sample y) = second)) := by
  cases large <;> cases first <;> cases second <;> decide +kernel

theorem core_bitsPositive (large : Bool) : BitsPositive (core large) rich := by
  intro target
  have compared := (core large).observationalDist.probVal_congr
    (fun sample => decide (bits rich sample = bits rich target))
    (fun sample => decide (bit rich x (sample x) = bit rich x (target x)) &&
      decide (bit rich y (sample y) = bit rich y (target y))) (by
        intro sample
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro selected
          have equal := of_decide_eq_true selected
          exact Bool.and_eq_true_iff.mpr
            ⟨decide_eq_true (congrFun equal x), decide_eq_true (congrFun equal y)⟩
        · intro selected
          have parts := Bool.and_eq_true_iff.mp selected
          apply decide_eq_true
          funext node
          have finite : node = x ∨ node = y := by
            apply Or.imp Fin.ext Fin.ext
            have bound : node.val < 2 := node.isLt
            change node.val = 0 ∨ node.val = 1
            omega
          rcases finite with same | same
          · subst node; exact of_decide_eq_true parts.1
          · subst node; exact of_decide_eq_true parts.2)
  exact (QProb.equiv_num_pos_iff compared).mpr
    (two_bits_positive large (bit rich x (target x)) (bit rich y (target y)))

def query : InterventionalQuery signature where
  intervention := (HardIntervention.empty signature).set x (rich.first x)
  outcomeNodes := NodeSet.singleton y
  action_outcome_disjoint := by
    intro node selected
    have action : node = x := by
      by_cases same : node = x
      · exact same
      · simp only [HardIntervention.targets, HardIntervention.set, dif_neg same,
          HardIntervention.empty, FiniteLatentSCM.noIntervention, Option.isSome] at selected
        cases selected
    subst node
    decide +kernel
  event := fun sample => bit rich y (sample y)
  event_local := by intro first second agree; exact congrArg (bit rich y) (agree y (by decide +kernel))

theorem core_gap : Not (QProb.Equiv (query.value (core true)) (query.value (core false))) := by decide +kernel

/-- The four installed candidates really use repeated pivots. -/
theorem candidates : (allSteps rich).map Step.pivot = [x, x, y, y] := by decide +kernel

/-- The old third label has no support, so the general positivity theorem
does materially more than preserve an already positive full-label model. -/
theorem core_third_label_impossible (large : Bool) :
    ((core large).observationalValue (fun sample => decide (sample x = (⟨2, by decide⟩ : Fin 3)))).num = 0 := by
  cases large <;> decide +kernel

/-- The support sweep does not attenuate the causal gap: its decoded
outcome probabilities are still exactly one half and one third. -/
theorem refined_query_probability (large : Bool) :
    QProb.Equiv (query.value (refine rich (core large)))
      (if large then (⟨1, 2, by decide⟩ : QProb) else ⟨1, 3, by decide⟩) :=
  QProb.equiv_trans (refine_queryValue rich (core large) (core_respects large) query
    (fun sample => sample y) (fun _sample => rfl)) (by cases large <;> decide +kernel)

noncomputable def counterexample : CounterexampleIn (GraphModelClass.positive graph) query.kernelQuery :=
  positiveCounterexampleOfBitEvent rich query (core true) (core false)
    (core_compatible true) (core_compatible false) (core_respects true) (core_respects false)
    (core_bitsPositive true) (core_bitsPositive false)
    (fun event => QProb.equiv_symm (core_observationally_equivalent event))
    (fun sample => sample y) (fun _sample => rfl) core_gap

/-- Full-alphabet positivity, full observational equality, and separation
are all fields of one actual original-query countermodel pair. -/
theorem refined_not_identifiable :
    Not ((GraphModelClass.positive graph).identifiable query.kernelQuery) :=
  counterexample.not_identifiable

/-! ## The adapter also accepts an ordinary Boolean-valued SCM -/

/-- Reuse the stated two source factors, now on the Boolean observed
signature.  This regression deliberately supplies a genuine binary model,
not a caller-proved parent-label or decoded-support invariant. -/
def binaryCore (large : Bool) : ExactModel signature.binary where
  latent := {
    count := 2
    Value := fun _ => Bool
    valueEnumeration := fun _ => [false, true]
    value_complete := by intro _ value; cases value <;> decide
    valueDecidableEq := fun _ => inferInstance
    incident := latent.incident }
  factor := factors
  prior := FiniteProduct.record 2 (fun _ => Bool) factors
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool) factors
  mechanism := fun child parents inputs => bit (S := signature) rich child
    (mechanism large child (fun parent _edge => BinaryEncoding.value rich parent (parents parent _edge)) inputs)

theorem binaryCore_compatible (large : Bool) : Compatible (binaryCore large) graph.binary :=
  core_compatible large

private def binaryAssignment (first second : Bool) : signature.binary.Assignment :=
  fun node => if node.val = 0 then first else second

theorem binaryCore_positive (large : Bool) : ObservationallyPositive (binaryCore large) := by
  have atoms (first second : Bool) :
      (binaryCore large).observationalDist.EventPositive
        (FiniteProbRecord.singletonEvent (binaryAssignment first second)) := by
    cases large <;> cases first <;> cases second <;> decide +kernel
  intro target
  have encoded : target = binaryAssignment (target x) (target y) := by
    funext node
    have finite : node = x ∨ node = y := by
      apply Or.imp Fin.ext Fin.ext
      have bound : node.val < 2 := node.isLt
      change node.val = 0 ∨ node.val = 1
      omega
    rcases finite with same | same <;> subst node <;> rfl
  rw [encoded]
  exact atoms (target x) (target y)

theorem binaryCore_observationally_equivalent :
    ObservationallyEquivalent (binaryCore true) (binaryCore false) := by
  have same : (binaryCore true).observationalDist.atoms = (binaryCore false).observationalDist.atoms := by decide +kernel
  intro event
  change FiniteProbRecord.eventMass (binaryCore true).observationalDist.atoms event * 6 =
    FiniteProbRecord.eventMass (binaryCore false).observationalDist.atoms event * 6
  rw [same]

private def queryBits : Event signature.binary.Assignment := fun sample => sample y

theorem binaryCore_gap : Not (QProb.Equiv
    ((binaryQuery rich query queryBits (fun _sample => rfl)).value (binaryCore true))
    ((binaryQuery rich query queryBits (fun _sample => rfl)).value (binaryCore false))) := by decide +kernel

/-- Ordinary binary positivity and the binary causal gap suffice.  The
constructor itself proves the encoding invariants and full-label positivity. -/
noncomputable def binaryCounterexample :
    CounterexampleIn (GraphModelClass.positive graph) query.kernelQuery :=
  positiveCounterexampleOfBinaryEvent rich query (binaryCore true) (binaryCore false)
    (binaryCore_compatible true) (binaryCore_compatible false)
    (binaryCore_positive true) (binaryCore_positive false) binaryCore_observationally_equivalent
    queryBits (fun _sample => rfl) binaryCore_gap

end BinaryLabelRefinement
end Examples
end Causality
end Thesis
