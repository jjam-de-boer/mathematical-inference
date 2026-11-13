import Thesis.CausalTransport.Hedge.ReadoutGeometry
import Thesis.Causality.PairRoot
import Thesis.Probability.ConstructivePermutation

namespace Thesis
namespace Causality

open Probability

/-!
# Finite hedge models, pair roots and parity readouts

The finite latent extensions, pair-root assignments, Boolean incidence and
routing-flow constructions below are shared mathematics, not properties of a
particular identification program. Their explicit finite enumerations retain
all observed labels, independent latent inputs and explicit readiness
conditions.

This module depends on graph readout geometry, pair-root semantics and finite
constructive permutations. It does not import legacy recursion, failure-stack
unpackers or certificate heuristics. Current channel constructions can therefore
use parity identities without inheriting the historical engine development.

These models alone do not prove published completeness. Some constructions
below have explicit local readiness premises; the unrestricted original-query
channel counterexample and positive-class theorem are assembled separately in
`HedgeChannelCounterexample` and `HedgeChannelCompleteness`.
-/

/-! ## Positive-class countermodels from hedge data -/

/-- Pair-root count plus one private enumeration index per observed node. -/
def hedgeLatentCount (G : ObservedGraph S) : Nat :=
  pairRootCount G + S.count

/-- Pair-root indices sit in the prefix of the hedge latent range. -/
def hedgePairRoot (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    Fin (hedgeLatentCount G) :=
  Fin.castAdd S.count root

/-- Private root of an observed node, placed after every pair-root. -/
def hedgePrivateRoot (G : ObservedGraph S) (child : Fin S.count) :
    Fin (hedgeLatentCount G) :=
  Fin.natAdd (pairRootCount G) child

/--
Incidence for the hedge skeleton: pair-roots keep their two endpoints,
and the private root of `child` is incident only to `child`.
-/
def hedgeIncident (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) (child : Fin S.count) : Bool :=
  if h : root.val < pairRootCount G then
    pairRootIncident G ⟨root.val, h⟩ child
  else
    decide (root.val - pairRootCount G = child.val)

theorem hedgePrivateRoot_not_pair (G : ObservedGraph S)
    (child : Fin S.count) :
    ¬ (hedgePrivateRoot G child).val < pairRootCount G := by
  simp [hedgePrivateRoot]

/-- Observed child attached to a non-pair (private) hedge root. -/
def hedgeChildOfPrivate (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G))
    (h : ¬ root.val < pairRootCount G) : Fin S.count :=
  ⟨root.val - pairRootCount G,
    Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) (by
      have hlt : root.val < hedgeLatentCount G := root.isLt
      exact Nat.lt_of_lt_of_eq hlt (by simp [hedgeLatentCount]))⟩

theorem hedgeChildOfPrivate_eq_child (G : ObservedGraph S)
    (child : Fin S.count)
    (h : ¬ (hedgePrivateRoot G child).val < pairRootCount G) :
    hedgeChildOfPrivate G (hedgePrivateRoot G child) h = child := by
  apply Fin.ext
  simp [hedgeChildOfPrivate, hedgePrivateRoot]

theorem hedgeChildOfPrivate_privateRoot (G : ObservedGraph S)
    (child : Fin S.count) :
    hedgeChildOfPrivate G (hedgePrivateRoot G child)
      (hedgePrivateRoot_not_pair G child) = child :=
  hedgeChildOfPrivate_eq_child G child _

/-- The private-root embedding is a section of `hedgeChildOfPrivate`. -/
theorem hedgePrivateRoot_of_childOfPrivate (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G))
    (h : ¬ root.val < pairRootCount G) :
    hedgePrivateRoot G (hedgeChildOfPrivate G root h) = root := by
  apply Fin.ext
  unfold hedgePrivateRoot hedgeChildOfPrivate
  exact Nat.add_sub_of_le (Nat.le_of_not_lt h)

/-- Cardinality of the observed enumeration at one node. -/
def hedgePrivateCard (S : ObservedSignature) (child : Fin S.count) : Nat :=
  (S.valueEnumeration child).length

theorem hedgePrivateCard_pos (S : ObservedSignature) (child : Fin S.count) :
    0 < hedgePrivateCard S child := by
  have hmem := S.value_complete child (S.defaultValue child)
  exact List.length_pos_of_mem hmem

/--
Pair-roots remain Boolean.  Private roots are indices into the observed
enumeration, so they inhabit `Type` together with `Bool` and still hit every
value of an arbitrarily large finite type.
-/
def hedgeLatentValue (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) : Type :=
  if h : root.val < pairRootCount G then Bool
  else Fin (hedgePrivateCard S (hedgeChildOfPrivate G root h))

instance (G : ObservedGraph S) (root : Fin (hedgeLatentCount G)) :
    DecidableEq (hedgeLatentValue G root) := by
  unfold hedgeLatentValue
  split <;> infer_instance

theorem hedgeLatentValue_eq_bool (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G))
    (h : root.val < pairRootCount G) :
    hedgeLatentValue G root = Bool := by
  unfold hedgeLatentValue
  rw [dif_pos h]

theorem hedgeLatentValue_eq_fin (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G))
    (h : ¬ root.val < pairRootCount G) :
    hedgeLatentValue G root =
      Fin (hedgePrivateCard S (hedgeChildOfPrivate G root h)) := by
  unfold hedgeLatentValue
  rw [dif_neg h]

theorem mem_cast_list {α β : Type} (h : α = β) (xs : List α) (x : β) :
    x ∈ cast (congrArg List h) xs ↔ cast h.symm x ∈ xs := by
  cases h
  rfl

/-- `Nodup` is invariant under transporting a list along an equality of
element types.  The hedge enumerations are defined by such a transport. -/
theorem nodup_cast_list {α β : Type} (h : α = β) (xs : List α) :
    (cast (congrArg List h) xs).Nodup ↔ xs.Nodup := by
  cases h
  rfl

/-- Mapping by an injective function preserves `Nodup`. -/
theorem nodup_map_of_injective {α β : Type} {f : α → β} {l : List α}
    (hinj : ∀ a b, f a = f b → a = b) (hn : l.Nodup) :
    (l.map f).Nodup :=
  List.Pairwise.map f (fun a b (hne : a ≠ b) heq => hne (hinj a b heq)) hn

/-- `List.finRange` lists each `Fin n` once. -/
theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero =>
      simp [List.finRange]
  | succ n ih =>
      rw [List.finRange_succ]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨i, _, heq⟩
        exact (Fin.succ_ne_zero i) heq
      · exact nodup_map_of_injective
          (fun a b h => Fin.ext (Nat.succ.inj (congrArg Fin.val h))) ih

/-- Enumerated atoms of one hedge latent, transported onto `hedgeLatentValue`. -/
def hedgeLatentEnum (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) : List (hedgeLatentValue G root) :=
  if h : root.val < pairRootCount G then
    cast (congrArg List (hedgeLatentValue_eq_bool G root h).symm) [false, true]
  else
    cast (congrArg List (hedgeLatentValue_eq_fin G root h).symm)
      (List.finRange (hedgePrivateCard S (hedgeChildOfPrivate G root h)))

theorem hedgeLatentEnum_complete (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) (value : hedgeLatentValue G root) :
    value ∈ hedgeLatentEnum G root := by
  if h : root.val < pairRootCount G then
    have hEq := hedgeLatentValue_eq_bool G root h
    have bit : Bool := cast hEq value
    unfold hedgeLatentEnum
    rw [dif_pos h]
    refine (mem_cast_list hEq.symm [false, true] value).mpr ?_
    cases bit with
    | false => simp
    | true => simp
  else
    have hEq := hedgeLatentValue_eq_fin G root h
    unfold hedgeLatentEnum
    rw [dif_neg h]
    refine (mem_cast_list hEq.symm
        (List.finRange (hedgePrivateCard S (hedgeChildOfPrivate G root h)))
        value).mpr ?_
    exact List.mem_finRange (cast hEq value)

/-- Pair-root enumerations are `[false, true]`; private enumerations are
`finRange` of the child's observed cardinality.  Both are duplicate-free,
so singleton masses on the ones-weighted atoms equal one. -/
theorem hedgeLatentEnum_nodup (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) :
    (hedgeLatentEnum G root).Nodup := by
  if h : root.val < pairRootCount G then
    unfold hedgeLatentEnum
    rw [dif_pos h]
    exact (nodup_cast_list (hedgeLatentValue_eq_bool G root h).symm
      [false, true]).mpr (by simp)
  else
    unfold hedgeLatentEnum
    rw [dif_neg h]
    exact (nodup_cast_list (hedgeLatentValue_eq_fin G root h).symm
        (List.finRange (hedgePrivateCard S (hedgeChildOfPrivate G root h)))).mpr
      (nodup_finRange _)

def hedgeLatentDefault (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) : hedgeLatentValue G root :=
  if h : root.val < pairRootCount G then
    cast (hedgeLatentValue_eq_bool G root h).symm false
  else
    cast (hedgeLatentValue_eq_fin G root h).symm
      ⟨0, hedgePrivateCard_pos S (hedgeChildOfPrivate G root h)⟩

theorem hedgeLatentEnum_nonempty (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) :
    0 < (hedgeLatentEnum G root).length :=
  List.length_pos_of_mem
    (hedgeLatentEnum_complete G root (hedgeLatentDefault G root))

theorem totalMass_ones {Ω : Type _} (values : List Ω) :
    FiniteProbRecord.totalMass (values.map (fun v => (v, 1))) = values.length := by
  induction values with
  | nil =>
      rfl
  | cons _ vs ih =>
      simp [FiniteProbRecord.totalMass]
      omega

def hedgeLatentFactor (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) :
    FiniteProbRecord (hedgeLatentValue G root) where
  atoms := (hedgeLatentEnum G root).map (fun value => (value, 1))
  den := (hedgeLatentEnum G root).length
  den_pos := hedgeLatentEnum_nonempty G root
  total_mass := totalMass_ones (hedgeLatentEnum G root)

/--
Pair-root expansion with a private enumeration index at every observed node.
Projected bidirected edges are exactly those of `G`; the extra roots are
Markovian and do not add confounding.
-/
def hedgeLatentExtension (G : ObservedGraph S) : LatentExtension S where
  count := hedgeLatentCount G
  Value := hedgeLatentValue G
  valueEnumeration := hedgeLatentEnum G
  value_complete := hedgeLatentEnum_complete G
  valueDecidableEq := fun root => by
    unfold hedgeLatentValue
    split <;> infer_instance
  incident := hedgeIncident G

theorem hedgePairRoot_val (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    (hedgePairRoot G root).val = root.val :=
  rfl

theorem hedgeIncident_pair (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) (child : Fin S.count) :
    hedgeIncident G (hedgePairRoot G root) child =
      pairRootIncident G root child := by
  unfold hedgeIncident
  rw [dif_pos (by exact root.isLt)]
  congr 1

/-- Private roots never join two distinct observed nodes. -/
theorem hedgeIncident_private_both
    (G : ObservedGraph S) (root : Fin (hedgeLatentCount G))
    {i j : Fin S.count} (hne : i ≠ j)
    (hlt : ¬ root.val < pairRootCount G) :
    (hedgeIncident G root i && hedgeIncident G root j) = false := by
  unfold hedgeIncident
  rw [dif_neg hlt, dif_neg hlt]
  cases hi : decide (root.val - pairRootCount G = i.val) with
  | false =>
      simp
  | true =>
      cases hj : decide (root.val - pairRootCount G = j.val) with
      | false =>
          simp
      | true =>
          have hi' : root.val - pairRootCount G = i.val :=
            of_decide_eq_true hi
          have hj' : root.val - pairRootCount G = j.val :=
            of_decide_eq_true hj
          have hij : i = j := Fin.ext (hi'.symm.trans hj')
          exact (hne hij).elim

theorem hedgeLatentExtension_projected (G : ObservedGraph S)
    (i j : Fin S.count) :
    (hedgeLatentExtension G).projectedBidirected i j =
      G.bidirected i j := by
  cases hbeq : Nat.beq i.val j.val with
  | true =>
      have hij : i = j := Fin.ext (Nat.eq_of_beq_eq_true hbeq)
      cases hij
      simp [LatentExtension.projectedBidirected, hedgeLatentExtension,
        G.bidirected_irreflexive]
  | false =>
      have hne : i ≠ j := by
        intro equal
        cases equal
        simp at hbeq
      have hpair := pairRootExtension_projected G i j
      cases hedge : G.bidirected i j with
      | true =>
          have hany :
              finAny (pairRootCount G)
                (fun latent =>
                  pairRootIncident G latent i &&
                    pairRootIncident G latent j) = true := by
            simpa [LatentExtension.projectedBidirected, pairRootExtension,
              hbeq, hedge] using hpair
          rcases (finAny_eq_true_iff _).mp hany with ⟨latent, hinc⟩
          have hlift :
              (hedgeIncident G (hedgePairRoot G latent) i &&
                hedgeIncident G (hedgePairRoot G latent) j) = true := by
            simpa [hedgeIncident_pair] using hinc
          have hfin :
              finAny (hedgeLatentCount G)
                (fun root =>
                  hedgeIncident G root i && hedgeIncident G root j) = true :=
            finAny_eq_true_of _ (hedgePairRoot G latent) hlift
          simp [LatentExtension.projectedBidirected, hedgeLatentExtension,
            hbeq, hfin]
      | false =>
          have hany :
              finAny (pairRootCount G)
                (fun latent =>
                  pairRootIncident G latent i &&
                    pairRootIncident G latent j) = false := by
            simpa [LatentExtension.projectedBidirected, pairRootExtension,
              hbeq, hedge] using hpair
          have hall := (finAny_eq_false_iff _).mp hany
          have hfin :
              finAny (hedgeLatentCount G)
                (fun root =>
                  hedgeIncident G root i && hedgeIncident G root j) = false := by
            refine (finAny_eq_false_iff _).mpr fun root => ?_
            if hlt : root.val < pairRootCount G then
              have hroot := hall ⟨root.val, hlt⟩
              simpa [hedgeIncident, hlt] using hroot
            else
              exact hedgeIncident_private_both G root hne hlt
          simp [LatentExtension.projectedBidirected, hedgeLatentExtension,
            hbeq, hfin]

/-- Each hedge root has at most two observed children. -/
theorem hedgeLatentExtension_canonical (G : ObservedGraph S) :
    (hedgeLatentExtension G).CanonicalSemiMarkovian := by
  intro latent i j k hi hj hk
  if hlt : latent.val < pairRootCount G then
    have hi' :=
      (pairRootIncident_iff G ⟨latent.val, hlt⟩ i).mp
        (by simpa [hedgeLatentExtension, hedgeIncident, hlt] using hi)
    have hj' :=
      (pairRootIncident_iff G ⟨latent.val, hlt⟩ j).mp
        (by simpa [hedgeLatentExtension, hedgeIncident, hlt] using hj)
    have hk' :=
      (pairRootIncident_iff G ⟨latent.val, hlt⟩ k).mp
        (by simpa [hedgeLatentExtension, hedgeIncident, hlt] using hk)
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;>
      rcases hk' with hk' | hk'
    · exact Or.inl (hi'.trans hj'.symm)
    · exact Or.inl (hi'.trans hj'.symm)
    · exact Or.inr (Or.inl (hi'.trans hk'.symm))
    · exact Or.inr (Or.inr (hj'.trans hk'.symm))
    · exact Or.inr (Or.inr (hj'.trans hk'.symm))
    · exact Or.inr (Or.inl (hi'.trans hk'.symm))
    · exact Or.inl (hi'.trans hj'.symm)
    · exact Or.inl (hi'.trans hj'.symm)
  else
    have bit (node : Fin S.count)
        (hinc : (hedgeLatentExtension G).incident latent node = true) :
        node.val = latent.val - pairRootCount G := by
      have hinc' : hedgeIncident G latent node = true := by
        simpa [hedgeLatentExtension] using hinc
      simp [hedgeIncident, hlt, decide_eq_true_eq] at hinc'
      exact hinc'.symm
    exact Or.inl (Fin.ext ((bit i hi).trans (bit j hj).symm))

theorem hedgeLatentValue_pair (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    hedgeLatentValue G (hedgePairRoot G root) = Bool :=
  hedgeLatentValue_eq_bool G (hedgePairRoot G root) root.isLt

theorem hedgeLatentValue_private (G : ObservedGraph S)
    (child : Fin S.count) :
    hedgeLatentValue G (hedgePrivateRoot G child) =
      Fin (hedgePrivateCard S child) := by
  rw [hedgeLatentValue_eq_fin G (hedgePrivateRoot G child)
    (hedgePrivateRoot_not_pair G child),
    hedgeChildOfPrivate_privateRoot]

theorem hedgePrivateIncident (G : ObservedGraph S)
    (child : Fin S.count) :
    (hedgeLatentExtension G).incident (hedgePrivateRoot G child) child =
      true := by
  change
    (if h : (hedgePrivateRoot G child).val < pairRootCount G then
      pairRootIncident G ⟨(hedgePrivateRoot G child).val, h⟩ child
    else
      decide ((hedgePrivateRoot G child).val - pairRootCount G = child.val)) = true
  rw [dif_neg (hedgePrivateRoot_not_pair G child)]
  simp [hedgePrivateRoot]

/-- Pair-root bits incident to `child`, starting from `false`. -/
def hedgeXorPairBits (G : ObservedGraph S) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child) : Bool :=
  (List.finRange (pairRootCount G)).foldl
    (fun acc root =>
      if h : (hedgeLatentExtension G).incident (hedgePairRoot G root) child then
        Bool.xor acc
          (cast (hedgeLatentValue_pair G root) (inputs (hedgePairRoot G root) h))
      else acc)
    false

/-- Decode the private enumeration index of `child`. -/
def hedgePrivateIndex (G : ObservedGraph S) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child) :
    Fin (hedgePrivateCard S child) :=
  (cast
      (hedgeLatentValue_eq_fin G (hedgePrivateRoot G child)
        (hedgePrivateRoot_not_pair G child))
      (inputs (hedgePrivateRoot G child) (hedgePrivateIncident G child))).cast
    (by rw [hedgeChildOfPrivate_privateRoot])

def hedgePrivateDecode (S : ObservedSignature) (child : Fin S.count)
    (index : Fin (hedgePrivateCard S child)) : S.Value child :=
  (S.valueEnumeration child).get
    (index.cast (by simp [hedgePrivateCard]))

/-- Swap the two `ValueRich` labels and leave every other value fixed. -/
def hedgeToggle (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (bit : Bool) (base : S.Value child) :
    S.Value child :=
  if bit then
    if _hfirst : base = rich.first child then
      rich.second child
    else if _hsecond : base = rich.second child then
      rich.first child
    else
      base
  else
    base

theorem hedgeToggle_false (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (base : S.Value child) :
    hedgeToggle rich child false base = base :=
  rfl

theorem hedgeToggle_involution (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (bit : Bool) (base : S.Value child) :
    hedgeToggle rich child bit (hedgeToggle rich child bit base) = base := by
  cases bit with
  | false =>
      rfl
  | true =>
      by_cases hfirst : base = rich.first child
      · subst hfirst
        simp [hedgeToggle]
      · by_cases hsecond : base = rich.second child
        · subst hsecond
          simp [hedgeToggle, hfirst]
        · simp [hedgeToggle, hfirst, hsecond]

/-- `hedgeToggle` is a `Bool`-group action on the two `ValueRich` labels. -/
theorem hedgeToggle_xor (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (a b : Bool) (base : S.Value child) :
    hedgeToggle rich child a (hedgeToggle rich child b base) =
      hedgeToggle rich child (Bool.xor a b) base := by
  cases a with
  | false =>
      cases b with
      | false =>
          simp [hedgeToggle_false]
      | true =>
          simp [hedgeToggle_false]
  | true =>
      cases b with
      | false =>
          simp [hedgeToggle_false]
      | true =>
          simp [hedgeToggle_involution, hedgeToggle_false]

/-- Whether a value is the second `ValueRich` label of its node. -/
def hedgeIsSecond (rich : ObservedSignature.ValueRich S)
    (i : Fin S.count) (value : S.Value i) : Bool :=
  decide (value = rich.second i)

/--
XOR of `ValueRich` second-bits of every directed parent that lies in `mask`.
The empty mask recovers the parent-ignoring base embedding.
-/
def hedgeParentBitsFrom (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S) (child : Fin S.count)
    (get : forall parent, S.directed parent child = true → S.Value parent) :
    Bool :=
  (List.finRange S.count).foldl
    (fun acc parent =>
      if hdir : S.directed parent child = true then
        if mask parent then
          Bool.xor acc (hedgeIsSecond rich parent (get parent hdir))
        else acc
      else acc)
    false

/--
Parity of the directed parents of `child` selected by an action set.  This is
the graph-only value computed by `hedgeParentBitsFrom` under the intervention
that pins every selected parent to its `ValueRich` second label.
-/
def actionParentParity (action : NodeSet S) (child : Fin S.count) : Bool :=
  (List.finRange S.count).foldl
    (fun acc parent =>
      if S.directed parent child then
        if action parent then !acc else acc
      else acc)
    false

theorem foldl_unchanged {α β} (f : α → β → α) (init : α) (xs : List β)
    (hstep : forall acc x, f acc x = acc) :
    xs.foldl f init = init := by
  induction xs generalizing init with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [hstep]
      exact ih _

theorem foldl_congr {α β} (f g : α → β → α) (init : α) (xs : List β)
    (hstep : forall acc x, f acc x = g acc x) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [hstep]
      exact ih _

/-- Pointwise fold congruence whose step proof may use membership in the
fixed input list.  This form is useful for node-set folds: semantic equations
usually hold only on selected vertices, and `NodeSet.members` carries exactly
that evidence. -/
theorem foldl_congr_of_mem {α β} (f g : α → β → α) (init : α)
    (xs : List β)
    (step : forall acc x, x ∈ xs → f acc x = g acc x) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.foldl, List.foldl, step init head (by simp)]
      exact inductionHypothesis _ (fun acc x member =>
        step acc x (by simp [member]))

/-- An XOR fold with an arbitrary accumulator is its zero-based fold plus that accumulator. -/
theorem foldl_xor_init {α} (bits : α → Bool) (xs : List α) (init : Bool) :
    xs.foldl (fun acc x => Bool.xor acc (bits x)) init =
      Bool.xor init
        (xs.foldl (fun acc x => Bool.xor acc (bits x)) false) := by
  induction xs generalizing init with
  | nil =>
      cases init <;> rfl
  | cons x xs ih =>
      simp only [List.foldl]
      rw [ih (Bool.xor init (bits x)), ih (Bool.xor false (bits x))]
      generalize
        xs.foldl (fun acc y => Bool.xor acc (bits y)) false = tail
      cases init <;> cases bits x <;> cases tail <;> rfl

/--
General accumulator form of pointwise XOR distributivity.  Carrying two
separate accumulators makes the induction step exact after the four Boolean
inputs are normalized.
-/
theorem foldl_xor_pointwise_init {α} (left right : α → Bool)
    (xs : List α) (leftInit rightInit : Bool) :
    xs.foldl
        (fun acc x => Bool.xor acc (Bool.xor (left x) (right x)))
        (Bool.xor leftInit rightInit) =
      Bool.xor
        (xs.foldl (fun acc x => Bool.xor acc (left x)) leftInit)
        (xs.foldl (fun acc x => Bool.xor acc (right x)) rightInit) := by
  induction xs generalizing leftInit rightInit with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl]
      have accumulators :
          Bool.xor (Bool.xor leftInit rightInit)
              (Bool.xor (left x) (right x)) =
            Bool.xor
              (Bool.xor leftInit (left x))
              (Bool.xor rightInit (right x)) := by
        cases leftInit <;> cases rightInit <;>
          cases left x <;> cases right x <;> rfl
      rw [accumulators]
      exact ih (Bool.xor leftInit (left x))
        (Bool.xor rightInit (right x))

/-- XOR-folding pointwise XORs distributes over the two separate folds. -/
theorem foldl_xor_pointwise {α} (left right : α → Bool) (xs : List α) :
    xs.foldl
        (fun acc x => Bool.xor acc (Bool.xor (left x) (right x))) false =
      Bool.xor
        (xs.foldl (fun acc x => Bool.xor acc (left x)) false)
        (xs.foldl (fun acc x => Bool.xor acc (right x)) false) := by
  simpa using foldl_xor_pointwise_init left right xs false false

/-- An XOR fold is true exactly when its Boolean filter has odd length. -/
theorem foldl_xor_eq_decide_filter_odd {α}
    (bits : α → Bool) (xs : List α) :
    xs.foldl (fun acc x => Bool.xor acc (bits x)) false =
      decide ((xs.filter bits).length % 2 = 1) := by
  induction xs with
  | nil => simp
  | cons x xs inductionHypothesis =>
      rw [List.filter, List.foldl, foldl_xor_init]
      cases hbit : bits x
      · simp [inductionHypothesis]
      · rw [inductionHypothesis]
        cases hmod : (xs.filter bits).length % 2 with
        | zero => simp [Nat.add_mod, hmod]
        | succ remainder =>
            have remainderZero : remainder = 0 := by omega
            subst remainder
            simp [Nat.add_mod, hmod]

/-- Equivalently, an XOR fold is false exactly when its filter is even. -/
theorem foldl_xor_eq_false_iff_filter_even {α}
    (bits : α → Bool) (xs : List α) :
    xs.foldl (fun acc x => Bool.xor acc (bits x)) false = false ↔
      (xs.filter bits).length % 2 = 0 := by
  rw [foldl_xor_eq_decide_filter_odd]
  cases hmod : (xs.filter bits).length % 2 with
  | zero => simp
  | succ remainder =>
      have remainderZero : remainder = 0 := by omega
      subst remainder
      simp

/--
Finite XORs may be transposed: folding row parities equals folding column
parities.  This is the Boolean finite-sum interchange used to count each
pair-root once by node and once by root.
-/
theorem foldl_xor_swap {α β} (rows : List α) (columns : List β)
    (entry : α → β → Bool) :
    rows.foldl
        (fun total row => Bool.xor total
          (columns.foldl
            (fun rowTotal column => Bool.xor rowTotal (entry row column))
            false)) false =
      columns.foldl
        (fun total column => Bool.xor total
          (rows.foldl
            (fun columnTotal row => Bool.xor columnTotal (entry row column))
            false)) false := by
  induction columns with
  | nil =>
      simp only [List.foldl]
      exact foldl_unchanged _ false rows (fun acc _ => by simp)
  | cons column columns inductionHypothesis =>
      simp only [List.foldl, Bool.false_xor]
      have rowSplit :
          rows.foldl
              (fun total row => Bool.xor total
                (columns.foldl
                  (fun rowTotal remaining =>
                    Bool.xor rowTotal (entry row remaining))
                  (entry row column))) false =
            Bool.xor
              (rows.foldl
                (fun total row => Bool.xor total (entry row column)) false)
              (rows.foldl
                (fun total row => Bool.xor total
                  (columns.foldl
                    (fun rowTotal remaining =>
                      Bool.xor rowTotal (entry row remaining)) false))
                false) := by
        have innerSplit : ∀ row,
            columns.foldl
                (fun rowTotal remaining =>
                  Bool.xor rowTotal (entry row remaining))
                (entry row column) =
              Bool.xor (entry row column)
                (columns.foldl
                  (fun rowTotal remaining =>
                    Bool.xor rowTotal (entry row remaining)) false) :=
          fun row => foldl_xor_init (entry row) columns (entry row column)
        have outerCongruence := foldl_congr
          (fun total row => Bool.xor total
            (columns.foldl
              (fun rowTotal remaining =>
                Bool.xor rowTotal (entry row remaining))
              (entry row column)))
          (fun total row => Bool.xor total
            (Bool.xor (entry row column)
              (columns.foldl
                (fun rowTotal remaining =>
                  Bool.xor rowTotal (entry row remaining)) false)))
          false rows (fun total row => by
            change Bool.xor total _ = Bool.xor total _
            rw [innerSplit row])
        rw [outerCongruence, foldl_xor_pointwise]
      rw [rowSplit, inductionHypothesis]
      exact (foldl_xor_init
        (fun remaining =>
          rows.foldl
            (fun total row => Bool.xor total (entry row remaining)) false)
        columns
        (rows.foldl
          (fun total row => Bool.xor total (entry row column)) false)).symm

theorem hedgeParentBitsFrom_empty (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count)
    (get : forall parent, S.directed parent child = true → S.Value parent) :
    hedgeParentBitsFrom rich NodeSet.empty child get = false := by
  unfold hedgeParentBitsFrom NodeSet.empty
  refine foldl_unchanged _ false (List.finRange S.count) ?_
  intro acc parent
  if hdir : S.directed parent child = true then
    simp [hdir]
  else
    simp [hdir]

theorem hedgeParentBitsFrom_congr (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S) (child : Fin S.count)
    {getLeft getRight :
      forall parent, S.directed parent child = true → S.Value parent}
    (hget : forall parent hp, getLeft parent hp = getRight parent hp) :
    hedgeParentBitsFrom rich mask child getLeft =
      hedgeParentBitsFrom rich mask child getRight := by
  unfold hedgeParentBitsFrom
  refine foldl_congr _ _ _ _ ?_
  intro acc parent
  if hdir : S.directed parent child = true then
    simp [hdir, hget parent hdir]
  else
    simp [hdir]

/--
XOR of the `ValueRich` second-bits carried by the explicitly kept directed
parents of `child`.  The outer directed-edge test supplies the dependent
argument expected by `get`; a malformed child map is therefore harmless here
and simply cannot smuggle a non-edge into a structural mechanism.  For a
`CForest`, `child_edge` shows that every selected entry passes this test.
-/
def hedgeForestParentBitsFrom (rich : ObservedSignature.ValueRich S)
    (kept : ForestChild S) (child : Fin S.count)
    (get : forall parent, S.directed parent child = true → S.Value parent) :
    Bool :=
  (List.finRange S.count).foldl
    (fun acc parent =>
      if hdir : S.directed parent child = true then
        if kept parent = some child then
          Bool.xor acc (hedgeIsSecond rich parent (get parent hdir))
        else acc
      else acc)
    false

/-- An empty kept-edge map contributes no directed parity. -/
theorem hedgeForestParentBitsFrom_empty
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (get : forall parent, S.directed parent child = true → S.Value parent) :
    hedgeForestParentBitsFrom rich (emptyChild S) child get = false := by
  unfold hedgeForestParentBitsFrom emptyChild
  refine foldl_unchanged _ false (List.finRange S.count) ?_
  intro acc parent
  if hdir : S.directed parent child = true then
    simp [hdir]
  else
    simp [hdir]

/-- Pointwise-equal child maps and parent values induce the same parity bit. -/
theorem hedgeForestParentBitsFrom_congr
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    {leftKept rightKept : ForestChild S}
    {leftGet rightGet :
      forall parent, S.directed parent child = true → S.Value parent}
    (hkept : forall parent, leftKept parent = rightKept parent)
    (hget : forall parent hp, leftGet parent hp = rightGet parent hp) :
    hedgeForestParentBitsFrom rich leftKept child leftGet =
      hedgeForestParentBitsFrom rich rightKept child rightGet := by
  unfold hedgeForestParentBitsFrom
  refine foldl_congr _ _ _ _ ?_
  intro acc parent
  if hdir : S.directed parent child = true then
    rw [hkept parent]
    simp [hdir, hget parent hdir]
  else
    simp [hdir]

/-- Congruence for the forest-parent fold only needs equality at parents whose
kept edge actually reaches `child`.  This sharper form is useful for recursive
comparisons: values at all other graph parents are inspected by neither side
of the fold. -/
theorem hedgeForestParentBitsFrom_congr_of_kept
    (rich : ObservedSignature.ValueRich S) (kept : ForestChild S)
    (child : Fin S.count)
    (left right : forall parent, S.directed parent child = true →
      S.Value parent)
    (equalBit : forall parent edge, kept parent = some child →
      hedgeIsSecond rich parent (left parent edge) =
        hedgeIsSecond rich parent (right parent edge)) :
    hedgeForestParentBitsFrom rich kept child left =
      hedgeForestParentBitsFrom rich kept child right := by
  unfold hedgeForestParentBitsFrom
  apply foldl_congr
  intro total parent
  if edge : S.directed parent child = true then
    cases keptEq : kept parent with
    | none => simp [edge]
    | some selectedChild =>
        by_cases selected : selectedChild = child
        · subst selectedChild
          simp [edge, equalBit parent edge keptEq]
        · simp [edge, selected]
  else
    simp [edge]

/--
Restricting a child map does nothing at `child` when every parent whose kept
edge reaches `child` is already selected.  This is the local equality used on
small-forest edges that do not cross the `F \ F'` boundary.
-/
theorem hedgeForestParentBitsFrom_restrict_eq
    (rich : ObservedSignature.ValueRich S) (nodes : NodeSet S)
    (kept : ForestChild S) (child : Fin S.count)
    (get : forall parent, S.directed parent child = true → S.Value parent)
    (hinside : forall parent, kept parent = some child → nodes parent = true) :
    hedgeForestParentBitsFrom rich (restrictChild nodes kept) child get =
      hedgeForestParentBitsFrom rich kept child get := by
  unfold hedgeForestParentBitsFrom
  refine foldl_congr _ _ _ _ ?_
  intro acc parent
  if hdir : S.directed parent child = true then
    cases hkept : kept parent with
    | none =>
        simp [hdir, restrictChild, hkept]
    | some c =>
        if hc : c = child then
          subst hc
          have hin := hinside parent hkept
          simp [hdir, restrictChild, hkept, hin]
        else
          simp [hdir, restrictChild, hkept, hc]
  else
    simp [hdir]

/-- Whether both endpoints represented by a canonical pair-root lie in `nodes`. -/
def hedgePairRootWithin (G : ObservedGraph S) (nodes : NodeSet S)
    (root : Fin (pairRootCount G)) : Bool :=
  let endpoints := (pairRoots G).get root
  nodes endpoints.1 && nodes endpoints.2

/-- A bidirected edge with selected endpoints names an internal pair-root. -/
theorem hedgePairRootWithin_between
    (G : ObservedGraph S) (nodes : NodeSet S)
    {i j : Fin S.count}
    (hi : nodes i = true) (hj : nodes j = true)
    (edge : G.bidirected i j = true) :
    hedgePairRootWithin G nodes (pairRootBetween G edge) = true := by
  unfold pairRootBetween
  split
  · next ordered =>
      rw [hedgePairRootWithin, pairRoots_get_of G ordered edge]
      simp [hi, hj]
  · next notOrdered =>
      have reverseOrdered : j.val < i.val := by
        rcases Nat.lt_or_gt_of_ne (val_ne_of_bidirected G edge) with
          forward | reverse
        · exact False.elim (notOrdered forward)
        · exact reverse
      rw [hedgePairRootWithin,
        pairRoots_get_of G reverseOrdered (G.bidirected_symmetric edge)]
      simp [hi, hj]

/-- The canonical root of a bidirected edge is incident in the hedge extension. -/
theorem hedgePairRootBetween_incident_left
    (G : ObservedGraph S) {i j : Fin S.count}
    (edge : G.bidirected i j = true) :
    (hedgeLatentExtension G).incident
      (hedgePairRoot G (pairRootBetween G edge)) i = true := by
  simpa [hedgeLatentExtension, hedgeIncident_pair] using
    pairRootIncident_between_left G edge

/-- The same canonical root is incident to the edge's right endpoint. -/
theorem hedgePairRootBetween_incident_right
    (G : ObservedGraph S) {i j : Fin S.count}
    (edge : G.bidirected i j = true) :
    (hedgeLatentExtension G).incident
      (hedgePairRoot G (pairRootBetween G edge)) j = true := by
  simpa [hedgeLatentExtension, hedgeIncident_pair] using
    pairRootIncident_between_right G edge

/--
XOR of the pair-root bits whose two observed endpoints lie in `nodes` and
whose root is incident to `child`.  Pair-roots elsewhere in `G` remain in the
latent extension, but are semantically inert in this forest circuit.
-/
def hedgeXorPairBitsWithin (G : ObservedGraph S) (nodes : NodeSet S)
    (child : Fin S.count) (inputs : (hedgeLatentExtension G).Inputs child) :
    Bool :=
  (List.finRange (pairRootCount G)).foldl
    (fun acc root =>
      if hinc :
          (hedgeLatentExtension G).incident (hedgePairRoot G root) child then
        if hedgePairRootWithin G nodes root then
          Bool.xor acc
            (cast (hedgeLatentValue_pair G root)
              (inputs (hedgePairRoot G root) hinc))
        else acc
      else acc)
    false

/-!
### The unsoftened forest-parity pair

The published hedge proof first constructs a binary parity pair and only then
softens it to obtain a strictly positive observed law.  Keeping those stages
separate is important here.  In particular, inserting the positive
`hedgeMixFrom` gate at this point is unsound: on the two-node bow it destroys
the observational equality of the large and small parity circuits.

The definitions below therefore encode only the faithful unsoftened core.
They use `ValueRich.first` and `ValueRich.second` as zero and one, ignore the
private coordinate inside the selected forest, and retain the private decode
outside it.  No theorem below claims that these models are observationally
positive.
-/

/-- Encode one Boolean parity bit by the two distinguished observed values. -/
def hedgeParityValue (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (bit : Bool) : S.Value child :=
  if bit then rich.second child else rich.first child

theorem hedgeParityValue_false (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) :
    hedgeParityValue rich child false = rich.first child :=
  rfl

theorem hedgeParityValue_true (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) :
    hedgeParityValue rich child true = rich.second child :=
  rfl

/-- Reading the distinguished second-value bit inverts `hedgeParityValue`. -/
theorem hedgeIsSecond_parityValue
    (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (bit : Bool) :
    hedgeIsSecond rich child (hedgeParityValue rich child bit) = bit := by
  cases bit with
  | false =>
      simp [hedgeParityValue, hedgeIsSecond, rich.different]
  | true =>
      simp [hedgeParityValue, hedgeIsSecond]

/-!
### Structural readout along a directed route

The hedge parity difference is born at a forest root, whereas the published
query may observe only a directed descendant.  The wrapper below provides the
mechanism-level transport needed to carry that bit along an explicit route.
It retains the base latent extension and product law verbatim, so projected
graph compatibility is unchanged.  An invalid proposed parent falls back to
the base mechanism; canonical readout maps never take that branch, by
`HedgeWitness.parityReadoutParent_directed`.
-/

/-- Replace indexed children by exact copies of their indexed parent's
distinguished Boolean label, leaving every unindexed mechanism unchanged. -/
def hedgeRouteReadoutModel (rich : ObservedSignature.ValueRich S)
    (parentOf : Fin S.count → Option (Fin S.count))
    (base : ExactModel S) : ExactModel S where
  latent := base.latent
  factor := base.factor
  prior := base.prior
  product_law := base.product_law
  mechanism := fun child parents inputs =>
    match parentOf child with
    | none => base.mechanism child parents inputs
    | some parent =>
        if edge : S.directed parent child = true then
          hedgeParityValue rich child
            (hedgeIsSecond rich parent (parents parent edge))
        else
          base.mechanism child parents inputs

/-- Route readout changes mechanisms only; the latent projection and hence
compatibility with the observed graph are inherited from the base model. -/
theorem hedgeRouteReadoutModel_compatible
    (rich : ObservedSignature.ValueRich S)
    (parentOf : Fin S.count → Option (Fin S.count))
    (base : ExactModel S) (compatible : Compatible base G) :
    Compatible (hedgeRouteReadoutModel rich parentOf base) G := by
  exact ⟨compatible.1, fun i j => compatible.2 i j⟩

/-- At an unintervened indexed child with a valid directed parent, evaluating
the wrapper preserves exactly the parent's encoded bit. -/
theorem hedgeRouteReadoutModel_evalNodeUnder_bit_of_parent
    (rich : ObservedSignature.ValueRich S)
    (parentOf : Fin S.count → Option (Fin S.count))
    (base : ExactModel S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : base.latent.Assignment) {parent child : Fin S.count}
    (free : intervention child = none)
    (parentEq : parentOf child = some parent)
    (edge : S.directed parent child = true) :
    hedgeIsSecond rich child
        ((hedgeRouteReadoutModel rich parentOf base).evalNodeUnder
          intervention u child) =
      hedgeIsSecond rich parent
        ((hedgeRouteReadoutModel rich parentOf base).evalNodeUnder
          intervention u parent) := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  simp only [hedgeRouteReadoutModel, parentEq, edge, dite_true]
  exact hedgeIsSecond_parityValue rich child
    (hedgeIsSecond rich parent
      ((hedgeRouteReadoutModel rich parentOf base).evalNodeUnder
        intervention u parent))

/--
Structural output of one c-forest parity circuit.  Selected nodes XOR the
internal pair-root bits with the values of their explicitly kept directed
parents.  Unselected nodes remain ordinary private-noise coordinates.
-/
def hedgeForestParityOutput (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (nodes : NodeSet S)
    (kept : ForestChild S) (child : Fin S.count)
    (parents : S.ParentValues child)
    (inputs : (hedgeLatentExtension G).Inputs child) : S.Value child :=
  if nodes child then
    hedgeParityValue rich child
      (Bool.xor
        (hedgeXorPairBitsWithin G nodes child inputs)
        (hedgeForestParentBitsFrom rich kept child parents))
  else
    hedgePrivateDecode S child (hedgePrivateIndex G child inputs)

/-- At a selected node, the output bit is exactly latent XOR directed parity. -/
theorem hedgeForestParityOutput_bit_of_mem
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (child : Fin S.count) (parents : S.ParentValues child)
    (inputs : (hedgeLatentExtension G).Inputs child)
    (hin : nodes child = true) :
    hedgeIsSecond rich child
        (hedgeForestParityOutput G rich nodes kept child parents inputs) =
      Bool.xor
        (hedgeXorPairBitsWithin G nodes child inputs)
        (hedgeForestParentBitsFrom rich kept child parents) := by
  simp [hedgeForestParityOutput, hin, hedgeIsSecond_parityValue]

/-- Exact SCM carrying one unsoftened forest-parity circuit. -/
def hedgeForestParityModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (nodes : NodeSet S)
    (kept : ForestChild S) : ExactModel S where
  latent := hedgeLatentExtension G
  factor := hedgeLatentFactor G
  prior :=
    FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
      (hedgeLatentFactor G)
  product_law := fun events => by
    simpa [LatentExtension.rectangularEvent, hedgeLatentExtension] using
      FiniteProduct.record_rectangular_probVal
        (hedgeLatentCount G) (hedgeLatentValue G) (hedgeLatentFactor G) events
  mechanism := hedgeForestParityOutput G rich nodes kept

/-- The parity circuit keeps the full latent projection of `G`. -/
theorem hedgeForestParityModel_compatible (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (nodes : NodeSet S)
    (kept : ForestChild S) :
    Compatible (hedgeForestParityModel G rich nodes kept) G :=
  ⟨hedgeLatentExtension_canonical G, fun i j => by
    simpa [FiniteLatentSCM.observedGraph, LatentExtension.observedGraph,
      hedgeForestParityModel] using hedgeLatentExtension_projected G i j⟩

/--
Piecewise parity model for nested forests `inner ⊆ outer`.  Nodes outside the
inner forest keep the outer mechanism verbatim; nodes inside it use only the
inner pair-roots and kept edges.  The definition itself does not require the
subset proof, allowing the semantic equality outside `inner` to be a direct
computation rather than a cast-heavy transport.
-/
def hedgeNestedForestParityModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S)
    (outerKept innerKept : ForestChild S) : ExactModel S where
  latent := hedgeLatentExtension G
  factor := hedgeLatentFactor G
  prior :=
    FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
      (hedgeLatentFactor G)
  product_law := fun events => by
    simpa [LatentExtension.rectangularEvent, hedgeLatentExtension] using
      FiniteProduct.record_rectangular_probVal
        (hedgeLatentCount G) (hedgeLatentValue G) (hedgeLatentFactor G) events
  mechanism := fun child parents inputs =>
    if inner child then
      hedgeForestParityOutput G rich inner innerKept child parents inputs
    else
      hedgeForestParityOutput G rich outer outerKept child parents inputs

/-- Piecewise restriction also keeps the full latent projection of `G`. -/
theorem hedgeNestedForestParityModel_compatible (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S)
    (outerKept innerKept : ForestChild S) :
    Compatible
      (hedgeNestedForestParityModel G rich outer inner outerKept innerKept) G :=
  ⟨hedgeLatentExtension_canonical G, fun i j => by
    simpa [FiniteLatentSCM.observedGraph, LatentExtension.observedGraph,
      hedgeNestedForestParityModel] using hedgeLatentExtension_projected G i j⟩

/-- The first, large-forest model from the classical hedge construction. -/
def HedgeWitness.largeParityModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeForestParityModel G rich w.large w.child

/--
The second hedge model: unchanged on `F \ F'`, but with every node of `F'`
ignoring pair-roots and kept directed parents that are not internal to `F'`.
-/
def HedgeWitness.smallParityModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeNestedForestParityModel G rich w.large w.small w.child
    (restrictChild w.small w.child)

/-- The large unsoftened hedge model is compatible with the observed graph. -/
theorem HedgeWitness.largeParityModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.largeParityModel rich) G :=
  hedgeForestParityModel_compatible G rich w.large w.child

/-- The small unsoftened hedge model is compatible with the observed graph. -/
theorem HedgeWitness.smallParityModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.smallParityModel rich) G :=
  hedgeNestedForestParityModel_compatible G rich w.large w.small w.child
    (restrictChild w.small w.child)

/-- Both unsoftened models use definitionally the same product prior. -/
theorem HedgeWitness.parityModel_prior_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    (w.largeParityModel rich).prior = (w.smallParityModel rich).prior :=
  rfl

/-- The large parity circuit with its root bit routed to the selected query
outcome. -/
def HedgeWitness.largeReadoutParityModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeRouteReadoutModel rich w.parityReadoutParent
    (w.largeParityModel rich)

/-- The nested small parity circuit with the identical directed readout
wrapper. -/
def HedgeWitness.smallReadoutParityModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeRouteReadoutModel rich w.parityReadoutParent
    (w.smallParityModel rich)

/-- The wrapped large model remains compatible with the same ADMG. -/
theorem HedgeWitness.largeReadoutParityModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.largeReadoutParityModel rich) G :=
  hedgeRouteReadoutModel_compatible rich w.parityReadoutParent
    (w.largeParityModel rich) (w.largeParityModel_compatible rich)

/-- The wrapped small model remains compatible with the same ADMG. -/
theorem HedgeWitness.smallReadoutParityModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.smallReadoutParityModel rich) G :=
  hedgeRouteReadoutModel_compatible rich w.parityReadoutParent
    (w.smallParityModel rich) (w.smallParityModel_compatible rich)

/-- Wrapping both parity circuits leaves their shared product prior
definitionally unchanged. -/
theorem HedgeWitness.readoutParityModel_prior_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    (w.largeReadoutParityModel rich).prior =
      (w.smallReadoutParityModel rich).prior :=
  rfl

/-- Every free canonical route child in the large wrapped model copies its
canonical parent's parity bit. -/
theorem HedgeWitness.largeReadoutParityModel_evalNodeUnder_bit_of_parent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    {parent child : Fin S.count}
    (free : intervention child = none)
    (parentEq : w.parityReadoutParent child = some parent) :
    hedgeIsSecond rich child
        ((w.largeReadoutParityModel rich).evalNodeUnder
          intervention u child) =
      hedgeIsSecond rich parent
        ((w.largeReadoutParityModel rich).evalNodeUnder
          intervention u parent) :=
  hedgeRouteReadoutModel_evalNodeUnder_bit_of_parent rich
    w.parityReadoutParent (w.largeParityModel rich) intervention u free
    parentEq (w.parityReadoutParent_directed parentEq)

/-- Every free canonical route child in the small wrapped model copies its
canonical parent's parity bit. -/
theorem HedgeWitness.smallReadoutParityModel_evalNodeUnder_bit_of_parent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    {parent child : Fin S.count}
    (free : intervention child = none)
    (parentEq : w.parityReadoutParent child = some parent) :
    hedgeIsSecond rich child
        ((w.smallReadoutParityModel rich).evalNodeUnder
          intervention u child) =
      hedgeIsSecond rich parent
        ((w.smallReadoutParityModel rich).evalNodeUnder
          intervention u parent) :=
  hedgeRouteReadoutModel_evalNodeUnder_bit_of_parent rich
    w.parityReadoutParent (w.smallParityModel rich) intervention u free
    parentEq (w.parityReadoutParent_directed parentEq)

/-- Whenever the route vertices are free, the wrapped large model carries the
root's encoded bit all the way to the canonically selected outcome. -/
theorem HedgeWitness.largeReadoutParityModel_parityReadoutOutcome_bit
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    (routeFree : ∀ parent child,
      w.parityReadoutParent child = some parent →
        intervention child = none) :
    hedgeIsSecond rich w.parityReadoutOutcome
        ((w.largeReadoutParityModel rich).evalNodeUnder
          intervention u w.parityReadoutOutcome) =
      hedgeIsSecond rich w.actionRoot
        ((w.largeReadoutParityModel rich).evalNodeUnder
          intervention u w.actionRoot) := by
  apply PathSpecification.Consecutive.end_eq_start_of_step_eq
    (fun node =>
      hedgeIsSecond rich node
        ((w.largeReadoutParityModel rich).evalNodeUnder
          intervention u node))
    w.parityReadoutRoute w.actionRoot w.parityReadoutOutcome
    w.parityReadoutRoute_starts w.parityReadoutRoute_finishes
  exact w.parityReadoutParent_consecutive.mono (fun parent child found =>
    w.largeReadoutParityModel_evalNodeUnder_bit_of_parent rich
      intervention u (routeFree parent child found) found)

/-- The same free-route parity transport holds in the wrapped small model. -/
theorem HedgeWitness.smallReadoutParityModel_parityReadoutOutcome_bit
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    (routeFree : ∀ parent child,
      w.parityReadoutParent child = some parent →
        intervention child = none) :
    hedgeIsSecond rich w.parityReadoutOutcome
        ((w.smallReadoutParityModel rich).evalNodeUnder
          intervention u w.parityReadoutOutcome) =
      hedgeIsSecond rich w.actionRoot
        ((w.smallReadoutParityModel rich).evalNodeUnder
          intervention u w.actionRoot) := by
  apply PathSpecification.Consecutive.end_eq_start_of_step_eq
    (fun node =>
      hedgeIsSecond rich node
        ((w.smallReadoutParityModel rich).evalNodeUnder
          intervention u node))
    w.parityReadoutRoute w.actionRoot w.parityReadoutOutcome
    w.parityReadoutRoute_starts w.parityReadoutRoute_finishes
  exact w.parityReadoutParent_consecutive.mono (fun parent child found =>
    w.smallReadoutParityModel_evalNodeUnder_bit_of_parent rich
      intervention u (routeFree parent child found) found)

/--
Outside `F'` the two structural mechanisms are identical.  This is the
formal version of the clause that the second published model changes only
nodes of the small forest.
-/
theorem HedgeWitness.parityMechanism_eq_of_not_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (parents : S.ParentValues child)
    (inputs : (hedgeLatentExtension G).Inputs child)
    (hout : w.small child = false) :
    (w.largeParityModel rich).mechanism child parents inputs =
      (w.smallParityModel rich).mechanism child parents inputs := by
  simp [HedgeWitness.largeParityModel, HedgeWitness.smallParityModel,
    hedgeForestParityModel, hedgeNestedForestParityModel, hout]

/-- On `F'`, the second model evaluates exactly the restricted parity circuit. -/
theorem HedgeWitness.smallParityMechanism_of_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (parents : S.ParentValues child)
    (inputs : (hedgeLatentExtension G).Inputs child)
    (hin : w.small child = true) :
    (w.smallParityModel rich).mechanism child parents inputs =
      hedgeForestParityOutput G rich w.small
        (restrictChild w.small w.child) child parents inputs := by
  simp [HedgeWitness.smallParityModel, hedgeNestedForestParityModel, hin]

/-- The selected action-boundary edge is removed from the `F'` child map. -/
theorem HedgeWitness.actionBoundary_not_kept_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    restrictChild w.small w.child w.actionBoundaryParent = none :=
  restrictChild_of_false w.actionBoundaryParent_not_in_small

/--
At a free large-forest node, evaluation satisfies the large parity equation.
The recursive parent values in the right-hand side are the model's actual
values under the same intervention and latent assignment.
-/
theorem HedgeWitness.largeParityModel_evalNodeUnder_bit
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count)
    (hfree : intervention child = none)
    (hin : w.large child = true) :
    hedgeIsSecond rich child
        ((w.largeParityModel rich).evalNodeUnder intervention u child) =
      Bool.xor
        (hedgeXorPairBitsWithin G w.large child
          (fun latent _ => u latent))
        (hedgeForestParentBitsFrom rich w.child child
          (fun parent _ =>
            (w.largeParityModel rich).evalNodeUnder intervention u parent)) := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [hfree]
  exact hedgeForestParityOutput_bit_of_mem G rich w.large w.child child _ _ hin

/-- At a free small-forest node, evaluation satisfies the restricted equation. -/
theorem HedgeWitness.smallParityModel_evalNodeUnder_bit
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count)
    (hfree : intervention child = none)
    (hin : w.small child = true) :
    hedgeIsSecond rich child
        ((w.smallParityModel rich).evalNodeUnder intervention u child) =
      Bool.xor
        (hedgeXorPairBitsWithin G w.small child
          (fun latent _ => u latent))
        (hedgeForestParentBitsFrom rich
          (restrictChild w.small w.child) child
          (fun parent _ =>
            (w.smallParityModel rich).evalNodeUnder intervention u parent)) := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [hfree]
  rw [HedgeWitness.smallParityMechanism_of_small w rich child _ _ hin]
  exact hedgeForestParityOutput_bit_of_mem G rich w.small
    (restrictChild w.small w.child) child _ _ hin

/-- Index of an observed value in its enumeration. -/
def hedgeIndexOfValue (S : ObservedSignature) (child : Fin S.count)
    (value : S.Value child) : Fin (hedgePrivateCard S child) :=
  ⟨(S.valueEnumeration child).idxOf value,
    List.idxOf_lt_length_of_mem (S.value_complete child value)⟩

theorem get_idxOf_mem {α : Type _} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    l.get ⟨l.idxOf a, List.idxOf_lt_length_of_mem h⟩ = a := by
  induction l with
  | nil =>
      cases h
  | cons x xs ih =>
      if hx : x = a then
        subst hx
        simp [List.idxOf_cons_self]
      else
        have htail : a ∈ xs := by
          rw [List.mem_cons] at h
          cases h with
          | inl heq => exact (hx heq.symm).elim
          | inr hmem => exact hmem
        have hbeq : (x == a) = false := beq_eq_false_iff_ne.mpr hx
        simp [List.idxOf_cons, hbeq]
        exact ih htail

/-- Transport `List.get` along an equality of lists that preserves the
numeric index. -/
theorem list_get_eq_of_eq {α : Type _} {l₁ l₂ : List α} (h : l₁ = l₂)
    (i : Fin l₁.length) (j : Fin l₂.length) (hij : i.val = j.val) :
    l₁.get i = l₂.get j := by
  cases h
  exact congrArg _ (Fin.ext hij)

/-- Transport `idxOf` along equal lists and equal search values. -/
theorem list_idxOf_eq_of_eq {α : Type _} [DecidableEq α]
    {l₁ l₂ : List α} (h : l₁ = l₂) {a b : α} (hab : a = b) :
    l₁.idxOf a = l₂.idxOf b := by
  cases h
  cases hab
  rfl

theorem hedgePrivateDecode_index (S : ObservedSignature)
    (child : Fin S.count) (value : S.Value child) :
    hedgePrivateDecode S child (hedgeIndexOfValue S child value) = value := by
  unfold hedgePrivateDecode hedgeIndexOfValue
  simpa [Fin.cast, hedgePrivateCard] using
    get_idxOf_mem (S.value_complete child value)

/-- The inverse of `hedgePrivateDecode_index` on enumerated indices, using
the signature's `value_nodup` rather than a search through a `Prop`. -/
theorem hedgeIndexOf_decode (S : ObservedSignature)
    (child : Fin S.count) (index : Fin (hedgePrivateCard S child)) :
    hedgeIndexOfValue S child (hedgePrivateDecode S child index) = index := by
  apply Fin.ext
  unfold hedgeIndexOfValue hedgePrivateDecode hedgePrivateCard
  simpa [Fin.cast] using
    idxOf_get_of_nodup (S.valueEnumeration child) (S.value_nodup child)
      (index.cast (by simp [hedgePrivateCard]))

/--
Latent assignment that realises an arbitrary observed point.  Pair-roots are
`false`.  The private index of each node is the `ValueRich` preimage of the
target under the parent-bit toggle of `mask`, so the empty mask recovers a
plain enumeration index.
-/
def hedgeSupportLatent (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    (root : Fin (hedgeLatentCount G)) : hedgeLatentValue G root :=
  if h : root.val < pairRootCount G then
    cast (hedgeLatentValue_eq_bool G root h).symm false
  else
    let child := hedgeChildOfPrivate G root h
    let needed :=
      hedgeParentBitsFrom rich mask child (fun parent _ => target parent)
    cast (hedgeLatentValue_eq_fin G root h).symm
      (hedgeIndexOfValue S child
        (hedgeToggle rich child needed (target child)))

theorem hedgeXorPairBits_of_false_pair_roots
    (G : ObservedGraph S) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child)
    (hfalse : forall root
        (hinc : (hedgeLatentExtension G).incident
          (hedgePairRoot G root) child = true),
        cast (hedgeLatentValue_pair G root)
          (inputs (hedgePairRoot G root) hinc) = false) :
    hedgeXorPairBits G child inputs = false := by
  unfold hedgeXorPairBits
  refine foldl_unchanged _ false (List.finRange (pairRootCount G)) ?_
  intro acc root
  if hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) child then
    simp [hinc, hfalse root hinc]
  else
    simp [hinc]

/-- Pair-root XOR depends only on the pair-root coordinates of the assignment. -/
theorem hedgeXorPairBits_of_pair_eq (G : ObservedGraph S) (child : Fin S.count)
    {left right : (hedgeLatentExtension G).Inputs child}
    (hpair : forall root
        (hinc : (hedgeLatentExtension G).incident
          (hedgePairRoot G root) child = true),
        left (hedgePairRoot G root) hinc =
          right (hedgePairRoot G root) hinc) :
    hedgeXorPairBits G child left = hedgeXorPairBits G child right := by
  unfold hedgeXorPairBits
  refine foldl_congr _ _ _ _ ?_
  intro acc root
  if hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) child then
    simp [hinc, hpair root hinc]
  else
    simp [hinc]

/-!
### Laws for parity restricted to a hedge forest

The elementary `hedgeMixModel` reads every pair-root incident to a node. A
general hedge needs a finer distinction: the large forest uses bidirected
edges internal to `F`, whereas the small forest uses only edges internal to
`F'`.  The latent extension itself is deliberately unchanged.  Roots outside
the selected forest remain present (and therefore preserve compatibility with
`G`), but the structural mechanism is allowed to ignore their values.
-/

/-- An internal pair-root incident to `child` certifies that `child` is selected. -/
theorem hedgePairRootWithin_child
    (G : ObservedGraph S) (nodes : NodeSet S)
    {root : Fin (pairRootCount G)} {child : Fin S.count}
    (hwithin : hedgePairRootWithin G nodes root = true)
    (hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true) :
    nodes child = true := by
  have endpoints := Bool.and_eq_true_iff.mp hwithin
  have hinc' : pairRootIncident G root child = true := by
    have hinc' : hedgeIncident G (hedgePairRoot G root) child = true := by
      simpa [hedgeLatentExtension] using hinc
    rw [hedgeIncident_pair] at hinc'
    exact hinc'
  rcases (pairRootIncident_iff G root child).mp hinc' with hleft | hright
  · simpa [hedgePairRootWithin, hleft] using endpoints.1
  · simpa [hedgePairRootWithin, hright] using endpoints.2

/-- No internal pair-root can contribute at a node outside the selected forest. -/
theorem hedgeXorPairBitsWithin_of_child_outside
    (G : ObservedGraph S) (nodes : NodeSet S) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child)
    (hout : nodes child = false) :
    hedgeXorPairBitsWithin G nodes child inputs = false := by
  unfold hedgeXorPairBitsWithin
  refine foldl_unchanged _ false (List.finRange (pairRootCount G)) ?_
  intro acc root
  if hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true then
    cases hwithin : hedgePairRootWithin G nodes root with
    | false =>
        simp [hinc]
    | true =>
        have hin := hedgePairRootWithin_child G nodes hwithin hinc
        exact False.elim (Bool.false_ne_true (hout.symm.trans hin))
  else
    simp [hinc]

/-- With no selected vertices, every forest-restricted pair XOR vanishes. -/
theorem hedgeXorPairBitsWithin_empty
    (G : ObservedGraph S) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child) :
    hedgeXorPairBitsWithin G NodeSet.empty child inputs = false :=
  hedgeXorPairBitsWithin_of_child_outside G NodeSet.empty child inputs rfl

/-- Selecting every vertex recovers the original, unrestricted pair-root XOR. -/
theorem hedgeXorPairBitsWithin_full
    (G : ObservedGraph S) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child) :
    hedgeXorPairBitsWithin G NodeSet.full child inputs =
      hedgeXorPairBits G child inputs := by
  unfold hedgeXorPairBitsWithin hedgeXorPairBits
  refine foldl_congr _ _ _ _ ?_
  intro acc root
  if hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true then
    simp [hinc, hedgePairRootWithin, NodeSet.full]
  else
    simp [hinc]

/-- All-false pair-root coordinates also annihilate every restricted XOR. -/
theorem hedgeXorPairBitsWithin_of_false_pair_roots
    (G : ObservedGraph S) (nodes : NodeSet S) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child)
    (hfalse : forall root
      (hinc : (hedgeLatentExtension G).incident
        (hedgePairRoot G root) child = true),
      cast (hedgeLatentValue_pair G root)
        (inputs (hedgePairRoot G root) hinc) = false) :
    hedgeXorPairBitsWithin G nodes child inputs = false := by
  unfold hedgeXorPairBitsWithin
  refine foldl_unchanged _ false (List.finRange (pairRootCount G)) ?_
  intro acc root
  if hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true then
    cases hwithin : hedgePairRootWithin G nodes root <;>
      simp [hinc, hfalse root hinc]
  else
    simp [hinc]

/--
A compatible embedding on the hedge skeleton, parameterized by which
directed parents contribute a `ValueRich` second-bit.  The empty mask is
the parent-ignoring base model; a later hedge pair can XOR action parents
without changing the latent skeleton or the product prior.
-/
def hedgeModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    ExactModel S where
  latent := hedgeLatentExtension G
  factor := hedgeLatentFactor G
  prior :=
    FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
      (hedgeLatentFactor G)
  product_law := fun events => by
    simpa [LatentExtension.rectangularEvent, hedgeLatentExtension] using
      FiniteProduct.record_rectangular_probVal
        (hedgeLatentCount G) (hedgeLatentValue G) (hedgeLatentFactor G) events
  mechanism := fun child parents inputs =>
    hedgeToggle rich child
      (Bool.xor (hedgeXorPairBits G child inputs)
        (hedgeParentBitsFrom rich mask child parents))
      (hedgePrivateDecode S child (hedgePrivateIndex G child inputs))

abbrev hedgeBaseModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) : ExactModel S :=
  hedgeModel G rich NodeSet.empty

abbrev hedgeCopyModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) : ExactModel S :=
  hedgeModel G rich NodeSet.full

theorem hedgeModel_compatible (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    Compatible (hedgeModel G rich mask) G :=
  ⟨hedgeLatentExtension_canonical G, fun i j => by
    simpa [FiniteLatentSCM.observedGraph, LatentExtension.observedGraph,
      hedgeModel] using hedgeLatentExtension_projected G i j⟩

theorem hedgeBaseModel_compatible (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) :
    Compatible (hedgeBaseModel G rich) G :=
  hedgeModel_compatible G rich NodeSet.empty

theorem hedgeCopyModel_compatible (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) :
    Compatible (hedgeCopyModel G rich) G :=
  hedgeModel_compatible G rich NodeSet.full

theorem eventMass_ones_mem {Ω : Type _} [DecidableEq Ω]
    (values : List Ω) {chosen : Ω} (hmem : chosen ∈ values) :
    0 <
      FiniteProbRecord.eventMass (values.map (fun v => (v, 1)))
        (FiniteProbRecord.singletonEvent chosen) := by
  induction values with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.map, FiniteProbRecord.eventMass]
      cases hE : FiniteProbRecord.singletonEvent chosen x with
      | true =>
          simp
          omega
      | false =>
          have htail : chosen ∈ xs := by
            rw [List.mem_cons] at hmem
            cases hmem with
            | inl heq =>
                have : FiniteProbRecord.singletonEvent chosen x = true := by
                  simp [FiniteProbRecord.singletonEvent, heq]
                simp [this] at hE
            | inr hmem =>
                exact hmem
          exact ih htail

/-- Ones-weighted atoms contribute nothing at a missing label. -/
theorem eventMass_ones_not_mem {Ω : Type _} [DecidableEq Ω]
    (values : List Ω) {chosen : Ω} (hnmem : chosen ∉ values) :
    FiniteProbRecord.eventMass (values.map (fun v => (v, 1)))
      (FiniteProbRecord.singletonEvent chosen) = 0 := by
  induction values with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map, FiniteProbRecord.eventMass]
      have hx : FiniteProbRecord.singletonEvent chosen x = false := by
        simp [FiniteProbRecord.singletonEvent]
        intro heq
        exact hnmem (List.mem_cons.mpr (Or.inl heq.symm))
      have htail : chosen ∉ xs := fun hmem =>
        hnmem (List.mem_cons.mpr (Or.inr hmem))
      simp [hx]
      exact ih htail

/-- Duplicate-free ones-weighted atoms give singleton mass exactly one. -/
theorem eventMass_ones_singleton {Ω : Type _} [DecidableEq Ω]
    (values : List Ω) {chosen : Ω}
    (hmem : chosen ∈ values) (nodup : values.Nodup) :
    FiniteProbRecord.eventMass (values.map (fun v => (v, 1)))
      (FiniteProbRecord.singletonEvent chosen) = 1 := by
  induction values with
  | nil =>
      cases hmem
  | cons x xs ih =>
      have parts := List.nodup_cons.mp nodup
      simp only [List.map, FiniteProbRecord.eventMass]
      cases hE : FiniteProbRecord.singletonEvent chosen x with
      | true =>
          have hx : x = chosen := by
            simpa [FiniteProbRecord.singletonEvent] using hE
          have htail :
              FiniteProbRecord.eventMass (xs.map (fun v => (v, 1)))
                (FiniteProbRecord.singletonEvent chosen) = 0 :=
            eventMass_ones_not_mem xs (hx ▸ parts.1)
          simp [htail]
      | false =>
          have htail : chosen ∈ xs := by
            rw [List.mem_cons] at hmem
            cases hmem with
            | inl heq =>
                have : FiniteProbRecord.singletonEvent chosen x = true := by
                  simp [FiniteProbRecord.singletonEvent, heq]
                simp [this] at hE
            | inr hmem =>
                exact hmem
          exact ih htail parts.2

theorem hedgeSupportLatent_pair (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment) (root : Fin (pairRootCount G)) :
    cast (hedgeLatentValue_pair G root)
      (hedgeSupportLatent G rich mask target (hedgePairRoot G root)) = false := by
  simp [hedgeSupportLatent, hedgePairRoot]

theorem hedgeSupportLatent_private (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment) (child : Fin S.count) :
    hedgePrivateIndex G child
        (fun root _ => hedgeSupportLatent G rich mask target root) =
      hedgeIndexOfValue S child
        (hedgeToggle rich child
          (hedgeParentBitsFrom rich mask child (fun parent _ => target parent))
          (target child)) := by
  apply Fin.ext
  unfold hedgePrivateIndex hedgeIndexOfValue
  simp [hedgeSupportLatent, hedgePrivateRoot_not_pair, hedgeIndexOfValue]
  exact congrArg (fun node : Fin S.count =>
      (S.valueEnumeration node).idxOf
        (hedgeToggle rich node
          (hedgeParentBitsFrom rich mask node (fun parent _ => target parent))
          (target node)))
    (by
      apply Fin.ext
      simp [hedgeChildOfPrivate, hedgePrivateRoot])

theorem hedgeModel_evalNode_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S) (target : S.Assignment) (child : Fin S.count) :
    (hedgeModel G rich mask).evalNodeUnder (FiniteLatentSCM.noIntervention S)
      (hedgeSupportLatent G rich mask target) child = target child := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp [hedgeModel]
  have hxor :
      hedgeXorPairBits G child
          (fun root _ => hedgeSupportLatent G rich mask target root) = false :=
    hedgeXorPairBits_of_false_pair_roots G child _
      (fun root _ => hedgeSupportLatent_pair G rich mask target root)
  rw [hxor, Bool.false_xor]
  refine
    (congrArg
        (fun bit =>
          hedgeToggle rich child bit
            (hedgePrivateDecode S child
              (hedgePrivateIndex G child
                (fun latent _ =>
                  hedgeSupportLatent G rich mask target latent))))
        (hedgeParentBitsFrom_congr rich mask child
          (fun parent hp =>
            hedgeModel_evalNode_support G rich mask target parent))).trans
      ?_
  rw [hedgeSupportLatent_private, hedgePrivateDecode_index,
    hedgeToggle_involution]
termination_by child.val
decreasing_by
  exact S.directed_earlier hp

theorem hedgeModel_eval_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S) (target : S.Assignment) :
    (hedgeModel G rich mask).eval (hedgeSupportLatent G rich mask target) =
      target := by
  funext child
  exact hedgeModel_evalNode_support G rich mask target child

theorem hedgeLatentFactor_support_pos (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment) (root : Fin (hedgeLatentCount G)) :
    0 <
      FiniteProbRecord.eventMass (hedgeLatentFactor G root).atoms
        (FiniteProbRecord.singletonEvent
          (hedgeSupportLatent G rich mask target root)) := by
  simpa [hedgeLatentFactor] using
    eventMass_ones_mem (hedgeLatentEnum G root)
      (hedgeLatentEnum_complete G root
        (hedgeSupportLatent G rich mask target root))

theorem natProduct_pos (n : Nat) (values : Fin n → Nat)
    (hpos : forall i, 0 < values i) :
    0 < FiniteProduct.natProduct n values := by
  induction n with
  | zero =>
      simp [FiniteProduct.natProduct]
  | succ n ih =>
      exact Nat.mul_pos (hpos (Fin.last n))
        (ih (fun i => values i.castSucc) (fun i => hpos i.castSucc))

/--
Every `hedgeModel` puts strictly positive mass on every observed assignment:
private indices cover the enumeration after undoing the parent-bit toggle,
and the all-false pair-root assignment is a positive-mass preimage.
-/
theorem hedgeModel_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    ObservationallyPositive (hedgeModel G rich mask) := by
  intro assignment
  have heval := hedgeModel_eval_support G rich mask assignment
  have hsubset :
      forall u,
        (hedgeLatentExtension G).rectangularEvent
            (fun root value =>
              decide (value = hedgeSupportLatent G rich mask assignment root))
            u = true →
          FiniteProbRecord.singletonEvent assignment
            ((hedgeModel G rich mask).eval u) = true := by
    intro u hrect
    have hu : u = hedgeSupportLatent G rich mask assignment := by
      funext root
      have hroot :=
        (FiniteProduct.rectangularEvent_eq_true_iff
            (hedgeLatentCount G) (hedgeLatentValue G)
            (fun root value =>
              decide (value = hedgeSupportLatent G rich mask assignment root))
            u).mp
          (by simpa [LatentExtension.rectangularEvent, hedgeLatentExtension]
            using hrect) root
      exact of_decide_eq_true hroot
    simp [hu, heval, FiniteProbRecord.singletonEvent]
  have hmono :
      FiniteProbRecord.eventMass
          (hedgeModel G rich mask).prior.atoms
          ((hedgeLatentExtension G).rectangularEvent
            (fun root value =>
              decide (value = hedgeSupportLatent G rich mask assignment root))) ≤
        FiniteProbRecord.eventMass
          (hedgeModel G rich mask).prior.atoms
          (fun u =>
            FiniteProbRecord.singletonEvent assignment
              ((hedgeModel G rich mask).eval u)) :=
    FiniteProbRecord.eventMass_mono _ _ _ hsubset
  have hrect :
      FiniteProbRecord.eventMass
          (hedgeModel G rich mask).prior.atoms
          ((hedgeLatentExtension G).rectangularEvent
            (fun root value =>
              decide (value = hedgeSupportLatent G rich mask assignment root))) =
        FiniteProduct.natProduct (hedgeLatentCount G)
          (fun root =>
            FiniteProbRecord.eventMass (hedgeLatentFactor G root).atoms
              (fun value =>
                decide (value = hedgeSupportLatent G rich mask assignment root))) := by
    simpa [hedgeModel, FiniteProduct.record, LatentExtension.rectangularEvent,
      hedgeLatentExtension] using
      FiniteProduct.eventMass_atoms (hedgeLatentCount G) (hedgeLatentValue G)
        (hedgeLatentFactor G)
        (fun root value =>
          decide (value = hedgeSupportLatent G rich mask assignment root))
  have hpos :
      0 <
        FiniteProduct.natProduct (hedgeLatentCount G)
          (fun root =>
            FiniteProbRecord.eventMass (hedgeLatentFactor G root).atoms
              (fun value =>
                decide (value = hedgeSupportLatent G rich mask assignment root))) :=
    natProduct_pos _ _ (fun root => by
      simpa [FiniteProbRecord.singletonEvent] using
        hedgeLatentFactor_support_pos G rich mask assignment root)
  have hprior :
      0 <
        FiniteProbRecord.eventMass
          (hedgeModel G rich mask).prior.atoms
          (fun u =>
            FiniteProbRecord.singletonEvent assignment
              ((hedgeModel G rich mask).eval u)) :=
    Nat.lt_of_lt_of_le (hrect ▸ hpos) hmono
  simpa [FiniteLatentSCM.observationalDist, FiniteProbRecord.probVal,
    FiniteProbRecord.map, hedgeModel, FiniteProbRecord.eventMass_map_labels]
    using hprior

theorem hedgeModel_mem_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    (GraphModelClass.positive G).Mem (hedgeModel G rich mask) :=
  ⟨hedgeModel_compatible G rich mask, hedgeModel_positive G rich mask⟩

theorem hedgeBaseModel_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) :
    ObservationallyPositive (hedgeBaseModel G rich) :=
  hedgeModel_positive G rich NodeSet.empty

theorem hedgeBaseModel_mem_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) :
    (GraphModelClass.positive G).Mem (hedgeBaseModel G rich) :=
  hedgeModel_mem_positive G rich NodeSet.empty

theorem hedgeCopyModel_mem_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) :
    (GraphModelClass.positive G).Mem (hedgeCopyModel G rich) :=
  hedgeModel_mem_positive G rich NodeSet.full

/--
Recode the private indices of `u` so that the empty-mask embedding
reproduces the masked embedding's observed assignment.  Pair-roots are
copied unchanged; each private index is the `ValueRich` preimage of the
old decode under the parent-bit toggle of `mask` at the masked evaluation
of `u`.  The construction is a data-level group action, not a search
through a `Prop`.
-/
def hedgeRecodeLatent (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment)
    (root : Fin (hedgeLatentCount G)) : hedgeLatentValue G root :=
  if h : root.val < pairRootCount G then
    u root
  else
    let child := hedgeChildOfPrivate G root h
    let needed :=
      hedgeParentBitsFrom rich mask child
        (fun parent _ => (hedgeModel G rich mask).eval u parent)
    let oldVal :=
      hedgePrivateDecode S child
        (hedgePrivateIndex G child (fun latent _ => u latent))
    cast (hedgeLatentValue_eq_fin G root h).symm
      (hedgeIndexOfValue S child (hedgeToggle rich child needed oldVal))

/-- Inverse recoding: flip privates by the parent bits of the *base*
evaluation, so that applying the masked embedding recovers the base
evaluation of `w`. -/
def hedgeUnrecodeLatent (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (w : (hedgeLatentExtension G).Assignment)
    (root : Fin (hedgeLatentCount G)) : hedgeLatentValue G root :=
  if h : root.val < pairRootCount G then
    w root
  else
    let child := hedgeChildOfPrivate G root h
    let needed :=
      hedgeParentBitsFrom rich mask child
        (fun parent _ => (hedgeBaseModel G rich).eval w parent)
    let oldVal :=
      hedgePrivateDecode S child
        (hedgePrivateIndex G child (fun latent _ => w latent))
    cast (hedgeLatentValue_eq_fin G root h).symm
      (hedgeIndexOfValue S child (hedgeToggle rich child needed oldVal))

theorem hedgeRecode_pairRoot (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment)
    (root : Fin (pairRootCount G)) :
    hedgeRecodeLatent G rich mask u (hedgePairRoot G root) =
      u (hedgePairRoot G root) := by
  unfold hedgeRecodeLatent
  rw [dif_pos (by exact root.isLt)]

theorem hedgeUnrecode_pairRoot (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (w : (hedgeLatentExtension G).Assignment)
    (root : Fin (pairRootCount G)) :
    hedgeUnrecodeLatent G rich mask w (hedgePairRoot G root) =
      w (hedgePairRoot G root) := by
  unfold hedgeUnrecodeLatent
  rw [dif_pos (by exact root.isLt)]

theorem hedgeRecode_privateIndex (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    hedgePrivateIndex G child
        (fun root _ => hedgeRecodeLatent G rich mask u root) =
      hedgeIndexOfValue S child
        (hedgeToggle rich child
          (hedgeParentBitsFrom rich mask child
            (fun parent _ => (hedgeModel G rich mask).eval u parent))
          (hedgePrivateDecode S child
            (hedgePrivateIndex G child (fun root _ => u root)))) := by
  apply Fin.ext
  unfold hedgePrivateIndex hedgeIndexOfValue
  simp [hedgeRecodeLatent, hedgePrivateRoot_not_pair, hedgeIndexOfValue]
  exact congrArg (fun node : Fin S.count =>
      (S.valueEnumeration node).idxOf
        (hedgeToggle rich node
          (hedgeParentBitsFrom rich mask node
            (fun parent _ => (hedgeModel G rich mask).eval u parent))
          (hedgePrivateDecode S node
            (hedgePrivateIndex G node (fun root _ => u root)))))
    (hedgeChildOfPrivate_privateRoot G child)

theorem hedgeUnrecode_privateIndex (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (w : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    hedgePrivateIndex G child
        (fun root _ => hedgeUnrecodeLatent G rich mask w root) =
      hedgeIndexOfValue S child
        (hedgeToggle rich child
          (hedgeParentBitsFrom rich mask child
            (fun parent _ => (hedgeBaseModel G rich).eval w parent))
          (hedgePrivateDecode S child
            (hedgePrivateIndex G child (fun root _ => w root)))) := by
  apply Fin.ext
  unfold hedgePrivateIndex hedgeIndexOfValue
  simp [hedgeUnrecodeLatent, hedgePrivateRoot_not_pair, hedgeIndexOfValue]
  exact congrArg (fun node : Fin S.count =>
      (S.valueEnumeration node).idxOf
        (hedgeToggle rich node
          (hedgeParentBitsFrom rich mask node
            (fun parent _ => (hedgeBaseModel G rich).eval w parent))
          (hedgePrivateDecode S node
            (hedgePrivateIndex G node (fun root _ => w root)))))
    (hedgeChildOfPrivate_privateRoot G child)

/--
The empty-mask embedding of a recoded latent assignment equals the masked
embedding of the original assignment.  Pair-root XOR is copied; the private
index absorbs the parent-bit toggle, and `hedgeToggle_xor` reconstitutes the
masked mechanism.  No well-founded recursion is needed: recoding is defined
from the already-complete masked evaluation of `u`.
-/
theorem hedgeRecode_evalNode (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeBaseModel G rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (hedgeRecodeLatent G rich mask u) child =
      (hedgeModel G rich mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child := by
  unfold hedgeBaseModel
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp only [hedgeModel]
  have hxor :
      hedgeXorPairBits G child
          (fun root _ => hedgeRecodeLatent G rich mask u root) =
        hedgeXorPairBits G child (fun root _ => u root) :=
    hedgeXorPairBits_of_pair_eq G child
      (fun root _ => hedgeRecode_pairRoot G rich mask u root)
  rw [hxor, hedgeParentBitsFrom_empty, Bool.xor_false]
  rw [hedgeRecode_privateIndex, hedgePrivateDecode_index, hedgeToggle_xor]
  refine congrArg (fun bit =>
      hedgeToggle rich child
        (Bool.xor (hedgeXorPairBits G child (fun root _ => u root)) bit)
        (hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _ => u root)))) ?_
  exact hedgeParentBitsFrom_congr rich mask child
    (fun parent _ => rfl)

theorem hedgeRecode_eval (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeBaseModel G rich).eval (hedgeRecodeLatent G rich mask u) =
      (hedgeModel G rich mask).eval u := by
  funext child
  exact hedgeRecode_evalNode G rich mask u child

/--
The masked embedding of an unrecoded latent assignment equals the empty-mask
embedding of the original assignment.  Parent bits of the masked evaluation
are recovered by well-founded recursion along directed parents; the private
index then cancels the same toggle that recoding inserted.
-/
theorem hedgeUnrecode_evalNode (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (w : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeModel G rich mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (hedgeUnrecodeLatent G rich mask w) child =
      (hedgeBaseModel G rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) w child := by
  unfold hedgeBaseModel
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp only [hedgeModel]
  have hxor :
      hedgeXorPairBits G child
          (fun root _ => hedgeUnrecodeLatent G rich mask w root) =
        hedgeXorPairBits G child (fun root _ => w root) :=
    hedgeXorPairBits_of_pair_eq G child
      (fun root _ => hedgeUnrecode_pairRoot G rich mask w root)
  rw [hxor, hedgeParentBitsFrom_empty, Bool.xor_false]
  rw [hedgeUnrecode_privateIndex, hedgePrivateDecode_index, hedgeToggle_xor]
  refine
    (congrArg
        (fun bit =>
          hedgeToggle rich child
            (Bool.xor
              (Bool.xor
                (hedgeXorPairBits G child (fun root _ => w root))
                bit)
              (hedgeParentBitsFrom rich mask child
                (fun parent _ => (hedgeBaseModel G rich).eval w parent)))
            (hedgePrivateDecode S child
              (hedgePrivateIndex G child (fun root _ => w root))))
        (hedgeParentBitsFrom_congr rich mask child
          (fun parent hp =>
            hedgeUnrecode_evalNode G rich mask w parent))).trans
      ?_
  have hbits :
      (hedgeParentBitsFrom rich mask child
          (fun parent _ =>
            (hedgeBaseModel G rich).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) w parent)) =
        hedgeParentBitsFrom rich mask child
          (fun parent _ => (hedgeBaseModel G rich).eval w parent) :=
    hedgeParentBitsFrom_congr rich mask child
      (fun parent _ => by
        simp [FiniteLatentSCM.eval, FiniteLatentSCM.evalUnder])
  rw [hbits, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
termination_by child.val
decreasing_by
  exact S.directed_earlier hp

theorem hedgeUnrecode_eval (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (w : (hedgeLatentExtension G).Assignment) :
    (hedgeModel G rich mask).eval (hedgeUnrecodeLatent G rich mask w) =
      (hedgeBaseModel G rich).eval w := by
  funext child
  exact hedgeUnrecode_evalNode G rich mask w child

/-- Pair-root bits of a latent assignment, read as `Bool`. -/
def hedgePairBitsOf (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment)
    (root : Fin (pairRootCount G)) : Bool :=
  cast (hedgeLatentValue_pair G root) (u (hedgePairRoot G root))

/-- The pair-root coordinate is exactly the `Bool` embedding of `hedgePairBitsOf`. -/
theorem hedgePairBitsOf_cast (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment)
    (root : Fin (pairRootCount G)) :
    u (hedgePairRoot G root) =
      cast (hedgeLatentValue_pair G root).symm
        (hedgePairBitsOf G u root) := by
  unfold hedgePairBitsOf
  rw [cast_cast]
  exact (cast_eq _ _).symm

/--
Invert `hedgePrivateIndex` at the canonical private root of an observed
node.  Both sides live at `hedgePrivateRoot child`, so the `Fin` cards
match by `hedgeChildOfPrivate_privateRoot` and the dependent root-walk
is avoided.
-/
theorem hedgePrivateIndex_inv_at_child (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    cast
      (hedgeLatentValue_eq_fin G (hedgePrivateRoot G child)
        (hedgePrivateRoot_not_pair G child)).symm
      ((hedgePrivateIndex G child (fun root _ => u root)).cast
        (by rw [hedgeChildOfPrivate_privateRoot])) =
      u (hedgePrivateRoot G child) := by
  have e :=
    hedgeLatentValue_eq_fin G (hedgePrivateRoot G child)
      (hedgePrivateRoot_not_pair G child)
  have hfin :
      (hedgePrivateIndex G child (fun root _ => u root)).cast
          (by rw [hedgeChildOfPrivate_privateRoot]) =
        cast e (u (hedgePrivateRoot G child)) := by
    unfold hedgePrivateIndex
    simp [Fin.cast]
  rw [hfin, cast_cast]
  exact cast_eq _ _

/-- XOR of selected pair-root bits incident to `child`. -/
def hedgeXorPairBitsFrom (G : ObservedGraph S) (child : Fin S.count)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) : Bool :=
  (List.finRange (pairRootCount G)).foldl
    (fun acc root =>
      if (hedgeLatentExtension G).incident (hedgePairRoot G root) child then
        Bool.xor acc (pairBits root)
      else acc)
    false

/-- Forest-restricted pair parity read from an ordinary Boolean root vector. -/
def hedgeXorPairBitsWithinFrom (G : ObservedGraph S)
    (nodes : NodeSet S) (child : Fin S.count)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) : Bool :=
  (List.finRange (pairRootCount G)).foldl
    (fun acc root =>
      if (hedgeLatentExtension G).incident (hedgePairRoot G root) child &&
          hedgePairRootWithin G nodes root then
        Bool.xor acc (pairBits root)
      else acc)
    false

/-- Pointwise addition of pair-root vectors over `Bool` parity. -/
def hedgePairBitsXor (G : ObservedGraph S)
    (left right : (root : Fin (pairRootCount G)) → Bool) :
    (root : Fin (pairRootCount G)) → Bool :=
  fun root => Bool.xor (left root) (right root)

/-- The zero pair-root vector. -/
def hedgeZeroPairBits (G : ObservedGraph S) :
    (root : Fin (pairRootCount G)) → Bool :=
  fun _root => false

/-- The zero vector induces zero incidence parity at every node. -/
theorem hedgeXorPairBitsWithinFrom_zero
    (G : ObservedGraph S) (nodes : NodeSet S)
    (child : Fin S.count) :
    hedgeXorPairBitsWithinFrom G nodes child (hedgeZeroPairBits G) = false := by
  unfold hedgeXorPairBitsWithinFrom hedgeZeroPairBits
  refine foldl_unchanged _ false (List.finRange (pairRootCount G)) ?_
  intro acc root
  cases
      ((hedgeLatentExtension G).incident (hedgePairRoot G root) child &&
        hedgePairRootWithin G nodes root) <;> simp

/-- Forest incidence parity is linear in the pair-root vector. -/
theorem hedgeXorPairBitsWithinFrom_xor
    (G : ObservedGraph S) (nodes : NodeSet S)
    (child : Fin S.count)
    (left right : (root : Fin (pairRootCount G)) → Bool) :
    hedgeXorPairBitsWithinFrom G nodes child
        (hedgePairBitsXor G left right) =
      Bool.xor
        (hedgeXorPairBitsWithinFrom G nodes child left)
        (hedgeXorPairBitsWithinFrom G nodes child right) := by
  let selected : Fin (pairRootCount G) → Bool := fun root =>
    (hedgeLatentExtension G).incident (hedgePairRoot G root) child &&
      hedgePairRootWithin G nodes root
  let leftSelected : Fin (pairRootCount G) → Bool := fun root =>
    if selected root then left root else false
  let rightSelected : Fin (pairRootCount G) → Bool := fun root =>
    if selected root then right root else false
  have combined :
      hedgeXorPairBitsWithinFrom G nodes child
          (hedgePairBitsXor G left right) =
        (List.finRange (pairRootCount G)).foldl
          (fun acc root =>
            Bool.xor acc
              (Bool.xor (leftSelected root) (rightSelected root))) false := by
    change
      (List.finRange (pairRootCount G)).foldl
          (fun acc root =>
            if selected root then
              Bool.xor acc (Bool.xor (left root) (right root))
            else acc) false = _
    refine foldl_congr _ _ _ _ ?_
    intro acc root
    cases hselected : selected root <;>
      simp [leftSelected, rightSelected, hselected]
  have leftFold :
      (List.finRange (pairRootCount G)).foldl
          (fun acc root => Bool.xor acc (leftSelected root)) false =
        hedgeXorPairBitsWithinFrom G nodes child left := by
    change _ =
      (List.finRange (pairRootCount G)).foldl
        (fun acc root =>
          if selected root then Bool.xor acc (left root) else acc) false
    refine foldl_congr _ _ _ _ ?_
    intro acc root
    cases hselected : selected root <;>
      simp [leftSelected, hselected]
  have rightFold :
      (List.finRange (pairRootCount G)).foldl
          (fun acc root => Bool.xor acc (rightSelected root)) false =
        hedgeXorPairBitsWithinFrom G nodes child right := by
    change _ =
      (List.finRange (pairRootCount G)).foldl
        (fun acc root =>
          if selected root then Bool.xor acc (right root) else acc) false
    refine foldl_congr _ _ _ _ ?_
    intro acc root
    cases hselected : selected root <;>
      simp [rightSelected, hselected]
  rw [combined, foldl_xor_pointwise, leftFold, rightFold]

/-- The dependent-input and root-vector presentations compute the same bit. -/
theorem hedgeXorPairBitsWithin_pairBitsOf
    (G : ObservedGraph S) (nodes : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count) :
    hedgeXorPairBitsWithin G nodes child (fun root _ => u root) =
      hedgeXorPairBitsWithinFrom G nodes child (hedgePairBitsOf G u) := by
  unfold hedgeXorPairBitsWithin hedgeXorPairBitsWithinFrom hedgePairBitsOf
  refine foldl_congr _ _ _ _ ?_
  intro acc root
  if hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true then
    cases hwithin : hedgePairRootWithin G nodes root <;>
      simp [hinc]
  else
    simp [hinc]

/--
Latent assignment that realises `target` with prescribed pair-root bits.
Privates are the unique `ValueRich` preimage under the parent-bit toggle
of `mask` together with those pair-root bits.  Pair-roots are free; every
observed atom therefore has the same number of equal-weight preimages in
every `hedgeModel`.
-/
def hedgeSupportLatentWithPairs (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (root : Fin (hedgeLatentCount G)) : hedgeLatentValue G root :=
  if h : root.val < pairRootCount G then
    cast (hedgeLatentValue_eq_bool G root h).symm (pairBits ⟨root.val, h⟩)
  else
    let child := hedgeChildOfPrivate G root h
    let needed :=
      hedgeParentBitsFrom rich mask child (fun parent _ => target parent)
    let xorBits := hedgeXorPairBitsFrom G child pairBits
    cast (hedgeLatentValue_eq_fin G root h).symm
      (hedgeIndexOfValue S child
        (hedgeToggle rich child (Bool.xor xorBits needed) (target child)))

theorem hedgeSupportLatentWithPairs_pair (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (root : Fin (pairRootCount G)) :
    cast (hedgeLatentValue_pair G root)
      (hedgeSupportLatentWithPairs G rich mask target pairBits
        (hedgePairRoot G root)) =
      pairBits root := by
  simp [hedgeSupportLatentWithPairs, hedgePairRoot]

theorem hedgeXorPairBits_supportWithPairs (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (child : Fin S.count) :
    hedgeXorPairBits G child
        (fun root _ =>
          hedgeSupportLatentWithPairs G rich mask target pairBits root) =
      hedgeXorPairBitsFrom G child pairBits := by
  unfold hedgeXorPairBits hedgeXorPairBitsFrom
  refine foldl_congr _ _ _ _ ?_
  intro acc root
  if hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) child then
    simp [hinc, hedgeSupportLatentWithPairs_pair G rich mask target pairBits root]
  else
    simp [hinc]

theorem hedgeSupportLatentWithPairs_private (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (child : Fin S.count) :
    hedgePrivateIndex G child
        (fun root _ =>
          hedgeSupportLatentWithPairs G rich mask target pairBits root) =
      hedgeIndexOfValue S child
        (hedgeToggle rich child
          (Bool.xor (hedgeXorPairBitsFrom G child pairBits)
            (hedgeParentBitsFrom rich mask child
              (fun parent _ => target parent)))
          (target child)) := by
  apply Fin.ext
  unfold hedgePrivateIndex hedgeIndexOfValue
  simp [hedgeSupportLatentWithPairs, hedgePrivateRoot_not_pair, hedgeIndexOfValue]
  exact congrArg (fun node : Fin S.count =>
      (S.valueEnumeration node).idxOf
        (hedgeToggle rich node
          (Bool.xor (hedgeXorPairBitsFrom G node pairBits)
            (hedgeParentBitsFrom rich mask node
              (fun parent _ => target parent)))
          (target node)))
    (hedgeChildOfPrivate_privateRoot G child)

theorem hedgeModel_evalNode_supportWithPairs
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S) (target : S.Assignment)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (child : Fin S.count) :
    (hedgeModel G rich mask).evalNodeUnder (FiniteLatentSCM.noIntervention S)
      (hedgeSupportLatentWithPairs G rich mask target pairBits) child =
      target child := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp [hedgeModel]
  have hxor :=
    hedgeXorPairBits_supportWithPairs G rich mask target pairBits child
  rw [hxor]
  refine
    (congrArg
        (fun bit =>
          hedgeToggle rich child
            (Bool.xor (hedgeXorPairBitsFrom G child pairBits) bit)
            (hedgePrivateDecode S child
              (hedgePrivateIndex G child
                (fun latent _ =>
                  hedgeSupportLatentWithPairs G rich mask target pairBits
                    latent))))
        (hedgeParentBitsFrom_congr rich mask child
          (fun parent hp =>
            hedgeModel_evalNode_supportWithPairs G rich mask target pairBits
              parent))).trans
      ?_
  rw [hedgeSupportLatentWithPairs_private, hedgePrivateDecode_index,
    hedgeToggle_involution]
termination_by child.val
decreasing_by
  exact S.directed_earlier hp

theorem hedgeModel_eval_supportWithPairs (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) :
    (hedgeModel G rich mask).eval
        (hedgeSupportLatentWithPairs G rich mask target pairBits) =
      target := by
  funext child
  exact hedgeModel_evalNode_supportWithPairs G rich mask target pairBits child

/-- Pair-root bits recovered from a latent assignment match the stored `Bool`s. -/
theorem hedgePairBitsOf_supportWithPairs (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) :
    hedgePairBitsOf G
        (hedgeSupportLatentWithPairs G rich mask target pairBits) =
      pairBits := by
  funext root
  exact hedgeSupportLatentWithPairs_pair G rich mask target pairBits root

/-- The mechanism XOR of pair-roots is the XOR of recovered pair-bits. -/
theorem hedgeXorPairBits_pairBitsOf (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    hedgeXorPairBits G child (fun root _ => u root) =
      hedgeXorPairBitsFrom G child (hedgePairBitsOf G u) := by
  unfold hedgeXorPairBits hedgeXorPairBitsFrom hedgePairBitsOf
  refine foldl_congr _ _ _ _ ?_
  intro acc root
  if hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) child then
    simp [hinc]
  else
    simp [hinc]

/-- Pair-root embedding of a `Fin` index recovers that index. -/
theorem hedgePairRoot_of_lt (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G))
    (h : root.val < pairRootCount G) :
    hedgePairRoot G ⟨root.val, h⟩ = root := by
  apply Fin.ext
  simp [hedgePairRoot]

/--
Mechanism evaluation at an observed node, rewritten through the recovered
pair-bits and the observed assignment.  Used to invert the private index.
-/
theorem hedgeModel_toggle_eq_of_eval (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (target : S.Assignment)
    (heval : (hedgeModel G rich mask).eval u = target)
    (child : Fin S.count) :
    hedgeToggle rich child
      (Bool.xor (hedgeXorPairBitsFrom G child (hedgePairBitsOf G u))
        (hedgeParentBitsFrom rich mask child (fun _ _ => target _)))
      (hedgePrivateDecode S child
        (hedgePrivateIndex G child (fun root _ => u root))) =
      target child := by
  have hnode :
      (hedgeModel G rich mask).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child =
        target child :=
    congrFun heval child
  rw [FiniteLatentSCM.evalNodeUnder] at hnode
  have hmech :
      (hedgeModel G rich mask).equationUnder
          (FiniteLatentSCM.noIntervention S) child
          (fun parent _ =>
            (hedgeModel G rich mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent)
          (fun latent _ => u latent) =
        (hedgeModel G rich mask).mechanism child
          (fun parent _ =>
            (hedgeModel G rich mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent)
          (fun latent _ => u latent) := by
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    rfl
  rw [hmech] at hnode
  have hdef :
      (hedgeModel G rich mask).mechanism child
          (fun parent _ =>
            (hedgeModel G rich mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent)
          (fun latent _ => u latent) =
        hedgeToggle rich child
          (Bool.xor
            (hedgeXorPairBits G child (fun latent _ => u latent))
            (hedgeParentBitsFrom rich mask child
              (fun parent _ =>
                (hedgeModel G rich mask).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent)))
          (hedgePrivateDecode S child
            (hedgePrivateIndex G child (fun latent _ => u latent))) :=
    rfl
  rw [hdef] at hnode
  have hxor := hedgeXorPairBits_pairBitsOf G u child
  have hpar :
      hedgeParentBitsFrom rich mask child
          (fun parent _ =>
            (hedgeModel G rich mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent) =
        hedgeParentBitsFrom rich mask child (fun _ _ => target _) :=
    hedgeParentBitsFrom_congr rich mask child (fun parent _ =>
      congrFun heval parent)
  rw [hxor, hpar] at hnode
  exact hnode

/--
The private index of a realising assignment is the `ValueRich` preimage
under the parent-bit toggle of the recovered pair-bits.  Both sides are
`Fin (hedgePrivateCard child)`, so no dependent root-walk is required.
-/
theorem hedgeModel_privateIndex_of_eval (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (target : S.Assignment)
    (heval : (hedgeModel G rich mask).eval u = target)
    (child : Fin S.count) :
    hedgePrivateIndex G child (fun root _ => u root) =
      hedgeIndexOfValue S child
        (hedgeToggle rich child
          (Bool.xor (hedgeXorPairBitsFrom G child (hedgePairBitsOf G u))
            (hedgeParentBitsFrom rich mask child (fun _ _ => target _)))
          (target child)) := by
  have htoggle := hedgeModel_toggle_eq_of_eval G rich mask u target heval child
  have hdecode :
      hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _ => u root)) =
        hedgeToggle rich child
          (Bool.xor (hedgeXorPairBitsFrom G child (hedgePairBitsOf G u))
            (hedgeParentBitsFrom rich mask child (fun _ _ => target _)))
          (target child) := by
    have hbit :=
      congrArg
        (hedgeToggle rich child
          (Bool.xor (hedgeXorPairBitsFrom G child (hedgePairBitsOf G u))
            (hedgeParentBitsFrom rich mask child (fun _ _ => target _))))
        htoggle
    rw [hedgeToggle_involution] at hbit
    exact hbit
  have hidx :=
    congrArg (hedgeIndexOfValue S child) hdecode
  rw [hedgeIndexOf_decode] at hidx
  exact hidx

/--
A realising assignment agrees with `hedgeSupportLatentWithPairs` at the
canonical private root of an observed node.
-/
theorem hedgeEq_supportWithPairs_at_privateRoot (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (target : S.Assignment)
    (heval : (hedgeModel G rich mask).eval u = target)
    (child : Fin S.count) :
    u (hedgePrivateRoot G child) =
      hedgeSupportLatentWithPairs G rich mask target (hedgePairBitsOf G u)
        (hedgePrivateRoot G child) := by
  have hidx :=
    hedgeModel_privateIndex_of_eval G rich mask u target heval child
  have hinv := hedgePrivateIndex_inv_at_child G u child
  rw [← hinv]
  unfold hedgeSupportLatentWithPairs
  rw [dif_neg (hedgePrivateRoot_not_pair G child)]
  apply congrArg
  apply Fin.ext
  simp only [hidx, Fin.cast]
  have hnode := hedgeChildOfPrivate_privateRoot G child
  rw [hnode]

/--
Every realising latent assignment is exactly the pair-bit support of its
own recovered pair-bits.  Pair-roots are free; privates are forced.
-/
theorem hedgeEq_supportWithPairs_of_eval (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (target : S.Assignment)
    (heval : (hedgeModel G rich mask).eval u = target) :
    u =
      hedgeSupportLatentWithPairs G rich mask target (hedgePairBitsOf G u) := by
  funext root
  if h : root.val < pairRootCount G then
    have hpr := hedgePairRoot_of_lt G root h
    rw [← hpr]
    exact
      (hedgePairBitsOf_cast G u ⟨root.val, h⟩).trans
        (by
          unfold hedgeSupportLatentWithPairs
          have hlt :
              (hedgePairRoot G ⟨root.val, h⟩).val < pairRootCount G := by
            simp [hedgePairRoot]
            exact h
          rw [dif_pos hlt]
          simp [hedgePairRoot])
  else
    have hr := hedgePrivateRoot_of_childOfPrivate G root h
    rw [← hr]
    exact hedgeEq_supportWithPairs_at_privateRoot G rich mask u target heval
      (hedgeChildOfPrivate G root h)

/-- Decidable equality of pair-bit assignments. -/
instance (G : ObservedGraph S) :
    DecidableEq ((root : Fin (pairRootCount G)) → Bool) :=
  FiniteProduct.assignmentDecidableEq (pairRootCount G) (fun _ => Bool)
    (fun _ => inferInstance)

/-- Decidable equality of hedge latent assignments as raw dependent functions. -/
instance (G : ObservedGraph S) :
    DecidableEq ((root : Fin (hedgeLatentCount G)) → hedgeLatentValue G root) :=
  FiniteProduct.assignmentDecidableEq (hedgeLatentCount G) (hedgeLatentValue G)
    (fun _ => inferInstance)

/-- Every Boolean appears in the two-element enumeration. -/
theorem mem_bool_two (b : Bool) : b ∈ ([false, true] : List Bool) := by
  cases b with
  | false =>
      exact List.mem_cons_self
  | true =>
      exact List.mem_cons_of_mem _ List.mem_cons_self

/--
Duplicate-free enumeration of pair-root bit assignments.  This indexes the
equal-weight observational preimages of every `hedgeModel`.
-/
def hedgePairBitEnum (G : ObservedGraph S) :
    List ((root : Fin (pairRootCount G)) → Bool) :=
  deduplicate
    (FiniteProduct.enumeration (pairRootCount G) (fun _ => Bool)
      (fun _ => [false, true]))

theorem hedgePairBitEnum_complete (G : ObservedGraph S)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) :
    pairBits ∈ hedgePairBitEnum G := by
  unfold hedgePairBitEnum
  rw [mem_deduplicate]
  exact FiniteProduct.enumeration_complete (pairRootCount G)
    (fun _ => Bool) (fun _ => [false, true])
    (fun _ => mem_bool_two) pairBits

theorem hedgePairBitEnum_nodup (G : ObservedGraph S) :
    (hedgePairBitEnum G).Nodup := by
  unfold hedgePairBitEnum
  exact deduplicate_nodup _

/-- Distinct pair-bit vectors produce distinct support assignments. -/
theorem hedgeSupportLatentWithPairs_injective (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment)
    {left right : (root : Fin (pairRootCount G)) → Bool}
    (heq :
      hedgeSupportLatentWithPairs G rich mask target left =
        hedgeSupportLatentWithPairs G rich mask target right) :
    left = right := by
  have hleft :=
    hedgePairBitsOf_supportWithPairs G rich mask target left
  have hright :=
    hedgePairBitsOf_supportWithPairs G rich mask target right
  exact hleft.symm.trans (congrArg (hedgePairBitsOf G) heq |>.trans hright)

/--
Observed evaluation hits `target` exactly on the pair-bit support family.
Pair-roots remain free; every observational atom therefore has the same
number of realising latents in every `hedgeModel`.
-/
theorem hedgeModel_eval_mem_support (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (target : S.Assignment) :
    (hedgeModel G rich mask).eval u = target ↔
      u ∈
        (hedgePairBitEnum G).map
          (hedgeSupportLatentWithPairs G rich mask target) := by
  constructor
  · intro heval
    have hu :=
      hedgeEq_supportWithPairs_of_eval G rich mask u target heval
    rw [hu]
    exact List.mem_map_of_mem
      (hedgePairBitEnum_complete G (hedgePairBitsOf G u))
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pairBits, _, heq⟩
    rw [← heq]
    exact hedgeModel_eval_supportWithPairs G rich mask target pairBits

/-- The observational singleton of an observed atom is the membership event
of that atom's pair-bit realisers. -/
theorem hedgeModel_eval_singleton_eq_membership (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment) :
    (fun u =>
        FiniteProbRecord.singletonEvent target
          ((hedgeModel G rich mask).eval u)) =
      FiniteProbRecord.membershipEvent
        ((hedgePairBitEnum G).map
          (hedgeSupportLatentWithPairs G rich mask target)) := by
  funext u
  unfold FiniteProbRecord.singletonEvent FiniteProbRecord.membershipEvent
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  exact hedgeModel_eval_mem_support G rich mask u target

/-- Ones-weighted hedge factors put mass one on every enumerated atom. -/
theorem hedgeFactor_singleton_mass (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) (value : hedgeLatentValue G root) :
    FiniteProbRecord.eventMass (hedgeLatentFactor G root).atoms
      (FiniteProbRecord.singletonEvent value) = 1 :=
  eventMass_ones_singleton (hedgeLatentEnum G root)
    (hedgeLatentEnum_complete G root value)
    (hedgeLatentEnum_nodup G root)

theorem natProduct_one (n : Nat) :
    FiniteProduct.natProduct n (fun _ => 1) = 1 := by
  induction n with
  | zero =>
      simp [FiniteProduct.natProduct]
  | succ n ih =>
      simp [FiniteProduct.natProduct, ih]

/-- A rectangular of coordinate singletons is the assignment singleton. -/
theorem hedgeRectangular_eq_singleton (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment) :
    FiniteProduct.rectangularEvent (hedgeLatentCount G) (hedgeLatentValue G)
        (fun root value => decide (value = u root)) =
      FiniteProbRecord.singletonEvent u := by
  funext w
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hrect
    have hpt :=
      (FiniteProduct.rectangularEvent_eq_true_iff (hedgeLatentCount G)
          (hedgeLatentValue G)
          (fun root value => decide (value = u root)) w).mp hrect
    have heq : w = u := funext fun root => of_decide_eq_true (hpt root)
    simp [FiniteProbRecord.singletonEvent, heq]
  · intro hsing
    have heq : w = u :=
      of_decide_eq_true (by simpa [FiniteProbRecord.singletonEvent] using hsing)
    exact
      (FiniteProduct.rectangularEvent_eq_true_iff (hedgeLatentCount G)
          (hedgeLatentValue G)
          (fun root value => decide (value = u root)) w).mpr
        (fun root => by simp [heq])

/-- Every hedge latent atom carries the same prior numerator. -/
theorem hedgePrior_eventMass_singleton (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment) :
    FiniteProbRecord.eventMass
        (FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).atoms
        (FiniteProbRecord.singletonEvent u) =
      1 := by
  refine
    (FiniteProbRecord.eventMass_congr
        (FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).atoms
        (FiniteProbRecord.singletonEvent u)
        (FiniteProduct.rectangularEvent (hedgeLatentCount G)
          (hedgeLatentValue G)
          (fun root value => decide (value = u root)))
        (fun w =>
          congrFun (hedgeRectangular_eq_singleton G u).symm w)).trans ?_
  have hmass :=
    FiniteProduct.eventMass_atoms (hedgeLatentCount G) (hedgeLatentValue G)
      (hedgeLatentFactor G)
      (fun root value => decide (value = u root))
  have hones :
      FiniteProduct.natProduct (hedgeLatentCount G)
          (fun root =>
            FiniteProbRecord.eventMass (hedgeLatentFactor G root).atoms
              (fun value => decide (value = u root))) =
        1 := by
    have hcoord :
        (fun root =>
            FiniteProbRecord.eventMass (hedgeLatentFactor G root).atoms
              (fun value => decide (value = u root))) =
          fun _ => 1 :=
      funext fun root => by
        simpa [FiniteProbRecord.singletonEvent] using
          hedgeFactor_singleton_mass G root (u root)
    simpa [hcoord] using natProduct_one (hedgeLatentCount G)
  simpa [FiniteProduct.record] using hmass.trans hones

/-- The shared hedge prior is independent of the parent-bit mask. -/
theorem hedgeModel_prior_eq (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask mask' : NodeSet S) :
    (hedgeModel G rich mask).prior = (hedgeModel G rich mask').prior :=
  rfl

/-- All hedge latent atoms have equivalent prior mass. -/
theorem hedgePrior_singleton_equiv (G : ObservedGraph S)
    (u w : (hedgeLatentExtension G).Assignment) :
    QProb.Equiv
      ((FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).probVal
        (FiniteProbRecord.singletonEvent u))
      ((FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).probVal
        (FiniteProbRecord.singletonEvent w)) := by
  simp [QProb.Equiv, FiniteProbRecord.probVal,
    hedgePrior_eventMass_singleton G u,
    hedgePrior_eventMass_singleton G w]

/--
Observational atoms of any two `hedgeModel`s agree: each observed point is
the image of the same number of equal-weight pair-bit realisers, and the
prior does not depend on the parent-bit mask.
-/
theorem hedgeModel_observational_singleton_equiv (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment) :
    QProb.Equiv
      ((hedgeBaseModel G rich).observationalValue
        (FiniteProbRecord.singletonEvent target))
      ((hedgeModel G rich mask).observationalValue
        (FiniteProbRecord.singletonEvent target)) := by
  have hleft :=
    FiniteLatentSCM.observationalValue_eq (hedgeBaseModel G rich)
      (FiniteProbRecord.singletonEvent target)
  have hright :=
    FiniteLatentSCM.observationalValue_eq (hedgeModel G rich mask)
      (FiniteProbRecord.singletonEvent target)
  have hmemLeft :=
    hedgeModel_eval_singleton_eq_membership G rich NodeSet.empty target
  have hmemRight :=
    hedgeModel_eval_singleton_eq_membership G rich mask target
  have hevalMemLeft :
      QProb.Equiv
        ((hedgeBaseModel G rich).prior.probVal
          (fun u =>
            FiniteProbRecord.singletonEvent target
              ((hedgeBaseModel G rich).eval u)))
        ((hedgeBaseModel G rich).prior.probVal
          (FiniteProbRecord.membershipEvent
            ((hedgePairBitEnum G).map
              (hedgeSupportLatentWithPairs G rich NodeSet.empty target)))) := by
    unfold QProb.Equiv FiniteProbRecord.probVal
    refine congrArg (fun mass => mass * (hedgeBaseModel G rich).prior.den) ?_
    exact FiniteProbRecord.eventMass_congr
      (hedgeBaseModel G rich).prior.atoms
      (fun u =>
        FiniteProbRecord.singletonEvent target
          ((hedgeBaseModel G rich).eval u))
      (FiniteProbRecord.membershipEvent
        ((hedgePairBitEnum G).map
          (hedgeSupportLatentWithPairs G rich NodeSet.empty target)))
      (fun u => by
        simpa [hedgeBaseModel] using congrFun hmemLeft u)
  have hevalMemRight :
      QProb.Equiv
        ((hedgeModel G rich mask).prior.probVal
          (fun u =>
            FiniteProbRecord.singletonEvent target
              ((hedgeModel G rich mask).eval u)))
        ((hedgeModel G rich mask).prior.probVal
          (FiniteProbRecord.membershipEvent
            ((hedgePairBitEnum G).map
              (hedgeSupportLatentWithPairs G rich mask target)))) := by
    unfold QProb.Equiv FiniteProbRecord.probVal
    refine congrArg (fun mass => mass * (hedgeModel G rich mask).prior.den) ?_
    exact FiniteProbRecord.eventMass_congr
      (hedgeModel G rich mask).prior.atoms
      (fun u =>
        FiniteProbRecord.singletonEvent target
          ((hedgeModel G rich mask).eval u))
      (FiniteProbRecord.membershipEvent
        ((hedgePairBitEnum G).map
          (hedgeSupportLatentWithPairs G rich mask target)))
      (fun u => congrFun hmemRight u)
  have hsumLeft :=
    FiniteProbRecord.probVal_membership_equiv_listSum
      (hedgeBaseModel G rich).prior
      ((hedgePairBitEnum G).map
        (hedgeSupportLatentWithPairs G rich NodeSet.empty target))
      (nodup_map_of_injective
        (fun left right heq =>
          hedgeSupportLatentWithPairs_injective G rich NodeSet.empty target heq)
        (hedgePairBitEnum_nodup G))
  have hsumRight :=
    FiniteProbRecord.probVal_membership_equiv_listSum
      (hedgeModel G rich mask).prior
      ((hedgePairBitEnum G).map
        (hedgeSupportLatentWithPairs G rich mask target))
      (nodup_map_of_injective
        (fun left right heq =>
          hedgeSupportLatentWithPairs_injective G rich mask target heq)
        (hedgePairBitEnum_nodup G))
  have hmapLeft :
      List.map
          (fun value =>
            (hedgeBaseModel G rich).prior.probVal
              (FiniteProbRecord.singletonEvent value))
          (List.map
            (hedgeSupportLatentWithPairs G rich NodeSet.empty target)
            (hedgePairBitEnum G)) =
        List.map
          (fun pairBits =>
            (hedgeBaseModel G rich).prior.probVal
              (FiniteProbRecord.singletonEvent
                (hedgeSupportLatentWithPairs G rich NodeSet.empty target
                  pairBits)))
          (hedgePairBitEnum G) :=
    List.map_map
  have hmapRight :
      List.map
          (fun value =>
            (hedgeModel G rich mask).prior.probVal
              (FiniteProbRecord.singletonEvent value))
          (List.map
            (hedgeSupportLatentWithPairs G rich mask target)
            (hedgePairBitEnum G)) =
        List.map
          (fun pairBits =>
            (hedgeModel G rich mask).prior.probVal
              (FiniteProbRecord.singletonEvent
                (hedgeSupportLatentWithPairs G rich mask target pairBits)))
          (hedgePairBitEnum G) :=
    List.map_map
  have hprior :
      (hedgeBaseModel G rich).prior = (hedgeModel G rich mask).prior :=
    hedgeModel_prior_eq G rich NodeSet.empty mask
  have hconst :
      QProb.Equiv
        (QProb.listSum
          ((hedgePairBitEnum G).map (fun pairBits =>
            (hedgeBaseModel G rich).prior.probVal
              (FiniteProbRecord.singletonEvent
                (hedgeSupportLatentWithPairs G rich NodeSet.empty target
                  pairBits)))))
        (QProb.listSum
          ((hedgePairBitEnum G).map (fun pairBits =>
            (hedgeModel G rich mask).prior.probVal
              (FiniteProbRecord.singletonEvent
                (hedgeSupportLatentWithPairs G rich mask target
                  pairBits))))) := by
    refine QProb.listSum_map_congr (hedgePairBitEnum G) _ _ ?_
    intro pairBits
    rw [hprior]
    exact hedgePrior_singleton_equiv G
      (hedgeSupportLatentWithPairs G rich NodeSet.empty target pairBits)
      (hedgeSupportLatentWithPairs G rich mask target pairBits)
  refine QProb.equiv_trans hleft ?_
  refine QProb.equiv_trans hevalMemLeft ?_
  refine QProb.equiv_trans hsumLeft ?_
  rw [hmapLeft]
  refine QProb.equiv_trans hconst ?_
  rw [← hmapRight]
  refine QProb.equiv_trans (QProb.equiv_symm hsumRight) ?_
  refine QProb.equiv_trans (QProb.equiv_symm hevalMemRight) ?_
  exact QProb.equiv_symm hright

/--
Any two parent-bit masks induce observationally equivalent hedge models.
The empty mask (base) versus an arbitrary mask is the most general statement;
the copy model is the full-mask special case.
-/
theorem hedgeModel_observationally_equivalent (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    ObservationallyEquivalent (hedgeBaseModel G rich)
      (hedgeModel G rich mask) := by
  intro event
  exact FiniteProbRecord.probVal_extensional_of_singletons
    (hedgeBaseModel G rich).observationalDist
    (hedgeModel G rich mask).observationalDist
    S.assignmentEnumeration
    S.assignmentEnumeration_nodup
    S.assignmentEnumeration_complete
    (fun target =>
      hedgeModel_observational_singleton_equiv G rich mask target)
    event

theorem hedgeBaseModel_observationally_equivalent_copy (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) :
    ObservationallyEquivalent (hedgeBaseModel G rich)
      (hedgeCopyModel G rich) :=
  hedgeModel_observationally_equivalent G rich NodeSet.full

/--
Nonlinear hedge mechanism: when the incident pair-root XOR is true, the
node copies a `ValueRich` label of its masked parents; otherwise it emits
its private decode.  XOR-plus-uniform copies preserve interventional
margins; this switch does not, because the copy branch is a constant under
`do(X)`.
-/
def hedgeMixFrom (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (switch parentBit : Bool)
    (base : S.Value child) : S.Value child :=
  if switch then
    if parentBit then rich.second child else rich.first child
  else
    base

/--
Same skeleton and product prior as `hedgeModel`, with the mix mechanism in
place of the parent-bit XOR.  Pair-roots remain graph-incident; the empty
mask recovers a parent-ignoring mix (switch copies `first`).
-/
def hedgeMixModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    ExactModel S where
  latent := hedgeLatentExtension G
  factor := hedgeLatentFactor G
  prior :=
    FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
      (hedgeLatentFactor G)
  product_law := fun events => by
    simpa [LatentExtension.rectangularEvent, hedgeLatentExtension] using
      FiniteProduct.record_rectangular_probVal
        (hedgeLatentCount G) (hedgeLatentValue G) (hedgeLatentFactor G) events
  mechanism := fun child parents inputs =>
    hedgeMixFrom rich child
      (hedgeXorPairBits G child inputs)
      (hedgeParentBitsFrom rich mask child parents)
      (hedgePrivateDecode S child (hedgePrivateIndex G child inputs))

theorem hedgeMixModel_compatible (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    Compatible (hedgeMixModel G rich mask) G :=
  ⟨hedgeLatentExtension_canonical G, fun i j => by
    simpa [FiniteLatentSCM.observedGraph, LatentExtension.observedGraph,
      hedgeMixModel] using hedgeLatentExtension_projected G i j⟩

theorem hedgeMixFrom_false (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (parentBit : Bool) (base : S.Value child) :
    hedgeMixFrom rich child false parentBit base = base :=
  rfl

theorem hedgeMixFrom_true_second (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (base : S.Value child) :
    hedgeMixFrom rich child true true base = rich.second child :=
  rfl

theorem hedgeMixFrom_true_first (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (base : S.Value child) :
    hedgeMixFrom rich child true false base = rich.first child :=
  rfl

/--
All-false pair-roots make the mix reduce to the private decode, so the
empty-mask support of `hedgeModel` realises every observed atom in every
`hedgeMixModel` as well.
-/
theorem hedgeMixModel_evalNode_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S) (target : S.Assignment) (child : Fin S.count) :
    (hedgeMixModel G rich mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (hedgeSupportLatent G rich NodeSet.empty target) child =
      target child := by
  rw [FiniteLatentSCM.evalNodeUnder]
  have hmech :
      (hedgeMixModel G rich mask).equationUnder
          (FiniteLatentSCM.noIntervention S) child
          (fun parent _ =>
            (hedgeMixModel G rich mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S)
              (hedgeSupportLatent G rich NodeSet.empty target) parent)
          (fun latent _ =>
            hedgeSupportLatent G rich NodeSet.empty target latent) =
        (hedgeMixModel G rich mask).mechanism child
          (fun parent _ =>
            (hedgeMixModel G rich mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S)
              (hedgeSupportLatent G rich NodeSet.empty target) parent)
          (fun latent _ =>
            hedgeSupportLatent G rich NodeSet.empty target latent) := by
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    rfl
  rw [hmech]
  have hxor :
      hedgeXorPairBits G child
          (fun latent _ =>
            hedgeSupportLatent G rich NodeSet.empty target latent) =
        false :=
    hedgeXorPairBits_of_false_pair_roots G child _
      (fun root _ => hedgeSupportLatent_pair G rich NodeSet.empty target root)
  simp [hedgeMixModel, hxor, hedgeMixFrom_false]
  rw [hedgeSupportLatent_private, hedgeParentBitsFrom_empty, hedgeToggle_false,
    hedgePrivateDecode_index]

theorem hedgeMixModel_eval_support (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (target : S.Assignment) :
    (hedgeMixModel G rich mask).eval
        (hedgeSupportLatent G rich NodeSet.empty target) =
      target := by
  funext child
  exact hedgeMixModel_evalNode_support G rich mask target child

theorem hedgeMixModel_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    ObservationallyPositive (hedgeMixModel G rich mask) := by
  intro assignment
  have heval := hedgeMixModel_eval_support G rich mask assignment
  have hsubset :
      forall u,
        (hedgeLatentExtension G).rectangularEvent
            (fun root value =>
              decide
                (value = hedgeSupportLatent G rich NodeSet.empty assignment root))
            u = true →
          FiniteProbRecord.singletonEvent assignment
            ((hedgeMixModel G rich mask).eval u) = true := by
    intro u hrect
    have hu : u = hedgeSupportLatent G rich NodeSet.empty assignment := by
      funext root
      have hroot :=
        (FiniteProduct.rectangularEvent_eq_true_iff
            (hedgeLatentCount G) (hedgeLatentValue G)
            (fun root value =>
              decide
                (value =
                  hedgeSupportLatent G rich NodeSet.empty assignment root))
            u).mp
          (by simpa [LatentExtension.rectangularEvent, hedgeLatentExtension]
            using hrect) root
      exact of_decide_eq_true hroot
    simp [hu, heval, FiniteProbRecord.singletonEvent]
  have hmono :=
    FiniteProbRecord.eventMass_mono
      (hedgeMixModel G rich mask).prior.atoms _ _ hsubset
  have hrect := by
    simpa [hedgeMixModel, FiniteProduct.record, LatentExtension.rectangularEvent,
      hedgeLatentExtension] using
      FiniteProduct.eventMass_atoms (hedgeLatentCount G) (hedgeLatentValue G)
        (hedgeLatentFactor G)
        (fun root value =>
          decide
            (value = hedgeSupportLatent G rich NodeSet.empty assignment root))
  have hpos :=
    natProduct_pos _ _
      (fun root => by
        simpa [FiniteProbRecord.singletonEvent] using
          hedgeLatentFactor_support_pos G rich NodeSet.empty assignment root)
  have hprior :
      0 <
        FiniteProbRecord.eventMass
          (hedgeMixModel G rich mask).prior.atoms
          (fun u =>
            FiniteProbRecord.singletonEvent assignment
              ((hedgeMixModel G rich mask).eval u)) :=
    Nat.lt_of_lt_of_le (hrect ▸ hpos) hmono
  simpa [FiniteLatentSCM.observationalDist, FiniteProbRecord.probVal,
    FiniteProbRecord.map, hedgeMixModel, FiniteProbRecord.eventMass_map_labels]
    using hprior

theorem hedgeMixModel_mem_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S) :
    (GraphModelClass.positive G).Mem (hedgeMixModel G rich mask) :=
  ⟨hedgeMixModel_compatible G rich mask, hedgeMixModel_positive G rich mask⟩

/-!
### A mix localized to one pair-root

`hedgeMixModel` switches on the XOR of every pair-root incident to a node.
That makes its pointwise observational coupling require complete pair-root
incidence equality across each active directed edge.  For a bow, this is much
stronger than necessary: one common pair-root already supplies the random
switch used by the separation argument.

The model below ignores all other pair-roots in its mechanism while retaining
them in the latent extension.  Its projected graph therefore remains exactly
`G`, and the all-false pair-root assignment still realizes every observed
atom through private noise.  Localizing the switch, rather than deleting
latent coordinates, is what preserves both compatibility and positivity.
-/

/--
Read one selected pair-root at `child`, returning `false` when that root is
not incident to the child.  The dependent input is accessed only in the
incident branch.
-/
def hedgePairRootBit (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) (child : Fin S.count)
    (inputs : (hedgeLatentExtension G).Inputs child) : Bool :=
  if incident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true
  then
    cast (hedgeLatentValue_pair G root)
      (inputs (hedgePairRoot G root) incident)
  else
    false

/--
Positive hedge mix whose switch is one selected pair-root.  `mask` still
chooses the directed parents whose `second` bits are copied.
-/
def hedgeSingleRootMixModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S) : ExactModel S where
  latent := hedgeLatentExtension G
  factor := hedgeLatentFactor G
  prior :=
    FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
      (hedgeLatentFactor G)
  product_law := fun events => by
    simpa [LatentExtension.rectangularEvent, hedgeLatentExtension] using
      FiniteProduct.record_rectangular_probVal
        (hedgeLatentCount G) (hedgeLatentValue G) (hedgeLatentFactor G) events
  mechanism := fun child parents inputs =>
    hedgeMixFrom rich child
      (hedgePairRootBit G root child inputs)
      (hedgeParentBitsFrom rich mask child parents)
      (hedgePrivateDecode S child (hedgePrivateIndex G child inputs))

/-- Ignoring unused pair-roots does not change the model's projected graph. -/
theorem hedgeSingleRootMixModel_compatible (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S) :
    Compatible (hedgeSingleRootMixModel G rich root mask) G :=
  ⟨hedgeLatentExtension_canonical G, fun i j => by
    simpa [FiniteLatentSCM.observedGraph, LatentExtension.observedGraph,
      hedgeSingleRootMixModel] using hedgeLatentExtension_projected G i j⟩

/-- The all-false support assignment turns every selected-root switch off. -/
theorem hedgePairRootBit_support_false (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (target : S.Assignment)
    (child : Fin S.count) :
    hedgePairRootBit G root child
        (fun latent _ =>
          hedgeSupportLatent G rich NodeSet.empty target latent) = false := by
  unfold hedgePairRootBit
  split
  · next incident =>
      exact hedgeSupportLatent_pair G rich NodeSet.empty target root
  · rfl

/-- Every observed assignment has an explicit preimage in a root-local mix. -/
theorem hedgeSingleRootMixModel_evalNode_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (target : S.Assignment) (child : Fin S.count) :
    (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (hedgeSupportLatent G rich NodeSet.empty target) child =
      target child := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp only [hedgeSingleRootMixModel]
  rw [hedgePairRootBit_support_false G rich root target child,
    hedgeMixFrom_false]
  rw [hedgeSupportLatent_private, hedgeParentBitsFrom_empty,
    hedgeToggle_false, hedgePrivateDecode_index]

theorem hedgeSingleRootMixModel_eval_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (target : S.Assignment) :
    (hedgeSingleRootMixModel G rich root mask).eval
        (hedgeSupportLatent G rich NodeSet.empty target) = target := by
  funext child
  exact hedgeSingleRootMixModel_evalNode_support G rich root mask target child

/--
Every root-local mix is observationally positive.  A rectangular singleton
around the explicit all-false support assignment has positive product mass
and lies inside the requested observed singleton event.
-/
theorem hedgeSingleRootMixModel_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S) :
    ObservationallyPositive (hedgeSingleRootMixModel G rich root mask) := by
  intro assignment
  have evaluates :=
    hedgeSingleRootMixModel_eval_support G rich root mask assignment
  have subset :
      forall u,
        (hedgeLatentExtension G).rectangularEvent
            (fun latent value =>
              decide
                (value =
                  hedgeSupportLatent G rich NodeSet.empty assignment latent))
            u = true →
          FiniteProbRecord.singletonEvent assignment
            ((hedgeSingleRootMixModel G rich root mask).eval u) = true := by
    intro u rectangular
    have assignmentEq :
        u = hedgeSupportLatent G rich NodeSet.empty assignment := by
      funext latent
      have coordinate :=
        (FiniteProduct.rectangularEvent_eq_true_iff
            (hedgeLatentCount G) (hedgeLatentValue G)
            (fun index value =>
              decide
                (value =
                  hedgeSupportLatent G rich NodeSet.empty assignment index))
            u).mp
          (by simpa [LatentExtension.rectangularEvent, hedgeLatentExtension]
            using rectangular) latent
      exact of_decide_eq_true coordinate
    simp [assignmentEq, evaluates, FiniteProbRecord.singletonEvent]
  have monotone :=
    FiniteProbRecord.eventMass_mono
      (hedgeSingleRootMixModel G rich root mask).prior.atoms _ _ subset
  have rectangularMass := by
    simpa [hedgeSingleRootMixModel, FiniteProduct.record,
      LatentExtension.rectangularEvent, hedgeLatentExtension] using
      FiniteProduct.eventMass_atoms
        (hedgeLatentCount G) (hedgeLatentValue G) (hedgeLatentFactor G)
        (fun latent value =>
          decide
            (value =
              hedgeSupportLatent G rich NodeSet.empty assignment latent))
  have productPositive :=
    natProduct_pos _ _
      (fun latent => by
        simpa [FiniteProbRecord.singletonEvent] using
          hedgeLatentFactor_support_pos G rich NodeSet.empty assignment latent)
  have priorPositive :
      0 <
        FiniteProbRecord.eventMass
          (hedgeSingleRootMixModel G rich root mask).prior.atoms
          (fun u =>
            FiniteProbRecord.singletonEvent assignment
              ((hedgeSingleRootMixModel G rich root mask).eval u)) :=
    Nat.lt_of_lt_of_le (rectangularMass ▸ productPositive) monotone
  simpa [FiniteLatentSCM.observationalDist, FiniteProbRecord.probVal,
    FiniteProbRecord.map, hedgeSingleRootMixModel,
    FiniteProbRecord.eventMass_map_labels] using priorPositive

theorem hedgeSingleRootMixModel_mem_positive (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S) :
    (GraphModelClass.positive G).Mem
      (hedgeSingleRootMixModel G rich root mask) :=
  ⟨hedgeSingleRootMixModel_compatible G rich root mask,
    hedgeSingleRootMixModel_positive G rich root mask⟩

/-- Hard intervention that sets every selected node to its `ValueRich` second label. -/
def hedgeDoSecond (rich : ObservedSignature.ValueRich S) (action : NodeSet S) :
    (i : Fin S.count) -> Option (S.Value i) :=
  fun i => if action i then some (rich.second i) else none

theorem hedgeDoSecond_of_true (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) {i : Fin S.count} (h : action i = true) :
    hedgeDoSecond rich action i = some (rich.second i) := by
  simp [hedgeDoSecond, h]

theorem hedgeDoSecond_of_false (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) {i : Fin S.count} (h : action i = false) :
    hedgeDoSecond rich action i = none := by
  simp [hedgeDoSecond, h]

/-- Every indexed readout child remains free under the query intervention. -/
theorem HedgeWitness.parityReadoutParent_free_under_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {parent child : Fin S.count}
    (found : w.parityReadoutParent child = some parent) :
    hedgeDoSecond rich q.action child = none :=
  hedgeDoSecond_of_false rich q.action
    (action_false_of_mutilatedDirected q.action
      (w.parityReadoutParent_mutilatedDirected found))

/-- Every vertex of the all-root routing forest remains free under the query
intervention.  Unlike the single-route predecessor lemma, this also covers
sources and merge vertices that have no indexed predecessor. -/
theorem HedgeWitness.rootReadoutNodes_free_under_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (node : Fin S.count) (selected : w.rootReadoutNodes node = true) :
    hedgeDoSecond rich q.action node = none :=
  hedgeDoSecond_of_false rich q.action
    (w.rootReadoutNodes_avoids_action node selected)

/-- Under `do(X = second)`, the wrapped large model exposes its root parity at
the selected query outcome. -/
theorem HedgeWitness.largeReadoutParityModel_parityReadoutOutcome_bit_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeIsSecond rich w.parityReadoutOutcome
        ((w.largeReadoutParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action) u w.parityReadoutOutcome) =
      hedgeIsSecond rich w.actionRoot
        ((w.largeReadoutParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action) u w.actionRoot) :=
  w.largeReadoutParityModel_parityReadoutOutcome_bit rich
    (hedgeDoSecond rich q.action) u
    (fun _parent _child found =>
      w.parityReadoutParent_free_under_doSecond rich found)

/-- The wrapped small model has the identical end-to-end readout equation
under `do(X = second)`. -/
theorem HedgeWitness.smallReadoutParityModel_parityReadoutOutcome_bit_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeIsSecond rich w.parityReadoutOutcome
        ((w.smallReadoutParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action) u w.parityReadoutOutcome) =
      hedgeIsSecond rich w.actionRoot
        ((w.smallReadoutParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action) u w.actionRoot) :=
  w.smallReadoutParityModel_parityReadoutOutcome_bit rich
    (hedgeDoSecond rich q.action) u
    (fun _parent _child found =>
      w.parityReadoutParent_free_under_doSecond rich found)

/--
Reference assignment that pins every action vertex to `second` and every
free vertex to `first`.  Intervening on this assignment is `hedgeDoSecond`
for an arbitrary action, with no singleton hypothesis.
-/
def hedgeActionReference (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) : S.Assignment :=
  fun i => if action i then rich.second i else rich.first i

theorem hedgeActionReference_of_true (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) {i : Fin S.count} (h : action i = true) :
    hedgeActionReference rich action i = rich.second i := by
  simp [hedgeActionReference, h]

theorem hedgeActionReference_of_false (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) {i : Fin S.count} (h : action i = false) :
    hedgeActionReference rich action i = rich.first i := by
  simp [hedgeActionReference, h]

theorem hedgeDoSecond_eq_action_intervention
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S) :
    (fun i =>
      if action i then some (hedgeActionReference rich action i) else none) =
      hedgeDoSecond rich action := by
  funext i
  cases hi : action i with
  | false =>
      simp [hedgeDoSecond, hi]
  | true =>
      simp [hedgeDoSecond, hi, hedgeActionReference]

/--
Reference assignment with one distinguished action vertex at `second` and
every other coordinate at `first`.  Unlike `hedgeActionReference`, this lets a
single chosen parent contribute the mix XOR even when the outcome has several
action parents.
-/
def hedgeActionPivotReference (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (pivot : Fin S.count) : S.Assignment :=
  fun i =>
    if action i then
      if i = pivot then rich.second i else rich.first i
    else rich.first i

theorem hedgeActionPivotReference_pivot
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    {pivot : Fin S.count} (selected : action pivot = true) :
    hedgeActionPivotReference rich action pivot pivot = rich.second pivot := by
  simp [hedgeActionPivotReference, selected]

theorem hedgeActionPivotReference_of_ne
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    {pivot i : Fin S.count} (different : i ≠ pivot) :
    hedgeActionPivotReference rich action pivot i = rich.first i := by
  cases selected : action i <;>
    simp [hedgeActionPivotReference, selected, different]

theorem hedgeActionPivotReference_of_false
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    (pivot : Fin S.count) {i : Fin S.count} (free : action i = false) :
    hedgeActionPivotReference rich action pivot i = rich.first i := by
  simp [hedgeActionPivotReference, free]

/-- Hard intervention induced by `hedgeActionPivotReference`. -/
def hedgeDoPivot (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (pivot : Fin S.count) :
    (i : Fin S.count) → Option (S.Value i) :=
  fun i =>
    if action i then
      some (hedgeActionPivotReference rich action pivot i)
    else none

theorem hedgeDoPivot_of_true (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (pivot : Fin S.count) {i : Fin S.count}
    (selected : action i = true) :
    hedgeDoPivot rich action pivot i =
      some (hedgeActionPivotReference rich action pivot i) := by
  simp [hedgeDoPivot, selected]

theorem hedgeDoPivot_of_false (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (pivot : Fin S.count) {i : Fin S.count}
    (free : action i = false) :
    hedgeDoPivot rich action pivot i = none := by
  simp [hedgeDoPivot, free]

theorem hedgeDoPivot_eq_action_intervention
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    (pivot : Fin S.count) :
    (fun i =>
      if action i then
        some (hedgeActionPivotReference rich action pivot i)
      else none) =
      hedgeDoPivot rich action pivot :=
  rfl

/--
At a selected vertex, evaluation under the pivot intervention is exactly the
chosen reference value, independently of the model's parent mask.
-/
theorem hedgeMixModel_evalNodeUnder_doPivot
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask action : NodeSet S) (pivot : Fin S.count)
    (u : (hedgeLatentExtension G).Assignment) {i : Fin S.count}
    (selected : action i = true) :
    (hedgeMixModel G rich mask).evalNodeUnder
        (hedgeDoPivot rich action pivot) u i =
      hedgeActionPivotReference rich action pivot i := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [hedgeDoPivot_of_true rich action pivot selected]

/--
The selected action value contributes a second-bit exactly at the pivot.
-/
theorem hedgeIsSecond_actionPivotReference
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    {pivot i : Fin S.count} (selected : action i = true) :
    hedgeIsSecond rich i (hedgeActionPivotReference rich action pivot i) =
      decide (i = pivot) := by
  if equal : i = pivot then
    subst i
    simp [hedgeActionPivotReference, selected, hedgeIsSecond]
  else
    simp [hedgeActionPivotReference, selected, equal, hedgeIsSecond,
      rich.different]

/--
A node left free by an arbitrary intervention evaluates through the mix
mechanism.  This generic form supports both the all-`second` and one-pivot
query assignments.
-/
theorem hedgeMixModel_evalNodeUnder_of_none (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment) {child : Fin S.count}
    (free : intervention child = none) :
    (hedgeMixModel G rich mask).evalNodeUnder intervention u child =
      hedgeMixFrom rich child
        (hedgeXorPairBits G child (fun latent _ => u latent))
        (hedgeParentBitsFrom rich mask child
          (fun parent _ =>
            (hedgeMixModel G rich mask).evalNodeUnder
              intervention u parent))
        (hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun latent _ => u latent))) := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  rfl

/-- All-`second` specialization of free-node mix evaluation. -/
theorem hedgeMixModel_evalNodeUnder_free (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask action : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) {child : Fin S.count}
    (hfree : action child = false) :
    (hedgeMixModel G rich mask).evalNodeUnder (hedgeDoSecond rich action) u
        child =
      hedgeMixFrom rich child
        (hedgeXorPairBits G child (fun latent _ => u latent))
        (hedgeParentBitsFrom rich mask child
          (fun parent _ =>
            (hedgeMixModel G rich mask).evalNodeUnder
              (hedgeDoSecond rich action) u parent))
        (hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun latent _ => u latent))) :=
  hedgeMixModel_evalNodeUnder_of_none G rich mask (hedgeDoSecond rich action) u
    (hedgeDoSecond_of_false rich action hfree)

/-- Folding a step that is the identity off `pivot` leaves the accumulator
unchanged when `pivot` is absent from the list. -/
theorem foldl_keep_of_not_mem {n : Nat} {pivot : Fin n}
    (f : Bool → Fin n → Bool)
    (hkeep : forall acc p, p ≠ pivot → f acc p = acc)
    (xs : List (Fin n)) (hnmem : pivot ∉ xs) (init : Bool) :
    xs.foldl f init = init := by
  induction xs generalizing init with
  | nil =>
      rfl
  | cons a as ih =>
      have ha : a ≠ pivot := fun heq =>
        hnmem (List.mem_cons.mpr (Or.inl heq.symm))
      have htail : pivot ∉ as := fun hmem =>
        hnmem (List.mem_cons.mpr (Or.inr hmem))
      simp [hkeep init a ha]
      exact ih htail _

/-- XOR-fold that flips exactly at the unique occurrence of `pivot` yields `true`. -/
theorem foldl_xor_true_of_mem_nodup {n : Nat} {pivot : Fin n}
    (xs : List (Fin n)) (hmem : pivot ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc p => if p = pivot then !acc else acc) false =
      true := by
  induction xs with
  | nil =>
      cases hmem
  | cons a as ih =>
      have parts := List.nodup_cons.mp hnodup
      simp only [List.foldl]
      if ha : a = pivot then
        have hnin : pivot ∉ as := ha ▸ parts.1
        have hkeep :
            as.foldl (fun acc p => if p = pivot then !acc else acc) true =
              true :=
          foldl_keep_of_not_mem
            (fun acc p => if p = pivot then !acc else acc)
            (fun acc p hp => by simp [hp]) as hnin true
        simp [ha]
        exact hkeep
      else
        have htail : pivot ∈ as :=
          match List.mem_cons.mp hmem with
          | Or.inl heq => False.elim (ha heq.symm)
          | Or.inr hmem => hmem
        simpa [ha] using ih htail parts.2

theorem foldl_xor_true_at (n : Nat) (x : Fin n) :
    (List.finRange n).foldl
      (fun acc p => if p = x then !acc else acc) false = true :=
  foldl_xor_true_of_mem_nodup _ (List.mem_finRange x) (nodup_finRange n)

/-- XOR-fold that inserts `bit` at the unique occurrence of `pivot`. -/
theorem foldl_xor_bit_of_mem_nodup {n : Nat} {pivot : Fin n}
    (xs : List (Fin n)) (hmem : pivot ∈ xs) (hnodup : xs.Nodup) (bit : Bool) :
    xs.foldl (fun acc p => if p = pivot then Bool.xor acc bit else acc) false =
      bit := by
  cases bit with
  | true =>
      simpa [Bool.xor_true] using foldl_xor_true_of_mem_nodup xs hmem hnodup
  | false =>
      refine foldl_unchanged _ false xs ?_
      intro acc p
      if hp : p = pivot then
        simp [hp]
      else
        simp [hp]

theorem foldl_xor_bit_at (n : Nat) (x : Fin n) (bit : Bool) :
    (List.finRange n).foldl
      (fun acc p => if p = x then Bool.xor acc bit else acc) false = bit :=
  foldl_xor_bit_of_mem_nodup _ (List.mem_finRange x) (nodup_finRange n) bit

/-- A unique selected directed parent gives odd action-parent parity. -/
theorem actionParentParity_eq_true_of_unique
    (action : NodeSet S) {x child : Fin S.count}
    (edge : S.directed x child = true) (selected : action x = true)
    (unique : forall parent, action parent = true →
      S.directed parent child = true → parent = x) :
    actionParentParity action child = true := by
  unfold actionParentParity
  have step (acc : Bool) (parent : Fin S.count) :
      (if S.directed parent child then
          if action parent then !acc else acc
        else acc) =
      if parent = x then !acc else acc := by
    if equal : parent = x then
      subst parent
      simp [edge, selected]
    else
      cases inAction : action parent with
      | false =>
          simp [equal]
      | true =>
          cases parentEdge : S.directed parent child with
          | false =>
              simp [equal]
          | true =>
              exact False.elim (equal (unique parent inAction parentEdge))
  rw [foldl_congr _ _ false (List.finRange S.count) step]
  exact foldl_xor_true_at S.count x

theorem hedgeIsSecond_second (rich : ObservedSignature.ValueRich S)
    (i : Fin S.count) :
    hedgeIsSecond rich i (rich.second i) = true := by
  simp [hedgeIsSecond]

theorem hedgeIsSecond_first (rich : ObservedSignature.ValueRich S)
    (i : Fin S.count) :
    hedgeIsSecond rich i (rich.first i) = false := by
  simp [hedgeIsSecond, rich.different]

/-- An intervened mix node is pinned to the `ValueRich` second label. -/
theorem hedgeMixModel_evalNodeUnder_doSecond (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask action : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) {i : Fin S.count}
    (hact : action i = true) :
    (hedgeMixModel G rich mask).evalNodeUnder (hedgeDoSecond rich action) u i =
      rich.second i := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [hedgeDoSecond_of_true rich action hact]

/--
Under the action-wide `second` intervention, the mix parent bit is exactly
the parity of all directed action parents.  This removes the artificial
unique-parent restriction from the separation argument: three, five, or any
other odd number of action parents contributes the same `true` copy bit.
-/
theorem hedgeParentBitsFrom_doSecond_eq_actionParentParity
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count) :
    hedgeParentBitsFrom rich action child
        (fun parent _ =>
          (hedgeMixModel G rich action).evalNodeUnder
            (hedgeDoSecond rich action) u parent) =
      actionParentParity action child := by
  unfold hedgeParentBitsFrom actionParentParity
  apply foldl_congr
  intro acc parent
  if edge : S.directed parent child = true then
    cases selected : action parent with
    | false =>
        simp [edge]
    | true =>
        simp [edge,
          hedgeMixModel_evalNodeUnder_doSecond G rich action action u selected,
          hedgeIsSecond_second]
  else
    simp [edge]

/--
The pivot intervention makes the action-mask parent XOR true at every child
of the selected pivot.  Additional action parents contribute `first`, hence
zero, so neither uniqueness nor odd cardinality is required.
-/
theorem hedgeParentBitsFrom_doPivot_eq_true
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (u : (hedgeLatentExtension G).Assignment)
    {pivot child : Fin S.count} (selected : action pivot = true)
    (edge : S.directed pivot child = true) :
    hedgeParentBitsFrom rich action child
        (fun parent _ =>
          (hedgeMixModel G rich action).evalNodeUnder
            (hedgeDoPivot rich action pivot) u parent) = true := by
  unfold hedgeParentBitsFrom
  have step (acc : Bool) (parent : Fin S.count) :
      (if parentEdge : S.directed parent child = true then
          if action parent then
            Bool.xor acc
              (hedgeIsSecond rich parent
                ((hedgeMixModel G rich action).evalNodeUnder
                  (hedgeDoPivot rich action pivot) u parent))
          else acc
        else acc) =
      if parent = pivot then !acc else acc := by
    if equal : parent = pivot then
      subst parent
      simp [edge, selected,
        hedgeMixModel_evalNodeUnder_doPivot G rich action action pivot u,
        hedgeIsSecond_actionPivotReference]
    else
      cases parentEdge : S.directed parent child with
      | false =>
          simp [equal]
      | true =>
          cases parentSelected : action parent with
          | false =>
              simp [equal]
          | true =>
              simp [equal,
                hedgeMixModel_evalNodeUnder_doPivot G rich action action pivot u
                  parentSelected,
                hedgeIsSecond_actionPivotReference rich action parentSelected]
  rw [foldl_congr _ _ false (List.finRange S.count) step]
  exact foldl_xor_true_at S.count pivot

/--
Masked parent-bits under `hedgeDoSecond` are `true` when exactly one
directed parent lies in the action and that parent is therefore pinned
to `second`.
-/
theorem hedgeParentBitsFrom_of_unique_doSecond (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask action : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) {x y : Fin S.count}
    (hdir : S.directed x y = true) (hx : action x = true)
    (hmask : mask x = true)
    (huniq : forall p, mask p = true → S.directed p y = true → p = x) :
    hedgeParentBitsFrom rich mask y
        (fun parent _ =>
          (hedgeMixModel G rich mask).evalNodeUnder
            (hedgeDoSecond rich action) u parent) = true := by
  unfold hedgeParentBitsFrom
  have hstep (acc : Bool) (p : Fin S.count) :
      (if hdir' : S.directed p y = true then
          if mask p then
            Bool.xor acc
              (hedgeIsSecond rich p
                ((hedgeMixModel G rich mask).evalNodeUnder
                  (hedgeDoSecond rich action) u p))
          else acc
        else acc) =
        if p = x then !acc else acc := by
    if hp : p = x then
      rw [hp]
      simp [hdir, hmask,
        hedgeMixModel_evalNodeUnder_doSecond G rich mask action u hx,
        hedgeIsSecond_second]
    else
      cases hmaskb : mask p
      · if hdir' : S.directed p y = true then
          simp [hdir', hp]
        else
          simp [hdir', hp]
      · if hdir' : S.directed p y = true then
          exact False.elim (hp (huniq p hmaskb hdir'))
        else
          simp [hdir', hp]
  have hfold :=
    foldl_congr
      (fun acc p =>
        if hdir' : S.directed p y = true then
          if mask p then
            Bool.xor acc
              (hedgeIsSecond rich p
                ((hedgeMixModel G rich mask).evalNodeUnder
                  (hedgeDoSecond rich action) u p))
          else acc
        else acc)
      (fun acc p => if p = x then !acc else acc)
      false (List.finRange S.count) hstep
  rw [hfold]
  exact foldl_xor_true_at S.count x

/-- Parent-bits vanish when no directed parent lies in the mask. -/
theorem hedgeParentBitsFrom_of_no_masked_parent
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (child : Fin S.count)
    (get : forall parent, S.directed parent child = true → S.Value parent)
    (hnone : forall p, mask p = true → S.directed p child = true → False) :
    hedgeParentBitsFrom rich mask child get = false := by
  unfold hedgeParentBitsFrom
  refine foldl_unchanged _ false (List.finRange S.count) ?_
  intro acc p
  if hdir : S.directed p child = true then
    cases hmask : mask p
    · simp [hdir]
    · exact False.elim (hnone p hmask hdir)
  else
    simp [hdir]

/--
Masked parent parity vanishes when every masked directed parent carries the
distinguished `first` label.  This is the many-parent counterpart of
`hedgeParentBitsFrom_of_no_masked_parent`: masked parents may now be present,
but each contributes the zero bit to the XOR fold.

Keeping this lemma independent of `hedgeMixModel` is useful for the general
shared-switch argument below.  The recursive model proof establishes the
`first`-label premise from earlier vertices, while this finite fold performs
the purely Boolean aggregation.
-/
theorem hedgeParentBitsFrom_false_of_masked_parents_first
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (child : Fin S.count)
    (get : forall parent, S.directed parent child = true → S.Value parent)
    (hfirst : forall parent (edge : S.directed parent child = true),
      mask parent = true → hedgeIsSecond rich parent (get parent edge) = false) :
    hedgeParentBitsFrom rich mask child get = false := by
  unfold hedgeParentBitsFrom
  refine foldl_unchanged _ false (List.finRange S.count) ?_
  intro acc parent
  if edge : S.directed parent child = true then
    cases selected : mask parent with
    | false =>
        simp [edge]
    | true =>
        simp [edge, hfirst parent edge selected]
  else
    simp [edge]

/--
A unique masked directed parent contributes exactly its `ValueRich`
second-bit to the parent-bit XOR.
-/
theorem hedgeParentBitsFrom_of_unique
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    {x child : Fin S.count}
    (get : forall parent, S.directed parent child = true → S.Value parent)
    (hdir : S.directed x child = true) (hmask : mask x = true)
    (huniq : forall p, mask p = true → S.directed p child = true → p = x) :
    hedgeParentBitsFrom rich mask child get =
      hedgeIsSecond rich x (get x hdir) := by
  unfold hedgeParentBitsFrom
  have hstep (acc : Bool) (p : Fin S.count) :
      (if hdir' : S.directed p child = true then
          if mask p then
            Bool.xor acc (hedgeIsSecond rich p (get p hdir'))
          else acc
        else acc) =
        if p = x then
          Bool.xor acc (hedgeIsSecond rich x (get x hdir))
        else acc := by
    if hp : p = x then
      rw [hp]
      simp [hdir, hmask]
    else
      cases hmaskb : mask p
      · if hdir' : S.directed p child = true then
          simp [hdir', hp]
        else
          simp [hdir', hp]
      · if hdir' : S.directed p child = true then
          exact False.elim (hp (huniq p hmaskb hdir'))
        else
          simp [hdir', hp]
  have hfold :=
    foldl_congr
      (fun acc p =>
        if hdir' : S.directed p child = true then
          if mask p then
            Bool.xor acc (hedgeIsSecond rich p (get p hdir'))
          else acc
        else acc)
      (fun acc p =>
        if p = x then
          Bool.xor acc (hedgeIsSecond rich x (get x hdir))
        else acc)
      false (List.finRange S.count) hstep
  rw [hfold]
  exact foldl_xor_bit_at S.count x (hedgeIsSecond rich x (get x hdir))

/-- Pair-bit XOR is `true` when a single designated incident root is `true`. -/
theorem hedgeXorPairBitsFrom_of_one (G : ObservedGraph S)
    (child : Fin S.count) (root : Fin (pairRootCount G))
    (pairBits : (r : Fin (pairRootCount G)) → Bool)
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true)
    (htrue : pairBits root = true)
    (hrest : forall r, r ≠ root → pairBits r = false) :
    hedgeXorPairBitsFrom G child pairBits = true := by
  unfold hedgeXorPairBitsFrom
  have hstep (acc : Bool) (r : Fin (pairRootCount G)) :
      (if (hedgeLatentExtension G).incident (hedgePairRoot G r) child then
          Bool.xor acc (pairBits r)
        else acc) =
        if r = root then !acc else acc := by
    if hr : r = root then
      subst r
      simp [hinc, htrue]
    else
      have hb : pairBits r = false := hrest r hr
      if hinc' : (hedgeLatentExtension G).incident (hedgePairRoot G r) child then
        simp [hinc', hb, hr]
      else
        simp [hinc', hr]
  have hfold :=
    foldl_congr
      (fun acc r =>
        if (hedgeLatentExtension G).incident (hedgePairRoot G r) child then
          Bool.xor acc (pairBits r)
        else acc)
      (fun acc r => if r = root then !acc else acc)
      false (List.finRange (pairRootCount G)) hstep
  rw [hfold]
  exact foldl_xor_true_at (pairRootCount G) root

/-- Pair-bits that light exactly one root. -/
def hedgeOnePairBits (G : ObservedGraph S) (root : Fin (pairRootCount G)) :
    (r : Fin (pairRootCount G)) → Bool :=
  fun r => decide (r = root)

theorem hedgeOnePairBits_self (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    hedgeOnePairBits G root root = true := by
  simp [hedgeOnePairBits]

theorem hedgeOnePairBits_rest (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) {r : Fin (pairRootCount G)}
    (hne : r ≠ root) :
    hedgeOnePairBits G root r = false := by
  simp [hedgeOnePairBits, hne]

/-- A one-root vector evaluates to that root's restricted incidence bit. -/
theorem hedgeXorPairBitsWithinFrom_one_eq
    (G : ObservedGraph S) (nodes : NodeSet S)
    (child : Fin S.count) (root : Fin (pairRootCount G)) :
    hedgeXorPairBitsWithinFrom G nodes child (hedgeOnePairBits G root) =
      ((hedgeLatentExtension G).incident (hedgePairRoot G root) child &&
        hedgePairRootWithin G nodes root) := by
  unfold hedgeXorPairBitsWithinFrom
  let selected : Bool :=
    (hedgeLatentExtension G).incident (hedgePairRoot G root) child &&
      hedgePairRootWithin G nodes root
  have hstep (acc : Bool) (r : Fin (pairRootCount G)) :
      (if (hedgeLatentExtension G).incident (hedgePairRoot G r) child &&
            hedgePairRootWithin G nodes r then
          Bool.xor acc (hedgeOnePairBits G root r)
        else acc) =
        if r = root then Bool.xor acc selected else acc := by
    if hr : r = root then
      rw [hr]
      cases hinc :
          (hedgeLatentExtension G).incident (hedgePairRoot G root) child <;>
        cases hwithin : hedgePairRootWithin G nodes root <;>
        simp [selected, hinc, hwithin, hedgeOnePairBits_self]
    else
      simp [hr, hedgeOnePairBits_rest G root hr]
  have hfold :=
    foldl_congr
      (fun acc r =>
        if (hedgeLatentExtension G).incident (hedgePairRoot G r) child &&
              hedgePairRootWithin G nodes r then
          Bool.xor acc (hedgeOnePairBits G root r)
        else acc)
      (fun acc r => if r = root then Bool.xor acc selected else acc)
      false (List.finRange (pairRootCount G)) hstep
  rw [hfold]
  exact foldl_xor_bit_at (pairRootCount G) root selected

/--
The one-root vector of a selected bidirected edge has precisely the two
endpoint boundary bits.  This is the algebraic base case for a path vector.
-/
theorem hedgeXorPairBitsWithinFrom_one_between
    (G : ObservedGraph S) (nodes : NodeSet S)
    {i j : Fin S.count}
    (hi : nodes i = true) (hj : nodes j = true)
    (edge : G.bidirected i j = true) (node : Fin S.count) :
    hedgeXorPairBitsWithinFrom G nodes node
        (hedgeOnePairBits G (pairRootBetween G edge)) =
      Bool.xor (decide (node = i)) (decide (node = j)) := by
  rw [hedgeXorPairBitsWithinFrom_one_eq,
    hedgePairRootWithin_between G nodes hi hj edge]
  have hincident :
      (hedgeLatentExtension G).incident
          (hedgePairRoot G (pairRootBetween G edge)) node =
        (decide (node = i) || decide (node = j)) := by
    simpa [hedgeLatentExtension, hedgeIncident_pair] using
      pairRootIncident_between G edge node
  rw [hincident]
  have different : i ≠ j := fun same => by
    subst same
    rw [G.bidirected_irreflexive] at edge
    exact Bool.false_ne_true edge
  by_cases hleft : node = i
  · subst hleft
    simp [different]
  · by_cases hright : node = j
    · subst hright
      simp [hleft]
    · simp [hleft, hright]

/--
Every bidirected walk has a pair-root vector whose incidence boundary is its
two endpoints.  The proof XORs the canonical root of each successive edge;
the shared intermediate endpoint cancels.  This existence proof stays in
`Prop`.  A later finite search can recover an actual vector in `Type` without
choice.
-/
theorem bidirectedConnectedWithin_pairBits
    (G : ObservedGraph S) (nodes : NodeSet S)
    {start finish : Fin S.count}
    (connected : BidirectedConnectedWithin G nodes start finish) :
    Exists fun pairBits : (root : Fin (pairRootCount G)) → Bool =>
      forall node,
        hedgeXorPairBitsWithinFrom G nodes node pairBits =
          Bool.xor (decide (node = start)) (decide (node = finish)) := by
  induction connected with
  | @refl selected =>
      refine ⟨hedgeZeroPairBits G, ?_⟩
      intro node
      rw [hedgeXorPairBitsWithinFrom_zero]
      by_cases equal : node = start <;> simp [equal]
  | @tail j k previous selected edge inductionHypothesis =>
      rcases inductionHypothesis with ⟨previousBits, previousBoundary⟩
      let edgeBits := hedgeOnePairBits G (pairRootBetween G edge)
      refine ⟨hedgePairBitsXor G previousBits edgeBits, ?_⟩
      intro node
      rw [hedgeXorPairBitsWithinFrom_xor,
        previousBoundary node,
        hedgeXorPairBitsWithinFrom_one_between G nodes
          (BidirectedConnectedWithin.mem_right previous) selected edge node]
      cases hstart : decide (node = start) <;>
        cases hmiddle : decide (node = j) <;>
        cases hend : decide (node = k) <;> rfl

/--
A duplicate-free selected list of length `2 * pairs` is an incidence boundary.
This explicit pair count gives structural recursion in steps of two.
-/
theorem BidirectedComponent.pairBits_of_length_twice
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (vertices : List (Fin S.count))
    (pairs : Nat)
    (lengthEq : vertices.length = 2 * pairs)
    (nodup : vertices.Nodup)
    (inside : forall node, node ∈ vertices → nodes node = true) :
    Exists fun pairBits : (root : Fin (pairRootCount G)) → Bool =>
      forall node,
        hedgeXorPairBitsWithinFrom G nodes node pairBits =
          decide (node ∈ vertices) := by
  induction pairs generalizing vertices with
  | zero =>
      cases vertices with
      | nil =>
          refine ⟨hedgeZeroPairBits G, ?_⟩
          intro node
          simp [hedgeXorPairBitsWithinFrom_zero]
      | cons first rest =>
          change rest.length + 1 = 2 * 0 at lengthEq
          have impossible : False := by omega
          exact False.elim impossible
  | succ pairs inductionHypothesis =>
      cases vertices with
      | nil =>
          change 0 = 2 * (pairs + 1) at lengthEq
          have impossible : False := by omega
          exact False.elim impossible
      | cons first tail =>
          cases tail with
          | nil =>
              simp only [List.length_cons, List.length_nil] at lengthEq
              have impossible : False := by omega
              exact False.elim impossible
          | cons second rest =>
              have nodupFirst := List.nodup_cons.mp nodup
              have nodupSecond := List.nodup_cons.mp nodupFirst.2
              have firstInside : nodes first = true :=
                inside first (by simp)
              have secondInside : nodes second = true :=
                inside second (by simp)
              have restInside :
                  forall node, node ∈ rest → nodes node = true := by
                intro node hmem
                exact inside node (by simp [hmem])
              have restLength : rest.length = 2 * pairs := by
                simp only [List.length_cons] at lengthEq
                omega
              rcases inductionHypothesis rest restLength nodupSecond.2
                  restInside with ⟨restBits, restBoundary⟩
              have connected :
                  BidirectedConnectedWithin G nodes first second :=
                component.2 first second firstInside secondInside
              rcases bidirectedConnectedWithin_pairBits G nodes connected with
                ⟨pathBits, pathBoundary⟩
              refine ⟨hedgePairBitsXor G pathBits restBits, ?_⟩
              intro node
              rw [hedgeXorPairBitsWithinFrom_xor,
                pathBoundary node, restBoundary node]
              have firstNeSecond : first ≠ second := by
                intro equal
                exact nodupFirst.1 (by simp [equal])
              have firstNotRest : first ∉ rest := by
                intro hmem
                exact nodupFirst.1 (by simp [hmem])
              have secondNotRest : second ∉ rest := nodupSecond.1
              by_cases hfirst : node = first
              · subst hfirst
                simp [firstNeSecond, firstNotRest]
              · by_cases hsecond : node = second
                · subst hsecond
                  simp [hfirst, secondNotRest]
                · by_cases hrest : node ∈ rest <;>
                    simp [hfirst, hsecond, hrest]

/--
Every even duplicate-free list of selected vertices is the incidence boundary
of some pair-root vector.  Consecutive list elements are connected inside the
c-component and their path vectors are XORed.
-/
theorem BidirectedComponent.pairBits_of_even_list
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (vertices : List (Fin S.count))
    (nodup : vertices.Nodup)
    (inside : forall node, node ∈ vertices → nodes node = true)
    (even : vertices.length % 2 = 0) :
    Exists fun pairBits : (root : Fin (pairRootCount G)) → Bool =>
      forall node,
        hedgeXorPairBitsWithinFrom G nodes node pairBits =
          decide (node ∈ vertices) := by
  have decomposition := Nat.mod_add_div vertices.length 2
  have lengthEq : vertices.length = 2 * (vertices.length / 2) := by
    omega
  exact component.pairBits_of_length_twice G nodes vertices
    (vertices.length / 2) lengthEq nodup inside

/-- Selected vertices at which a requested incidence pattern is true. -/
def hedgeTrueVertices (nodes : NodeSet S)
    (target : Fin S.count → Bool) : List (Fin S.count) :=
  (NodeSet.members nodes).filter target

theorem hedgeTrueVertices_nodup (nodes : NodeSet S)
    (target : Fin S.count → Bool) :
    (hedgeTrueVertices nodes target).Nodup :=
  (NodeSet.nodup_members nodes).filter target

theorem hedgeTrueVertices_inside (nodes : NodeSet S)
    (target : Fin S.count → Bool) :
    forall node, node ∈ hedgeTrueVertices nodes target → nodes node = true := by
  intro node hmem
  exact (NodeSet.mem_members_iff nodes node).mp
    (List.mem_filter.mp hmem).1

/--
Every even incidence pattern on a bidirected component is generated by some
pair-root vector.  This is the constructive graph-theoretic surjectivity
lemma behind the unsoftened hedge model: the proof produces existence in
`Prop`, ready to be turned into data by the finite pair-bit enumeration.
-/
theorem BidirectedComponent.pairBits_of_even_target
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (target : Fin S.count → Bool)
    (even : (hedgeTrueVertices nodes target).length % 2 = 0) :
    Exists fun pairBits : (root : Fin (pairRootCount G)) → Bool =>
      forall node, nodes node = true →
        hedgeXorPairBitsWithinFrom G nodes node pairBits = target node := by
  rcases component.pairBits_of_even_list G nodes
      (hedgeTrueVertices nodes target)
      (hedgeTrueVertices_nodup nodes target)
      (hedgeTrueVertices_inside nodes target) even with
    ⟨pairBits, boundary⟩
  refine ⟨pairBits, ?_⟩
  intro node hin
  rw [boundary node]
  cases htarget : target node <;>
    simp [hedgeTrueVertices, List.mem_filter,
      NodeSet.mem_members_iff, hin, htarget]

/-- Executable test that a pair-root vector realizes `target` on `nodes`. -/
def hedgePairBitsRealizes (G : ObservedGraph S) (nodes : NodeSet S)
    (target : Fin S.count → Bool)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) : Bool :=
  (NodeSet.members nodes).all fun node =>
    hedgeXorPairBitsWithinFrom G nodes node pairBits == target node

theorem hedgePairBitsRealizes_of
    (G : ObservedGraph S) (nodes : NodeSet S)
    (target : Fin S.count → Bool)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (agrees : forall node, nodes node = true →
      hedgeXorPairBitsWithinFrom G nodes node pairBits = target node) :
    hedgePairBitsRealizes G nodes target pairBits = true := by
  unfold hedgePairBitsRealizes
  refine List.all_eq_true.mpr ?_
  intro node hmem
  exact beq_iff_eq.mpr
    (agrees node ((NodeSet.mem_members_iff nodes node).mp hmem))

theorem hedgePairBitsRealizes_spec
    (G : ObservedGraph S) (nodes : NodeSet S)
    (target : Fin S.count → Bool)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (realizes : hedgePairBitsRealizes G nodes target pairBits = true) :
    forall node, nodes node = true →
      hedgeXorPairBitsWithinFrom G nodes node pairBits = target node := by
  intro node hin
  have hmem := (NodeSet.mem_members_iff nodes node).mpr hin
  have tested := (List.all_eq_true.mp realizes) node hmem
  exact beq_iff_eq.mp tested

/-- The exhaustive pair-bit enumeration detects every even target pattern. -/
theorem BidirectedComponent.pairBitsRealizes_any_of_even
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (target : Fin S.count → Bool)
    (even : (hedgeTrueVertices nodes target).length % 2 = 0) :
    (hedgePairBitEnum G).any
      (hedgePairBitsRealizes G nodes target) = true := by
  rcases component.pairBits_of_even_target G nodes target even with
    ⟨pairBits, agrees⟩
  exact List.any_eq_true.mpr
    ⟨pairBits, hedgePairBitEnum_complete G pairBits,
      hedgePairBitsRealizes_of G nodes target pairBits agrees⟩

/--
First enumerated pair-root vector realizing an even component pattern.

Although `component.pairBits_of_even_target` proves existence, this definition
does not eliminate that existential into `Type`.  It evaluates the finite
enumeration and uses the existence proof only to rule out `find? = none`.
-/
def BidirectedComponent.evenTargetPairBits
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (target : Fin S.count → Bool)
    (even : (hedgeTrueVertices nodes target).length % 2 = 0) :
    (root : Fin (pairRootCount G)) → Bool :=
  listFirstAny (hedgePairBitEnum G)
    (hedgePairBitsRealizes G nodes target)
    (component.pairBitsRealizes_any_of_even G nodes target even)

/-- The computed vector realizes the requested pattern at every selected node. -/
theorem BidirectedComponent.evenTargetPairBits_spec
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (target : Fin S.count → Bool)
    (even : (hedgeTrueVertices nodes target).length % 2 = 0) :
    forall node, nodes node = true →
      hedgeXorPairBitsWithinFrom G nodes node
          (component.evenTargetPairBits G nodes target even) = target node :=
  hedgePairBitsRealizes_spec G nodes target _
    (listFirstAny_pred (hedgePairBitEnum G)
      (hedgePairBitsRealizes G nodes target)
      (component.pairBitsRealizes_any_of_even G nodes target even))

/--
Root-vector translation carrying one even component pattern to another.
The two computed representatives are XORed, so their incidences are the
pointwise difference of the requested patterns.
-/
def BidirectedComponent.targetTranslation
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices nodes left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices nodes right).length % 2 = 0) :
    (root : Fin (pairRootCount G)) → Bool :=
  hedgePairBitsXor G
    (component.evenTargetPairBits G nodes left leftEven)
    (component.evenTargetPairBits G nodes right rightEven)

/-- The translation's incidence is `left XOR right` on the component. -/
theorem BidirectedComponent.targetTranslation_spec
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices nodes left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices nodes right).length % 2 = 0) :
    forall node, nodes node = true →
      hedgeXorPairBitsWithinFrom G nodes node
          (component.targetTranslation G nodes left right
            leftEven rightEven) =
        Bool.xor (left node) (right node) := by
  intro node hin
  rw [BidirectedComponent.targetTranslation,
    hedgeXorPairBitsWithinFrom_xor,
    component.evenTargetPairBits_spec G nodes left leftEven node hin,
    component.evenTargetPairBits_spec G nodes right rightEven node hin]

/-- XORing the same root vector twice is the identity. -/
theorem hedgePairBitsXor_self_right
    (G : ObservedGraph S)
    (pairBits delta : (root : Fin (pairRootCount G)) → Bool) :
    hedgePairBitsXor G (hedgePairBitsXor G pairBits delta) delta =
      pairBits := by
  funext root
  unfold hedgePairBitsXor
  cases pairBits root <;> cases delta root <;> rfl

/-- Translation by a fixed root vector is an involution. -/
theorem BidirectedComponent.targetTranslation_involution
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices nodes left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices nodes right).length % 2 = 0)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) :
    hedgePairBitsXor G
        (hedgePairBitsXor G pairBits
          (component.targetTranslation G nodes left right
            leftEven rightEven))
        (component.targetTranslation G nodes left right
          leftEven rightEven) = pairBits :=
  hedgePairBitsXor_self_right G pairBits
    (component.targetTranslation G nodes left right leftEven rightEven)

/-- Translating a realization of `left` produces a realization of `right`. -/
theorem BidirectedComponent.targetTranslation_realizes
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices nodes left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices nodes right).length % 2 = 0)
    (pairBits : (root : Fin (pairRootCount G)) → Bool)
    (realizes : hedgePairBitsRealizes G nodes left pairBits = true) :
    hedgePairBitsRealizes G nodes right
        (hedgePairBitsXor G pairBits
          (component.targetTranslation G nodes left right
            leftEven rightEven)) = true := by
  apply hedgePairBitsRealizes_of
  intro node hin
  rw [hedgeXorPairBitsWithinFrom_xor,
    hedgePairBitsRealizes_spec G nodes left pairBits realizes node hin,
    component.targetTranslation_spec G nodes left right
      leftEven rightEven node hin]
  cases left node <;> cases right node <;> rfl

/--
XOR by a fixed root vector permutes the exhaustive pair-bit enumeration.
The inverse is the same XOR operation, and completeness of the enumeration
supplies membership on both sides; no inverse is selected from an existential.
-/
theorem hedgePairBitEnum_map_xor_perm
    (G : ObservedGraph S)
    (delta : (root : Fin (pairRootCount G)) → Bool) :
    ((hedgePairBitEnum G).map
        (fun pairBits => hedgePairBitsXor G pairBits delta)).Perm
      (hedgePairBitEnum G) := by
  apply Probability.ConstructivePermutation.perm_of_nodup_mem_iff
  · apply nodup_map_of_injective
    · intro left right equal
      have twice :=
        congrArg (fun pairBits => hedgePairBitsXor G pairBits delta) equal
      simpa only [hedgePairBitsXor_self_right] using twice
    · exact hedgePairBitEnum_nodup G
  · exact hedgePairBitEnum_nodup G
  · intro pairBits
    constructor
    · intro _member
      exact hedgePairBitEnum_complete G pairBits
    · intro _member
      exact List.mem_map.mpr
        ⟨hedgePairBitsXor G pairBits delta,
          hedgePairBitEnum_complete G _,
          hedgePairBitsXor_self_right G pairBits delta⟩

/--
Translation carries the realization test for `left` exactly to the test for
`right`.  The reverse implication uses the same XOR vector: adding the
translation twice cancels pointwise.
-/
theorem BidirectedComponent.targetTranslation_realizes_eq
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices nodes left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices nodes right).length % 2 = 0)
    (pairBits : (root : Fin (pairRootCount G)) → Bool) :
    hedgePairBitsRealizes G nodes right
        (hedgePairBitsXor G pairBits
          (component.targetTranslation G nodes left right
            leftEven rightEven)) =
      hedgePairBitsRealizes G nodes left pairBits := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro translatedRealizes
    apply hedgePairBitsRealizes_of
    intro node hin
    have translatedAtNode :=
      hedgePairBitsRealizes_spec G nodes right _ translatedRealizes node hin
    rw [hedgeXorPairBitsWithinFrom_xor,
      component.targetTranslation_spec G nodes left right
        leftEven rightEven node hin] at translatedAtNode
    cases hpair : hedgeXorPairBitsWithinFrom G nodes node pairBits <;>
      cases hleft : left node <;> cases hright : right node <;>
      simp_all
  · intro leftRealizes
    exact component.targetTranslation_realizes G nodes left right
      leftEven rightEven pairBits leftRealizes

/--
All even incidence patterns on one bidirected component have equally many
pair-root preimages.  Filtering the finite enumeration after translation is
the same as translating the filtered source, while the translation itself is
a permutation.  This is the finite counting statement required by the
observational-equivalence argument for the parity hedge pair.
-/
theorem BidirectedComponent.pairBitRealizers_length_eq_of_even
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices nodes left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices nodes right).length % 2 = 0) :
    ((hedgePairBitEnum G).filter
        (hedgePairBitsRealizes G nodes left)).length =
      ((hedgePairBitEnum G).filter
        (hedgePairBitsRealizes G nodes right)).length := by
  let delta :=
    component.targetTranslation G nodes left right leftEven rightEven
  have translatedEnumeration := hedgePairBitEnum_map_xor_perm G delta
  have translatedRealizers :=
    translatedEnumeration.filter (hedgePairBitsRealizes G nodes right)
  have predicateEq :
      hedgePairBitsRealizes G nodes right ∘
          (fun pairBits => hedgePairBitsXor G pairBits delta) =
        hedgePairBitsRealizes G nodes left := by
    funext pairBits
    exact component.targetTranslation_realizes_eq G nodes left right
      leftEven rightEven pairBits
  rw [List.filter_map, predicateEq] at translatedRealizers
  simpa using translatedRealizers.length_eq

/-- The XOR of a singleton indicator over a duplicate-free containing list. -/
theorem foldl_xor_indicator_of_mem_nodup {n : Nat}
    (xs : List (Fin n)) (pivot : Fin n)
    (member : pivot ∈ xs) (nodup : xs.Nodup) :
    xs.foldl
        (fun total node => Bool.xor total (decide (node = pivot))) false =
      true := by
  have congruence := foldl_congr
    (fun total node => Bool.xor total (decide (node = pivot)))
    (fun total node => if node = pivot then !total else total)
    false xs (fun total node => by
      by_cases equal : node = pivot <;> simp [equal])
  rw [congruence]
  exact foldl_xor_true_of_mem_nodup xs member nodup

/-- Two present singleton indicators cancel in an XOR fold. -/
theorem foldl_xor_two_indicators {n : Nat}
    (xs : List (Fin n)) (left right : Fin n)
    (leftMem : left ∈ xs) (rightMem : right ∈ xs)
    (nodup : xs.Nodup) :
    xs.foldl
        (fun total node => Bool.xor total
          (Bool.xor (decide (node = left)) (decide (node = right)))) false =
      false := by
  rw [foldl_xor_pointwise,
    foldl_xor_indicator_of_mem_nodup xs left leftMem nodup,
    foldl_xor_indicator_of_mem_nodup xs right rightMem nodup]
  rfl

/-- Contribution of one pair-root to one restricted incidence coordinate. -/
def hedgePairRootContributionWithin (G : ObservedGraph S)
    (nodes : NodeSet S) (root : Fin (pairRootCount G)) (bit : Bool)
    (node : Fin S.count) : Bool :=
  if (hedgeLatentExtension G).incident (hedgePairRoot G root) node &&
      hedgePairRootWithin G nodes root then bit else false

/--
One internal pair-root has even endpoint parity.  A disabled or zero root
contributes nowhere; an enabled one contributes at its two distinct selected
endpoints, whose singleton indicators cancel.
-/
theorem hedgePairRootContributionWithin_parity
    (G : ObservedGraph S) (nodes : NodeSet S)
    (root : Fin (pairRootCount G)) (bit : Bool) :
    (NodeSet.members nodes).foldl
        (fun total node => Bool.xor total
          (hedgePairRootContributionWithin G nodes root bit node)) false =
      false := by
  cases hwithin : hedgePairRootWithin G nodes root
  · exact foldl_unchanged _ false (NodeSet.members nodes) (fun total node => by
      simp [hedgePairRootContributionWithin, hwithin])
  · cases bit with
    | false =>
      exact foldl_unchanged _ false (NodeSet.members nodes) (fun total node => by
        simp [hedgePairRootContributionWithin])
    | true =>
      let endpoints := (pairRoots G).get root
      have selected :
          nodes endpoints.1 = true ∧ nodes endpoints.2 = true := by
        simpa [hedgePairRootWithin, endpoints] using
          (Bool.and_eq_true_iff.mp hwithin)
      have leftMem : endpoints.1 ∈ NodeSet.members nodes :=
        (NodeSet.mem_members_iff nodes endpoints.1).mpr selected.1
      have rightMem : endpoints.2 ∈ NodeSet.members nodes :=
        (NodeSet.mem_members_iff nodes endpoints.2).mpr selected.2
      have different : endpoints.1 ≠ endpoints.2 := by
        intro equal
        have valuesEqual : endpoints.1.val = endpoints.2.val :=
          congrArg Fin.val equal
        exact (Nat.ne_of_lt (pairRoots_get_spec G root).1) valuesEqual
      have contributionEq : ∀ node,
          hedgePairRootContributionWithin G nodes root true node =
            Bool.xor (decide (node = endpoints.1))
              (decide (node = endpoints.2)) := by
        intro node
        have incidentEq :
            (hedgeLatentExtension G).incident (hedgePairRoot G root) node =
              (decide (node = endpoints.1) ||
                decide (node = endpoints.2)) := by
          simp [hedgeLatentExtension, hedgeIncident_pair,
            pairRootIncident, endpoints]
        rw [hedgePairRootContributionWithin, incidentEq]
        by_cases left : node = endpoints.1
        · subst node
          simp [hwithin, different]
        · by_cases right : node = endpoints.2
          · subst node
            simp [hwithin, left]
          · simp [hwithin, left, right]
      have congruence := foldl_congr
        (fun total node => Bool.xor total
          (hedgePairRootContributionWithin G nodes root true node))
        (fun total node => Bool.xor total
          (Bool.xor (decide (node = endpoints.1))
            (decide (node = endpoints.2))))
        false (NodeSet.members nodes)
        (fun total node => by
          change Bool.xor total _ = Bool.xor total _
          rw [contributionEq node])
      rw [congruence]
      exact foldl_xor_two_indicators (NodeSet.members nodes)
        endpoints.1 endpoints.2 leftMem rightMem
        (NodeSet.nodup_members nodes)

/-- XOR all coordinates of a Boolean vector selected by a node set. -/
def hedgeNodeXor (nodes : NodeSet S) (bits : Fin S.count → Bool) : Bool :=
  (NodeSet.members nodes).foldl
    (fun total node => Bool.xor total (bits node)) false

/-- Extending a Boolean vector by zero from a subset to a larger node family
does not change its XOR. -/
theorem hedgeNodeXor_mask_of_subset
    (small large : NodeSet S) (subset : NodeSet.Subset small large)
    (bits : Fin S.count → Bool) :
    hedgeNodeXor large (fun node => if small node then bits node else false) =
      hedgeNodeXor small bits := by
  unfold hedgeNodeXor NodeSet.members NodeSet.enumerated
  rw [List.foldl_filter, List.foldl_filter]
  apply foldl_congr
  intro total node
  cases selected : small node with
  | true =>
      have inside := subset node selected
      simp [selected, inside]
  | false =>
      cases large node <;> simp [selected]

/-- A true finite XOR has at least one true summand.  The induction follows
the input list directly and therefore extracts the witness constructively. -/
theorem exists_true_of_foldl_xor_eq_true
    {α : Type} (bits : α → Bool) : forall xs : List α,
    xs.foldl (fun total x => Bool.xor total (bits x)) false = true →
      Exists fun x => x ∈ xs ∧ bits x = true
  | [], parity => by simp at parity
  | head :: tail, parity => by
      cases headBit : bits head with
      | true => exact ⟨head, by simp, headBit⟩
      | false =>
          have tailParity :
              tail.foldl (fun total x => Bool.xor total (bits x)) false =
                true := by
            simpa [headBit] using parity
          rcases exists_true_of_foldl_xor_eq_true bits tail tailParity with
            ⟨x, member, selected⟩
          exact ⟨x, by simp [member], selected⟩

/-!
### Conservation for no-splitting readout flows

The canonical all-root readout is a `ForestChild`: every routing vertex sends
its bit to at most one successor, while several streams may merge at a later
vertex.  The following algebra is deliberately independent of the hedge
mechanisms.  It says that any Boolean labelling satisfying the local flow
equation

`value(v) = source(v) XOR XOR { value(u) | successor(u) = v }`

has total sink parity equal to total source parity.  This is the finite,
constructive replacement for following one distinguished root: merging never
loses information because it is addition in `Bool`'s XOR group.
-/

/-- Contribution of one routed parent to a prospective child. -/
def hedgeRoutingParentEntry (kept : ForestChild S)
    (bits : Fin S.count → Bool) (child parent : Fin S.count) : Bool :=
  if kept parent = some child then bits parent else false

/-- XOR of the bits entering `child` through a no-splitting successor map. -/
def hedgeRoutingIncomingBits (kept : ForestChild S)
    (bits : Fin S.count → Bool) (child : Fin S.count) : Bool :=
  (List.finRange S.count).foldl
    (fun total parent => Bool.xor total
      (hedgeRoutingParentEntry kept bits child parent)) false

/-- A selected parent's bit when it has a routing successor, and zero at a
routing sink or outside the routing node set. -/
def hedgeRoutingNonSinkBit (nodes : NodeSet S) (kept : ForestChild S)
    (bits : Fin S.count → Bool) (parent : Fin S.count) : Bool :=
  if nodes parent then
    match kept parent with
    | none => false
    | some _child => bits parent
  else
    false

/-- For one fixed parent, the XOR over all possible receiving children is
its bit exactly when the parent is a selected non-sink.  Well-formedness puts
the unique selected child inside `nodes`; off-set parents have no successor. -/
theorem hedgeRoutingParentEntry_fold_of_wellFormed
    (nodes : NodeSet S) (kept : ForestChild S)
    (wellFormed : childWellFormedBool nodes kept = true)
    (bits : Fin S.count → Bool) (parent : Fin S.count) :
    (NodeSet.members nodes).foldl
        (fun total child => Bool.xor total
          (hedgeRoutingParentEntry kept bits child parent)) false =
      hedgeRoutingNonSinkBit nodes kept bits parent := by
  cases parentInside : nodes parent
  · have parentNone := childWellFormed_off nodes kept wellFormed parentInside
    unfold hedgeRoutingNonSinkBit
    rw [if_neg (by simp [parentInside])]
    exact foldl_unchanged _ false (NodeSet.members nodes) (fun total child => by
      simp [hedgeRoutingParentEntry, parentNone])
  · cases parentChild : kept parent with
    | none =>
        unfold hedgeRoutingNonSinkBit
        rw [if_pos parentInside, parentChild]
        exact foldl_unchanged _ false (NodeSet.members nodes)
          (fun total child => by
            simp [hedgeRoutingParentEntry, parentChild])
    | some selectedChild =>
        have edgeData := childWellFormed_edge nodes kept wellFormed parentChild
        have childMember : selectedChild ∈ NodeSet.members nodes :=
          (NodeSet.mem_members_iff nodes selectedChild).mpr edgeData.2.1
        have rowEq :
            (NodeSet.members nodes).foldl
                (fun total child => Bool.xor total
                  (hedgeRoutingParentEntry kept bits child parent)) false =
              (NodeSet.members nodes).foldl
                (fun total child =>
                  if child = selectedChild then
                    Bool.xor total (bits parent)
                  else total) false := by
          apply foldl_congr
          intro total child
          by_cases same : child = selectedChild
          · subst child
            simp [hedgeRoutingParentEntry, parentChild]
          · have reverse : selectedChild ≠ child :=
              fun equal => same equal.symm
            simp [hedgeRoutingParentEntry, parentChild, same, reverse]
        rw [rowEq, foldl_xor_bit_of_mem_nodup
          (NodeSet.members nodes) childMember (NodeSet.nodup_members nodes)]
        simp [hedgeRoutingNonSinkBit, parentInside, parentChild]

/-- Transposing child and parent folds counts each routed non-sink exactly
once, independently of how many streams merge at one child. -/
theorem hedgeNodeXor_routingIncoming_of_wellFormed
    (nodes : NodeSet S) (kept : ForestChild S)
    (wellFormed : childWellFormedBool nodes kept = true)
    (bits : Fin S.count → Bool) :
    hedgeNodeXor nodes (hedgeRoutingIncomingBits kept bits) =
      (List.finRange S.count).foldl
        (fun total parent => Bool.xor total
          (hedgeRoutingNonSinkBit nodes kept bits parent)) false := by
  unfold hedgeNodeXor hedgeRoutingIncomingBits
  rw [foldl_xor_swap]
  apply foldl_congr
  intro total parent
  rw [hedgeRoutingParentEntry_fold_of_wellFormed
    nodes kept wellFormed bits parent]

/-- The full enumeration with an explicit node guard is the same as folding
the non-sink contribution over `NodeSet.members`. -/
theorem hedgeNodeXor_routingNonSink_members
    (nodes : NodeSet S) (kept : ForestChild S)
    (bits : Fin S.count → Bool) :
    (List.finRange S.count).foldl
        (fun total parent => Bool.xor total
          (hedgeRoutingNonSinkBit nodes kept bits parent)) false =
      (NodeSet.members nodes).foldl
        (fun total parent => Bool.xor total
          (match kept parent with
          | none => false
          | some _child => bits parent)) false := by
  unfold NodeSet.members NodeSet.enumerated
  rw [List.foldl_filter]
  apply foldl_congr
  intro total parent
  cases inside : nodes parent <;>
    simp [hedgeRoutingNonSinkBit, inside]

/-- The member list of the routing sinks is obtained by filtering selected
vertices for the absence of a successor. -/
theorem keptSinks_members (nodes : NodeSet S) (kept : ForestChild S) :
    NodeSet.members (keptSinks nodes kept) =
      (NodeSet.members nodes).filter fun node => decide (kept node = none) := by
  unfold NodeSet.members NodeSet.enumerated
  rw [List.filter_filter]
  apply List.filter_congr
  intro node _member
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro sink
    have parts := (keptSinks_iff nodes kept node).mp sink
    exact ⟨parts.2, parts.1⟩
  · intro parts
    exact (keptSinks_iff nodes kept node).mpr ⟨parts.2, parts.1⟩

/-- XORing all selected values with all selected non-sink values cancels
every internal stream and leaves precisely the routing-sink parity. -/
theorem hedgeNodeXor_split_keptSinks
    (nodes : NodeSet S) (kept : ForestChild S)
    (bits : Fin S.count → Bool) :
    Bool.xor
        (hedgeNodeXor nodes bits)
        ((NodeSet.members nodes).foldl
          (fun total parent => Bool.xor total
            (match kept parent with
            | none => false
            | some _child => bits parent)) false) =
      hedgeNodeXor (keptSinks nodes kept) bits := by
  unfold hedgeNodeXor
  rw [← foldl_xor_pointwise]
  have pointwise :
      (NodeSet.members nodes).foldl
          (fun total node => Bool.xor total
            (Bool.xor (bits node)
              (match kept node with
              | none => false
              | some _child => bits node))) false =
        (NodeSet.members nodes).foldl
          (fun total node => Bool.xor total
            (if kept node = none then bits node else false)) false := by
    apply foldl_congr
    intro total node
    cases childEq : kept node with
    | none => cases bits node <;> rfl
    | some child => cases bits node <;> rfl
  rw [pointwise, keptSinks_members nodes kept, List.foldl_filter]
  apply foldl_congr
  intro total node
  by_cases sink : kept node = none <;> simp [sink]

/--
Finite XOR-flow conservation for a well-formed no-splitting routing forest.
No acyclicity or choice principle is needed for the algebra itself: each
selected non-sink contributes on the left once as a node value and once as
the unique incoming contribution to its successor, so it cancels.  The
hedge's strict topological routing order is used later to establish the local
flow equations from recursive SCM evaluation.
-/
theorem hedgeRoutingFlow_conservation
    (nodes : NodeSet S) (kept : ForestChild S)
    (wellFormed : childWellFormedBool nodes kept = true)
    (source bits : Fin S.count → Bool)
    (flow : forall node, nodes node = true →
      bits node = Bool.xor (source node)
        (hedgeRoutingIncomingBits kept bits node)) :
    hedgeNodeXor (keptSinks nodes kept) bits =
      hedgeNodeXor nodes source := by
  have allNodes :
      hedgeNodeXor nodes bits =
        Bool.xor (hedgeNodeXor nodes source)
          (hedgeNodeXor nodes (hedgeRoutingIncomingBits kept bits)) := by
    unfold hedgeNodeXor
    have rewritten :
        (NodeSet.members nodes).foldl
            (fun total node => Bool.xor total (bits node)) false =
          (NodeSet.members nodes).foldl
            (fun total node => Bool.xor total
              (Bool.xor (source node)
                (hedgeRoutingIncomingBits kept bits node))) false := by
      apply foldl_congr_of_mem
      intro total node member
      rw [flow node ((NodeSet.mem_members_iff nodes node).mp member)]
    rw [rewritten, foldl_xor_pointwise]
  have incoming := hedgeNodeXor_routingIncoming_of_wellFormed
    nodes kept wellFormed bits
  rw [hedgeNodeXor_routingNonSink_members nodes kept bits] at incoming
  have split := hedgeNodeXor_split_keptSinks nodes kept bits
  rw [allNodes, incoming] at split
  symm
  rw [← split]
  generalize hedgeNodeXor nodes source = sourceParity
  generalize
    (NodeSet.members nodes).foldl
      (fun total parent => Bool.xor total
        (match kept parent with
        | none => false
        | some _child => bits parent)) false = nonSinkParity
  cases sourceParity <;> cases nonSinkParity <;> rfl

/-- Recover the effective local source of an arbitrary routed bit labelling:
the vertex bit with all incoming routed bits cancelled by XOR. -/
def hedgeRoutingLocalSource (kept : ForestChild S)
    (bits : Fin S.count → Bool) (node : Fin S.count) : Bool :=
  Bool.xor (bits node) (hedgeRoutingIncomingBits kept bits node)

/-- Flow conservation can always be stated using the recovered local source.
The Boolean group law makes the required local equation an identity, so this
form remains useful at vertices whose structural mechanism was intervened
upon and no longer satisfies its original equation. -/
theorem hedgeRoutingFlow_conservation_localSource
    (nodes : NodeSet S) (kept : ForestChild S)
    (wellFormed : childWellFormedBool nodes kept = true)
    (bits : Fin S.count → Bool) :
    hedgeNodeXor (keptSinks nodes kept) bits =
      hedgeNodeXor nodes (hedgeRoutingLocalSource kept bits) := by
  apply hedgeRoutingFlow_conservation nodes kept wellFormed
  intro node _selected
  unfold hedgeRoutingLocalSource
  generalize bits node = bit
  generalize hedgeRoutingIncomingBits kept bits node = incoming
  cases bit <;> cases incoming <;> rfl

/-- Incoming parity is unchanged when two labellings agree at every parent
that the successor map actually sends to the chosen child.  The proof scans
the finite parent enumeration and does not decide any proposition globally. -/
theorem hedgeRoutingIncomingBits_congr_of_kept
    (kept : ForestChild S) (child : Fin S.count)
    (left right : Fin S.count → Bool)
    (equal : forall parent, kept parent = some child →
      left parent = right parent) :
    hedgeRoutingIncomingBits kept left child =
      hedgeRoutingIncomingBits kept right child := by
  unfold hedgeRoutingIncomingBits hedgeRoutingParentEntry
  apply foldl_congr
  intro total parent
  cases keptEq : kept parent with
  | none => simp
  | some selectedChild =>
      by_cases selected : selectedChild = child
      · subst selectedChild
        simp [equal parent keptEq]
      · simp [selected]

/-!
The hedge's canonical all-root route forest now inherits the generic
conservation law.  Its source vector is the supplied bit vector masked to the
common c-forest roots.  Every selected root lies on a route, and every routing
sink belongs to the query outcome, so odd source parity must be visible at at
least one queried vertex.
-/

/-- The roots of a hedge are contained in its canonical routing node set. -/
theorem HedgeWitness.roots_subset_rootReadoutNodes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    NodeSet.Subset w.roots w.rootReadoutNodes :=
  fun root rootIn => w.root_in_rootReadoutNodes root rootIn

/-- Every sink of the canonical all-root routing forest is a query outcome. -/
theorem HedgeWitness.rootReadoutSinks_subset_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    NodeSet.Subset
      (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) q.outcome := by
  intro node sink
  have parts :=
    (keptSinks_iff w.rootReadoutNodes w.rootReadoutSuccessor node).mp sink
  exact w.rootReadoutSuccessor_none_is_outcome node parts.1 parts.2

/-- Source-to-sink parity conservation specialized to the hedge's canonical
all-root readout.  `sourceBits` need only be meaningful at hedge roots; the
local equation injects zero at every other routing vertex. -/
theorem HedgeWitness.rootReadoutFlow_conservation
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q)
    (sourceBits routedBits : Fin S.count → Bool)
    (flow : forall node, w.rootReadoutNodes node = true →
      routedBits node =
        Bool.xor (if w.roots node then sourceBits node else false)
          (hedgeRoutingIncomingBits w.rootReadoutSuccessor routedBits node)) :
    hedgeNodeXor
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) routedBits =
      hedgeNodeXor w.roots sourceBits := by
  calc
    hedgeNodeXor
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) routedBits =
      hedgeNodeXor w.rootReadoutNodes
        (fun node => if w.roots node then sourceBits node else false) :=
      hedgeRoutingFlow_conservation w.rootReadoutNodes
        w.rootReadoutSuccessor w.rootReadoutSuccessor_wellFormed
        (fun node => if w.roots node then sourceBits node else false)
        routedBits flow
    _ = hedgeNodeXor w.roots sourceBits :=
      hedgeNodeXor_mask_of_subset w.roots w.rootReadoutNodes
        w.roots_subset_rootReadoutNodes sourceBits

/-- If the injected hedge-root parity is odd, some queried routing sink
carries a true output bit.  This is the root-uniform observability statement
needed by the eventual multi-root countermodel. -/
theorem HedgeWitness.exists_outcome_bit_of_rootReadoutFlow
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q)
    (sourceBits routedBits : Fin S.count → Bool)
    (flow : forall node, w.rootReadoutNodes node = true →
      routedBits node =
        Bool.xor (if w.roots node then sourceBits node else false)
          (hedgeRoutingIncomingBits w.rootReadoutSuccessor routedBits node))
    (odd : hedgeNodeXor w.roots sourceBits = true) :
    Exists fun outcome =>
      q.outcome outcome = true ∧ routedBits outcome = true := by
  have sinkParity :
      hedgeNodeXor
          (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) routedBits =
        true := by
    rw [w.rootReadoutFlow_conservation sourceBits routedBits flow, odd]
  rcases exists_true_of_foldl_xor_eq_true routedBits
      (NodeSet.members
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor))
      sinkParity with
    ⟨outcome, member, outputBit⟩
  have sink :=
    (NodeSet.mem_members_iff
      (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) outcome).mp member
  exact ⟨outcome, w.rootReadoutSinks_subset_outcome outcome sink, outputBit⟩

/-!
### Executable additive readout mechanisms

The single-route wrapper above overwrites a child by one parent's bit.  That
operation cannot represent several hedge roots whose routes merge.  The
wrapper below implements the flow equation proved by the preceding section:
on a routing vertex it XORs a caller-supplied local injection with the bits of
all parents whose selected successor is that vertex.  The successor map is
still a genuine directed-edge map, so the resulting model changes mechanisms
without changing its latent projection.

`sourceBit` is kept abstract on purpose.  The later hedge construction must
choose an injection that exposes the *difference* of the two base parity
circuits at their common roots.  This layer proves transport and compatibility
only; it does not claim observational equivalence for an arbitrary injection.
-/

/-- Replace every selected routing mechanism by an additive Boolean-flow
mechanism, retaining the base model verbatim away from the routing forest. -/
def hedgeFlowReadoutModel (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (base : ExactModel S)
    (sourceBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool) : ExactModel S where
  latent := base.latent
  factor := base.factor
  prior := base.prior
  product_law := base.product_law
  mechanism := fun child parents inputs =>
    if nodes child then
      hedgeParityValue rich child
        (Bool.xor (sourceBit child parents inputs)
          (hedgeForestParentBitsFrom rich successor child parents))
    else
      base.mechanism child parents inputs

/-- Additive readout changes only structural mechanisms, so compatibility is
inherited from the base model's unchanged latent extension and projection. -/
theorem hedgeFlowReadoutModel_compatible
    (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (base : ExactModel S)
    (sourceBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (compatible : Compatible base G) :
    Compatible
      (hedgeFlowReadoutModel rich nodes successor base sourceBit) G := by
  exact ⟨compatible.1, fun i j => compatible.2 i j⟩

/-- For a well-formed routing map, the typed directed-parent fold used by an
SCM mechanism is exactly the abstract incoming-flow fold.  A proposed
successor is guaranteed to be a directed edge; all other parents contribute
zero on both sides. -/
theorem hedgeForestParentBitsFrom_eq_routingIncomingBits
    (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (values : S.Assignment) (child : Fin S.count) :
    hedgeForestParentBitsFrom rich successor child
        (fun parent _edge => values parent) =
      hedgeRoutingIncomingBits successor
        (fun parent => hedgeIsSecond rich parent (values parent)) child := by
  unfold hedgeForestParentBitsFrom hedgeRoutingIncomingBits
  apply foldl_congr
  intro total parent
  cases selected : successor parent with
  | none =>
      simp [hedgeRoutingParentEntry, selected]
  | some selectedChild =>
      by_cases same : selectedChild = child
      · subst selectedChild
        have edge :=
          (childWellFormed_edge nodes successor wellFormed selected).2.2
        simp [hedgeRoutingParentEntry, selected, edge]
      · by_cases edge : S.directed parent child = true <;>
          simp [hedgeRoutingParentEntry, selected, same, edge]

/-- At a free routing vertex, recursive SCM evaluation satisfies the exact
local XOR-flow equation: local injection plus the evaluated bits of every
selected routing parent. -/
theorem hedgeFlowReadoutModel_evalNodeUnder_bit
    (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (base : ExactModel S)
    (sourceBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : base.latent.Assignment) (child : Fin S.count)
    (selected : nodes child = true) (free : intervention child = none) :
    let routed := hedgeFlowReadoutModel rich nodes successor base sourceBit
    hedgeIsSecond rich child (routed.evalNodeUnder intervention u child) =
      Bool.xor
        (sourceBit child
          (fun parent _edge => routed.evalNodeUnder intervention u parent)
          (fun root _incident => u root))
        (hedgeRoutingIncomingBits successor (fun parent =>
          hedgeIsSecond rich parent
            (routed.evalNodeUnder intervention u parent)) child) := by
  dsimp only
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  simp only [hedgeFlowReadoutModel, selected, ↓reduceIte,
    hedgeIsSecond_parityValue]
  congr 1
  exact hedgeForestParentBitsFrom_eq_routingIncomingBits rich nodes successor
    wellFormed
    (fun parent =>
      (hedgeFlowReadoutModel rich nodes successor base sourceBit).evalNodeUnder
        intervention u parent)
    child

/-- Invert the additive routing equation at one free selected vertex.

`hedgeRoutingLocalSource` XORs the vertex output with every routed incoming
bit.  The forward mechanism XORed exactly those incoming bits with the local
injection, so the second XOR cancels them and recovers `sourceBit`.  Keeping
this lemma generic is important for observational fiber counting: both hedge
models use the same inversion principle even though their forest incidence
sources and combined successor maps differ. -/
theorem hedgeFlowReadoutModel_localSource_of_free
    (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (base : ExactModel S)
    (sourceBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : base.latent.Assignment) (child : Fin S.count)
    (selected : nodes child = true) (free : intervention child = none) :
    let routed := hedgeFlowReadoutModel rich nodes successor base sourceBit
    let bits := fun node => hedgeIsSecond rich node
      (routed.evalNodeUnder intervention u node)
    hedgeRoutingLocalSource successor bits child =
      sourceBit child
        (fun parent _edge => routed.evalNodeUnder intervention u parent)
        (fun root _incident => u root) := by
  dsimp only
  let routed := hedgeFlowReadoutModel rich nodes successor base sourceBit
  let bits := fun node => hedgeIsSecond rich node
    (routed.evalNodeUnder intervention u node)
  have equation := hedgeFlowReadoutModel_evalNodeUnder_bit rich nodes
    successor wellFormed base sourceBit intervention u child selected free
  change bits child = Bool.xor
    (sourceBit child
      (fun parent _edge => routed.evalNodeUnder intervention u parent)
      (fun root _incident => u root))
    (hedgeRoutingIncomingBits successor bits child) at equation
  unfold hedgeRoutingLocalSource
  change Bool.xor (bits child)
      (hedgeRoutingIncomingBits successor bits child) = _
  rw [equation]
  generalize
    sourceBit child
      (fun parent _edge => routed.evalNodeUnder intervention u parent)
      (fun root _incident => u root) = source
  generalize hedgeRoutingIncomingBits successor bits child = incoming
  cases source <;> cases incoming <;> rfl

/-- Observational sink parity of an additive readout is exactly the parity of
its local injections over all selected vertices.

No intervention is present, so every selected structural equation can be
inverted by `hedgeFlowReadoutModel_localSource_of_free`.  Conservation then
removes every internal routed edge in pairs.  This generic statement keeps
the combinatorial cancellation separate from the hedge-specific proof that
pair-root incidence has even total parity. -/
theorem hedgeFlowReadoutModel_sinkParity_observational
    (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (base : ExactModel S)
    (sourceBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (u : base.latent.Assignment) :
    let routed := hedgeFlowReadoutModel rich nodes successor base sourceBit
    hedgeNodeXor (keptSinks nodes successor) (fun node =>
        hedgeIsSecond rich node (routed.eval u node)) =
      hedgeNodeXor nodes (fun child =>
        sourceBit child
          (fun parent _edge => routed.eval u parent)
          (fun root _incident => u root)) := by
  dsimp only
  let routed := hedgeFlowReadoutModel rich nodes successor base sourceBit
  let bits := fun node => hedgeIsSecond rich node (routed.eval u node)
  rw [hedgeRoutingFlow_conservation_localSource nodes successor wellFormed bits]
  unfold hedgeNodeXor
  apply foldl_congr_of_mem
  intro total child member
  have selected := (NodeSet.mem_members_iff nodes child).mp member
  have recovered := hedgeFlowReadoutModel_localSource_of_free rich nodes
    successor wellFormed base sourceBit (FiniteLatentSCM.noIntervention S)
    u child selected rfl
  change hedgeRoutingLocalSource successor bits child =
    sourceBit child
      (fun parent _edge => routed.eval u parent)
      (fun root _incident => u root) at recovered
  rw [recovered]

/-- Canonical additive wrapper for a hedge.  Only hedge roots inject a local
source bit; all other routing vertices merely XOR and forward incoming flow. -/
def HedgeWitness.rootFlowReadoutModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S)
    (rootBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool) : ExactModel S :=
  hedgeFlowReadoutModel rich w.rootReadoutNodes w.rootReadoutSuccessor base
    (fun child parents inputs =>
      if w.roots child then rootBit child parents inputs else false)

/-- The canonical root-flow wrapper preserves compatibility with `G`. -/
theorem HedgeWitness.rootFlowReadoutModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S)
    (rootBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (compatible : Compatible base G) :
    Compatible (w.rootFlowReadoutModel rich base rootBit) G :=
  hedgeFlowReadoutModel_compatible rich w.rootReadoutNodes
    w.rootReadoutSuccessor base
    (fun child parents inputs =>
      if w.roots child then rootBit child parents inputs else false)
    compatible

/-- Under any intervention that leaves the routing forest free, the total bit
at its outcome sinks equals the total local bit injected at all hedge roots.
This theorem is the mechanism-level realization of
`rootReadoutFlow_conservation`. -/
theorem HedgeWitness.rootFlowReadoutModel_sinkParity
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S)
    (rootBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : base.latent.Assignment)
    (routeFree : forall node, w.rootReadoutNodes node = true →
      intervention node = none) :
    let routed := w.rootFlowReadoutModel rich base rootBit
    hedgeNodeXor
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node
          (routed.evalNodeUnder intervention u node)) =
      hedgeNodeXor w.roots (fun node =>
        rootBit node
          (fun parent _edge => routed.evalNodeUnder intervention u parent)
          (fun root _incident => u root)) := by
  dsimp only
  apply w.rootReadoutFlow_conservation
  intro node selected
  exact hedgeFlowReadoutModel_evalNodeUnder_bit rich w.rootReadoutNodes
    w.rootReadoutSuccessor w.rootReadoutSuccessor_wellFormed base
    (fun child parents inputs =>
      if w.roots child then rootBit child parents inputs else false)
    intervention u node selected (routeFree node selected)

/-- The query's canonical `do(X = second)` intervention satisfies the freedom
hypothesis of the root-flow parity theorem automatically. -/
theorem HedgeWitness.rootFlowReadoutModel_sinkParity_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S)
    (rootBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (u : base.latent.Assignment) :
    let routed := w.rootFlowReadoutModel rich base rootBit
    hedgeNodeXor
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node
          (routed.evalNodeUnder (hedgeDoSecond rich q.action) u node)) =
      hedgeNodeXor w.roots (fun node =>
        rootBit node
          (fun parent _edge =>
            routed.evalNodeUnder (hedgeDoSecond rich q.action) u parent)
          (fun root _incident => u root)) := by
  exact w.rootFlowReadoutModel_sinkParity rich base rootBit
    (hedgeDoSecond rich q.action) u
    (w.rootReadoutNodes_free_under_doSecond rich)

/-- Odd total root injection under the query intervention is observable at a
queried routing sink.  The returned outcome is concrete data extracted from
the finite sink list, not from a proposition-level choice. -/
theorem HedgeWitness.rootFlowReadoutModel_exists_outcome_bit_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S)
    (rootBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (u : base.latent.Assignment)
    (odd :
      let routed := w.rootFlowReadoutModel rich base rootBit
      hedgeNodeXor w.roots (fun node =>
        rootBit node
          (fun parent _edge =>
            routed.evalNodeUnder (hedgeDoSecond rich q.action) u parent)
          (fun root _incident => u root)) = true) :
    let routed := w.rootFlowReadoutModel rich base rootBit
    Exists fun outcome =>
      q.outcome outcome = true ∧
        hedgeIsSecond rich outcome
          (routed.evalNodeUnder (hedgeDoSecond rich q.action) u outcome) =
            true := by
  dsimp only at odd ⊢
  let routed := w.rootFlowReadoutModel rich base rootBit
  let routedBits := fun node => hedgeIsSecond rich node
    (routed.evalNodeUnder (hedgeDoSecond rich q.action) u node)
  have sinkParity :=
    w.rootFlowReadoutModel_sinkParity_doSecond rich base rootBit u
  have sinkTrue :
      hedgeNodeXor
          (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) routedBits =
        true := by
    simpa [routed, routedBits, odd] using sinkParity
  rcases exists_true_of_foldl_xor_eq_true routedBits
      (NodeSet.members
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor))
      sinkTrue with
    ⟨outcome, member, outputBit⟩
  have sink :=
    (NodeSet.mem_members_iff
      (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) outcome).mp member
  exact ⟨outcome, w.rootReadoutSinks_subset_outcome outcome sink, outputBit⟩


end Causality
end Thesis
