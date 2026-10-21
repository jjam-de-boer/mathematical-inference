import Thesis.CausalTransport.Hedge.Parity
import Thesis.CausalTransport.Hedge.WitnessSearch
import Thesis.CausalTransport.ActionDeletion

namespace Thesis
namespace Causality

open Probability

/-!
# Observational hedge equalities and countermodel bridges

This layer proves observational equalities for the finite parity pair and
constructs the older, geometrically qualified mix counterexamples. Its Boolean
readiness conditions remain explicit: a successful ready-case constructor is
not the general arbitrary-hedge completeness theorem. The unrestricted current
result is assembled separately in `HedgeChannelCompleteness`.

Only the shared parity models, graph witness search and action/query geometry
are needed here. In particular, positive carriers and outcome-flow support may
use these results without importing the historical identification engine or its
finite-depth failure stacks. The original `CompletenessHedgeCountermodels`
path remains a compatibility facade for clients that need that broad interface.
All existing declaration names, statements, computations and proof bodies are
preserved; this boundary adds no soundness or completeness assumption.
-/

/-! ### Observational equivalence of the unsoftened parity pair -/

/--
Two equally long lists have equivalent sums of singleton masses whenever any
singleton on the left is equivalent to any singleton on the right.  This
form is tailored to a uniform finite prior: no permutation or chosen matching
between the two supports is needed.
-/
theorem FiniteProbRecord.listSum_singletons_equiv_of_length
    {Ω : Type} [DecidableEq Ω]
    (leftRecord rightRecord : FiniteProbRecord Ω)
    (leftValues rightValues : List Ω)
    (sameLength : leftValues.length = rightValues.length)
    (atomEquiv : ∀ left right,
      QProb.Equiv
        (leftRecord.probVal (FiniteProbRecord.singletonEvent left))
        (rightRecord.probVal (FiniteProbRecord.singletonEvent right))) :
    QProb.Equiv
      (QProb.listSum (leftValues.map fun value =>
        leftRecord.probVal (FiniteProbRecord.singletonEvent value)))
      (QProb.listSum (rightValues.map fun value =>
        rightRecord.probVal (FiniteProbRecord.singletonEvent value))) := by
  induction leftValues generalizing rightValues with
  | nil =>
      cases rightValues with
      | nil => exact QProb.equiv_refl QProb.zero
      | cons _head _tail => cases sameLength
  | cons left leftTail ih =>
      cases rightValues with
      | nil => cases sameLength
      | cons right rightTail =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp only [List.map_cons, QProb.listSum]
          exact QProb.add_congr (atomEquiv left right)
            (ih rightTail sameLength)

/--
Every observed atom has the same probability in the large and small
unsoftened hedge models.  Valid targets are counted by the coordinate-support
theorems above.  Invalid targets have zero mass on both sides because neither
parity circuit can emit a non-distinguished value inside the large forest.
-/
theorem HedgeWitness.parityModels_observational_singleton_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    QProb.Equiv
      ((w.largeParityModel rich).observationalValue
        (FiniteProbRecord.singletonEvent target))
      ((w.smallParityModel rich).observationalValue
        (FiniteProbRecord.singletonEvent target)) := by
  cases valid : hedgeParityTargetValid rich w.large target
  · have largeNever (u : (hedgeLatentExtension G).Assignment) :
        FiniteProbRecord.singletonEvent target
            ((w.largeParityModel rich).eval u) = false := by
      apply Bool.eq_false_iff.mpr
      intro holds
      have evaluates : (w.largeParityModel rich).eval u = target :=
        of_decide_eq_true (by
          simpa [FiniteProbRecord.singletonEvent] using holds)
      have outputValid := hedgeForestParityModel_eval_valid G rich w.large
        w.child u
      change hedgeParityTargetValid rich w.large
        ((w.largeParityModel rich).eval u) = true at outputValid
      rw [evaluates, valid] at outputValid
      contradiction
    have smallNever (u : (hedgeLatentExtension G).Assignment) :
        FiniteProbRecord.singletonEvent target
            ((w.smallParityModel rich).eval u) = false := by
      apply Bool.eq_false_iff.mpr
      intro holds
      have evaluates : (w.smallParityModel rich).eval u = target :=
        of_decide_eq_true (by
          simpa [FiniteProbRecord.singletonEvent] using holds)
      have outputValid := hedgeNestedForestParityModel_eval_valid G rich
        w.large w.small w.child (restrictChild w.small w.child) u
      change hedgeParityTargetValid rich w.large
        ((w.smallParityModel rich).eval u) = true at outputValid
      rw [evaluates, valid] at outputValid
      contradiction
    have largeZero :
        QProb.Equiv
          ((w.largeParityModel rich).observationalValue
            (FiniteProbRecord.singletonEvent target)) QProb.zero :=
      QProb.equiv_trans
        ((w.largeParityModel rich).observationalValue_eq
          (FiniteProbRecord.singletonEvent target))
        (QProb.equiv_trans
          ((w.largeParityModel rich).prior.probVal_congr _ _ largeNever)
          ((w.largeParityModel rich).prior.probVal_false))
    have smallZero :
        QProb.Equiv
          ((w.smallParityModel rich).observationalValue
            (FiniteProbRecord.singletonEvent target)) QProb.zero :=
      QProb.equiv_trans
        ((w.smallParityModel rich).observationalValue_eq
          (FiniteProbRecord.singletonEvent target))
        (QProb.equiv_trans
          ((w.smallParityModel rich).prior.probVal_congr _ _ smallNever)
          ((w.smallParityModel rich).prior.probVal_false))
    exact QProb.equiv_trans largeZero (QProb.equiv_symm smallZero)
  · let largeSupport :=
      hedgeCoordinateSupportLatents G w.large target
        (hedgePairBitsRealizes G w.large
          (hedgeForestRequiredIncidence rich w.child target))
    let smallSupport :=
      hedgeCoordinateSupportLatents G w.large target
        (hedgeNestedPairBitsRealizes G w.large w.small
          (hedgeNestedForestRequiredIncidence rich w.small w.child
            (restrictChild w.small w.child) target))
    have largeEvalIff (u : (hedgeLatentExtension G).Assignment) :
        (w.largeParityModel rich).eval u = target ↔ u ∈ largeSupport := by
      simpa [HedgeWitness.largeParityModel, largeSupport] using
        (hedgeForestParityModel_eval_mem_coordinateSupport_iff
          G rich w.large w.child target valid u)
    have smallEvalIff (u : (hedgeLatentExtension G).Assignment) :
        (w.smallParityModel rich).eval u = target ↔ u ∈ smallSupport := by
      simpa [HedgeWitness.smallParityModel, smallSupport] using
        (hedgeNestedForestParityModel_eval_mem_coordinateSupport_iff
          G rich w.large w.small w.child
          (restrictChild w.small w.child) w.small_subset_large
          target valid u)
    have largeEvent (u : (hedgeLatentExtension G).Assignment) :
        FiniteProbRecord.singletonEvent target
            ((w.largeParityModel rich).eval u) =
          FiniteProbRecord.membershipEvent largeSupport u := by
      apply Bool.eq_iff_iff.mpr
      simpa only [FiniteProbRecord.singletonEvent,
        FiniteProbRecord.membershipEvent, decide_eq_true_eq] using
          largeEvalIff u
    have smallEvent (u : (hedgeLatentExtension G).Assignment) :
        FiniteProbRecord.singletonEvent target
            ((w.smallParityModel rich).eval u) =
          FiniteProbRecord.membershipEvent smallSupport u := by
      apply Bool.eq_iff_iff.mpr
      simpa only [FiniteProbRecord.singletonEvent,
        FiniteProbRecord.membershipEvent, decide_eq_true_eq] using
          smallEvalIff u
    have largeMembership :
        QProb.Equiv
          ((w.largeParityModel rich).prior.probVal fun u =>
            FiniteProbRecord.singletonEvent target
              ((w.largeParityModel rich).eval u))
          ((w.largeParityModel rich).prior.probVal
            (FiniteProbRecord.membershipEvent largeSupport)) :=
      (w.largeParityModel rich).prior.probVal_congr _ _ largeEvent
    have smallMembership :
        QProb.Equiv
          ((w.smallParityModel rich).prior.probVal fun u =>
            FiniteProbRecord.singletonEvent target
              ((w.smallParityModel rich).eval u))
          ((w.smallParityModel rich).prior.probVal
            (FiniteProbRecord.membershipEvent smallSupport)) :=
      (w.smallParityModel rich).prior.probVal_congr _ _ smallEvent
    have largeSum := FiniteProbRecord.probVal_membership_equiv_listSum
      (w.largeParityModel rich).prior largeSupport
      (by
        simpa [largeSupport] using
          hedgeCoordinateSupportLatents_nodup G w.large target
            (hedgePairBitsRealizes G w.large
              (hedgeForestRequiredIncidence rich w.child target)))
    have smallSum := FiniteProbRecord.probVal_membership_equiv_listSum
      (w.smallParityModel rich).prior smallSupport
      (by
        simpa [smallSupport] using
          hedgeCoordinateSupportLatents_nodup G w.large target
            (hedgeNestedPairBitsRealizes G w.large w.small
              (hedgeNestedForestRequiredIncidence rich w.small w.child
                (restrictChild w.small w.child) target)))
    have supportLength : largeSupport.length = smallSupport.length := by
      simpa [largeSupport, smallSupport] using
        w.parityCoordinateSupport_length_eq rich target
    have atomEquiv
        (left right : (hedgeLatentExtension G).Assignment) :
        QProb.Equiv
          ((w.largeParityModel rich).prior.probVal
            (FiniteProbRecord.singletonEvent left))
          ((w.smallParityModel rich).prior.probVal
            (FiniteProbRecord.singletonEvent right)) := by
      change QProb.Equiv
        ((FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).probVal
            (FiniteProbRecord.singletonEvent left))
        ((FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).probVal
            (FiniteProbRecord.singletonEvent right))
      exact hedgePrior_singleton_equiv G left right
    have equalSums :=
      FiniteProbRecord.listSum_singletons_equiv_of_length
        (w.largeParityModel rich).prior (w.smallParityModel rich).prior
        largeSupport smallSupport supportLength atomEquiv
    exact QProb.equiv_trans
      ((w.largeParityModel rich).observationalValue_eq
        (FiniteProbRecord.singletonEvent target))
      (QProb.equiv_trans largeMembership
        (QProb.equiv_trans largeSum
          (QProb.equiv_trans equalSums
            (QProb.equiv_trans (QProb.equiv_symm smallSum)
              (QProb.equiv_trans (QProb.equiv_symm smallMembership)
                (QProb.equiv_symm
                  ((w.smallParityModel rich).observationalValue_eq
                    (FiniteProbRecord.singletonEvent target))))))))

/-- The faithful unsoftened large and small hedge models agree observationally. -/
theorem HedgeWitness.parityModels_observationally_equivalent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ObservationallyEquivalent (w.largeParityModel rich)
      (w.smallParityModel rich) := by
  intro event
  exact FiniteProbRecord.probVal_extensional_of_singletons
    (w.largeParityModel rich).observationalDist
    (w.smallParityModel rich).observationalDist
    S.assignmentEnumeration S.assignmentEnumeration_nodup
    S.assignmentEnumeration_complete
    (w.parityModels_observational_singleton_equiv rich) event

/-- Complete unrestricted-class counterexample for the common-root parity
query. This record concerns `w.rootParityQuery rich`, not the original outcome
query, and it does not claim positivity of its unsoftened pair. The separate
channel construction in `HedgeChannelCompleteness` supplies positive
countermodels for the original query. No unproved general-completeness
obligation is hidden in this root-parity constructor. -/
def HedgeWitness.rootParityCounterexample
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    CounterexampleIn (GraphModelClass.all G) (w.rootParityQuery rich) where
  left := w.largeParityModel rich
  right := w.smallParityModel rich
  left_mem := w.largeParityModel_compatible rich
  right_mem := w.smallParityModel_compatible rich
  observationally_equal := w.parityModels_observationally_equivalent rich
  query_separated :=
    (w.rootParityInterventionalQuery rich).not_kernelValueEquivalent_of_not_value
      (w.largeParityModel rich) (w.smallParityModel rich)
      (w.rootParityInterventionalQuery_not_equiv rich)

/-- A single selected internal root contributes one at an incident endpoint. -/
theorem hedgeXorPairBitsWithinFrom_of_one
    (G : ObservedGraph S) (nodes : NodeSet S)
    (child : Fin S.count) (root : Fin (pairRootCount G))
    (pairBits : (r : Fin (pairRootCount G)) → Bool)
    (hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true)
    (hwithin : hedgePairRootWithin G nodes root = true)
    (htrue : pairBits root = true)
    (hrest : forall r, r ≠ root → pairBits r = false) :
    hedgeXorPairBitsWithinFrom G nodes child pairBits = true := by
  unfold hedgeXorPairBitsWithinFrom
  have hstep (acc : Bool) (r : Fin (pairRootCount G)) :
      (if (hedgeLatentExtension G).incident (hedgePairRoot G r) child &&
            hedgePairRootWithin G nodes r then
          Bool.xor acc (pairBits r)
        else acc) =
        if r = root then !acc else acc := by
    if hr : r = root then
      subst hr
      simp [hinc, hwithin, htrue]
    else
      simp [hr, hrest r hr]
  have hfold :=
    foldl_congr
      (fun acc r =>
        if (hedgeLatentExtension G).incident (hedgePairRoot G r) child &&
              hedgePairRootWithin G nodes r then
          Bool.xor acc (pairBits r)
        else acc)
      (fun acc r => if r = root then !acc else acc)
      false (List.finRange (pairRootCount G)) hstep
  rw [hfold]
  exact foldl_xor_true_at (pairRootCount G) root

/-- Lighting one path edge flips the restricted parity at its left endpoint. -/
theorem hedgeXorPairBitsWithinFrom_one_between_left
    (G : ObservedGraph S) (nodes : NodeSet S)
    {i j : Fin S.count}
    (hi : nodes i = true) (hj : nodes j = true)
    (edge : G.bidirected i j = true) :
    hedgeXorPairBitsWithinFrom G nodes i
        (hedgeOnePairBits G (pairRootBetween G edge)) = true :=
  hedgeXorPairBitsWithinFrom_of_one G nodes i (pairRootBetween G edge)
    (hedgeOnePairBits G (pairRootBetween G edge))
    (hedgePairRootBetween_incident_left G edge)
    (hedgePairRootWithin_between G nodes hi hj edge)
    (hedgeOnePairBits_self G (pairRootBetween G edge))
    (fun _root hne => hedgeOnePairBits_rest G (pairRootBetween G edge) hne)

/-- Lighting one path edge also flips the parity at its right endpoint. -/
theorem hedgeXorPairBitsWithinFrom_one_between_right
    (G : ObservedGraph S) (nodes : NodeSet S)
    {i j : Fin S.count}
    (hi : nodes i = true) (hj : nodes j = true)
    (edge : G.bidirected i j = true) :
    hedgeXorPairBitsWithinFrom G nodes j
        (hedgeOnePairBits G (pairRootBetween G edge)) = true :=
  hedgeXorPairBitsWithinFrom_of_one G nodes j (pairRootBetween G edge)
    (hedgeOnePairBits G (pairRootBetween G edge))
    (hedgePairRootBetween_incident_right G edge)
    (hedgePairRootWithin_between G nodes hi hj edge)
    (hedgeOnePairBits_self G (pairRootBetween G edge))
    (fun _root hne => hedgeOnePairBits_rest G (pairRootBetween G edge) hne)

/--
Latent assignment with a single incident pair-root set, used as an extra
preimage of `Y = first` under the empty-mask mix.
-/
def hedgeMixExtraLatent (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (root : Fin (pairRootCount G)) :
    (hedgeLatentExtension G).Assignment :=
  hedgeSupportLatentWithPairs G rich NodeSet.empty
    (fun i => rich.first i) (hedgeOnePairBits G root)

theorem hedgeMixExtraLatent_xor (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (root : Fin (pairRootCount G))
    {y : Fin S.count}
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    hedgeXorPairBits G y (fun latent _ => hedgeMixExtraLatent G rich root latent) =
      true := by
  unfold hedgeMixExtraLatent
  exact
    (hedgeXorPairBits_supportWithPairs G rich NodeSet.empty
          (fun i => rich.first i) (hedgeOnePairBits G root) y).trans
      (hedgeXorPairBitsFrom_of_one G y root (hedgeOnePairBits G root) hinc
        (hedgeOnePairBits_self G root)
        (fun r hne => hedgeOnePairBits_rest G root hne))

theorem eventMass_union_disjoint {Ω : Type _}
    (atoms : List (Ω × Nat)) (E F : Event Ω) (h : disjoint E F) :
    FiniteProbRecord.eventMass atoms (union E F) =
      FiniteProbRecord.eventMass atoms E +
        FiniteProbRecord.eventMass atoms F := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases hE : E value <;> cases hF : F value
      · simp [FiniteProbRecord.eventMass, union, hE, hF, ih]
      · simp [FiniteProbRecord.eventMass, union, hE, hF, ih]
        omega
      · simp [FiniteProbRecord.eventMass, union, hE, hF, ih]
        omega
      · exact False.elim (h value hE hF)

/-- A free node in the one-root model evaluates through its local mix. -/
theorem hedgeSingleRootMixModel_evalNodeUnder_of_none
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment) {child : Fin S.count}
    (free : intervention child = none) :
    (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
        intervention u child =
      hedgeMixFrom rich child
        (hedgePairRootBit G root child (fun latent _ => u latent))
        (hedgeParentBitsFrom rich mask child
          (fun parent _ =>
            (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
              intervention u parent))
        (hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun latent _ => u latent))) := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  rfl

/-- Interventions override a selected one-root mix node definitionally. -/
theorem hedgeSingleRootMixModel_evalNodeUnder_doSecond
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask action : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) {node : Fin S.count}
    (selected : action node = true) :
    (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
        (hedgeDoSecond rich action) u node = rich.second node := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [hedgeDoSecond_of_true rich action selected]

/--
With a singleton mask, a selected directed pivot is the unique contributor to
the child's parent bit under the all-`second` query intervention.
-/
theorem hedgeSingleRootMix_parentBits_singleton_doSecond
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (action : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) {pivot child : Fin S.count}
    (selected : action pivot = true)
    (edge : S.directed pivot child = true) :
    hedgeParentBitsFrom rich (NodeSet.singleton pivot) child
        (fun parent _ =>
          (hedgeSingleRootMixModel G rich root
            (NodeSet.singleton pivot)).evalNodeUnder
              (hedgeDoSecond rich action) u parent) = true := by
  rw [hedgeParentBitsFrom_of_unique rich (NodeSet.singleton pivot)
    (fun parent _ =>
      (hedgeSingleRootMixModel G rich root
        (NodeSet.singleton pivot)).evalNodeUnder
          (hedgeDoSecond rich action) u parent)
    edge (by simp [NodeSet.singleton])
    (fun parent inMask _parentEdge =>
      (NodeSet.singleton_eq_true_iff pivot parent).mp inMask)]
  rw [hedgeSingleRootMixModel_evalNodeUnder_doSecond G rich root
    (NodeSet.singleton pivot) action u selected, hedgeIsSecond_second]

/-- The designated extra latent assignment turns on its selected root bit. -/
theorem hedgeMixExtraLatent_pairRootBit
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) {child : Fin S.count}
    (incident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true) :
    hedgePairRootBit G root child
        (fun latent _ => hedgeMixExtraLatent G rich root latent) = true := by
  simp [hedgePairRootBit, incident, hedgeMixExtraLatent,
    hedgeSupportLatentWithPairs_pair, hedgeOnePairBits_self]

/--
For a one-root mix, turning on an incident selected root contributes a strict
extra mass of `Y = first` to the empty mask.  This is the root-local analogue
of `hedgeMix_interventional_first_mass_lt_of_parentBit`; unrelated pair-roots
play no role in either event.
-/
theorem hedgeSingleRootMix_interventional_first_mass_lt_of_parentBit
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {y : Fin S.count}
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (free : intervention y = none)
    (parentBit : forall u : (hedgeLatentExtension G).Assignment,
      hedgeParentBitsFrom rich mask y
          (fun parent _ =>
            (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
              intervention u parent) = true)
    (incident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    FiniteProbRecord.eventMass
        (hedgeSingleRootMixModel G rich root mask).prior.atoms
        (fun u =>
          decide
            ((hedgeSingleRootMixModel G rich root mask).evalUnder
                intervention u y = rich.first y)) <
      FiniteProbRecord.eventMass
        (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
        (fun u =>
          decide
            ((hedgeSingleRootMixModel G rich root NodeSet.empty).evalUnder
                intervention u y = rich.first y)) := by
  let extra : Event ((hedgeLatentExtension G).Assignment) :=
    fun u => hedgePairRootBit G root y (fun latent _ => u latent)
  let maskedFirst : Event ((hedgeLatentExtension G).Assignment) :=
    fun u =>
      decide
        ((hedgeSingleRootMixModel G rich root mask).evalUnder intervention u y =
          rich.first y)
  let emptyFirst : Event ((hedgeLatentExtension G).Assignment) :=
    fun u =>
      decide
        ((hedgeSingleRootMixModel G rich root NodeSet.empty).evalUnder
            intervention u y = rich.first y)
  have maskedEval (u : (hedgeLatentExtension G).Assignment) :
      (hedgeSingleRootMixModel G rich root mask).evalUnder intervention u y =
        hedgeMixFrom rich y
          (hedgePairRootBit G root y (fun latent _ => u latent)) true
          (hedgePrivateDecode S y
            (hedgePrivateIndex G y (fun latent _ => u latent))) := by
    unfold FiniteLatentSCM.evalUnder
    rw [hedgeSingleRootMixModel_evalNodeUnder_of_none G rich root mask
      intervention u free]
    rw [parentBit u]
  have emptyEval (u : (hedgeLatentExtension G).Assignment) :
      (hedgeSingleRootMixModel G rich root NodeSet.empty).evalUnder
          intervention u y =
        hedgeMixFrom rich y
          (hedgePairRootBit G root y (fun latent _ => u latent)) false
          (hedgePrivateDecode S y
            (hedgePrivateIndex G y (fun latent _ => u latent))) := by
    unfold FiniteLatentSCM.evalUnder
    rw [hedgeSingleRootMixModel_evalNodeUnder_of_none G rich root
      NodeSet.empty intervention u free]
    rw [hedgeParentBitsFrom_empty]
  have disjointExtra : disjoint extra maskedFirst := by
    intro u extraTrue maskedTrue
    have valueEq := maskedEval u
    have switchTrue :
        hedgePairRootBit G root y (fun latent _ => u latent) = true :=
      extraTrue
    rw [switchTrue, hedgeMixFrom_true_second] at valueEq
    have valueFirst :
        (hedgeSingleRootMixModel G rich root mask).evalUnder intervention u y =
          rich.first y :=
      of_decide_eq_true (by simpa [maskedFirst] using maskedTrue)
    exact rich.different y (valueFirst.symm.trans valueEq)
  have emptyAsUnion (u : (hedgeLatentExtension G).Assignment) :
      emptyFirst u = union extra maskedFirst u := by
    simp [emptyFirst, extra, maskedFirst, union, emptyEval u, maskedEval u]
    cases switch : hedgePairRootBit G root y (fun latent _ => u latent) with
    | true =>
        have different : rich.second y ≠ rich.first y :=
          fun equal => rich.different y equal.symm
        simp [hedgeMixFrom_true_first, hedgeMixFrom_true_second, different]
    | false =>
        simp [hedgeMixFrom_false]
  have unionMass :
      FiniteProbRecord.eventMass
          (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
          emptyFirst =
        FiniteProbRecord.eventMass
            (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
            extra +
          FiniteProbRecord.eventMass
            (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
            maskedFirst := by
    have congruent :=
      FiniteProbRecord.eventMass_congr
        (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
        emptyFirst (union extra maskedFirst) emptyAsUnion
    exact congruent.trans
      (eventMass_union_disjoint
        (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
        extra maskedFirst disjointExtra)
  have extraPositive :
      0 <
        FiniteProbRecord.eventMass
          (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
          extra := by
    have extraTrue := hedgeMixExtraLatent_pairRootBit G rich root incident
    have singletonMass :=
      hedgePrior_eventMass_singleton G (hedgeMixExtraLatent G rich root)
    have singletonSubset :
        forall v,
          FiniteProbRecord.singletonEvent (hedgeMixExtraLatent G rich root) v =
              true →
            extra v = true := by
      intro v selected
      have equal : v = hedgeMixExtraLatent G rich root :=
        of_decide_eq_true
          (by simpa [FiniteProbRecord.singletonEvent] using selected)
      simpa [equal] using extraTrue
    have monotone :=
      FiniteProbRecord.eventMass_mono
        (FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).atoms
        (FiniteProbRecord.singletonEvent (hedgeMixExtraLatent G rich root))
        extra singletonSubset
    exact Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_eq Nat.zero_lt_one singletonMass.symm) monotone
  have atomsEqual :
      (hedgeSingleRootMixModel G rich root mask).prior.atoms =
        (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms :=
    rfl
  change
    FiniteProbRecord.eventMass
        (hedgeSingleRootMixModel G rich root mask).prior.atoms maskedFirst <
      FiniteProbRecord.eventMass
        (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
        emptyFirst
  rw [atomsEqual, unionMass]
  exact Nat.lt_add_of_pos_left extraPositive

/-- The strict one-root mass gap rules out equivalent interventional values. -/
theorem hedgeSingleRootMix_interventional_first_not_equiv_of_parentBit
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {y : Fin S.count}
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (free : intervention y = none)
    (parentBit : forall u : (hedgeLatentExtension G).Assignment,
      hedgeParentBitsFrom rich mask y
          (fun parent _ =>
            (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
              intervention u parent) = true)
    (incident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (QProb.Equiv
        ((hedgeSingleRootMixModel G rich root mask).interventionalValue
          intervention (fun a => decide (a y = rich.first y)))
        ((hedgeSingleRootMixModel G rich root NodeSet.empty).interventionalValue
          intervention (fun a => decide (a y = rich.first y)))) := by
  intro equivalent
  have maskedValue :=
    FiniteLatentSCM.interventionalValue_eq
      (hedgeSingleRootMixModel G rich root mask) intervention
      (fun a => decide (a y = rich.first y))
  have emptyValue :=
    FiniteLatentSCM.interventionalValue_eq
      (hedgeSingleRootMixModel G rich root NodeSet.empty) intervention
      (fun a => decide (a y = rich.first y))
  have priorEquivalent :
      QProb.Equiv
        ((hedgeSingleRootMixModel G rich root mask).prior.probVal
          (fun u =>
            decide
              ((hedgeSingleRootMixModel G rich root mask).evalUnder
                  intervention u y = rich.first y)))
        ((hedgeSingleRootMixModel G rich root NodeSet.empty).prior.probVal
          (fun u =>
            decide
              ((hedgeSingleRootMixModel G rich root NodeSet.empty).evalUnder
                  intervention u y = rich.first y))) :=
    QProb.equiv_trans (QProb.equiv_symm maskedValue)
      (QProb.equiv_trans equivalent emptyValue)
  have strictlyLess :=
    hedgeSingleRootMix_interventional_first_mass_lt_of_parentBit G rich root
      mask intervention free parentBit incident
  have priorEqual :
      (hedgeSingleRootMixModel G rich root mask).prior =
        (hedgeSingleRootMixModel G rich root NodeSet.empty).prior :=
    rfl
  have massesEqual :
      FiniteProbRecord.eventMass
          (hedgeSingleRootMixModel G rich root mask).prior.atoms
          (fun u =>
            decide
              ((hedgeSingleRootMixModel G rich root mask).evalUnder
                  intervention u y = rich.first y)) =
        FiniteProbRecord.eventMass
          (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
          (fun u =>
            decide
              ((hedgeSingleRootMixModel G rich root NodeSet.empty).evalUnder
                  intervention u y = rich.first y)) := by
    have crossProduct :
        FiniteProbRecord.eventMass
            (hedgeSingleRootMixModel G rich root mask).prior.atoms
            (fun u =>
              decide
                ((hedgeSingleRootMixModel G rich root mask).evalUnder
                    intervention u y = rich.first y)) *
          (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.den =
        FiniteProbRecord.eventMass
            (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.atoms
            (fun u =>
              decide
                ((hedgeSingleRootMixModel G rich root NodeSet.empty).evalUnder
                    intervention u y = rich.first y)) *
          (hedgeSingleRootMixModel G rich root mask).prior.den := by
      simpa [QProb.Equiv, FiniteProbRecord.probVal] using priorEquivalent
    have denominatorsEqual :
        (hedgeSingleRootMixModel G rich root mask).prior.den =
          (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.den := by
      rw [priorEqual]
    rw [denominatorsEqual] at crossProduct
    exact Nat.eq_of_mul_eq_mul_right
      (hedgeSingleRootMixModel G rich root NodeSet.empty).prior.den_pos
      crossProduct
  exact Nat.ne_of_lt strictlyLess massesEqual

/--
Whenever an intervention leaves `Y` free and makes its action-mask parent bit
true, `P(Y = first)` is strictly larger for the empty-mask mix than for the
action-mask mix.  The extra mass is the copy branch `xorBits = true`, which
emits `first` when parents are ignored and `second` when that parent bit is
copied.
-/
theorem hedgeMix_interventional_first_mass_lt_of_parentBit
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {y : Fin S.count}
    (action : NodeSet S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (root : Fin (pairRootCount G))
    (free : intervention y = none)
    (parentBit : forall u : (hedgeLatentExtension G).Assignment,
      hedgeParentBitsFrom rich action y
          (fun parent _ =>
            (hedgeMixModel G rich action).evalNodeUnder intervention u parent) =
        true)
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    FiniteProbRecord.eventMass
        (hedgeMixModel G rich action).prior.atoms
        (fun u =>
          decide
            ((hedgeMixModel G rich action).evalUnder
                intervention u y =
              rich.first y)) <
      FiniteProbRecord.eventMass
        (hedgeMixModel G rich NodeSet.empty).prior.atoms
        (fun u =>
          decide
            ((hedgeMixModel G rich NodeSet.empty).evalUnder
                intervention u y =
              rich.first y)) := by
  let extra : Event ((hedgeLatentExtension G).Assignment) :=
    fun u => hedgeXorPairBits G y (fun latent _ => u latent)
  let actionFirst : Event ((hedgeLatentExtension G).Assignment) :=
    fun u =>
      decide
        ((hedgeMixModel G rich action).evalUnder intervention u y =
          rich.first y)
  let emptyFirst : Event ((hedgeLatentExtension G).Assignment) :=
    fun u =>
      decide
        ((hedgeMixModel G rich NodeSet.empty).evalUnder
            intervention u y =
          rich.first y)
  have hactionEval (u : (hedgeLatentExtension G).Assignment) :
      (hedgeMixModel G rich action).evalUnder intervention u y =
        hedgeMixFrom rich y
          (hedgeXorPairBits G y (fun latent _ => u latent)) true
          (hedgePrivateDecode S y
            (hedgePrivateIndex G y (fun latent _ => u latent))) := by
    unfold FiniteLatentSCM.evalUnder
    rw [hedgeMixModel_evalNodeUnder_of_none G rich action intervention u free]
    rw [parentBit u]
  have hemptyEval (u : (hedgeLatentExtension G).Assignment) :
      (hedgeMixModel G rich NodeSet.empty).evalUnder
          intervention u y =
        hedgeMixFrom rich y
          (hedgeXorPairBits G y (fun latent _ => u latent)) false
          (hedgePrivateDecode S y
            (hedgePrivateIndex G y (fun latent _ => u latent))) := by
    unfold FiniteLatentSCM.evalUnder
    rw [hedgeMixModel_evalNodeUnder_of_none G rich NodeSet.empty intervention u
      free]
    rw [hedgeParentBitsFrom_empty]
  have hdis : disjoint extra actionFirst := by
    intro u hextra hact
    have hyval := hactionEval u
    have hxor :
        hedgeXorPairBits G y (fun latent _ => u latent) = true := hextra
    rw [hxor, hedgeMixFrom_true_second] at hyval
    have hyfirst :
        (hedgeMixModel G rich action).evalUnder intervention u y =
          rich.first y :=
      of_decide_eq_true (by simpa [actionFirst] using hact)
    exact rich.different y (hyfirst.symm.trans hyval)
  have hunion (u : (hedgeLatentExtension G).Assignment) :
      emptyFirst u = union extra actionFirst u := by
    simp [emptyFirst, extra, actionFirst, union, hemptyEval u, hactionEval u]
    cases hxor : hedgeXorPairBits G y (fun latent _ => u latent) with
    | true =>
        have hne : rich.second y ≠ rich.first y :=
          fun h => rich.different y h.symm
        simp [hedgeMixFrom_true_first, hedgeMixFrom_true_second, hne]
    | false =>
        simp [hedgeMixFrom_false]
  have hmass_union :
      FiniteProbRecord.eventMass
          (hedgeMixModel G rich NodeSet.empty).prior.atoms emptyFirst =
        FiniteProbRecord.eventMass
            (hedgeMixModel G rich NodeSet.empty).prior.atoms extra +
          FiniteProbRecord.eventMass
            (hedgeMixModel G rich NodeSet.empty).prior.atoms actionFirst := by
    have hcong :=
      FiniteProbRecord.eventMass_congr
        (hedgeMixModel G rich NodeSet.empty).prior.atoms emptyFirst
        (union extra actionFirst) hunion
    exact hcong.trans
      (eventMass_union_disjoint
        (hedgeMixModel G rich NodeSet.empty).prior.atoms extra actionFirst
        hdis)
  have hextra_pos :
      0 <
        FiniteProbRecord.eventMass
          (hedgeMixModel G rich NodeSet.empty).prior.atoms extra := by
    have hu := hedgeMixExtraLatent_xor G rich root hinc
    have hsing :=
      hedgePrior_eventMass_singleton G (hedgeMixExtraLatent G rich root)
    have hsub :
        forall v,
          FiniteProbRecord.singletonEvent (hedgeMixExtraLatent G rich root) v =
              true →
            extra v = true := by
      intro v hv
      have heq : v = hedgeMixExtraLatent G rich root :=
        of_decide_eq_true (by simpa [FiniteProbRecord.singletonEvent] using hv)
      simpa [heq] using hu
    have hmono :=
      FiniteProbRecord.eventMass_mono
        (FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).atoms
        (FiniteProbRecord.singletonEvent (hedgeMixExtraLatent G rich root))
        extra hsub
    exact Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_eq Nat.zero_lt_one hsing.symm) hmono
  have hatoms :
      (hedgeMixModel G rich action).prior.atoms =
        (hedgeMixModel G rich NodeSet.empty).prior.atoms :=
    rfl
  change
    FiniteProbRecord.eventMass
        (hedgeMixModel G rich action).prior.atoms actionFirst <
      FiniteProbRecord.eventMass
        (hedgeMixModel G rich NodeSet.empty).prior.atoms emptyFirst
  rw [hatoms, hmass_union]
  exact Nat.lt_add_of_pos_left hextra_pos

/--
All-`second` specialization of the generic parent-bit mass separation.  Odd
action-parent parity is exactly the parent bit produced by this intervention.
-/
theorem hedgeMix_interventional_first_mass_lt_of_parentParity
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {y : Fin S.count}
    (action : NodeSet S) (root : Fin (pairRootCount G))
    (hy : action y = false)
    (hparity : actionParentParity action y = true)
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    FiniteProbRecord.eventMass
        (hedgeMixModel G rich action).prior.atoms
        (fun u =>
          decide
            ((hedgeMixModel G rich action).evalUnder
                (hedgeDoSecond rich action) u y =
              rich.first y)) <
      FiniteProbRecord.eventMass
        (hedgeMixModel G rich NodeSet.empty).prior.atoms
        (fun u =>
          decide
            ((hedgeMixModel G rich NodeSet.empty).evalUnder
                (hedgeDoSecond rich action) u y =
              rich.first y)) :=
  hedgeMix_interventional_first_mass_lt_of_parentBit G rich action
    (hedgeDoSecond rich action) root
    (hedgeDoSecond_of_false rich action hy)
    (fun u =>
      (hedgeParentBitsFrom_doSecond_eq_actionParentParity G rich action u y).trans
        hparity)
    hinc

/--
Unique-parent compatibility form of
`hedgeMix_interventional_first_mass_lt_of_parentParity`.
-/
theorem hedgeMix_interventional_first_mass_lt (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {x y : Fin S.count}
    (action : NodeSet S) (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true) (hx : action x = true)
    (hy : action y = false)
    (huniq : forall p, action p = true → S.directed p y = true → p = x)
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    FiniteProbRecord.eventMass
        (hedgeMixModel G rich action).prior.atoms
        (fun u =>
          decide
            ((hedgeMixModel G rich action).evalUnder
                (hedgeDoSecond rich action) u y =
              rich.first y)) <
      FiniteProbRecord.eventMass
        (hedgeMixModel G rich NodeSet.empty).prior.atoms
        (fun u =>
          decide
            ((hedgeMixModel G rich NodeSet.empty).evalUnder
                (hedgeDoSecond rich action) u y =
              rich.first y)) :=
  hedgeMix_interventional_first_mass_lt_of_parentParity G rich action root hy
    (actionParentParity_eq_true_of_unique action hdir hx huniq) hinc

/--
The generic parent-bit mass gap gives inequivalent interventional
probabilities for the cylinder `Y = first`.
-/
theorem hedgeMix_interventional_first_not_equiv_of_parentBit
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {y : Fin S.count}
    (action : NodeSet S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (root : Fin (pairRootCount G))
    (free : intervention y = none)
    (parentBit : forall u : (hedgeLatentExtension G).Assignment,
      hedgeParentBitsFrom rich action y
          (fun parent _ =>
            (hedgeMixModel G rich action).evalNodeUnder intervention u parent) =
        true)
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (QProb.Equiv
        ((hedgeMixModel G rich action).interventionalValue
          intervention
          (fun a => decide (a y = rich.first y)))
        ((hedgeMixModel G rich NodeSet.empty).interventionalValue
          intervention
          (fun a => decide (a y = rich.first y)))) := by
  intro heq
  have hact :=
    FiniteLatentSCM.interventionalValue_eq
      (hedgeMixModel G rich action) intervention
      (fun a => decide (a y = rich.first y))
  have hemp :=
    FiniteLatentSCM.interventionalValue_eq
      (hedgeMixModel G rich NodeSet.empty) intervention
      (fun a => decide (a y = rich.first y))
  have hmass :
      QProb.Equiv
        ((hedgeMixModel G rich action).prior.probVal
          (fun u =>
            decide
              ((hedgeMixModel G rich action).evalUnder
                  intervention u y =
                rich.first y)))
        ((hedgeMixModel G rich NodeSet.empty).prior.probVal
          (fun u =>
            decide
              ((hedgeMixModel G rich NodeSet.empty).evalUnder
                  intervention u y =
                rich.first y))) :=
    QProb.equiv_trans (QProb.equiv_symm hact) (QProb.equiv_trans heq hemp)
  have hlt :=
    hedgeMix_interventional_first_mass_lt_of_parentBit G rich action
      intervention root free parentBit hinc
  have hprior :
      (hedgeMixModel G rich action).prior =
        (hedgeMixModel G rich NodeSet.empty).prior :=
    rfl
  have hnums :
      FiniteProbRecord.eventMass
          (hedgeMixModel G rich action).prior.atoms
          (fun u =>
            decide
              ((hedgeMixModel G rich action).evalUnder
                  intervention u y =
                rich.first y)) =
        FiniteProbRecord.eventMass
          (hedgeMixModel G rich NodeSet.empty).prior.atoms
          (fun u =>
            decide
              ((hedgeMixModel G rich NodeSet.empty).evalUnder
                  intervention u y =
                rich.first y)) := by
    have hmul :
        FiniteProbRecord.eventMass
            (hedgeMixModel G rich action).prior.atoms
            (fun u =>
              decide
                ((hedgeMixModel G rich action).evalUnder
                    intervention u y =
                  rich.first y)) *
          (hedgeMixModel G rich NodeSet.empty).prior.den =
          FiniteProbRecord.eventMass
            (hedgeMixModel G rich NodeSet.empty).prior.atoms
            (fun u =>
              decide
                ((hedgeMixModel G rich NodeSet.empty).evalUnder
                    intervention u y =
                  rich.first y)) *
            (hedgeMixModel G rich action).prior.den := by
      simpa [QProb.Equiv, FiniteProbRecord.probVal] using hmass
    have hden :
        (hedgeMixModel G rich action).prior.den =
          (hedgeMixModel G rich NodeSet.empty).prior.den := by
      rw [hprior]
    rw [hden] at hmul
    exact
      Nat.eq_of_mul_eq_mul_right
        (hedgeMixModel G rich NodeSet.empty).prior.den_pos
        hmul
  exact Nat.ne_of_lt hlt hnums

/--
All-`second` specialization of generic parent-bit inequivalence.  It retains
the odd-parity API used by the existing positive hedge leaves.
-/
theorem hedgeMix_interventional_first_not_equiv_of_parentParity
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {y : Fin S.count}
    (action : NodeSet S) (root : Fin (pairRootCount G))
    (hy : action y = false)
    (hparity : actionParentParity action y = true)
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (QProb.Equiv
        ((hedgeMixModel G rich action).interventionalValue
          (hedgeDoSecond rich action)
          (fun a => decide (a y = rich.first y)))
        ((hedgeMixModel G rich NodeSet.empty).interventionalValue
          (hedgeDoSecond rich action)
          (fun a => decide (a y = rich.first y)))) :=
  hedgeMix_interventional_first_not_equiv_of_parentBit G rich action
    (hedgeDoSecond rich action) root
    (hedgeDoSecond_of_false rich action hy)
    (fun u =>
      (hedgeParentBitsFrom_doSecond_eq_actionParentParity G rich action u y).trans
        hparity)
    hinc

/--
Unique-parent compatibility form of
`hedgeMix_interventional_first_not_equiv_of_parentParity`.
-/
theorem hedgeMix_interventional_first_not_equiv (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {x y : Fin S.count}
    (action : NodeSet S) (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true) (hx : action x = true)
    (hy : action y = false)
    (huniq : forall p, action p = true → S.directed p y = true → p = x)
    (hinc : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (QProb.Equiv
        ((hedgeMixModel G rich action).interventionalValue
          (hedgeDoSecond rich action)
          (fun a => decide (a y = rich.first y)))
        ((hedgeMixModel G rich NodeSet.empty).interventionalValue
          (hedgeDoSecond rich action)
          (fun a => decide (a y = rich.first y)))) :=
  hedgeMix_interventional_first_not_equiv_of_parentParity G rich action root hy
    (actionParentParity_eq_true_of_unique action hdir hx huniq) hinc

/--
A free mix child with odd action-parent parity copies the distinguished
`second` bit under `do(X = second)`.
-/
theorem hedgeMixModel_evalUnder_doSecond_action_child_of_parentParity
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) (u : (hedgeLatentExtension G).Assignment)
    {child : Fin S.count} (free : action child = false)
    (parity : actionParentParity action child = true) :
    (hedgeMixModel G rich action).evalUnder (hedgeDoSecond rich action) u child =
      hedgeMixFrom rich child
        (hedgeXorPairBits G child (fun latent _ => u latent)) true
        (hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun latent _ => u latent))) := by
  unfold FiniteLatentSCM.evalUnder
  rw [hedgeMixModel_evalNodeUnder_free G rich action action u free]
  rw [hedgeParentBitsFrom_doSecond_eq_actionParentParity G rich action u child,
    parity]

/--
A directed child of a unique action parent is the one-parent special case of
odd action-parent parity.
-/
theorem hedgeMixModel_evalUnder_doSecond_action_child (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) {x c : Fin S.count}
    (hdir : S.directed x c = true) (hx : action x = true)
    (hc : action c = false)
    (huniq : forall p, action p = true → S.directed p c = true → p = x) :
    (hedgeMixModel G rich action).evalUnder (hedgeDoSecond rich action) u c =
      hedgeMixFrom rich c
        (hedgeXorPairBits G c (fun latent _ => u latent)) true
        (hedgePrivateDecode S c
          (hedgePrivateIndex G c (fun latent _ => u latent))) :=
  hedgeMixModel_evalUnder_doSecond_action_child_of_parentParity G rich action u
    hc (actionParentParity_eq_true_of_unique action hdir hx huniq)

/--
The empty mix mask ignores parents, so a free child under `do(X = second)`
emits `first` on the copy branch and the private decode otherwise.
-/
theorem hedgeMixModel_evalUnder_doSecond_empty_child (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) {c : Fin S.count}
    (hc : action c = false) :
    (hedgeMixModel G rich NodeSet.empty).evalUnder
        (hedgeDoSecond rich action) u c =
      hedgeMixFrom rich c
        (hedgeXorPairBits G c (fun latent _ => u latent)) false
        (hedgePrivateDecode S c
          (hedgePrivateIndex G c (fun latent _ => u latent))) := by
  unfold FiniteLatentSCM.evalUnder
  rw [hedgeMixModel_evalNodeUnder_free G rich NodeSet.empty action u hc]
  rw [hedgeParentBitsFrom_empty]

/-- Observational mix evaluation is the mix of pair-root XOR, masked parent
bits, and private decode.  There is no intervention, so every node is free. -/
theorem hedgeMixModel_evalNode (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeMixModel G rich mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child =
      hedgeMixFrom rich child
        (hedgeXorPairBits G child (fun latent _ => u latent))
        (hedgeParentBitsFrom rich mask child
          (fun parent _ =>
            (hedgeMixModel G rich mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent))
        (hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun latent _ => u latent))) := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  rfl

/-- Pair-root XOR depends only on which roots are incident. -/
theorem hedgeXorPairBits_eq_of_incident_eq (G : ObservedGraph S)
    {left right : Fin S.count}
    (inputs : (root : Fin (hedgeLatentCount G)) → hedgeLatentValue G root)
    (hinc : forall root,
      (hedgeLatentExtension G).incident (hedgePairRoot G root) left =
        (hedgeLatentExtension G).incident (hedgePairRoot G root) right) :
    hedgeXorPairBits G left (fun latent _ => inputs latent) =
      hedgeXorPairBits G right (fun latent _ => inputs latent) := by
  unfold hedgeXorPairBits
  refine foldl_congr _ _ _ _ ?_
  intro acc root
  have hroot := hinc root
  if hL : (hedgeLatentExtension G).incident (hedgePairRoot G root) left then
    have hR :
        (hedgeLatentExtension G).incident (hedgePairRoot G root) right = true := by
      rw [← hroot, hL]
    simp [hL, hR]
  else
    have hR :
        (hedgeLatentExtension G).incident (hedgePairRoot G root) right = false := by
      have hLfalse :
          (hedgeLatentExtension G).incident (hedgePairRoot G root) left = false :=
        Bool.eq_false_iff.mpr hL
      rw [← hroot, hLfalse]
    simp [hL, hR]

/-- Shared pair-root incidence with a parent makes a child's XOR the parent's. -/
theorem hedgeXorPairBits_eq_of_shared_child (G : ObservedGraph S)
    {x c : Fin S.count}
    (hinc : forall child, S.directed x child = true →
      forall root,
        (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G root) child)
    (hd : S.directed x c = true)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeXorPairBits G c (fun latent _ => u latent) =
      hedgeXorPairBits G x (fun latent _ => u latent) :=
  hedgeXorPairBits_eq_of_incident_eq G u (fun root => (hinc c hd root).symm)

/--
A masked vertex that is a directed parent of anyone is the designated
seed: extra mask vertices are required to have no outgoing directed
edges, so they cannot appear as parents.
-/
theorem hedgeMaskParent_eq_seed {mask : NodeSet S} {x p child : Fin S.count}
    (hmask : forall q, mask q = true →
      q = x ∨ forall c, S.directed q c = false)
    (hm : mask p = true) (hd : S.directed p child = true) : p = x := by
  cases hmask p hm with
  | inl hp =>
      exact hp
  | inr hnone =>
      exact False.elim (Bool.false_ne_true ((hnone child).symm.trans hd))

/-- Singleton masks are the special case with no extra sink vertices. -/
theorem hedgeMask_of_singleton {mask : NodeSet S} {x : Fin S.count}
    (h : forall p, mask p = true → p = x) :
    forall p, mask p = true →
      p = x ∨ forall c, S.directed p c = false :=
  fun p hm => Or.inl (h p hm)

/-!
### Acyclic shared-switch masks

The seed-plus-sink result below is intentionally elementary, but its
single-seed hypothesis is stronger than the mix mechanism actually needs.
For observational agreement it is enough that every edge leaving a masked
parent preserves the complete pair-root incidence vector.  When a child's
switch is on, the same switch is therefore on at each masked parent.  Directed
acyclicity lets us inspect those parents first; inductively they agree with the
empty-mask model and hence emit `first`.  Every masked parent bit is zero, so
the child also emits `first`, exactly as it does under the empty mask.

This condition is deliberately stated as a hypothesis.  Arbitrary hedge
forests need not preserve all pair-root incidence across their directed edges,
especially in the presence of extra bidirected arms in the ambient graph.
-/

/--
Pointwise observational equality for an arbitrary mask whose every outgoing
directed edge shares the parent's pair-root switch.  The recursion is on the
topological node index: every directed parent has a strictly smaller index.
-/
theorem hedgeMixModel_evalNode_eq_of_edge_shared_switch
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S)
    (shared : forall parent child,
      mask parent = true → S.directed parent child = true →
        forall root,
          (hedgeLatentExtension G).incident (hedgePairRoot G root) parent =
            (hedgeLatentExtension G).incident (hedgePairRoot G root) child)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeMixModel G rich mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child =
      (hedgeMixModel G rich NodeSet.empty).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child := by
  rw [hedgeMixModel_evalNode G rich mask u child]
  rw [hedgeMixModel_evalNode G rich NodeSet.empty u child]
  rw [hedgeParentBitsFrom_empty]
  cases childSwitch :
      hedgeXorPairBits G child (fun latent _ => u latent) with
  | false =>
      simp [hedgeMixFrom_false]
  | true =>
      have parentBitsFalse :
          hedgeParentBitsFrom rich mask child
              (fun parent _ =>
                (hedgeMixModel G rich mask).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent) = false := by
        apply hedgeParentBitsFrom_false_of_masked_parents_first
        intro parent edge selected
        have parentSwitch :
            hedgeXorPairBits G parent (fun latent _ => u latent) = true := by
          have sameSwitch :=
            hedgeXorPairBits_eq_of_incident_eq G u
              (shared parent child selected edge)
          exact sameSwitch.trans childSwitch
        have parentAgreement :=
          hedgeMixModel_evalNode_eq_of_edge_shared_switch G rich mask shared
            u parent
        have emptyParentFirst :
            (hedgeMixModel G rich NodeSet.empty).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) u parent =
              rich.first parent := by
          rw [hedgeMixModel_evalNode G rich NodeSet.empty u parent,
            hedgeParentBitsFrom_empty, parentSwitch,
            hedgeMixFrom_true_first]
        rw [parentAgreement, emptyParentFirst, hedgeIsSecond_first]
      rw [parentBitsFalse, hedgeMixFrom_true_first]
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- The acyclic shared-switch equality holds for the complete observed output. -/
theorem hedgeMixModel_eval_eq_of_edge_shared_switch
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S)
    (shared : forall parent child,
      mask parent = true → S.directed parent child = true →
        forall root,
          (hedgeLatentExtension G).incident (hedgePairRoot G root) parent =
            (hedgeLatentExtension G).incident (hedgePairRoot G root) child)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeMixModel G rich mask).eval u =
      (hedgeMixModel G rich NodeSet.empty).eval u := by
  funext child
  simpa [FiniteLatentSCM.eval] using
    hedgeMixModel_evalNode_eq_of_edge_shared_switch G rich mask shared u child

/--
Any acyclic shared-switch mask produces the same observational law as the
empty mask.  The two models have definitionally the same product prior, and
the preceding induction identifies their observed evaluations latent point
by latent point; no probability reindexing or choice of a preimage is needed.
-/
theorem hedgeMixModel_observationally_equivalent_of_edge_shared_switch
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S)
    (shared : forall parent child,
      mask parent = true → S.directed parent child = true →
        forall root,
          (hedgeLatentExtension G).incident (hedgePairRoot G root) parent =
            (hedgeLatentExtension G).incident (hedgePairRoot G root) child) :
    ObservationallyEquivalent
      (hedgeMixModel G rich NodeSet.empty)
      (hedgeMixModel G rich mask) := by
  intro event
  have evaluation (u : (hedgeLatentExtension G).Assignment) :
      (hedgeMixModel G rich NodeSet.empty).eval u =
        (hedgeMixModel G rich mask).eval u :=
    (hedgeMixModel_eval_eq_of_edge_shared_switch G rich mask shared u).symm
  refine QProb.equiv_trans
    (FiniteLatentSCM.observationalValue_eq
      (hedgeMixModel G rich NodeSet.empty) event) ?_
  refine QProb.equiv_trans ?_
    (QProb.equiv_symm
      (FiniteLatentSCM.observationalValue_eq
        (hedgeMixModel G rich mask) event))
  exact FiniteProbRecord.probVal_congr _ _ _
    (fun u => congrArg event (evaluation u))

/-!
### Observational equality for one-root switches

For a switch localized to `root`, a masked parent need not share its complete
incidence vector with a child.  It is enough that whenever the selected root
is incident to the child it is also incident to that parent.  If the child's
switch is on, both nodes then read the same Boolean coordinate; the earlier
parent emits `first`, so its contribution to the child's parent parity is
zero.  If the root is absent from the child, the mix uses private noise and
ignores parent parity altogether.
-/

/-- Observational evaluation equation for a one-root mix. -/
theorem hedgeSingleRootMixModel_evalNode (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child =
      hedgeMixFrom rich child
        (hedgePairRootBit G root child (fun latent _ => u latent))
        (hedgeParentBitsFrom rich mask child
          (fun parent _ =>
            (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent))
        (hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun latent _ => u latent))) := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  rfl

/--
Pointwise observational equality when selected-root incidence propagates
backward from every child switch to each masked directed parent.
-/
theorem hedgeSingleRootMixModel_evalNode_eq_of_switch_backward
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (switchBackward : forall parent child,
      mask parent = true → S.directed parent child = true →
        (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true →
          (hedgeLatentExtension G).incident (hedgePairRoot G root) parent = true)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child =
      (hedgeSingleRootMixModel G rich root NodeSet.empty).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child := by
  rw [hedgeSingleRootMixModel_evalNode G rich root mask u child]
  rw [hedgeSingleRootMixModel_evalNode G rich root NodeSet.empty u child]
  rw [hedgeParentBitsFrom_empty]
  cases childSwitch :
      hedgePairRootBit G root child (fun latent _ => u latent) with
  | false =>
      simp [hedgeMixFrom_false]
  | true =>
      have childIncident :
          (hedgeLatentExtension G).incident (hedgePairRoot G root) child =
            true := by
        cases incident :
            (hedgeLatentExtension G).incident (hedgePairRoot G root) child
        · simp [hedgePairRootBit, incident] at childSwitch
        · rfl
      have parentBitsFalse :
          hedgeParentBitsFrom rich mask child
              (fun parent _ =>
                (hedgeSingleRootMixModel G rich root mask).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent) = false := by
        apply hedgeParentBitsFrom_false_of_masked_parents_first
        intro parent edge selected
        have parentIncident :=
          switchBackward parent child selected edge childIncident
        have parentSwitch :
            hedgePairRootBit G root parent (fun latent _ => u latent) = true :=
          by
            simpa [hedgePairRootBit, parentIncident, childIncident] using
              childSwitch
        have parentAgreement :=
          hedgeSingleRootMixModel_evalNode_eq_of_switch_backward G rich root
            mask switchBackward u parent
        have emptyParentFirst :
            (hedgeSingleRootMixModel G rich root NodeSet.empty).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) u parent =
              rich.first parent := by
          rw [hedgeSingleRootMixModel_evalNode G rich root NodeSet.empty u
            parent, hedgeParentBitsFrom_empty, parentSwitch,
            hedgeMixFrom_true_first]
        rw [parentAgreement, emptyParentFirst, hedgeIsSecond_first]
      rw [parentBitsFalse, hedgeMixFrom_true_first]
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

theorem hedgeSingleRootMixModel_eval_eq_of_switch_backward
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (switchBackward : forall parent child,
      mask parent = true → S.directed parent child = true →
        (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true →
          (hedgeLatentExtension G).incident (hedgePairRoot G root) parent = true)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeSingleRootMixModel G rich root mask).eval u =
      (hedgeSingleRootMixModel G rich root NodeSet.empty).eval u := by
  funext child
  simpa [FiniteLatentSCM.eval] using
    hedgeSingleRootMixModel_evalNode_eq_of_switch_backward G rich root mask
      switchBackward u child

/-- Equal pointwise evaluations give observational equality of one-root mixes. -/
theorem hedgeSingleRootMixModel_observationally_equivalent_of_switch_backward
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (mask : NodeSet S)
    (switchBackward : forall parent child,
      mask parent = true → S.directed parent child = true →
        (hedgeLatentExtension G).incident (hedgePairRoot G root) child = true →
          (hedgeLatentExtension G).incident (hedgePairRoot G root) parent = true) :
    ObservationallyEquivalent
      (hedgeSingleRootMixModel G rich root NodeSet.empty)
      (hedgeSingleRootMixModel G rich root mask) := by
  intro event
  have evaluation (u : (hedgeLatentExtension G).Assignment) :
      (hedgeSingleRootMixModel G rich root NodeSet.empty).eval u =
        (hedgeSingleRootMixModel G rich root mask).eval u :=
    (hedgeSingleRootMixModel_eval_eq_of_switch_backward G rich root mask
      switchBackward u).symm
  refine QProb.equiv_trans
    (FiniteLatentSCM.observationalValue_eq
      (hedgeSingleRootMixModel G rich root NodeSet.empty) event) ?_
  refine QProb.equiv_trans ?_
    (QProb.equiv_symm
      (FiniteLatentSCM.observationalValue_eq
        (hedgeSingleRootMixModel G rich root mask) event))
  exact FiniteProbRecord.probVal_congr _ _ _
    (fun u => congrArg event (evaluation u))

/--
A singleton pivot mask satisfies the backward-switch condition as soon as the
selected root is incident to the pivot.  No condition is imposed on the
pivot's other bidirected neighbours or directed children.
-/
theorem hedgeSingleRootMixModel_observationally_equivalent_singleton
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (root : Fin (pairRootCount G)) (pivot : Fin S.count)
    (pivotIncident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) pivot = true) :
    ObservationallyEquivalent
      (hedgeSingleRootMixModel G rich root NodeSet.empty)
      (hedgeSingleRootMixModel G rich root (NodeSet.singleton pivot)) := by
  apply hedgeSingleRootMixModel_observationally_equivalent_of_switch_backward
  intro parent _child inMask _edge _childIncident
  have parentEq : parent = pivot :=
    (NodeSet.singleton_eq_true_iff pivot parent).mp inMask
  subst parent
  exact pivotIncident

/--
Seed-plus-sink mix models agree observationally once every directed child
of the masked seed shares that seed's pair-root switch.  Extra mask
vertices may sit in the action so long as they have no outgoing directed
edges: they never contribute parent-bits.  When the switch is on, the
seed has no masked parent of its own, so it emits `first` and every
child copies `first` — the same constant the empty mask copies.
Unique-child bows are the special case that there is only one such child.
-/
theorem hedgeMixModel_evalNode_eq_of_shared_switch (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    {x : Fin S.count}
    (hmask : forall p, mask p = true →
      p = x ∨ forall c, S.directed p c = false)
    (hinc : forall c, S.directed x c = true →
      forall root,
        (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G root) c)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeMixModel G rich mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child =
      (hedgeMixModel G rich NodeSet.empty).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child := by
  apply hedgeMixModel_evalNode_eq_of_edge_shared_switch G rich mask
  intro parent c selected edge root
  have parentEq : parent = x := hedgeMaskParent_eq_seed hmask selected edge
  subst parent
  exact hinc c edge root

theorem hedgeMixModel_eval_eq_of_shared_switch (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    {x : Fin S.count}
    (hmask : forall p, mask p = true →
      p = x ∨ forall c, S.directed p c = false)
    (hinc : forall c, S.directed x c = true →
      forall root,
        (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G root) c)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeMixModel G rich mask).eval u =
      (hedgeMixModel G rich NodeSet.empty).eval u := by
  funext child
  simpa [FiniteLatentSCM.eval] using
    hedgeMixModel_evalNode_eq_of_shared_switch G rich mask hmask hinc u child

/--
Seed-plus-sink mix models with a shared pair-root switch at every
directed child of the masked seed are observationally equivalent to
the empty-mask mix.  Extra mask vertices that have no outgoing directed
edges do not contribute parent-bits, so they may sit in the action.
-/
theorem hedgeMixModel_observationally_equivalent_of_shared_switch
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (mask : NodeSet S) {x : Fin S.count}
    (hmask : forall p, mask p = true →
      p = x ∨ forall c, S.directed p c = false)
    (hinc : forall c, S.directed x c = true →
      forall root,
        (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G root) c) :
    ObservationallyEquivalent
      (hedgeMixModel G rich NodeSet.empty)
      (hedgeMixModel G rich mask) := by
  apply hedgeMixModel_observationally_equivalent_of_edge_shared_switch
  intro parent child selected edge root
  have parentEq : parent = x := hedgeMaskParent_eq_seed hmask selected edge
  subst parent
  exact hinc child edge root

/-- Unique-child bows share the parent's switch at their only child. -/
theorem hedgeMix_bow_shared_switch {G : ObservedGraph S}
    {x y : Fin S.count}
    (honly : forall c, S.directed x c = true → c = y)
    (hinc : forall root,
      (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
        (hedgeLatentExtension G).incident (hedgePairRoot G root) y) :
    forall c, S.directed x c = true →
      forall root,
        (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G root) c := by
  intro c hd root
  have hc : c = y := honly c hd
  simpa [hc] using hinc root

/--
On a bow `X → Y` with `X ↔ Y` neighbourhood (identical pair-root
incidence) and no other directed child of `X`, the mix parent-bits of
every node vanish observationally: the copy branch of `Y` only fires
when `X` is already pinned to `first` by the shared switch.  Empty-mask
and masked mix therefore agree as functions of the latent assignment.
-/
theorem hedgeMixModel_evalNode_eq_of_bow (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    {x y : Fin S.count}
    (hdirXY : S.directed x y = true)
    (hmask : forall p, mask p = true → p = x)
    (honly : forall c, S.directed x c = true → c = y)
    (hinc : forall root,
      (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
        (hedgeLatentExtension G).incident (hedgePairRoot G root) y)
    (u : (hedgeLatentExtension G).Assignment) (child : Fin S.count) :
    (hedgeMixModel G rich mask).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child =
      (hedgeMixModel G rich NodeSet.empty).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child :=
  have _ := hdirXY
  hedgeMixModel_evalNode_eq_of_shared_switch G rich mask
    (hedgeMask_of_singleton hmask)
    (hedgeMix_bow_shared_switch (G := G) honly hinc) u child

theorem hedgeMixModel_eval_eq_of_bow (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    {x y : Fin S.count}
    (hdirXY : S.directed x y = true)
    (hmask : forall p, mask p = true → p = x)
    (honly : forall c, S.directed x c = true → c = y)
    (hinc : forall root,
      (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
        (hedgeLatentExtension G).incident (hedgePairRoot G root) y)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeMixModel G rich mask).eval u =
      (hedgeMixModel G rich NodeSet.empty).eval u :=
  have _ := hdirXY
  hedgeMixModel_eval_eq_of_shared_switch G rich mask
    (hedgeMask_of_singleton hmask)
    (hedgeMix_bow_shared_switch (G := G) honly hinc) u

/--
Bow-arc mix models with a singleton action mask are observationally
equivalent: they evaluate identically, and they share the product prior.
The unique-child hypothesis is only used to specialise the shared-switch
lemma; several children with the same pair-root incidence are already
covered by `hedgeMixModel_observationally_equivalent_of_shared_switch`.
-/
theorem hedgeMixModel_observationally_equivalent_of_bow (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (mask : NodeSet S)
    {x y : Fin S.count}
    (hdirXY : S.directed x y = true)
    (hmask : forall p, mask p = true → p = x)
    (honly : forall c, S.directed x c = true → c = y)
    (hinc : forall root,
      (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
        (hedgeLatentExtension G).incident (hedgePairRoot G root) y) :
    ObservationallyEquivalent
      (hedgeMixModel G rich NodeSet.empty)
      (hedgeMixModel G rich mask) :=
  have _ := hdirXY
  hedgeMixModel_observationally_equivalent_of_shared_switch G rich mask
    (hedgeMask_of_singleton hmask)
    (hedgeMix_bow_shared_switch (G := G) honly hinc)

/-- Reference assignment that pins the bow parent to `second` and every
other node to `first`. -/
def hedgeBowReference (rich : ObservedSignature.ValueRich S)
    (x : Fin S.count) : S.Assignment :=
  fun i => if i = x then rich.second i else rich.first i

theorem hedgeBowReference_self (rich : ObservedSignature.ValueRich S)
    (x : Fin S.count) :
    hedgeBowReference rich x x = rich.second x := by
  simp [hedgeBowReference]

theorem hedgeBowReference_ne (rich : ObservedSignature.ValueRich S)
    {x i : Fin S.count} (hne : i ≠ x) :
    hedgeBowReference rich x i = rich.first i := by
  simp [hedgeBowReference, hne]

/-- Cylinder agreement on a singleton node set is a single coordinate test. -/
theorem agreesOn_of_unique_node (nodes : NodeSet S) {y : Fin S.count}
    (reference sample : S.Assignment)
    (hy : nodes y = true)
    (hunique : forall i, nodes i = true → i = y) :
    Kernel.agreesOn nodes reference sample =
      decide (sample y = reference y) := by
  unfold Kernel.agreesOn
  cases h : decide (sample y = reference y) with
  | true =>
      refine (finAll_eq_true_iff _).mpr ?_
      intro i
      cases hi : nodes i with
      | false =>
          simp
      | true =>
          have heq : i = y := hunique i hi
          subst heq
          simp [h]
  | false =>
      cases hall : finAll S.count
          (fun i => if nodes i then decide (sample i = reference i) else true) with
      | true =>
          have hyb := (finAll_eq_true_iff _).mp hall y
          simp [hy, h] at hyb
      | false =>
          rfl

/--
Cylinder agreement splits off one selected coordinate.  Composite
outcomes reduce to a singleton test times the complementary cylinder;
the complementary factor is identically true precisely when the
outcome is a singleton.
-/
theorem agreesOn_split_coord (nodes : NodeSet S) {y : Fin S.count}
    (reference sample : S.Assignment) (hy : nodes y = true) :
    Kernel.agreesOn nodes reference sample =
      (decide (sample y = reference y) &&
        Kernel.agreesOn (fun i => nodes i && decide (i ≠ y))
          reference sample) := by
  let rest : NodeSet S := fun i => nodes i && decide (i ≠ y)
  have hdecomp :
      nodes = NodeSet.union (NodeSet.singleton y) rest := by
    funext i
    if hiy : i = y then
      subst hiy
      simp [rest, NodeSet.union, NodeSet.singleton, hy]
    else
      simp [rest, NodeSet.union, NodeSet.singleton, hiy]
  have hleft :
      Kernel.agreesOn nodes reference sample =
        Kernel.agreesOn
          (NodeSet.union (NodeSet.singleton y) rest) reference sample := by
    rw [hdecomp]
  have hsing :
      Kernel.agreesOn (NodeSet.singleton y) reference sample =
        decide (sample y = reference y) :=
    agreesOn_of_unique_node (NodeSet.singleton y) reference sample
      (by simp [NodeSet.singleton])
      (fun i hi => (NodeSet.singleton_eq_true_iff y i).mp hi)
  rw [hleft, Kernel.agreesOn_union, hsing]

/--
The bow reference is `first` off the action seed, so cylinder agreement on
any set that avoids that seed is a conjunction of `= first` tests.
-/
theorem agreesOn_hedgeBowReference_eq_first
    (rich : ObservedSignature.ValueRich S) (outcome : NodeSet S)
    {x : Fin S.count} (sample : S.Assignment)
    (hnotx : forall i, outcome i = true → i ≠ x) :
    Kernel.agreesOn outcome (hedgeBowReference rich x) sample =
      Kernel.agreesOn outcome (fun i => rich.first i) sample :=
  Kernel.agreesOn_reference_congr outcome (hedgeBowReference rich x)
    (fun i => rich.first i) sample
    (fun i hi => hedgeBowReference_ne rich (hnotx i hi))

/--
`P(Y = first | do(X = second))` for a composite outcome that is a set of
directed children of one action seed, all sharing that seed's pair-root
switch.  Extra action vertices may have outgoing edges; they merely must not
be additional parents of a queried child.  The extra mass is the copy branch
`xorBits = true`, which emits `first` at every such child when parents are
ignored and `second` when the unique action parent is copied.
-/
theorem hedgeMix_interventional_children_mass_lt (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {x y : Fin S.count}
    (action outcome : NodeSet S) (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true) (hx : action x = true)
    (hy : outcome y = true)
    (hunique : forall i, outcome i = true →
      forall p, action p = true → S.directed p i = true → p = x)
    (hfree : forall i, outcome i = true → action i = false)
    (hchildren : forall i, outcome i = true → S.directed x i = true)
    (hincChildren : forall c, S.directed x c = true →
      forall r,
        (hedgeLatentExtension G).incident (hedgePairRoot G r) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G r) c)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y =
        true) :
    FiniteProbRecord.eventMass
        (hedgeMixModel G rich action).prior.atoms
        (fun u =>
          Kernel.agreesOn outcome (hedgeActionReference rich action)
            ((hedgeMixModel G rich action).evalUnder
              (hedgeDoSecond rich action) u)) <
      FiniteProbRecord.eventMass
        (hedgeMixModel G rich NodeSet.empty).prior.atoms
        (fun u =>
          Kernel.agreesOn outcome (hedgeActionReference rich action)
            ((hedgeMixModel G rich NodeSet.empty).evalUnder
              (hedgeDoSecond rich action) u)) := by
  let extra : Event ((hedgeLatentExtension G).Assignment) :=
    fun u => hedgeXorPairBits G y (fun latent _ => u latent)
  let actionAgrees : Event ((hedgeLatentExtension G).Assignment) :=
    fun u =>
      Kernel.agreesOn outcome (hedgeActionReference rich action)
        ((hedgeMixModel G rich action).evalUnder
          (hedgeDoSecond rich action) u)
  let emptyAgrees : Event ((hedgeLatentExtension G).Assignment) :=
    fun u =>
      Kernel.agreesOn outcome (hedgeActionReference rich action)
        ((hedgeMixModel G rich NodeSet.empty).evalUnder
          (hedgeDoSecond rich action) u)
  have hxor_eq (i : Fin S.count) (hi : outcome i = true)
      (u : (hedgeLatentExtension G).Assignment) :
      hedgeXorPairBits G i (fun latent _ => u latent) =
        hedgeXorPairBits G y (fun latent _ => u latent) :=
    (hedgeXorPairBits_eq_of_shared_child G hincChildren (hchildren i hi) u).trans
      (hedgeXorPairBits_eq_of_shared_child G hincChildren hdir u).symm
  have hempty_of_extra (u : (hedgeLatentExtension G).Assignment)
      (hextra : extra u = true) : emptyAgrees u = true := by
    unfold emptyAgrees Kernel.agreesOn extra at *
    refine (finAll_eq_true_iff _).mpr ?_
    intro i
    cases hi : outcome i with
    | false =>
        simp
    | true =>
        have heval :=
          hedgeMixModel_evalUnder_doSecond_empty_child G rich action u
            (hfree i hi)
        have hxorI :
            hedgeXorPairBits G i (fun latent _ => u latent) = true := by
          rw [hxor_eq i hi u]
          exact hextra
        rw [hxorI, hedgeMixFrom_true_first] at heval
        simp [heval, hedgeActionReference_of_false rich action (hfree i hi)]
  have hdis : disjoint extra actionAgrees := by
    intro u hextra hact
    have hyval :=
      hedgeMixModel_evalUnder_doSecond_action_child G rich action u hdir hx
        (hfree y hy) (hunique y hy)
    have hxorY : hedgeXorPairBits G y (fun latent _ => u latent) = true :=
      hextra
    rw [hxorY, hedgeMixFrom_true_second] at hyval
    have hsplit :=
      agreesOn_split_coord outcome (hedgeActionReference rich action)
        ((hedgeMixModel G rich action).evalUnder (hedgeDoSecond rich action) u)
        hy
    have hyfirst :
        (hedgeMixModel G rich action).evalUnder (hedgeDoSecond rich action) u y =
          hedgeActionReference rich action y := by
      have happ : actionAgrees u = true := hact
      unfold actionAgrees at happ
      rw [hsplit] at happ
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp happ).1
    have hrefy : hedgeActionReference rich action y = rich.first y :=
      hedgeActionReference_of_false rich action (hfree y hy)
    exact rich.different y ((hyfirst.trans hrefy).symm.trans hyval)
  have hunion (u : (hedgeLatentExtension G).Assignment) :
      emptyAgrees u = union extra actionAgrees u := by
    cases hxor : extra u with
    | true =>
        have hemp : emptyAgrees u = true := hempty_of_extra u hxor
        have hact : actionAgrees u = false := by
          cases hact : actionAgrees u with
          | false =>
              rfl
          | true =>
              exact False.elim (hdis u hxor hact)
        simp [union, hemp, hact, hxor]
    | false =>
        have heq :
            Kernel.agreesOn outcome (hedgeActionReference rich action)
                ((hedgeMixModel G rich action).evalUnder
                  (hedgeDoSecond rich action) u) =
              Kernel.agreesOn outcome (hedgeActionReference rich action)
                ((hedgeMixModel G rich NodeSet.empty).evalUnder
                  (hedgeDoSecond rich action) u) :=
          Kernel.agreesOn_sample_congr outcome (hedgeActionReference rich action) _ _
            (fun i hi => by
              have hc := hfree i hi
              have hxorI :
                  hedgeXorPairBits G i (fun latent _ => u latent) = false := by
                rw [hxor_eq i hi u]
                exact hxor
              rw [hedgeMixModel_evalUnder_doSecond_action_child G rich action u
                (hchildren i hi) hx hc (hunique i hi),
                hedgeMixModel_evalUnder_doSecond_empty_child G rich action u hc,
                hxorI]
              simp [hedgeMixFrom_false])
        unfold emptyAgrees actionAgrees extra at *
        simp [union, hxor, heq]
  have hmass_union :
      FiniteProbRecord.eventMass
          (hedgeMixModel G rich NodeSet.empty).prior.atoms emptyAgrees =
        FiniteProbRecord.eventMass
            (hedgeMixModel G rich NodeSet.empty).prior.atoms extra +
          FiniteProbRecord.eventMass
            (hedgeMixModel G rich NodeSet.empty).prior.atoms actionAgrees := by
    have hcong :=
      FiniteProbRecord.eventMass_congr
        (hedgeMixModel G rich NodeSet.empty).prior.atoms emptyAgrees
        (union extra actionAgrees) hunion
    exact hcong.trans
      (eventMass_union_disjoint
        (hedgeMixModel G rich NodeSet.empty).prior.atoms extra actionAgrees
        hdis)
  have hextra_pos :
      0 <
        FiniteProbRecord.eventMass
          (hedgeMixModel G rich NodeSet.empty).prior.atoms extra := by
    have hu := hedgeMixExtraLatent_xor G rich root hincy
    have hsing :=
      hedgePrior_eventMass_singleton G (hedgeMixExtraLatent G rich root)
    have hsub :
        forall v,
          FiniteProbRecord.singletonEvent (hedgeMixExtraLatent G rich root) v =
              true →
            extra v = true := by
      intro v hv
      have heq : v = hedgeMixExtraLatent G rich root :=
        of_decide_eq_true (by simpa [FiniteProbRecord.singletonEvent] using hv)
      simpa [heq] using hu
    have hmono :=
      FiniteProbRecord.eventMass_mono
        (FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
          (hedgeLatentFactor G)).atoms
        (FiniteProbRecord.singletonEvent (hedgeMixExtraLatent G rich root))
        extra hsub
    exact Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_eq Nat.zero_lt_one hsing.symm) hmono
  have hatoms :
      (hedgeMixModel G rich action).prior.atoms =
        (hedgeMixModel G rich NodeSet.empty).prior.atoms :=
    rfl
  change
    FiniteProbRecord.eventMass
        (hedgeMixModel G rich action).prior.atoms actionAgrees <
      FiniteProbRecord.eventMass
        (hedgeMixModel G rich NodeSet.empty).prior.atoms emptyAgrees
  rw [hatoms, hmass_union]
  exact Nat.lt_add_of_pos_left hextra_pos

/--
The two mix models therefore disagree on the interventional cylinder of a
composite outcome of shared-switch children under `do(X = second)`.
-/
theorem hedgeMix_interventional_children_not_equiv (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) {x y : Fin S.count}
    (action outcome : NodeSet S) (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true) (hx : action x = true)
    (hy : outcome y = true)
    (hunique : forall i, outcome i = true →
      forall p, action p = true → S.directed p i = true → p = x)
    (hfree : forall i, outcome i = true → action i = false)
    (hchildren : forall i, outcome i = true → S.directed x i = true)
    (hincChildren : forall c, S.directed x c = true →
      forall r,
        (hedgeLatentExtension G).incident (hedgePairRoot G r) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G r) c)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y =
        true) :
    Not
      (QProb.Equiv
        ((hedgeMixModel G rich action).interventionalValue
          (hedgeDoSecond rich action)
          (Kernel.agreesOn outcome (hedgeActionReference rich action)))
        ((hedgeMixModel G rich NodeSet.empty).interventionalValue
          (hedgeDoSecond rich action)
          (Kernel.agreesOn outcome (hedgeActionReference rich action)))) := by
  intro heq
  have hact :=
    FiniteLatentSCM.interventionalValue_eq
      (hedgeMixModel G rich action) (hedgeDoSecond rich action)
      (Kernel.agreesOn outcome (hedgeActionReference rich action))
  have hemp :=
    FiniteLatentSCM.interventionalValue_eq
      (hedgeMixModel G rich NodeSet.empty) (hedgeDoSecond rich action)
      (Kernel.agreesOn outcome (hedgeActionReference rich action))
  have hmass :
      QProb.Equiv
        ((hedgeMixModel G rich action).prior.probVal
          (fun u =>
            Kernel.agreesOn outcome (hedgeActionReference rich action)
              ((hedgeMixModel G rich action).evalUnder
                (hedgeDoSecond rich action) u)))
        ((hedgeMixModel G rich NodeSet.empty).prior.probVal
          (fun u =>
            Kernel.agreesOn outcome (hedgeActionReference rich action)
              ((hedgeMixModel G rich NodeSet.empty).evalUnder
                (hedgeDoSecond rich action) u))) :=
    QProb.equiv_trans (QProb.equiv_symm hact) (QProb.equiv_trans heq hemp)
  have hlt :=
    hedgeMix_interventional_children_mass_lt G rich action outcome root hdir hx
      hy hunique hfree hchildren hincChildren hincy
  have hprior :
      (hedgeMixModel G rich action).prior =
        (hedgeMixModel G rich NodeSet.empty).prior :=
    rfl
  have hnums :
      FiniteProbRecord.eventMass
          (hedgeMixModel G rich action).prior.atoms
          (fun u =>
            Kernel.agreesOn outcome (hedgeActionReference rich action)
              ((hedgeMixModel G rich action).evalUnder
                (hedgeDoSecond rich action) u)) =
        FiniteProbRecord.eventMass
          (hedgeMixModel G rich NodeSet.empty).prior.atoms
          (fun u =>
            Kernel.agreesOn outcome (hedgeActionReference rich action)
              ((hedgeMixModel G rich NodeSet.empty).evalUnder
                (hedgeDoSecond rich action) u)) := by
    have hmul :
        FiniteProbRecord.eventMass
            (hedgeMixModel G rich action).prior.atoms
            (fun u =>
              Kernel.agreesOn outcome (hedgeActionReference rich action)
                ((hedgeMixModel G rich action).evalUnder
                  (hedgeDoSecond rich action) u)) *
          (hedgeMixModel G rich NodeSet.empty).prior.den =
          FiniteProbRecord.eventMass
            (hedgeMixModel G rich NodeSet.empty).prior.atoms
            (fun u =>
              Kernel.agreesOn outcome (hedgeActionReference rich action)
                ((hedgeMixModel G rich NodeSet.empty).evalUnder
                  (hedgeDoSecond rich action) u)) *
            (hedgeMixModel G rich action).prior.den := by
      simpa [QProb.Equiv, FiniteProbRecord.probVal] using hmass
    have hden :
        (hedgeMixModel G rich action).prior.den =
          (hedgeMixModel G rich NodeSet.empty).prior.den := by
      rw [hprior]
    rw [hden] at hmul
    exact
      Nat.eq_of_mul_eq_mul_right
        (hedgeMixModel G rich NodeSet.empty).prior.den_pos
        hmul
  exact Nat.ne_of_lt hlt hnums

/--
Singleton-action special case of `hedgeDoSecond_eq_action_intervention`:
the bow reference pins only the seed to `second`, which agrees with the
action-wide reference once the action is that seed.
-/
theorem hedgeDoSecond_eq_bow_intervention
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S)
    {x : Fin S.count}
    (haction : forall p, action p = true → p = x) :
    (fun i => if action i then some (hedgeBowReference rich x i) else none) =
      hedgeDoSecond rich action := by
  funext i
  cases hi : action i with
  | false =>
      simp [hedgeDoSecond, hi]
  | true =>
      have hp : i = x := haction i hi
      subst hp
      simp [hedgeDoSecond, hi, hedgeBowReference]

/--
Kernel-level bridge from a singleton interventional event gap to failure of
query value-equivalence.  This statement is independent of the hedge model:
it rewrites the unconditional query kernel at one reference assignment,
identifies its singleton outcome cylinder, and transports an assumed kernel
equivalence to the forbidden interventional equivalence.
-/
theorem JointKernelQuery.not_valueEquivalent_of_singleton_interventional
    (q : JointKernelQuery S) (left right : ExactModel S)
    {x y : Fin S.count} (value : S.Value y)
    (hx : q.action x = true)
    (reference : S.Assignment)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (referenceY : reference y = value)
    (interventionEq :
      (fun i => if q.action i then some (reference i) else none) = intervention)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (separated :
      Not
        (QProb.Equiv
          (right.interventionalValue intervention
            (fun a => decide (a y = value)))
          (left.interventionalValue intervention
            (fun a => decide (a y = value))))) :
    Not (q.ValueEquivalent left right) := by
  intro valueEquivalent
  let ref : S.Assignment := reference
  have refY : ref y = value := referenceY
  have hasAction :
      (Kernel.mk q.outcome q.action NodeSet.empty).hasAction = true :=
    finAny_eq_true_of q.action x hx
  have doEq :
      (Kernel.mk q.outcome q.action NodeSet.empty).intervention ref =
        intervention := by
    unfold Kernel.intervention
    exact interventionEq
  have eventEq (sample : S.Assignment) :
      Kernel.agreesOn q.outcome ref sample =
        decide (sample y = value) := by
    have unique := agreesOn_of_unique_node q.outcome ref sample hy houtcome
    simpa [refY] using unique
  have leftDenote :=
    Kernel.unconditionalDenote left q.outcome q.action ref
  have rightDenote :=
    Kernel.unconditionalDenote right q.outcome q.action ref
  rcases valueEquivalent ref with ⟨denotesEquivalent⟩
  have someEquivalent :
      ProbabilityResult.Equivalent
        (some
          (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
              left ref).probVal
            (Kernel.agreesOn q.outcome ref)))
        (some
          (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
              right ref).probVal
            (Kernel.agreesOn q.outcome ref))) :=
    ProbabilityResult.trans (ProbabilityResult.symm leftDenote)
      (ProbabilityResult.trans denotesEquivalent rightDenote)
  cases someEquivalent with
  | value queryEquivalent =>
      have leftDistribution :
          (Kernel.mk q.outcome q.action NodeSet.empty).distribution left ref =
            left.interventionalDist intervention := by
        unfold Kernel.distribution
        rw [if_pos hasAction, doEq]
      have rightDistribution :
          (Kernel.mk q.outcome q.action NodeSet.empty).distribution right ref =
            right.interventionalDist intervention := by
        unfold Kernel.distribution
        rw [if_pos hasAction, doEq]
      have leftProbability :
          QProb.Equiv
            (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
                left ref).probVal
              (Kernel.agreesOn q.outcome ref))
            (left.interventionalValue intervention
              (fun a => decide (a y = value))) := by
        rw [leftDistribution]
        exact FiniteProbRecord.probVal_congr _ _ _ eventEq
      have rightProbability :
          QProb.Equiv
            (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
                right ref).probVal
              (Kernel.agreesOn q.outcome ref))
            (right.interventionalValue intervention
              (fun a => decide (a y = value))) := by
        rw [rightDistribution]
        exact FiniteProbRecord.probVal_congr _ _ _ eventEq
      exact separated
        (QProb.equiv_symm
          (QProb.equiv_trans (QProb.equiv_symm leftProbability)
            (QProb.equiv_trans queryEquivalent rightProbability)))

/--
Singleton-outcome separation for a one-root mix.  Incidence at the outcome
supplies the strict interventional mass gap.  The eventual counterexample
also asks for incidence at the action pivot, which independently supplies
observational equality of the singleton mask.
-/
theorem hedgeSingleRootSingletonOutcome_not_valueEquivalent
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {pivot y : Fin S.count} (root : Fin (pairRootCount G))
    (selected : q.action pivot = true)
    (edge : S.directed pivot y = true)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (outcomeIncident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (q.ValueEquivalent
        (hedgeSingleRootMixModel G rich root NodeSet.empty)
        (hedgeSingleRootMixModel G rich root (NodeSet.singleton pivot))) := by
  apply q.not_valueEquivalent_of_singleton_interventional
    (hedgeSingleRootMixModel G rich root NodeSet.empty)
    (hedgeSingleRootMixModel G rich root (NodeSet.singleton pivot))
    (rich.first y) selected
    (hedgeActionReference rich q.action) (hedgeDoSecond rich q.action)
  · exact hedgeActionReference_of_false rich q.action
      (q.outcome_action_disjoint y hy)
  · exact hedgeDoSecond_eq_action_intervention rich q.action
  · exact hy
  · exact houtcome
  · apply hedgeSingleRootMix_interventional_first_not_equiv_of_parentBit
    · exact hedgeDoSecond_of_false rich q.action
        (q.outcome_action_disjoint y hy)
    · intro u
      exact hedgeSingleRootMix_parentBits_singleton_doSecond G rich root
        q.action u selected edge
    · exact outcomeIncident

/--
Generic singleton-outcome separation from an intervention that makes the
model mask's parent bit true.  The model mask is deliberately independent of
the query action: the latter determines which coordinates the causal query
fixes, whereas the former determines which structural equations copy their
directed-parent bit.  Keeping these roles separate permits a countermodel to
change only one useful action parent while the query still intervenes on its
complete action set.

The reference and intervention are explicit data so the all-`second`,
one-pivot, and singleton-mask constructions can share the same kernel
argument.
-/
theorem hedgeSingletonOutcome_not_valueEquivalent_of_parentBit
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (mask : NodeSet S)
    {x y : Fin S.count} (root : Fin (pairRootCount G))
    (hx : q.action x = true)
    (reference : S.Assignment)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (referenceY : reference y = rich.first y)
    (interventionEq :
      (fun i => if q.action i then some (reference i) else none) = intervention)
    (free : intervention y = none)
    (parentBit : forall u : (hedgeLatentExtension G).Assignment,
      hedgeParentBitsFrom rich mask y
          (fun parent _ =>
            (hedgeMixModel G rich mask).evalNodeUnder intervention u
              parent) = true)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (q.ValueEquivalent
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich mask)) := by
  intro hVE
  let ref : S.Assignment := reference
  let left : ExactModel S := hedgeMixModel G rich NodeSet.empty
  let right : ExactModel S := hedgeMixModel G rich mask
  have hrefy : ref y = rich.first y := referenceY
  have hHas :
      (Kernel.mk q.outcome q.action NodeSet.empty).hasAction = true :=
    finAny_eq_true_of q.action x hx
  have hdo :
      (Kernel.mk q.outcome q.action NodeSet.empty).intervention ref =
        intervention := by
    unfold Kernel.intervention
    exact interventionEq
  have hevent (sample : S.Assignment) :
      Kernel.agreesOn q.outcome ref sample =
        decide (sample y = rich.first y) := by
    have h := agreesOn_of_unique_node q.outcome ref sample hy houtcome
    simpa [hrefy] using h
  have hL :=
    Kernel.unconditionalDenote left q.outcome q.action ref
  have hR :=
    Kernel.unconditionalDenote right q.outcome q.action ref
  rcases hVE ref with ⟨heqDenote⟩
  have hsome :
      ProbabilityResult.Equivalent
        (some
          (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
              left ref).probVal
            (Kernel.agreesOn q.outcome ref)))
        (some
          (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
              right ref).probVal
            (Kernel.agreesOn q.outcome ref))) :=
    ProbabilityResult.trans (ProbabilityResult.symm hL)
      (ProbabilityResult.trans heqDenote hR)
  cases hsome with
  | value hq =>
      have hdistL :
          (Kernel.mk q.outcome q.action NodeSet.empty).distribution left ref =
            left.interventionalDist intervention := by
        unfold Kernel.distribution
        rw [if_pos hHas, hdo]
      have hdistR :
          (Kernel.mk q.outcome q.action NodeSet.empty).distribution right ref =
            right.interventionalDist intervention := by
        unfold Kernel.distribution
        rw [if_pos hHas, hdo]
      have hpL :
          QProb.Equiv
            (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
                left ref).probVal
              (Kernel.agreesOn q.outcome ref))
            (left.interventionalValue intervention
              (fun a => decide (a y = rich.first y))) := by
        rw [hdistL]
        exact FiniteProbRecord.probVal_congr _ _ _ hevent
      have hpR :
          QProb.Equiv
            (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
                right ref).probVal
              (Kernel.agreesOn q.outcome ref))
            (right.interventionalValue intervention
              (fun a => decide (a y = rich.first y))) := by
        rw [hdistR]
        exact FiniteProbRecord.probVal_congr _ _ _ hevent
      exact
        hedgeMix_interventional_first_not_equiv_of_parentBit G rich mask
          intervention root free parentBit hincy
          (QProb.equiv_symm
            (QProb.equiv_trans (QProb.equiv_symm hpL)
              (QProb.equiv_trans hq hpR)))

/--
All-`second` singleton separation.  Odd action-parent parity supplies the
generic parent-bit premise.
-/
theorem hedgeSingletonOutcome_not_valueEquivalent_of_parentParity
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {x y : Fin S.count} (root : Fin (pairRootCount G))
    (hx : q.action x = true)
    (hparity : actionParentParity q.action y = true)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (q.ValueEquivalent
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich q.action)) :=
  hedgeSingletonOutcome_not_valueEquivalent_of_parentBit G rich q q.action
    root hx
    (hedgeActionReference rich q.action) (hedgeDoSecond rich q.action)
    (hedgeActionReference_of_false rich q.action
      (q.outcome_action_disjoint y hy))
    (hedgeDoSecond_eq_action_intervention rich q.action)
    (hedgeDoSecond_of_false rich q.action (q.outcome_action_disjoint y hy))
    (fun u =>
      (hedgeParentBitsFrom_doSecond_eq_actionParentParity G rich q.action u
        y).trans hparity)
    hy houtcome hincy

/--
One-pivot singleton separation.  Any directed action parent can be selected
as the unique `second` contributor, while all other action parents are pinned
to `first`; no uniqueness or parity hypothesis remains.
-/
theorem hedgeSingletonOutcome_not_valueEquivalent_of_actionParent
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {pivot y : Fin S.count} (root : Fin (pairRootCount G))
    (selected : q.action pivot = true)
    (edge : S.directed pivot y = true)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (q.ValueEquivalent
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich q.action)) :=
  hedgeSingletonOutcome_not_valueEquivalent_of_parentBit G rich q q.action
    root selected
    (hedgeActionPivotReference rich q.action pivot)
    (hedgeDoPivot rich q.action pivot)
    (hedgeActionPivotReference_of_false rich q.action pivot
      (q.outcome_action_disjoint y hy))
    (hedgeDoPivot_eq_action_intervention rich q.action pivot)
    (hedgeDoPivot_of_false rich q.action pivot
      (q.outcome_action_disjoint y hy))
    (fun u =>
      hedgeParentBitsFrom_doPivot_eq_true G rich q.action u selected edge)
    hy houtcome hincy

/--
Singleton-mask separation at an arbitrary directed action parent.  The query
still intervenes on every action coordinate, but only `pivot` changes its
structural equation between the two models.  Consequently the copied parent
bit has exactly one contributor, independently of how many other action
parents point to the selected outcome.

This is the local form needed by positive hedge countermodels: observational
agreement now has to control only the edges leaving `pivot`, rather than all
edges leaving the query action.
-/
theorem hedgeSingletonOutcome_not_valueEquivalent_of_singletonMask
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {pivot y : Fin S.count} (root : Fin (pairRootCount G))
    (selected : q.action pivot = true)
    (edge : S.directed pivot y = true)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (q.ValueEquivalent
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich (NodeSet.singleton pivot))) :=
  hedgeSingletonOutcome_not_valueEquivalent_of_parentBit G rich q
    (NodeSet.singleton pivot) root selected
    (hedgeActionReference rich q.action) (hedgeDoSecond rich q.action)
    (hedgeActionReference_of_false rich q.action
      (q.outcome_action_disjoint y hy))
    (hedgeDoSecond_eq_action_intervention rich q.action)
    (hedgeDoSecond_of_false rich q.action (q.outcome_action_disjoint y hy))
    (fun u =>
      hedgeParentBitsFrom_of_unique_doSecond G rich
        (NodeSet.singleton pivot) q.action u edge selected
        (by simp [NodeSet.singleton])
        (fun parent inMask _edge =>
          (NodeSet.singleton_eq_true_iff pivot parent).mp inMask))
    hy houtcome hincy

/--
Unique-parent specialization of singleton-outcome parity separation.  Other
action vertices may still have outgoing edges away from the queried node.
-/
theorem hedgeBow_not_valueEquivalent (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {x y : Fin S.count} (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true)
    (hx : q.action x = true)
    (hunique : forall p, q.action p = true →
      S.directed p y = true → p = x)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    Not
      (q.ValueEquivalent
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich q.action)) :=
  hedgeSingletonOutcome_not_valueEquivalent_of_parentParity G rich q root hx
    (actionParentParity_eq_true_of_unique q.action hdir hx hunique) hy houtcome
    hincy

/--
On a shared-switch query whose outcome vertices are directed children of one
action seed, the empty-mask and action-mask mix models disagree at the
action-wide `second` reference.  Other action vertices are permitted; the
only local restriction is that the seed is the unique action parent of every
queried child.
-/
theorem hedgeChildren_not_valueEquivalent (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {x y : Fin S.count} (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true)
    (hx : q.action x = true)
    (hunique : forall i, q.outcome i = true →
      forall p, q.action p = true → S.directed p i = true → p = x)
    (hy : q.outcome y = true)
    (hchildren : forall i, q.outcome i = true → S.directed x i = true)
    (hincChildren : forall c, S.directed x c = true →
      forall r,
        (hedgeLatentExtension G).incident (hedgePairRoot G r) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G r) c)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y =
        true) :
    Not
      (q.ValueEquivalent
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich q.action)) := by
  intro hVE
  let ref : S.Assignment := hedgeActionReference rich q.action
  let left : ExactModel S := hedgeMixModel G rich NodeSet.empty
  let right : ExactModel S := hedgeMixModel G rich q.action
  have hfree : forall i, q.outcome i = true → q.action i = false := by
    intro i hi
    cases hact : q.action i with
    | false =>
        rfl
    | true =>
        exact False.elim
          (Bool.false_ne_true
            ((q.action_outcome_disjoint i hact).symm.trans hi))
  have hHas :
      (Kernel.mk q.outcome q.action NodeSet.empty).hasAction = true :=
    finAny_eq_true_of q.action x hx
  have hdo :
      (Kernel.mk q.outcome q.action NodeSet.empty).intervention ref =
        hedgeDoSecond rich q.action := by
    unfold Kernel.intervention
    exact hedgeDoSecond_eq_action_intervention rich q.action
  have hL :=
    Kernel.unconditionalDenote left q.outcome q.action ref
  have hR :=
    Kernel.unconditionalDenote right q.outcome q.action ref
  rcases hVE ref with ⟨heqDenote⟩
  have hsome :
      ProbabilityResult.Equivalent
        (some
          (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
              left ref).probVal
            (Kernel.agreesOn q.outcome ref)))
        (some
          (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
              right ref).probVal
            (Kernel.agreesOn q.outcome ref))) :=
    ProbabilityResult.trans (ProbabilityResult.symm hL)
      (ProbabilityResult.trans heqDenote hR)
  cases hsome with
  | value hq =>
      have hdistL :
          (Kernel.mk q.outcome q.action NodeSet.empty).distribution left ref =
            left.interventionalDist (hedgeDoSecond rich q.action) := by
        unfold Kernel.distribution
        rw [if_pos hHas, hdo]
      have hdistR :
          (Kernel.mk q.outcome q.action NodeSet.empty).distribution right ref =
            right.interventionalDist (hedgeDoSecond rich q.action) := by
        unfold Kernel.distribution
        rw [if_pos hHas, hdo]
      have hpL :
          QProb.Equiv
            (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
                left ref).probVal
              (Kernel.agreesOn q.outcome ref))
            (left.interventionalValue (hedgeDoSecond rich q.action)
              (Kernel.agreesOn q.outcome ref)) := by
        rw [hdistL]
        rfl
      have hpR :
          QProb.Equiv
            (((Kernel.mk q.outcome q.action NodeSet.empty).distribution
                right ref).probVal
              (Kernel.agreesOn q.outcome ref))
            (right.interventionalValue (hedgeDoSecond rich q.action)
              (Kernel.agreesOn q.outcome ref)) := by
        rw [hdistR]
        rfl
      exact
        hedgeMix_interventional_children_not_equiv G rich q.action q.outcome
          root hdir hx hy hunique hfree hchildren hincChildren hincy
          (QProb.equiv_symm
            (QProb.equiv_trans (QProb.equiv_symm hpL)
              (QProb.equiv_trans hq hpR)))

/--
Positive counterexample for a general acyclic shared-switch action mask.
Every masked edge must preserve pair-root incidence, which gives
observational agreement by topological induction.  Query separation needs
only one action seed reaching every outcome and being the unique action
parent there.  In particular, non-sink extra action vertices are allowed when
they satisfy the same edge-wise switch condition and do not also parent a
queried child.
-/
def hedgeEdgeSharedChildrenCounterexampleIn (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {x y : Fin S.count} (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true)
    (hx : q.action x = true)
    (hy : q.outcome y = true)
    (hchildren : forall i, q.outcome i = true → S.directed x i = true)
    (hunique : forall i, q.outcome i = true →
      forall p, q.action p = true → S.directed p i = true → p = x)
    (shared : forall parent child,
      q.action parent = true → S.directed parent child = true →
        forall r,
          (hedgeLatentExtension G).incident (hedgePairRoot G r) parent =
            (hedgeLatentExtension G).incident (hedgePairRoot G r) child)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y =
        true) :
    CounterexampleIn (GraphModelClass.positive G) q where
  left := hedgeMixModel G rich NodeSet.empty
  right := hedgeMixModel G rich q.action
  left_mem := hedgeMixModel_mem_positive G rich NodeSet.empty
  right_mem := hedgeMixModel_mem_positive G rich q.action
  observationally_equal :=
    hedgeMixModel_observationally_equivalent_of_edge_shared_switch G rich
      q.action shared
  query_separated :=
    hedgeChildren_not_valueEquivalent G rich q root hdir hx hunique hy
      hchildren (fun child edge r => shared x child hx edge r) hincy

/--
A seed-or-sink-action hedge whose outcome is any set of directed children
of the action seed, all sharing that seed's pair-root switch.
Observational agreement is the shared-switch lemma; interventional
disagreement is the composite child cylinder under the action-wide
`second` reference.
-/
def hedgeSharedSwitchCounterexampleIn (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {x y : Fin S.count} (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true)
    (hx : q.action x = true)
    (hsink : forall p, q.action p = true →
      p = x ∨ forall c, S.directed p c = false)
    (hy : q.outcome y = true)
    (hchildren : forall i, q.outcome i = true → S.directed x i = true)
    (hincChildren : forall c, S.directed x c = true →
      forall r,
        (hedgeLatentExtension G).incident (hedgePairRoot G r) x =
          (hedgeLatentExtension G).incident (hedgePairRoot G r) c)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y =
        true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  hedgeEdgeSharedChildrenCounterexampleIn G rich q root hdir hx hy hchildren
    (fun _i _hi p selected edge =>
      hedgeMaskParent_eq_seed hsink selected edge)
    (fun parent child selected edge root => by
      have parentEq : parent = x :=
        hedgeMaskParent_eq_seed hsink selected edge
      subst parent
      exact hincChildren child edge root)
    hincy

/--
A bow-arc hedge query is not identifiable in the positive class: the
empty-mask and action-mask mix models are observationally equivalent and
disagree on `P(Y | do(X))`.  Unique-child is only used to specialise
shared-switch agreement.
-/
def hedgeBowCounterexampleIn (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    {x y : Fin S.count} (root : Fin (pairRootCount G))
    (hdir : S.directed x y = true)
    (hx : q.action x = true)
    (hsink : forall p, q.action p = true →
      p = x ∨ forall c, S.directed p c = false)
    (hy : q.outcome y = true)
    (houtcome : forall i, q.outcome i = true → i = y)
    (honly : forall c, S.directed x c = true → c = y)
    (hinc : forall r,
      (hedgeLatentExtension G).incident (hedgePairRoot G r) x =
        (hedgeLatentExtension G).incident (hedgePairRoot G r) y)
    (hincy : (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  hedgeSharedSwitchCounterexampleIn G rich q root hdir hx hsink hy
    (fun i hi => by
      have heq := houtcome i hi
      subst heq
      exact hdir)
    (hedgeMix_bow_shared_switch (G := G) honly hinc) hincy

/--
The first pair-root incident to `child`, recovered from `List.finRange`
rather than from an `Exists` incidence proof.
-/
def firstIncidentPairRoot (G : ObservedGraph S) (child : Fin S.count)
    (h : (List.finRange (pairRootCount G)).any (fun root =>
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child) =
        true) :
    Fin (pairRootCount G) :=
  listFirstAny (List.finRange (pairRootCount G))
    (fun root =>
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child)
    h

theorem firstIncidentPairRoot_incident
    (G : ObservedGraph S) (child : Fin S.count)
    (h : (List.finRange (pairRootCount G)).any (fun root =>
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child) =
        true) :
    (hedgeLatentExtension G).incident
      (hedgePairRoot G (firstIncidentPairRoot G child h)) child = true :=
  listFirstAny_pred (List.finRange (pairRootCount G))
    (fun root =>
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child)
    h

/--
Identical pair-root incidence of `x` and `y` is the ADMG neighbourhood
condition that each is the other's only bidirected neighbour.  Extra
bidirected arms would give a pair-root incident to one seed and not the
other; that is exactly the observational mismatch of the mix models.
-/
theorem pairRootIncident_eq_of_unique_bidirected
    (G : ObservedGraph S) {x y : Fin S.count}
    (hx : forall i, G.bidirected x i = true → i = y)
    (hy : forall i, G.bidirected y i = true → i = x)
    (root : Fin (pairRootCount G)) :
    pairRootIncident G root x = pairRootIncident G root y := by
  have hedgeAB :
      G.bidirected ((pairRoots G).get root).1 ((pairRoots G).get root).2 =
        true :=
    (pairRoots_get_spec G root).2
  have hsym :
      G.bidirected ((pairRoots G).get root).2 ((pairRoots G).get root).1 =
        true :=
    G.bidirected_symmetric hedgeAB
  cases hxInc : pairRootIncident G root x with
  | true =>
      have hxEnd := (pairRootIncident_iff G root x).mp hxInc
      cases hxEnd with
      | inl hxa =>
          have hxb :
              G.bidirected x ((pairRoots G).get root).2 = true := by
            simpa [hxa] using hedgeAB
          have hby : ((pairRoots G).get root).2 = y := hx _ hxb
          have hyInc : pairRootIncident G root y = true :=
            (pairRootIncident_iff G root y).mpr (Or.inr hby.symm)
          rw [hyInc]
      | inr hxb =>
          have hxa :
              G.bidirected x ((pairRoots G).get root).1 = true := by
            simpa [hxb] using hsym
          have hay : ((pairRoots G).get root).1 = y := hx _ hxa
          have hyInc : pairRootIncident G root y = true :=
            (pairRootIncident_iff G root y).mpr (Or.inl hay.symm)
          rw [hyInc]
  | false =>
      cases hyInc : pairRootIncident G root y with
      | false =>
          rfl
      | true =>
          have hyEnd := (pairRootIncident_iff G root y).mp hyInc
          cases hyEnd with
          | inl hya =>
              have hyb :
                  G.bidirected y ((pairRoots G).get root).2 = true := by
                simpa [hya] using hedgeAB
              have hbx : ((pairRoots G).get root).2 = x := hy _ hyb
              have hxTrue : pairRootIncident G root x = true :=
                (pairRootIncident_iff G root x).mpr (Or.inr hbx.symm)
              exact False.elim (Bool.false_ne_true (hxInc.symm.trans hxTrue))
          | inr hyb =>
              have hya :
                  G.bidirected y ((pairRoots G).get root).1 = true := by
                simpa [hyb] using hsym
              have hax : ((pairRoots G).get root).1 = x := hy _ hya
              have hxTrue : pairRootIncident G root x = true :=
                (pairRootIncident_iff G root x).mpr (Or.inl hax.symm)
              exact False.elim (Bool.false_ne_true (hxInc.symm.trans hxTrue))

theorem hedgeIncident_eq_of_unique_bidirected
    (G : ObservedGraph S) {x y : Fin S.count}
    (hx : forall i, G.bidirected x i = true → i = y)
    (hy : forall i, G.bidirected y i = true → i = x)
    (root : Fin (pairRootCount G)) :
    (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
      (hedgeLatentExtension G).incident (hedgePairRoot G root) y := by
  simpa [hedgeLatentExtension, hedgeIncident_pair] using
    pairRootIncident_eq_of_unique_bidirected G hx hy root

/--
The pair-root of an ordered bidirected edge, written so the two endpoints
need not be presented in rank order.
-/
def orderedBidirectedRoot (G : ObservedGraph S) {x y : Fin S.count}
    (hedge : G.bidirected x y = true) : Fin (pairRootCount G) :=
  if h : x.val < y.val then
    pairRootOf G h hedge
  else
    pairRootOf G (by
      have hne : x ≠ y := fun heq =>
        Bool.false_ne_true
          ((G.bidirected_irreflexive x).symm.trans (by simpa [heq] using hedge))
      have hord : x.val < y.val ∨ y.val < x.val :=
        Nat.lt_or_gt_of_ne (fun hv => hne (Fin.ext hv))
      cases hord with
      | inl hlt => exact False.elim (h hlt)
      | inr hgt => exact hgt)
      (G.bidirected_symmetric hedge)

theorem orderedBidirectedRoot_incident_right
    (G : ObservedGraph S) {x y : Fin S.count}
    (hedge : G.bidirected x y = true) :
    pairRootIncident G (orderedBidirectedRoot G hedge) y = true := by
  unfold orderedBidirectedRoot
  split
  · next hord =>
      exact (pairRootIncident_of G hord hedge).2
  · next hord =>
      exact (pairRootIncident_of G _ (G.bidirected_symmetric hedge)).1

theorem hedgePairRoot_incident_outcome_of_bidirected
    (G : ObservedGraph S) {x y : Fin S.count}
    (hedge : G.bidirected x y = true) :
    (hedgeLatentExtension G).incident
      (hedgePairRoot G (orderedBidirectedRoot G hedge)) y = true := by
  simpa [hedgeLatentExtension, hedgeIncident_pair] using
    orderedBidirectedRoot_incident_right G hedge

/--
A `HedgeWitness` whose action and outcome seeds form a bow, with
seed-or-sink action, singleton outcome and identical pair-root incidence,
inhabits a positive-class `CounterexampleIn`.  The seeds are the stored
data fields: no `Exists` elimination into `Type`.
-/
def hedgeBowCounterexampleIn_of_witness (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q) (root : Fin (pairRootCount G))
    (hdir : S.directed w.actionSeed w.outcomeSeed = true)
    (hsink : forall p, q.action p = true →
      p = w.actionSeed ∨ forall c, S.directed p c = false)
    (houtcome : forall i, q.outcome i = true → i = w.outcomeSeed)
    (honly : forall c, S.directed w.actionSeed c = true → c = w.outcomeSeed)
    (hinc : forall r,
      (hedgeLatentExtension G).incident (hedgePairRoot G r) w.actionSeed =
        (hedgeLatentExtension G).incident (hedgePairRoot G r) w.outcomeSeed)
    (hincy :
      (hedgeLatentExtension G).incident (hedgePairRoot G root)
        w.outcomeSeed = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  hedgeBowCounterexampleIn G rich q root hdir w.actionSeed_in_action
    hsink w.outcomeSeed_in_outcome houtcome honly hinc hincy

/--
Same seeds as `hedgeBowCounterexampleIn_of_witness`, but every directed
child of the action seed may share the pair-root switch — not only a
unique bow child.
-/
def hedgeSharedSwitchCounterexampleIn_of_witness (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q) (root : Fin (pairRootCount G))
    (hdir : S.directed w.actionSeed w.outcomeSeed = true)
    (hsink : forall p, q.action p = true →
      p = w.actionSeed ∨ forall c, S.directed p c = false)
    (hchildren : forall i, q.outcome i = true →
      S.directed w.actionSeed i = true)
    (hincChildren : forall c, S.directed w.actionSeed c = true →
      forall r,
        (hedgeLatentExtension G).incident (hedgePairRoot G r) w.actionSeed =
          (hedgeLatentExtension G).incident (hedgePairRoot G r) c)
    (hincy :
      (hedgeLatentExtension G).incident (hedgePairRoot G root)
        w.outcomeSeed = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  hedgeSharedSwitchCounterexampleIn G rich q root hdir w.actionSeed_in_action
    hsink w.outcomeSeed_in_outcome hchildren hincChildren hincy

/--
Same as `hedgeBowCounterexampleIn_of_witness`, with the incident pair-root
recovered by list search from a Boolean `any` rather than supplied as a
`Fin`.
-/
def hedgeBowCounterexampleIn_of_witness_any (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q)
    (hdir : S.directed w.actionSeed w.outcomeSeed = true)
    (hsink : forall p, q.action p = true →
      p = w.actionSeed ∨ forall c, S.directed p c = false)
    (houtcome : forall i, q.outcome i = true → i = w.outcomeSeed)
    (honly : forall c, S.directed w.actionSeed c = true → c = w.outcomeSeed)
    (hinc : forall r,
      (hedgeLatentExtension G).incident (hedgePairRoot G r) w.actionSeed =
        (hedgeLatentExtension G).incident (hedgePairRoot G r) w.outcomeSeed)
    (hroot :
      (List.finRange (pairRootCount G)).any (fun root =>
        (hedgeLatentExtension G).incident (hedgePairRoot G root)
          w.outcomeSeed) = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  hedgeBowCounterexampleIn_of_witness G rich q w
    (firstIncidentPairRoot G w.outcomeSeed hroot) hdir hsink houtcome
    honly hinc
    (firstIncidentPairRoot_incident G w.outcomeSeed hroot)

/--
A bow-shaped `HedgeWitness` whose only bidirected neighbour of each seed
is the other seed.  That ADMG neighbourhood condition is the most general
form of identical pair-root incidence, and the shared bidirected edge
supplies the mix pair-root as data via `orderedBidirectedRoot`.
-/
def hedgeBowCounterexampleIn_of_witness_unique_bidirected
    (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q)
    (hdir : S.directed w.actionSeed w.outcomeSeed = true)
    (hsink : forall p, q.action p = true →
      p = w.actionSeed ∨ forall c, S.directed p c = false)
    (houtcome : forall i, q.outcome i = true → i = w.outcomeSeed)
    (honly : forall c, S.directed w.actionSeed c = true → c = w.outcomeSeed)
    (hxOnly : forall i,
      G.bidirected w.actionSeed i = true → i = w.outcomeSeed)
    (hyOnly : forall i,
      G.bidirected w.outcomeSeed i = true → i = w.actionSeed)
    (hedge : G.bidirected w.actionSeed w.outcomeSeed = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  hedgeBowCounterexampleIn_of_witness G rich q w
    (orderedBidirectedRoot G hedge) hdir hsink houtcome honly
    (fun root =>
      hedgeIncident_eq_of_unique_bidirected G hxOnly hyOnly root)
    (hedgePairRoot_incident_outcome_of_bidirected G hedge)

/--
If the kept-child map of the large forest sends the action seed to the
outcome seed, that kept edge is an observed directed edge.  The
direction is data of `CForest.child_edge`, not a search through `Exists`.
-/
theorem HedgeWitness.directed_of_forest_child
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q)
    (h : w.child w.actionSeed = some w.outcomeSeed) :
    S.directed w.actionSeed w.outcomeSeed = true :=
  (w.large_forest.child_edge w.actionSeed w.outcomeSeed h).2.2

/-- Singleton action membership names the stored action seed. -/
theorem HedgeWitness.action_unique_of_members
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q)
    (h : NodeSet.members q.action = [w.actionSeed]) :
    forall p, q.action p = true → p = w.actionSeed :=
  fun _p hp => NodeSet.eq_of_members_singleton h hp

/-- Singleton outcome membership names the stored outcome seed. -/
theorem HedgeWitness.outcome_unique_of_members
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q)
    (h : NodeSet.members q.outcome = [w.outcomeSeed]) :
    forall i, q.outcome i = true → i = w.outcomeSeed :=
  fun _i hi => NodeSet.eq_of_members_singleton h hi

/--
The action contains `seed`, and every other selected vertex has no
outgoing directed edge.  Extra sink vertices do not contribute parent
bits, so shared-switch mix agreement (and the action-wide `second`
intervention) still applies.
-/
def actionSeedAndSinkExtrasBool (S : ObservedSignature)
    (action : NodeSet S) (seed : Fin S.count) : Bool :=
  action seed &&
    (NodeSet.enumerated S).all (fun p =>
      !(action p) || decide (p = seed) ||
        (NodeSet.enumerated S).all (fun c => !(S.directed p c)))

theorem actionSeedAndSinkExtrasBool_mem
    {S : ObservedSignature} {action : NodeSet S} {seed : Fin S.count}
    (h : actionSeedAndSinkExtrasBool S action seed = true) :
    action seed = true :=
  (Bool.and_eq_true_iff.mp h).1

theorem actionSeedAndSinkExtrasBool_sink
    {S : ObservedSignature} {action : NodeSet S} {seed : Fin S.count}
    (h : actionSeedAndSinkExtrasBool S action seed = true) :
    forall p, action p = true →
      p = seed ∨ forall c, S.directed p c = false := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  intro p hp
  if hpeq : p = seed then
    exact Or.inl hpeq
  else
    refine Or.inr ?_
    intro c
    have ok :=
      (List.all_eq_true.mp hall) p (NodeSet.mem_enumerated S p)
    have inner :
        (NodeSet.enumerated S).all (fun d => !(S.directed p d)) = true := by
      simpa [hp, decide_eq_false hpeq] using ok
    have hc :=
      (List.all_eq_true.mp inner) c (NodeSet.mem_enumerated S c)
    simpa using hc

/--
Every directed child of `parent` is `child`.  Enumerated Boolean search,
not a `Prop` quantification over `Fin`.
-/
def uniqueDirectedChildBool (S : ObservedSignature)
    (parent child : Fin S.count) : Bool :=
  (NodeSet.enumerated S).all (fun c =>
    !(S.directed parent c) || decide (c = child))

theorem uniqueDirectedChildBool_spec
    {S : ObservedSignature} {parent child : Fin S.count}
    (h : uniqueDirectedChildBool S parent child = true)
    {c : Fin S.count} (hd : S.directed parent c = true) : c = child := by
  have ok :=
    (List.all_eq_true.mp h) c (NodeSet.mem_enumerated S c)
  simp [hd] at ok
  exact ok

/--
Pair-root incidence of `left` and `right` agrees on every enumerated
pair-root.  This is the Boolean form of identical mix switches.
-/
def hedgePairRootIncidentEqBool (G : ObservedGraph S)
    (left right : Fin S.count) : Bool :=
  (List.finRange (pairRootCount G)).all (fun root =>
    decide (pairRootIncident G root left = pairRootIncident G root right))

theorem hedgePairRootIncidentEqBool_spec
    {G : ObservedGraph S} {left right : Fin S.count}
    (h : hedgePairRootIncidentEqBool G left right = true)
    (root : Fin (pairRootCount G)) :
    pairRootIncident G root left = pairRootIncident G root right := by
  have hmem : root ∈ List.finRange (pairRootCount G) :=
    List.mem_ofFn.mpr ⟨root, rfl⟩
  have ok := (List.all_eq_true.mp h) root hmem
  exact of_decide_eq_true ok

/--
Every directed child of `x` shares `x`'s pair-root incidence.  The
unique-child bow test is the special case that there is only one child.
-/
def sharedSwitchChildrenBool (G : ObservedGraph S) (x : Fin S.count) :
    Bool :=
  (NodeSet.enumerated S).all (fun c =>
    !(S.directed x c) || hedgePairRootIncidentEqBool G x c)

theorem sharedSwitchChildrenBool_spec
    {G : ObservedGraph S} {x c : Fin S.count}
    (h : sharedSwitchChildrenBool G x = true)
    (hd : S.directed x c = true) (root : Fin (pairRootCount G)) :
    pairRootIncident G root x = pairRootIncident G root c := by
  have ok :=
    (List.all_eq_true.mp h) c (NodeSet.mem_enumerated S c)
  simp [hd] at ok
  exact hedgePairRootIncidentEqBool_spec ok root

theorem sharedSwitchChildrenBool_hedgeIncident
    {G : ObservedGraph S} {x c : Fin S.count}
    (h : sharedSwitchChildrenBool G x = true)
    (hd : S.directed x c = true) (root : Fin (pairRootCount G)) :
    (hedgeLatentExtension G).incident (hedgePairRoot G root) x =
      (hedgeLatentExtension G).incident (hedgePairRoot G root) c := by
  simpa [hedgeLatentExtension, hedgeIncident_pair] using
    sharedSwitchChildrenBool_spec h hd root

/--
Every directed edge leaving the selected action mask preserves pair-root
incidence.  This is the finite Boolean form of the hypothesis used by
`hedgeMixModel_observationally_equivalent_of_edge_shared_switch`; unlike
`actionSeedAndSinkExtrasBool`, it permits extra action vertices with outgoing
edges.
-/
def actionEdgesSharePairRootSwitchBool (G : ObservedGraph S)
    (action : NodeSet S) : Bool :=
  (NodeSet.enumerated S).all fun parent =>
    !(action parent) ||
      (NodeSet.enumerated S).all fun child =>
        !(S.directed parent child) ||
          hedgePairRootIncidentEqBool G parent child

/-- Recover edge-wise pair-root equality from the executable action test. -/
theorem actionEdgesSharePairRootSwitchBool_spec
    {G : ObservedGraph S} {action : NodeSet S}
    (h : actionEdgesSharePairRootSwitchBool G action = true)
    {parent child : Fin S.count}
    (selected : action parent = true)
    (edge : S.directed parent child = true)
    (root : Fin (pairRootCount G)) :
    pairRootIncident G root parent = pairRootIncident G root child := by
  have parentOk :=
    (List.all_eq_true.mp h) parent (NodeSet.mem_enumerated S parent)
  have childrenOk :
      (NodeSet.enumerated S).all (fun c =>
        !(S.directed parent c) ||
          hedgePairRootIncidentEqBool G parent c) = true := by
    simpa [selected] using parentOk
  have childOk :=
    (List.all_eq_true.mp childrenOk) child (NodeSet.mem_enumerated S child)
  simp [edge] at childOk
  exact hedgePairRootIncidentEqBool_spec childOk root

/-- The same action-edge test, stated on the concrete hedge latent extension. -/
theorem actionEdgesSharePairRootSwitchBool_hedgeIncident
    {G : ObservedGraph S} {action : NodeSet S}
    (h : actionEdgesSharePairRootSwitchBool G action = true)
    {parent child : Fin S.count}
    (selected : action parent = true)
    (edge : S.directed parent child = true)
    (root : Fin (pairRootCount G)) :
    (hedgeLatentExtension G).incident (hedgePairRoot G root) parent =
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child := by
  simpa [hedgeLatentExtension, hedgeIncident_pair] using
    actionEdgesSharePairRootSwitchBool_spec h selected edge root

/--
Test that `seed` is the only action vertex with a directed edge into any
queried outcome.  Vertices outside the outcome are intentionally ignored:
the interventional separation proof only reads the queried cylinder.
-/
def uniqueActionParentAtOutcomesBool (S : ObservedSignature)
    (action outcome : NodeSet S) (seed : Fin S.count) : Bool :=
  (NodeSet.enumerated S).all fun child =>
    !(outcome child) ||
      (NodeSet.enumerated S).all fun parent =>
        !(action parent) || !(S.directed parent child) ||
          decide (parent = seed)

/-- Recover uniqueness of the action parent at every selected outcome. -/
theorem uniqueActionParentAtOutcomesBool_spec
    {S : ObservedSignature} {action outcome : NodeSet S}
    {seed : Fin S.count}
    (h : uniqueActionParentAtOutcomesBool S action outcome seed = true) :
    forall child, outcome child = true →
      forall parent, action parent = true →
        S.directed parent child = true → parent = seed := by
  intro child inOutcome parent inAction edge
  have childOk :=
    (List.all_eq_true.mp h) child (NodeSet.mem_enumerated S child)
  have parentsOk :
      (NodeSet.enumerated S).all (fun p =>
        !(action p) || !(S.directed p child) || decide (p = seed)) = true := by
    simpa [inOutcome] using childOk
  have parentOk :=
    (List.all_eq_true.mp parentsOk) parent (NodeSet.mem_enumerated S parent)
  simpa [inAction, edge] using parentOk

/--
Every bidirected neighbour of `node` is `neighbor`.  This is the ADMG
form of identical pair-root incidence at one endpoint.
-/
def uniqueBidirectedNeighborBool (G : ObservedGraph S)
    (node neighbor : Fin S.count) : Bool :=
  (NodeSet.enumerated S).all (fun i =>
    !(G.bidirected node i) || decide (i = neighbor))

theorem uniqueBidirectedNeighborBool_spec
    {G : ObservedGraph S} {node neighbor : Fin S.count}
    (h : uniqueBidirectedNeighborBool G node neighbor = true)
    {i : Fin S.count} (hedge : G.bidirected node i = true) :
    i = neighbor := by
  have ok :=
    (List.all_eq_true.mp h) i (NodeSet.mem_enumerated S i)
  simp [hedge] at ok
  exact ok

/-!
### Executable recognition of the generalized positive mix leaf

The theorem-level edge-shared counterexample above is useful only if the
finite failure pipeline can recognize its hypotheses.  The readiness test
below keeps every condition computational: subset, parent uniqueness,
edge-wise switch equality, and incident-root existence are all Boolean scans
over canonical duplicate-free enumerations.
-/

/--
Boolean tests that a `HedgeWitness` fits the generalized edge-shared mix
construction.  Compared with `hedgeWitnessSharedSwitchReady`, extra action
vertices need not be sinks.  Their outgoing edges must preserve pair-root
incidence, and no such extra vertex may also parent a queried outcome.
-/
def hedgeWitnessEdgeSharedReady (G : ObservedGraph S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) : Bool :=
  q.action w.actionSeed &&
    (NodeSet.subsetBool q.outcome (fun i => S.directed w.actionSeed i) &&
      (uniqueActionParentAtOutcomesBool S q.action q.outcome w.actionSeed &&
        (S.directed w.actionSeed w.outcomeSeed &&
          (actionEdgesSharePairRootSwitchBool G q.action &&
            (List.finRange (pairRootCount G)).any (fun root =>
              (hedgeLatentExtension G).incident (hedgePairRoot G root)
                w.outcomeSeed)))))

/--
Successful generalized readiness produces a positive-class counterexample.
The incident pair-root is selected by the existing finite first-match search;
all universal premises are recovered from their Boolean scans.
-/
def hedgeEdgeSharedChildrenCounterexampleIn_of_ready
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q)
    (h : hedgeWitnessEdgeSharedReady G q w = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let hAction := (Bool.and_eq_true_iff.mp h).1
  let hRest := (Bool.and_eq_true_iff.mp h).2
  let hOutcome := (Bool.and_eq_true_iff.mp hRest).1
  let hRest2 := (Bool.and_eq_true_iff.mp hRest).2
  let hUnique := (Bool.and_eq_true_iff.mp hRest2).1
  let hRest3 := (Bool.and_eq_true_iff.mp hRest2).2
  let hDirected := (Bool.and_eq_true_iff.mp hRest3).1
  let hRest4 := (Bool.and_eq_true_iff.mp hRest3).2
  let hShared := (Bool.and_eq_true_iff.mp hRest4).1
  let hRoot := (Bool.and_eq_true_iff.mp hRest4).2
  hedgeEdgeSharedChildrenCounterexampleIn G rich q
    (firstIncidentPairRoot G w.outcomeSeed hRoot)
    hDirected hAction w.outcomeSeed_in_outcome
    ((NodeSet.subsetBool_eq_true_iff q.outcome
      (fun i => S.directed w.actionSeed i)).mp hOutcome)
    (uniqueActionParentAtOutcomesBool_spec hUnique)
    (fun _parent _child selected edge root =>
      actionEdgesSharePairRootSwitchBool_hedgeIncident hShared selected edge
        root)
    (firstIncidentPairRoot_incident G w.outcomeSeed hRoot)

/--
Boolean tests that a `HedgeWitness` is a seed-or-sink-action query whose
outcome is a set of directed children of the action seed, those children
share that seed's pair-root switch, and some pair-root is incident to the
outcome seed.  Unique-child bows are a special case.  Extra action
vertices are allowed when they have no outgoing directed edges.
-/
def hedgeWitnessSharedSwitchReady (G : ObservedGraph S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) : Bool :=
  actionSeedAndSinkExtrasBool S q.action w.actionSeed &&
    (NodeSet.subsetBool q.outcome (fun i => S.directed w.actionSeed i) &&
      (S.directed w.actionSeed w.outcomeSeed &&
        (sharedSwitchChildrenBool G w.actionSeed &&
          (List.finRange (pairRootCount G)).any (fun root =>
            (hedgeLatentExtension G).incident (hedgePairRoot G root)
              w.outcomeSeed))))

/--
A `HedgeWitness` whose shared-switch tests succeed inhabits a
positive-class `CounterexampleIn`.
-/
def hedgeSharedSwitchCounterexampleIn_of_ready (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q)
    (h : hedgeWitnessSharedSwitchReady G q w = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let hAct := (Bool.and_eq_true_iff.mp h).1
  let hRest := (Bool.and_eq_true_iff.mp h).2
  let hOut := (Bool.and_eq_true_iff.mp hRest).1
  let hRest2 := (Bool.and_eq_true_iff.mp hRest).2
  let hdir := (Bool.and_eq_true_iff.mp hRest2).1
  let hRest3 := (Bool.and_eq_true_iff.mp hRest2).2
  let hswitch := (Bool.and_eq_true_iff.mp hRest3).1
  let hrootB := (Bool.and_eq_true_iff.mp hRest3).2
  let hsink : forall p, q.action p = true →
      p = w.actionSeed ∨ forall c, S.directed p c = false :=
    actionSeedAndSinkExtrasBool_sink hAct
  let hchildren : forall i, q.outcome i = true →
      S.directed w.actionSeed i = true :=
    (NodeSet.subsetBool_eq_true_iff q.outcome
      (fun i => S.directed w.actionSeed i)).mp hOut
  hedgeSharedSwitchCounterexampleIn_of_witness G rich q w
    (firstIncidentPairRoot G w.outcomeSeed hrootB) hdir hsink hchildren
    (fun _c hd root => sharedSwitchChildrenBool_hedgeIncident hswitch hd root)
    (firstIncidentPairRoot_incident G w.outcomeSeed hrootB)

/--
Boolean tests that a `HedgeWitness` is a seed-or-sink-action,
singleton-outcome bow with unique directed child and unique mutual
bidirected neighbourhoods.  Passing these tests is the most general
data-level bow special case.
-/
def hedgeWitnessBowReady (G : ObservedGraph S) (q : JointKernelQuery S)
    (w : HedgeWitness G q) : Bool :=
  actionSeedAndSinkExtrasBool S q.action w.actionSeed &&
    (NodeSet.equal q.outcome (NodeSet.singleton w.outcomeSeed) &&
      (S.directed w.actionSeed w.outcomeSeed &&
        (uniqueDirectedChildBool S w.actionSeed w.outcomeSeed &&
          (uniqueBidirectedNeighborBool G w.actionSeed w.outcomeSeed &&
            (uniqueBidirectedNeighborBool G w.outcomeSeed w.actionSeed &&
              G.bidirected w.actionSeed w.outcomeSeed)))))

/--
A `HedgeWitness` whose Boolean bow tests succeed inhabits a positive-class
`CounterexampleIn`.  The tests are member-list and edge-enumeration Bools;
the `Exists` fields of the witness are never unpacked into `Type`.
-/
def hedgeBowCounterexampleIn_of_ready (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q)
    (h : hedgeWitnessBowReady G q w = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let hAct := (Bool.and_eq_true_iff.mp h).1
  let hRest := (Bool.and_eq_true_iff.mp h).2
  let hOut := (Bool.and_eq_true_iff.mp hRest).1
  let hRest2 := (Bool.and_eq_true_iff.mp hRest).2
  let hdir := (Bool.and_eq_true_iff.mp hRest2).1
  let hRest3 := (Bool.and_eq_true_iff.mp hRest2).2
  let honlyB := (Bool.and_eq_true_iff.mp hRest3).1
  let hRest4 := (Bool.and_eq_true_iff.mp hRest3).2
  let hxB := (Bool.and_eq_true_iff.mp hRest4).1
  let hRest5 := (Bool.and_eq_true_iff.mp hRest4).2
  let hyB := (Bool.and_eq_true_iff.mp hRest5).1
  let hedge := (Bool.and_eq_true_iff.mp hRest5).2
  let hsink : forall p, q.action p = true →
      p = w.actionSeed ∨ forall c, S.directed p c = false :=
    actionSeedAndSinkExtrasBool_sink hAct
  let houtcome : forall i, q.outcome i = true → i = w.outcomeSeed := by
    have heq := (NodeSet.equal_eq_true_iff _ _).mp hOut
    intro i hi
    have : NodeSet.singleton w.outcomeSeed i = true := by
      simpa [heq] using hi
    exact (NodeSet.singleton_eq_true_iff w.outcomeSeed i).mp this
  hedgeBowCounterexampleIn_of_witness_unique_bidirected G rich q w hdir
    hsink houtcome
    (fun _c hd => uniqueDirectedChildBool_spec honlyB hd)
    (fun _i hedgei => uniqueBidirectedNeighborBool_spec hxB hedgei)
    (fun _i hedgei => uniqueBidirectedNeighborBool_spec hyB hedgei)
    hedge

/--
Run the executable positive-mix leaves in backward-compatible order.  The
established seed-plus-sink constructor remains the first branch
so callers that inspect the returned witness keep its canonical proof term;
the edge-shared branch then covers genuinely new non-sink action masks, and
the bow test remains as a narrow fallback.  Failure is `none`, never an
`Exists` unpacking into data.
-/
def hedgeCounterexampleIn? (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q) :
    Option (CounterexampleIn (GraphModelClass.positive G) q) :=
  if h : hedgeWitnessSharedSwitchReady G q w = true then
    some (hedgeSharedSwitchCounterexampleIn_of_ready G rich q w h)
  else if hedge : hedgeWitnessEdgeSharedReady G q w = true then
    some (hedgeEdgeSharedChildrenCounterexampleIn_of_ready G rich q w hedge)
  else if hbow : hedgeWitnessBowReady G q w = true then
    some (hedgeBowCounterexampleIn_of_ready G rich q w hbow)
  else
    none

theorem hedgeCounterexampleIn?_isSome_of_edge_shared
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q)
    (h : hedgeWitnessEdgeSharedReady G q w = true) :
    (hedgeCounterexampleIn? G rich q w).isSome = true := by
  dsimp [hedgeCounterexampleIn?]
  split
  · simp
  · simp

theorem hedgeCounterexampleIn?_isSome_of_shared_switch
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q)
    (h : hedgeWitnessSharedSwitchReady G q w = true) :
    (hedgeCounterexampleIn? G rich q w).isSome = true := by
  dsimp [hedgeCounterexampleIn?]
  simp [h]

theorem hedgeCounterexampleIn?_isSome_iff
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) :
    (hedgeCounterexampleIn? G rich q w).isSome =
      (hedgeWitnessSharedSwitchReady G q w ||
        hedgeWitnessEdgeSharedReady G q w ||
          hedgeWitnessBowReady G q w) := by
  dsimp [hedgeCounterexampleIn?]
  split
  · next h =>
    simp [h]
  · next h =>
    split
    · next hedge =>
        simp [h, hedge]
    · next hedge =>
        split
        · next hbow =>
            simp [h, hedge, hbow]
        · next hbow =>
            simp [h, hedge, hbow]

/--
ID-failure extraction followed by the Boolean edge-shared, seed-plus-sink,
and bow tests.  `none` means either the finite hedge search missed or the
extracted witness satisfies none of those positive mix leaves.  The first
leaf permits non-sink extra action vertices when every outgoing action edge
shares its pair-root switch and only the stored seed parents queried outcomes.
-/
def hedgeCounterexample? (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    Option (CounterexampleIn (GraphModelClass.positive G) q) :=
  match hedgeWitness? G q fail with
  | none => none
  | some w => hedgeCounterexampleIn? G rich q w

theorem hedgeCounterexample?_isSome_of_witness
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (fail : IdentificationFail S)
    (w : HedgeWitness G q)
    (hfound : hedgeWitness? G q fail = some w)
    (hready : hedgeWitnessSharedSwitchReady G q w = true) :
    hedgeCounterexample? G rich q fail =
      some (hedgeSharedSwitchCounterexampleIn_of_ready G rich q w hready) := by
  simp [hedgeCounterexample?, hfound, hedgeCounterexampleIn?, hready]

end Causality
end Thesis
