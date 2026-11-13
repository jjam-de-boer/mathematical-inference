import Thesis.CausalTransport.SoundnessRegions

namespace Thesis
namespace Causality

open Probability

/-!
# Latent partition witnesses and the three sound causal rules

This layer combines the imported kernel-region lemmas with independent-product
identities. It retains conditional cross-product witnesses, the rule-specific
latent-component arguments, and the supported ratio-algebra conversion.

Private Boolean rearrangement lemmas support the partition calculations.
`Soundness` assembles these rule-specific arguments into the published
interface and discharges their partition obligations from projected-graph
compatibility. This layer retains the explicit support conditions needed
when converting product identities into conditional probability statements.
-/

namespace Kernel

/-- Normalization removes the explicit `P(topEvent)` factor from the
denominator-free product identity. -/
theorem productRecord_inter_equiv_mul
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedEvent unselectedEvent : model.latent.Assignment -> Bool)
    (selectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedEvent)
    (unselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedEvent) :
    QProb.Equiv
      ((productRecord model).probVal
        (Probability.inter selectedEvent unselectedEvent))
      (QProb.mul
        ((productRecord model).probVal selectedEvent)
        ((productRecord model).probVal unselectedEvent)) := by
  let intersection := (productRecord model).probVal
    (Probability.inter selectedEvent unselectedEvent)
  let whole := (productRecord model).probVal Probability.topEvent
  have independent := productRecord_complementary_independence model selected
    selectedEvent unselectedEvent selectedDepends unselectedDepends
  have normalized : QProb.Equiv whole QProb.one :=
    (productRecord model).normalization
  exact QProb.equiv_trans (QProb.equiv_symm (QProb.mul_one intersection))
    (QProb.equiv_trans
      (QProb.mul_congr (QProb.equiv_refl intersection)
        (QProb.equiv_symm normalized))
      (by simpa [intersection, whole] using QProb.equiv_symm independent))

/-- Conditional independence in cross-product form.  A common conditioning
event may have one component on each side of the latent-root partition. -/
theorem productRecord_conditional_independence_cross
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedOutcome selectedCondition unselectedOutcome
      unselectedCondition : model.latent.Assignment -> Bool)
    (selectedOutcomeDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedOutcome)
    (selectedConditionDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedCondition)
    (unselectedOutcomeDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedOutcome)
    (unselectedConditionDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedCondition) :
    QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter
            (Probability.inter selectedOutcome selectedCondition)
            unselectedCondition))
        ((productRecord model).probVal
          (Probability.inter selectedCondition
            (Probability.inter unselectedOutcome unselectedCondition))))
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter
            (Probability.inter selectedOutcome selectedCondition)
            (Probability.inter unselectedOutcome unselectedCondition)))
        ((productRecord model).probVal
          (Probability.inter selectedCondition unselectedCondition))) := by
  let selectedJoint := Probability.inter selectedOutcome selectedCondition
  let unselectedJoint := Probability.inter unselectedOutcome unselectedCondition
  have selectedJointDepends := CanonicalFactorization.DependsOnSelected.inter
    model.latent.count model.latent.Value selected
      selectedOutcome selectedCondition selectedOutcomeDepends
      selectedConditionDepends
  have unselectedJointDepends :=
    CanonicalFactorization.DependsOnUnselected.inter model.latent.count
      model.latent.Value selected unselectedOutcome unselectedCondition
      unselectedOutcomeDepends unselectedConditionDepends
  have leftFactor := productRecord_inter_equiv_mul model selected
    selectedJoint unselectedCondition selectedJointDepends
    unselectedConditionDepends
  have rightFactor := productRecord_inter_equiv_mul model selected
    selectedCondition unselectedJoint selectedConditionDepends
    unselectedJointDepends
  have jointFactor := productRecord_inter_equiv_mul model selected
    selectedJoint unselectedJoint selectedJointDepends unselectedJointDepends
  have conditionFactor := productRecord_inter_equiv_mul model selected
    selectedCondition unselectedCondition selectedConditionDepends
    unselectedConditionDepends
  exact QProb.equiv_trans (QProb.mul_congr leftFactor rightFactor)
    (QProb.equiv_trans (by
      simp only [QProb.Equiv, QProb.mul]
      ac_rfl)
      (QProb.equiv_symm (QProb.mul_congr jointFactor conditionFactor)))

/-- Every kernel distribution is a pushforward of the canonical independent
latent product, including the action-free branch. -/
theorem distribution_probVal_productRecord
    (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    QProb.Equiv ((kernel.distribution model reference).probVal event)
      (productMass model kernel reference event) := by
  unfold productMass productRecord
  cases actionValue : kernel.hasAction with
  | true =>
      simpa [Kernel.distribution, actionValue,
        FiniteLatentSCM.interventionalValue] using
        model.interventionalValue_productRecord
          (kernel.intervention reference) event
  | false =>
      have noAction : forall node, kernel.action node = false :=
        (finAny_eq_false_iff kernel.action).mp (by
          simpa [Kernel.hasAction] using actionValue)
      have noIntervention : kernel.intervention reference =
          FiniteLatentSCM.noIntervention S := by
        funext node
        simp [Kernel.intervention, FiniteLatentSCM.noIntervention,
          noAction node]
      rw [noIntervention]
      simpa [Kernel.distribution, actionValue,
        FiniteLatentSCM.observationalValue,
        FiniteLatentSCM.evalUnder_noIntervention, productMass,
        productRecord] using
        model.observationalValue_productRecord event

/-- The denominator-free cross-product obligation for two conditional kernels. -/
structure CrossProductEquivalentAt (model : FiniteLatentSCM S)
    (left right : Kernel S) (assignment : S.Assignment) : Prop where
  cross : QProb.Equiv
    (QProb.mul
      ((left.distribution model assignment).probVal
        (left.numeratorEvent assignment))
      ((right.distribution model assignment).probVal
        (right.conditionEvent assignment)))
    (QProb.mul
      ((right.distribution model assignment).probVal
        (right.numeratorEvent assignment))
      ((left.distribution model assignment).probVal
        (left.conditionEvent assignment)))

/-- The same cross-product obligation after replacing the supplied latent
prior by its canonical independent product record. -/
structure ProductCrossProductEquivalentAt (model : FiniteLatentSCM S)
    (left right : Kernel S) (assignment : S.Assignment) : Prop where
  cross : QProb.Equiv
    (QProb.mul
      (productMass model left assignment (left.numeratorEvent assignment))
      (productMass model right assignment (right.conditionEvent assignment)))
    (QProb.mul
      (productMass model right assignment (right.numeratorEvent assignment))
      (productMass model left assignment (left.conditionEvent assignment)))

theorem ProductCrossProductEquivalentAt.symm
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : ProductCrossProductEquivalentAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model right left assignment :=
  ⟨QProb.equiv_symm equivalent.cross⟩

/-- A concrete latent partition witnessing the conditional-independence
identity required by a pair of kernels.  The four equalities isolate the
intervention/structural-equation work; the four dependence fields isolate the
graph-separation work. -/
structure ProductConditionalIndependenceWitnessAt
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  selectedOutcome : model.latent.Assignment -> Bool
  selectedCondition : model.latent.Assignment -> Bool
  unselectedOutcome : model.latent.Assignment -> Bool
  unselectedCondition : model.latent.Assignment -> Bool
  selectedOutcomeDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedOutcome
  selectedConditionDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedCondition
  unselectedOutcomeDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedOutcome
  unselectedConditionDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedCondition
  leftNumerator :
    productPreimage model left assignment (left.numeratorEvent assignment) =
      Probability.inter
        (Probability.inter selectedOutcome selectedCondition)
        (Probability.inter unselectedOutcome unselectedCondition)
  rightCondition :
    productPreimage model right assignment (right.conditionEvent assignment) =
      Probability.inter selectedCondition unselectedCondition
  rightNumerator :
    productPreimage model right assignment (right.numeratorEvent assignment) =
      Probability.inter selectedCondition
        (Probability.inter unselectedOutcome unselectedCondition)
  leftCondition :
    productPreimage model left assignment (left.conditionEvent assignment) =
      Probability.inter
        (Probability.inter selectedOutcome selectedCondition)
        unselectedCondition

/-- Build the latent conditional-independence witness for rule 1 from two
backward-closed, latent-separated regions and a partition of the common
conditioning nodes. -/
def rule1PartitionWitness (model : FiniteLatentSCM S)
    (x y z w wSelected wUnselected leftRelevant rightRelevant : NodeSet S)
    (assignment : S.Assignment)
    (wSplit : w = NodeSet.union wSelected wUnselected)
    (leftClosed : model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment) leftRelevant)
    (rightClosed : model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment) rightRelevant)
    (zContained : NodeSet.Subset z leftRelevant)
    (wSelectedContained : NodeSet.Subset wSelected leftRelevant)
    (yContained : NodeSet.Subset y rightRelevant)
    (wUnselectedContained : NodeSet.Subset wUnselected rightRelevant)
    (separated : model.LatentSeparatedUnder
      ((rule1Right x y z w).intervention assignment)
      leftRelevant rightRelevant) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let intervention := (rule1Right x y z w).intervention assignment
  let evaluated := fun roots : model.latent.Assignment =>
    model.evalUnder intervention roots
  let cylinder := fun nodes : NodeSet S => fun roots : model.latent.Assignment =>
    Kernel.agreesOn nodes assignment (evaluated roots)
  refine
    { selected := model.latentRelevantUnder intervention leftRelevant
      selectedOutcome := cylinder z
      selectedCondition := cylinder wSelected
      unselectedOutcome := cylinder y
      unselectedCondition := cylinder wUnselected
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnSelected model intervention leftRelevant z
        assignment leftClosed zContained
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnSelected model intervention leftRelevant
        wSelected assignment leftClosed wSelectedContained
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnUnselected model intervention leftRelevant
        rightRelevant y assignment rightClosed yContained separated
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnUnselected model intervention leftRelevant
        rightRelevant wUnselected assignment rightClosed
        wUnselectedContained separated
  · funext roots
    simp only [productPreimage, rule1Left, Kernel.numeratorEvent,
      cylinder, evaluated]
    change
      (Kernel.agreesOn y assignment (model.evalUnder intervention roots) &&
        Kernel.agreesOn (NodeSet.union z w) assignment
          (model.evalUnder intervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union z,
      Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule1Right, Kernel.conditionEvent,
      cylinder, evaluated]
    change Kernel.agreesOn w assignment
      (model.evalUnder intervention roots) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
  · funext roots
    simp only [productPreimage, rule1Right, Kernel.numeratorEvent,
      cylinder, evaluated]
    change
      (Kernel.agreesOn y assignment (model.evalUnder intervention roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder intervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule1Left, Kernel.conditionEvent,
      cylinder, evaluated]
    change Kernel.agreesOn (NodeSet.union z w) assignment
      (model.evalUnder intervention roots) = _
    rw [wSplit, Kernel.agreesOn_union z,
      Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl

/--
Rule 1 when `W` shares no latent with the open `Z` core: `Z` is selected,
`Y` and `W` are unselected, and the common condition is the whole of `W`.
-/
def rule1PartitionWitness_of_w_avoids_z_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (havoid : rule1WMeetsUnionAncestral model G x w assignment z = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  refine
    { selected := model.latentRelevantUnder Iu
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
      selectedOutcome := zEv
      selectedCondition := Probability.topEvent
      unselectedOutcome := yEv
      unselectedCondition := wEv
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [Iu, zEv] using
      agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment
  · exact CanonicalFactorization.DependsOnSelected.const _ _ _ true
  · simpa [Iu, yEv] using
      agreesOn_rule1Y_dependsOnUnselected_union model G projected x y z w
        assignment separated
  · simpa [wEv] using
      agreesOn_rule1W_dependsOnUnselected_of_avoids_z model G x y z w
        assignment havoid
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, zEv, yEv, wEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew]
    simp only [Bool.and_true]
    ac_rfl
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, wEv]
    rw [show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.true_and]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, yEv, wEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.true_and]
    rw [hR, Bool.and_comm]
    exact hy.trans (Bool.and_comm _ _)
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, zEv, wEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union]
    simp only [Bool.and_true]
    rw [hR, Bool.and_comm]
    exact hz.trans (Bool.and_comm _ _)

/--
Rule 1 when `W` shares no latent with the open `Y` core: selected
coordinates are everything except that core, `W` sits with `Z` on the
selected side, and `Y` is unselected.
-/
def rule1PartitionWitness_of_w_avoids_y_core
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (havoid : rule1WMeetsUnionAncestral model G x w assignment y = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let zCore := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z
  let yCore := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have hsep :=
    FiniteLatentSCM.rule1Ancestral_latentSeparated_union model G projected
      x y z w assignment separated
  have zCore_subset_not_y :
      forall root, model.latentRelevantUnder Iu zCore root = true ->
        (!model.latentRelevantUnder Iu yCore root) = true := by
    intro root hz
    have hy := hsep root (by simpa [Iu, zCore] using hz)
    cases hy' : model.latentRelevantUnder Iu yCore root with
    | false =>
        rfl
    | true =>
        simp [Iu, yCore, hy'] at hy
  refine
    { selected := fun root => !model.latentRelevantUnder Iu yCore root
      selectedOutcome := zEv
      selectedCondition := wEv
      unselectedOutcome := yEv
      unselectedCondition := Probability.topEvent
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value zEv zCore_subset_not_y
      (by simpa [Iu, zEv, zCore] using
        agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment)
  · simpa [wEv, Iu, yCore] using
      agreesOn_rule1W_dependsOnSelected_of_avoids_y model G x y z w
        assignment havoid
  · simpa [Iu, yEv, yCore] using
      CanonicalFactorization.DependsOnUnselected.of_selected_compl
        model.latent.count model.latent.Value
        (model.latentRelevantUnder Iu yCore) yEv
        (by simpa [Iu, yEv, yCore] using
          agreesOn_rule1Y_dependsOnSelected_union model G x y z w assignment)
  · exact CanonicalFactorization.DependsOnUnselected.const _ _ _ true
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, zEv, yEv, wEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew]
    simp only [Bool.and_true]
    ac_rfl
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, wEv]
    rw [show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.and_true]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      Probability.topEvent, yEv, wEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl]
    simp only [Bool.and_true]
    rw [hR]
    exact Bool.and_comm _ _ ▸ hy
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      Probability.topEvent, zEv, wEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union]
    simp only [Bool.and_true]
    rw [hR, Bool.and_comm]
    exact hz.trans (Bool.and_comm _ _)

/--
Rule 1 from the two one-sided core-avoidance witnesses, once `W` is known
not to meet both open cores.
-/
def rule1PartitionWitness_of_not_both_meet
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hnot :
      (rule1WMeetsUnionAncestral model G x w assignment z &&
        rule1WMeetsUnionAncestral model G x w assignment y) = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  cases hZ : rule1WMeetsUnionAncestral model G x w assignment z with
  | false =>
      exact rule1PartitionWitness_of_w_avoids_z_core model G projected
        x y z w assignment separated hZ
  | true =>
      cases hY : rule1WMeetsUnionAncestral model G x w assignment y with
      | false =>
          exact rule1PartitionWitness_of_w_avoids_y_core model G projected
            x y z w assignment separated hY
      | true =>
          simp [hZ, hY] at hnot

/--
Rule 1 with empty given-set `W`.  The both-meet obligation is vacuous, so
path d-separation and the projected graph already supply the partition
witness.  This is the empty-conditioner special case of
`PathDoRulePartitionWitnesses.rule1`.
-/
def rule1PartitionWitness_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hw : NodeSet.isEmpty w = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment :=
  rule1PartitionWitness_of_not_both_meet model G projected
    x y z w assignment separated (by
      have hZ :=
        rule1WMeetsUnionAncestral_of_empty_w model G x w assignment z hw
      simp [hZ])

/-- Boolean `&&` is associative and commutative; these rearrangements
avoid relying on the AC tactic at four-factor cylinders. -/
private theorem bool_and_four_pairs (a b c d : Bool) :
    ((a && b) && (c && d)) = ((d && a) && (c && b)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem bool_and_mid_swap (a b c : Bool) :
    ((a && b) && c) = (a && (c && b)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem bool_and_rot_left (a b c : Bool) :
    ((a && b) && c) = ((c && a) && b) := by
  cases a <;> cases b <;> cases c <;> rfl

/--
Rule 1 when `W` meets both open cores, but the two-block split of `W`
still factorizes. Selected coordinates are the complement of the `Y`
block: the open `Y` core together with ancestral latents of the
`Y`-meeting slice. The remaining obligations are that the complementary
slice avoids that block, and that the `Y`-meeting slice avoids the
open `Z` core.
-/
def rule1PartitionWitness_of_w_split
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hSelAvoids :
      rule1WSplitSelectedMeetsYCore model G x y z w assignment = false)
    (hOverlap :
      rule1WSplitAncestralLatentsOverlap model G x y z w assignment = false)
    (hUnselAvoidsZ :
      rule1WSplitUnselectedMeetsZCore model G x y z w assignment = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let wSel := rule1WSplitSelected model G x w assignment y
  let wUnsel := rule1WSplitUnselected model G x w assignment y
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wSelEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wSel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  let wUnselEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wUnsel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have wEq : forall roots,
      Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots) =
        (wSelEv roots && wUnselEv roots) := by
    intro roots
    have hnodes :=
      congrArg
        (fun nodes =>
          Kernel.agreesOn nodes assignment
            (model.evalUnder
              ((rule1Right x y z w).intervention assignment) roots))
        (rule1WSplit_union model G x w assignment y)
    simpa [wSelEv, wUnselEv, wSel, wUnsel, Kernel.agreesOn_union] using
      hnodes.symm
  refine
    { selected := fun root =>
        !(rule1WSplitYBlockLatents model G x y z w assignment root)
      selectedOutcome := zEv
      selectedCondition := wSelEv
      unselectedOutcome := yEv
      unselectedCondition := wUnselEv
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [zEv, Iu] using
      (agreesOn_rule1Z_dependsOnNotYBlock model G projected x y z w
        assignment separated hUnselAvoidsZ)
  · simpa [wSelEv, wSel] using
      (agreesOn_rule1WSplitSelected_dependsOnNotYBlock model G x y z w
        assignment hSelAvoids hOverlap)
  · simpa [yEv, Iu] using
      agreesOn_rule1Y_dependsOnYBlock model G x y z w assignment
  · simpa [wUnselEv, wUnsel] using
      agreesOn_rule1WSplitUnselected_dependsOnYBlock model G x y z w
        assignment
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      zEv, yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew, wEq roots]
    exact bool_and_four_pairs (wSelEv roots) (wUnselEv roots)
      (yEv roots) (zEv roots)
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      wSelEv, wUnselEv]
    rw [show (rule1Right x y z w).condition = w from rfl, wEq roots]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl, hR,
      Bool.and_comm, hy, ← hR, wEq roots]
    exact bool_and_mid_swap (wSelEv roots) (wUnselEv roots) (yEv roots)
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      zEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hR, Bool.and_comm, hz, ← hR, wEq roots]
    exact bool_and_rot_left (wSelEv roots) (wUnselEv roots) (zEv roots)

/-- The closed selected slice depends only on the complement of the closed
`Y` block. -/
theorem agreesOn_rule1WSplitClosedSelected_dependsOnNotYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hY :
      rule1WSplitClosedSelectedMeetsYCore model G x y z w assignment =
        false)
    (hOverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
        false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitSelectedClosed model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hallY :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelectedClosed model G x w assignment y))
          root)).mp
      (by simpa [rule1WSplitClosedSelectedMeetsYCore] using hY)
  have hallO :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitSelectedClosed model G x w assignment y)) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselectedClosed model G x w assignment y))
          root)).mp
      (by simpa [rule1WSplitClosedAncestralLatentsOverlap] using hOverlap)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitSelectedClosed model G x w assignment y))
            root = true ->
          (!(rule1WSplitClosedYBlockLatents model G x y z w assignment
              root)) = true := by
    intro root hr
    have hYroot := hallY root
    have hOroot := hallO root
    cases hy :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root with
    | true =>
        simp [hy, hr] at hYroot
    | false =>
        cases hu :
            model.latentRelevantUnder
              ((rule1Right x y z w).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G x
                (rule1WSplitUnselectedClosed model G x w assignment y))
              root with
        | true =>
            simp [hr, hu] at hOroot
        | false =>
            simp [rule1WSplitClosedYBlockLatents, hy, hu]
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitSelectedClosed model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    hsub
    (agreesOn_rule1WSplitClosedSelected_dependsOnAncestral model G x y z w
      assignment)

/-- Under `do(X ∪ W)`, `Z` depends only on the complement of the closed
`Y` block once that block shares no latent with the open `Z` core. -/
theorem agreesOn_rule1Z_dependsOnNotClosedYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hUnselZ :
      rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment =
        false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn z assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)) := by
  have hsep :=
    FiniteLatentSCM.rule1Ancestral_latentSeparated_union model G projected
      x y z w assignment separated
  have hallZ :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root &&
        model.latentRelevantUnder
          ((rule1Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselectedClosed model G x w assignment y))
          root)).mp
      (by simpa [rule1WSplitClosedUnselectedMeetsZCore] using hUnselZ)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
            root = true ->
          (!(rule1WSplitClosedYBlockLatents model G x y z w assignment
              root)) = true := by
    intro root hz
    have hy := hsep root hz
    have hZroot := hallZ root
    cases hy' :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root with
    | true =>
        simp [hy'] at hy
    | false =>
        cases hu :
            model.latentRelevantUnder
              ((rule1Right x y z w).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G x
                (rule1WSplitUnselectedClosed model G x w assignment y))
              root with
        | true =>
            simp [hz, hu] at hZroot
        | false =>
            simp [rule1WSplitClosedYBlockLatents, hy', hu]
  exact CanonicalFactorization.DependsOnSelected.subset model.latent.count
    model.latent.Value
    (fun roots =>
      Kernel.agreesOn z assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots))
    hsub
    (agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment)

/-- `Y` ignores the complement of the closed `Y` block. -/
theorem agreesOn_rule1Y_dependsOnClosedYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)) := by
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
            root = true ->
          rule1WSplitClosedYBlockLatents model G x y z w assignment root =
            true := by
    intro root hr
    simp [rule1WSplitClosedYBlockLatents, hr]
  exact CanonicalFactorization.DependsOnUnselected.of_selected_compl
    model.latent.count model.latent.Value
    (rule1WSplitClosedYBlockLatents model G x y z w assignment)
    (fun roots =>
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots))
    (CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots))
      hsub
      (agreesOn_rule1Y_dependsOnSelected_union model G x y z w assignment))

/-- The closed `Y` block of `W` ignores the complement of that block. -/
theorem agreesOn_rule1WSplitClosedUnselected_dependsOnYBlock
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root))
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselectedClosed model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots)) := by
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((rule1Right x y z w).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G x
              (rule1WSplitUnselectedClosed model G x w assignment y))
            root = true ->
          rule1WSplitClosedYBlockLatents model G x y z w assignment root =
            true := by
    intro root hr
    simp [rule1WSplitClosedYBlockLatents, hr]
  exact CanonicalFactorization.DependsOnUnselected.of_selected_compl
    model.latent.count model.latent.Value
    (rule1WSplitClosedYBlockLatents model G x y z w assignment)
    (fun roots =>
      Kernel.agreesOn
        (rule1WSplitUnselectedClosed model G x w assignment y) assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots))
    (CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn
          (rule1WSplitUnselectedClosed model G x w assignment y) assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots))
      hsub
      (agreesOn_rule1WSplitClosedUnselected_dependsOnAncestral model G x y
        z w assignment))

/--
Rule 1 when `W` meets both open cores, using the descendant-closed
`Y` block. Directed `W_Y → W'` and extra `do(X)`-free `Y`-core ancestors
outside `W` are absorbed as `Y`-side seeds, so the complementary slice
avoids the closed `Y` block by construction. The remaining obligations
are that the two slices share no ancestral latent, and that the closed
`Y` block avoids the open `Z` core.
-/
def rule1PartitionWitness_of_w_split_closed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hOverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
        false)
    (hUnselAvoidsZ :
      rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment =
        false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  have hSelAvoids :
      rule1WSplitClosedSelectedMeetsYCore model G x y z w assignment =
        false :=
    rule1WSplitClosedSelectedMeetsYCore_eq_false model G x y z w assignment
  let Iu :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w) NodeSet.empty).intervention
      assignment
  let wSel := rule1WSplitSelectedClosed model G x w assignment y
  let wUnsel := rule1WSplitUnselectedClosed model G x w assignment y
  let zEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder Iu roots)
  let yEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder Iu roots)
  let wSelEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wSel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  let wUnselEv : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn wUnsel assignment
      (model.evalUnder ((rule1Right x y z w).intervention assignment) roots)
  have hL :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext i
    simp [rule1Left, rule1Right, Kernel.intervention]
  have hR :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext i
    simp [rule1Right, Kernel.intervention]
  have wEq : forall roots,
      Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule1Right x y z w).intervention assignment) roots) =
        (wSelEv roots && wUnselEv roots) := by
    intro roots
    have hnodes :=
      congrArg
        (fun nodes =>
          Kernel.agreesOn nodes assignment
            (model.evalUnder
              ((rule1Right x y z w).intervention assignment) roots))
        (rule1WSplitClosed_union model G x w assignment y)
    simpa [wSelEv, wUnselEv, wSel, wUnsel, Kernel.agreesOn_union] using
      hnodes.symm
  refine
    { selected := fun root =>
        !(rule1WSplitClosedYBlockLatents model G x y z w assignment root)
      selectedOutcome := zEv
      selectedCondition := wSelEv
      unselectedOutcome := yEv
      unselectedCondition := wUnselEv
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [zEv, Iu] using
      (agreesOn_rule1Z_dependsOnNotClosedYBlock model G projected x y z w
        assignment separated hUnselAvoidsZ)
  · simpa [wSelEv, wSel] using
      (agreesOn_rule1WSplitClosedSelected_dependsOnNotYBlock model G x y z w
        assignment hSelAvoids hOverlap)
  · simpa [yEv, Iu] using
      agreesOn_rule1Y_dependsOnClosedYBlock model G x y z w assignment
  · simpa [wUnselEv, wUnsel] using
      agreesOn_rule1WSplitClosedUnselected_dependsOnYBlock model G x y z w
        assignment
  · funext roots
    have hrew :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      zEv, yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hrew, wEq roots]
    exact bool_and_four_pairs (wSelEv roots) (wUnselEv roots)
      (yEv roots) (zEv roots)
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      wSelEv, wUnselEv]
    rw [show (rule1Right x y z w).condition = w from rfl, wEq roots]
  · funext roots
    have hy :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      yEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl, hR,
      Bool.and_comm, hy, ← hR, wEq roots]
    exact bool_and_mid_swap (wSelEv roots) (wUnselEv roots) (yEv roots)
  · funext roots
    have hz :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      zEv, wSelEv, wUnselEv, Iu]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      hL, Kernel.agreesOn_union, hR, Bool.and_comm, hz, ← hR, wEq roots]
    exact bool_and_rot_left (wSelEv roots) (wUnselEv roots) (zEv roots)

/--
Rule 1 from path d-separation.  If `W` misses at least one open core, the
one-sided witnesses suffice.  If it meets both, the descendant-closed
split still factorizes once the two slices share no ancestral latent and
the closed `Y` block misses the open `Z` core.
-/
def rule1PartitionWitness_of_path
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hOverlap :
      rule1WSplitClosedAncestralLatentsOverlap model G x y z w assignment =
        false)
    (hUnselAvoidsZ :
      rule1WSplitClosedUnselectedMeetsZCore model G x y z w assignment =
        false) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  cases hboth :
      (rule1WMeetsUnionAncestral model G x w assignment z &&
        rule1WMeetsUnionAncestral model G x w assignment y) with
  | false =>
      exact rule1PartitionWitness_of_not_both_meet model G projected
        x y z w assignment separated hboth
  | true =>
      exact rule1PartitionWitness_of_w_split_closed model G projected
        x y z w assignment separated hOverlap hUnselAvoidsZ

/--
Rule 1 from path d-separation, with the remaining both-meet obligations
stated as graph-theoretic conditions on the closed split rather than as
raw Bools.
-/
def rule1PartitionWitness_of_closed_split
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (hSame : forall child,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y) child =
        true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselectedClosed model G x w assignment y) child =
          true ->
          (rule1WSplitUnselectedClosed model G x w assignment y child ||
            rule1WYSideSeed model G x w assignment y child) = true)
    (hDistinct : forall childSel childUnsel,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitSelectedClosed model G x w assignment y) childSel =
        true ->
        FiniteLatentSCM.ancestralInBar G x
            (rule1WSplitUnselectedClosed model G x w assignment y)
            childUnsel = true ->
          childSel ≠ childUnsel ->
            (rule1WVertexMeetsCore model G x w assignment z childSel &&
              rule1WVertexMeetsCore model G x w assignment y childUnsel) =
              true)
    (hSeed : forall child,
      FiniteLatentSCM.ancestralInBar G x
          (rule1WSplitUnselectedClosed model G x w assignment y) child =
        true ->
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment) child = none ->
          finAny model.latent.count (fun root =>
              model.latentRelevantUnder
                  ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                    NodeSet.empty).intervention assignment)
                  (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
                  root &&
                model.latent.incident root child) = true ->
            rule1WYSideSeed model G x w assignment y child = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment :=
  rule1PartitionWitness_of_path model G projected x y z w assignment
    separated
    (rule1WSplitClosedAncestralLatentsOverlap_eq_false_of model G projected
      x y z w assignment separated hSame hDistinct)
    (rule1WSplitClosedUnselectedMeetsZCore_eq_false_of model G projected
      x y z w assignment separated hSeed)

/-!
### Rule 1 through the `Y`-connected conditioning component

The older descendant-closed split above exposes two Boolean non-overlap
premises.  Those premises are useful sufficient conditions, but they are not
the general graph theorem: a `W` component irrelevant to `Z` may share a
latent with the `Y` block without opening a `Y`--`Z` path.  The construction
below instead closes the selected latent coordinates through every local
topological `W` factor, exactly where conditioning can couple them.  Path
separation is then used only for its necessary conclusion that no `Z` root
belongs to the component generated by `Y`.
-/

/-- One latent root can affect the local equality constraint for a
conditioned `W` vertex under `do(X)`. -/
def rule1WConditionRootRelevant (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S)
    (assignment : S.Assignment) (child : Fin S.count)
    (root : Fin model.latent.count) : Bool :=
  w child &&
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (localConditionAction x w child)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (localConditionAction x w child)
        (NodeSet.singleton child)) root

/-- Two latent roots are adjacent when the same local rule-1 conditioning
factor can observe both of them. -/
def rule1WConditionRootAdjacent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S)
    (assignment : S.Assignment)
    (left right : Fin model.latent.count) : Bool :=
  finAny S.count (fun child =>
    rule1WConditionRootRelevant model G x w assignment child left &&
      rule1WConditionRootRelevant model G x w assignment child right)

/-- The finite latent component generated by roots needed for `Y` under the
fully conditioned intervention `do(X ∪ W)`. -/
def rule1YConditionLatentComponent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y w : NodeSet S)
    (assignment : S.Assignment) (root : Fin model.latent.count) : Bool :=
  finAny model.latent.count (fun seed =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) seed &&
      FiniteReachability.within finBeq
        (List.ofFn (fun latent : Fin model.latent.count => latent))
        (rule1WConditionRootAdjacent model G x w assignment)
        (List.ofFn (fun latent : Fin model.latent.count => latent)).length
        seed root)

/-- A `W` factor is in the common `Y` block when one of its relevant roots
lies in the generated component. -/
def rule1WConditionCommon (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y w : NodeSet S)
    (assignment : S.Assignment) : NodeSet S :=
  fun child =>
    finAny model.latent.count (fun root =>
      rule1WConditionRootRelevant model G x w assignment child root &&
        rule1YConditionLatentComponent model G x y w assignment root)

/-- Every remaining `W` factor belongs to the complementary residual block. -/
def rule1WConditionResidual (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y w : NodeSet S)
    (assignment : S.Assignment) : NodeSet S :=
  NodeSet.diff w (rule1WConditionCommon model G x y w assignment)

/-- An observed route witnessing relevance of one concrete root to a local
rule-1 conditioning factor.  The route is embedded in `G_{̅X}`; every
proper route vertex is open given `X ∪ W`, while the terminal factor vertex
may itself be conditioned. -/
def Rule1LocalConditionRootWalk (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x w : NodeSet S)
    (child : Fin S.count) (root : Fin model.latent.count) : Prop :=
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      (GraphMutilation.bar x).removeIncoming source = false /\
        Exists fun length : Nat =>
          Exists fun walk : FiniteReachability.ExactWalk
            (G.observedDirectedEdge (GraphMutilation.bar x))
            length source child =>
            forall node, node ∈ walk.nodes -> node ≠ child ->
              ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
                false

/-- Unpack a rule-1 factor-relevance Boolean into its route in
`G_{̅X}`.  The original local route cuts `X` and the earlier `W` prefix;
incoming-cut monotonicity embeds it in `G_{̅X}`, while topological order
shows that every proper route vertex is outside the full conditioner. -/
def rule1LocalConditionRootWalk_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (relevant : rule1WConditionRootRelevant model G x w assignment
      child root = true) :
    Rule1LocalConditionRootWalk model G x w child root := by
  have parts := Bool.and_eq_true_iff.mp relevant
  have childInW : w child = true := parts.1
  let action := localConditionAction x w child
  let intervention :=
    (Kernel.mk NodeSet.empty action NodeSet.empty).intervention assignment
  let ancestors := FiniteLatentSCM.ancestralInBar G action
    (NodeSet.singleton child)
  rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
      root).mp (by simpa [intervention, ancestors, action] using parts.2) with
    ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
  rcases (G.observedAncestorOf_eq_true_iff (GraphMutilation.bar action)
      (NodeSet.singleton child) source).mp (by
        simpa [FiniteLatentSCM.ancestralInBar, ancestors, action] using
          sourceAncestor) with ⟨target, targetSelected, bounded⟩
  have targetEq : target = child :=
    (NodeSet.singleton_eq_true_iff child target).mp targetSelected
  subst target
  rcases bounded with ⟨length, _bound, exactWalk⟩
  rcases exactWalk with ⟨walk⟩
  have xSubset : NodeSet.Subset x action := by
    intro node selected
    simp [action, localConditionAction, NodeSet.union, selected]
  let mapped := FiniteLatentSCM.remapBarWalk_of_incoming_subset G xSubset
    walk
  have sourceOutsideAction : action source = false := by
    simpa [intervention, Kernel.intervention] using sourceFree
  have sourceOutsideX : x source = false := by
    cases selected : x source with
    | false => rfl
    | true =>
        have inAction : action source = true := by
          simp [action, localConditionAction, NodeSet.union, selected]
        rw [inAction] at sourceOutsideAction
        contradiction
  have sourceIncoming : (GraphMutilation.bar x).removeIncoming source =
      false := by
    simpa [GraphMutilation.bar] using sourceOutsideX
  have mappedNodes : mapped.nodes = walk.nodes := by
    simpa [mapped] using
      FiniteLatentSCM.remapBarWalk_of_incoming_subset_nodes G xSubset walk
  refine ⟨source, sourceIncident, sourceIncoming, length, mapped, ?_⟩
  intro node member notTarget
  have originalMember : node ∈ walk.nodes := by
    rw [mappedNodes] at member
    exact member
  by_cases atSource : node = source
  · subst node
    exact localConditionWalk_source_open_of_free G x x w
      (fun _node selected => selected) assignment child walk notTarget
      (by simpa [intervention, action] using sourceFree)
  · exact localConditionWalk_internal_open G x x w
      (fun _node selected => selected) child walk originalMember atSource
      notTarget

/-- A free ancestral observed representative showing that one concrete root
lies in the `Y` component of rule 1's moral separator in `G_{̅X}`. -/
def Rule1RootMoralLeftWitness (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (root : Fin model.latent.count) : Prop :=
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      mutilation.removeIncoming source = false /\
        G.ancestorOf mutilation targets (.observed source) = true /\
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
            false /\
            G.moralLeftSide mutilation y z (NodeSet.union x w)
              (.observed source) = true

/-- Every root needed by the `Y` cylinder under `do(X ∪ W)` has a
representative on the left moral side in `G_{̅X}`.

Its directed ancestry route initially lives in `G_{̅(X ∪ W)}`.  Removing
fewer incoming edges embeds that route in `G_{̅X}`; all route vertices remain
open under the conditioner, and the endpoint lies in `Y`. -/
theorem rule1RootMoralLeftWitness_of_y_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true) :
    Rule1RootMoralLeftWitness model G x y z w root := by
  let intervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let ancestors := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
      root).mp (by simpa [intervention, ancestors] using relevant) with
    ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar (NodeSet.union x w)) y source (by
        simpa [FiniteLatentSCM.ancestralInBar, ancestors] using
          sourceAncestor) with
    ⟨yEnd, yEndInY, length, walk, walkSimple, _minimal⟩
  have xSubset : NodeSet.Subset x (NodeSet.union x w) :=
    NodeSet.subset_union_left x w
  let mapped := FiniteLatentSCM.remapBarWalk_of_incoming_subset G xSubset
    walk
  have mappedNodes : mapped.nodes = walk.nodes := by
    simpa [mapped] using
      FiniteLatentSCM.remapBarWalk_of_incoming_subset_nodes G xSubset walk
  have walkOpen : forall node, node ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    by_cases atSource : node = source
    · subst node
      exact (FiniteLatentSCM.intervention_none_iff_unblocked
        (NodeSet.union x w) assignment source).mp (by
          simpa [intervention] using sourceFree)
    · have incoming :=
        PathSpecification.directed_walk_mem_not_removeIncoming G
          (GraphMutilation.bar (NodeSet.union x w)) walk member atSource
      simpa [GraphMutilation.bar, ObservedGraph.blockedBy] using incoming
  have mappedOpen : forall node, node ∈ mapped.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    rw [mappedNodes] at member
    exact walkOpen node member
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  have yEndTarget : targets yEnd = true := by
    simp [targets, NodeSet.union, yEndInY]
  have mappedAncestor : forall node, node ∈ mapped.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      mapped yEndTarget member
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have sourceToY := moralLeftSide_eq_of_open_observed_walk G mutilation
    y z (NodeSet.union x w) mapped mappedOpen (by
      simpa [targets] using mappedAncestor)
  have yOpen := FiniteLatentSCM.blockedBy_false_of_mem_y x y z w disjoint
    yEndInY
  have ySide := G.moralLeftSide_of_left mutilation y z
    (NodeSet.union x w) yEnd yEndInY (by
      simpa [ObservedGraph.blockedBy] using yOpen)
  have sourceOutsideX : x source = false := by
    have sourceOpen := mappedOpen source mapped.mem_source
    have outside : NodeSet.union x w source = false := by
      simpa [ObservedGraph.blockedBy] using sourceOpen
    exact (Bool.or_eq_false_iff.mp (by
      simpa [NodeSet.union] using outside)).1
  have sourceIncoming : mutilation.removeIncoming source = false := by
    simpa [mutilation, GraphMutilation.bar] using sourceOutsideX
  exact ⟨source, sourceIncident, sourceIncoming,
    mappedAncestor source mapped.mem_source,
    mappedOpen source mapped.mem_source, sourceToY.trans ySide⟩

/-- An open ancestral parent of a local rule-1 conditioning factor that lies
on the `Y` side of the canonical moral separator in `G_{̅X}`. -/
def Rule1FactorMoralLeftParent (G : ObservedGraph S)
    (x y z w : NodeSet S) (child : Fin S.count) : Prop :=
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  Exists fun parent : SeparationNode S =>
    G.expandedMutilatedEdge mutilation parent (.observed child) = true /\
      G.ancestorOf mutilation targets parent = true /\
        ObservedGraph.blockedBy (NodeSet.union x w) parent = false /\
          G.moralLeftSide mutilation y z (NodeSet.union x w) parent = true

/-- Moralization at a conditioned rule-1 factor transfers the stored left
label to every other open ancestral parent of the same child.  The equality
case is split by the explicit Boolean code of `SeparationNode`, keeping this
lemma free of classical decidability. -/
theorem Rule1FactorMoralLeftParent.marries
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (child : Fin S.count)
    (witness : Rule1FactorMoralLeftParent G x y z w child)
    (childConditioned : NodeSet.union x w child = true)
    (other : SeparationNode S)
    (otherEdge : G.expandedMutilatedEdge (GraphMutilation.bar x)
      other (.observed child) = true)
    (otherAncestor : G.ancestorOf (GraphMutilation.bar x)
      (NodeSet.union y (NodeSet.union z (NodeSet.union x w))) other = true)
    (otherOpen : ObservedGraph.blockedBy (NodeSet.union x w) other = false) :
    G.moralLeftSide (GraphMutilation.bar x) y z (NodeSet.union x w) other =
      true := by
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases witness with
    ⟨parent, parentEdge, parentAncestor, parentOpen, parentSide⟩
  have equalityCases : SeparationNode.beq parent other = true ∨
      SeparationNode.beq parent other = false := by
    cases value : SeparationNode.beq parent other with
    | false => exact Or.inr rfl
    | true => exact Or.inl rfl
  rcases equalityCases with sameValue | sameValue
  · have same := (SeparationNode.beq_eq_true_iff parent other).mp sameValue
    exact Eq.mp (congrArg (fun node =>
      G.moralLeftSide mutilation y z (NodeSet.union x w) node = true) same)
      parentSide
  · have different : parent ≠ other :=
      (SeparationNode.beq_eq_false_iff parent other).mp sameValue
    have conditionedPart : x child = true ∨ w child = true :=
      Bool.or_eq_true_iff.mp (by
        simpa [NodeSet.union] using childConditioned)
    have childTarget : targets child = true := by
      rcases conditionedPart with childInX | childInW
      · simp [targets, NodeSet.union, childInX]
      · simp [targets, NodeSet.union, childInW]
    have childAncestor : G.ancestorOf mutilation targets
        (.observed child) = true :=
      G.ancestorOf_target mutilation targets childTarget
    have collider : PathSpecification.IsCollider G mutilation parent
        (.observed child) other := ⟨parentEdge, otherEdge⟩
    have ancestralMoral := G.ancestralMoralEdge_of_collider mutilation
      targets parentAncestor childAncestor otherAncestor different collider
    have moral := G.moralOpenEdge_of_ancestral mutilation targets
      (NodeSet.union x w) parentOpen otherOpen ancestralMoral
    have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation y z
      (NodeSet.union x w) moral
    rw [parentSide] at sameSide
    exact sameSide.symm

/-- A rule-1 root represented on the `Y` moral side supplies a left-side
parent for every local `W` factor it affects.  Nontrivial relevance routes are
followed to their final observed parent; direct incidence is represented by
the projected latent-pair vertex joining the stored source to the factor. -/
theorem rule1FactorMoralLeftParent_of_root_witness
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (rootWitness : Rule1RootMoralLeftWitness model G x y z w root)
    (relevant : rule1WConditionRootRelevant model G x w assignment
      child root = true) :
    Rule1FactorMoralLeftParent G x y z w child := by
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases rootWitness with
    ⟨leftSource, leftIncident, leftIncoming, leftAncestor, leftOpen,
      leftSide⟩
  rcases rule1LocalConditionRootWalk_of_relevant model G x w assignment
      child root relevant with
    ⟨routeSource, routeIncident, routeIncoming, routeLength, route,
      routeProperOpen⟩
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp relevant).1
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  by_cases routeReflexive : routeSource = child
  · subst routeSource
    have leftDifferent : leftSource ≠ child := by
      intro same
      subst leftSource
      have childOpen : NodeSet.union x w child = false := by
        simpa [ObservedGraph.blockedBy] using leftOpen
      rw [childConditioned] at childOpen
      contradiction
    have bidirected := model.bidirected_of_shared_latent G projected root
      leftDifferent leftIncident routeIncident
    let latent : SeparationNode S := .latentPair leftSource child
    have leftIncoming' : mutilation.removeIncoming leftSource = false := by
      simpa [mutilation] using leftIncoming
    have childIncoming' : mutilation.removeIncoming child = false := by
      simpa [mutilation] using routeIncoming
    have edgeLeft : G.expandedMutilatedEdge mutilation latent
        (.observed leftSource) = true := by
      have self : finBeq leftSource leftSource = true :=
        (finBeq_eq_true_iff leftSource leftSource).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        leftIncoming', self]
    have edgeChild : G.expandedMutilatedEdge mutilation latent
        (.observed child) = true := by
      have self : finBeq child child = true :=
        (finBeq_eq_true_iff child child).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        childIncoming', self]
    have latentAncestor : G.ancestorOf mutilation targets latent = true :=
      G.ancestorOf_prepend mutilation targets edgeLeft leftAncestor
    have leftLatentMoral : G.MoralOpenEdge mutilation targets
        (NodeSet.union x w) (.observed leftSource) latent = true :=
      G.moralOpenEdge_of_ancestral mutilation targets (NodeSet.union x w)
        leftOpen (by dsimp [latent]; rfl)
        (G.ancestralMoralEdge_of_adjacent mutilation targets leftAncestor
          latentAncestor (Or.inr edgeLeft))
    have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation y z
      (NodeSet.union x w) leftLatentMoral
    have latentSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
        latent = true := by
      rw [leftSide] at sameSide
      exact sameSide.symm
    exact ⟨latent, edgeChild, latentAncestor, by dsimp [latent]; rfl,
      latentSide⟩
  · have routeOpen := routeProperOpen routeSource route.mem_source
      routeReflexive
    have routeObservedAncestor := G.observedAncestorOf_of_mem_walk
      mutilation targets route childTarget route.mem_source
    have routeAncestor := FiniteLatentSCM.ancestorOf_of_observedAncestorOf
      G mutilation targets routeSource routeObservedAncestor
    have routeSameSide :=
      FiniteLatentSCM.moralLeftSide_eq_of_shared_latent model G projected
        mutilation y z (NodeSet.union x w) root leftSource routeSource
        leftIncident routeIncident leftIncoming routeIncoming leftAncestor
        routeAncestor (by
          simpa [ObservedGraph.blockedBy] using leftOpen) (by
          simpa [ObservedGraph.blockedBy] using routeOpen)
    have routeSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
        (.observed routeSource) = true := by
      rw [leftSide] at routeSameSide
      exact routeSameSide.symm
    rcases exists_observedDirectedWalk_prefix_last G mutilation route
        routeReflexive with
      ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
    have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
        node ≠ child := by
      intro node member equal
      have parentDirected : S.directed parent child = true :=
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
      have parentEarlier := S.directed_earlier parentDirected
      have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
        prefixWalk member
      subst node
      exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
    have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
        ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
          false := by
      intro node member
      exact routeProperOpen node (prefixSubset node member)
        (prefixNotChild node member)
    have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
        G.ancestorOf mutilation targets (.observed node) = true := by
      intro node member
      have observed := G.observedAncestorOf_of_mem_walk mutilation targets
        route childTarget (prefixSubset node member)
      exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
        targets node observed
    have routeToParent := moralLeftSide_eq_of_open_observed_walk G
      mutilation y z (NodeSet.union x w) prefixWalk prefixOpen (by
        simpa [targets] using prefixAncestor)
    have parentSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
        (.observed parent) = true := by
      rw [routeSide] at routeToParent
      exact routeToParent.symm
    exact ⟨.observed parent, last,
      prefixAncestor parent prefixWalk.mem_target,
      prefixOpen parent prefixWalk.mem_target, parentSide⟩

/-- A nonincident root relevant to a rule-1 factor with a left-side parent
obtains an observed left representative from its nontrivial relevance route. -/
theorem rule1RootMoralLeftWitness_of_factor_parent_relevant_not_incident
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (factorParent : Rule1FactorMoralLeftParent G x y z w child)
    (relevant : rule1WConditionRootRelevant model G x w assignment
      child root = true)
    (notIncident : model.latent.incident root child = false) :
    Rule1RootMoralLeftWitness model G x y z w root := by
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases rule1LocalConditionRootWalk_of_relevant model G x w assignment
      child root relevant with
    ⟨source, sourceIncident, sourceIncoming, length, route,
      routeProperOpen⟩
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp relevant).1
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  have sourceDifferent : source ≠ child := by
    intro equal
    subst source
    rw [sourceIncident] at notIncident
    contradiction
  have sourceOpen := routeProperOpen source route.mem_source sourceDifferent
  have sourceObservedAncestor := G.observedAncestorOf_of_mem_walk
    mutilation targets route childTarget route.mem_source
  have sourceAncestor := FiniteLatentSCM.ancestorOf_of_observedAncestorOf
    G mutilation targets source sourceObservedAncestor
  rcases exists_observedDirectedWalk_prefix_last G mutilation route
      sourceDifferent with
    ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
  have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
      node ≠ child := by
    intro node member equal
    have parentDirected : S.directed parent child = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
    have parentEarlier := S.directed_earlier parentDirected
    have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
      prefixWalk member
    subst node
    exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
  have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) = false := by
    intro node member
    exact routeProperOpen node (prefixSubset node member)
      (prefixNotChild node member)
  have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      route childTarget (prefixSubset node member)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have parentSide := Rule1FactorMoralLeftParent.marries G x y z w child
    factorParent childConditioned (.observed parent) last
    (prefixAncestor parent prefixWalk.mem_target)
    (prefixOpen parent prefixWalk.mem_target)
  have sourceToParent := moralLeftSide_eq_of_open_observed_walk G
    mutilation y z (NodeSet.union x w) prefixWalk prefixOpen (by
      simpa [targets] using prefixAncestor)
  have sourceSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
      (.observed source) = true := by
    rw [parentSide] at sourceToParent
    exact sourceToParent
  exact ⟨source, sourceIncident, sourceIncoming, sourceAncestor,
    sourceOpen, sourceSide⟩

/-- Every `W` vertex survives the incoming cut of `G_{̅X}` by four-way
disjointness. -/
theorem rule1_w_not_removeIncoming
    (x y z w : NodeSet S) (disjoint : FourWayDisjoint x y z w)
    (child : Fin S.count) (childInW : w child = true) :
    (GraphMutilation.bar x).removeIncoming child = false := by
  have outsideX : x child = false := disjoint.xw.symm child childInW
  simpa [GraphMutilation.bar] using outsideX

/-- Transport a left-side factor parent across one concrete latent root.

The proof follows the same four incidence cases as the rule-3 component
transport, but in the simpler mutilation `G_{̅X}`.  A nonincident current
factor exposes an ordinary observed representative of the root.  When the
root is directly incident to the current factor, projection materializes the
shared root as a latent-pair parent joining that factor either to the open
source of the next relevance route or directly to the next factor.  The
stored left label crosses the conditioned collider by
`Rule1FactorMoralLeftParent.marries`.

This is the local induction step for arbitrary root-component walks.  It is
deliberately stated without a depth bound and extracts no witnesses from
`Prop` into executable data. -/
theorem rule1FactorMoralLeftParent_transfer
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (fromChild toChild : Fin S.count) (root : Fin model.latent.count)
    (fromParent : Rule1FactorMoralLeftParent G x y z w fromChild)
    (fromRelevant : rule1WConditionRootRelevant model G x w assignment
      fromChild root = true)
    (toRelevant : rule1WConditionRootRelevant model G x w assignment
      toChild root = true) :
    Rule1FactorMoralLeftParent G x y z w toChild := by
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  have fromChildInW : w fromChild = true :=
    (Bool.and_eq_true_iff.mp fromRelevant).1
  have toChildInW : w toChild = true :=
    (Bool.and_eq_true_iff.mp toRelevant).1
  have fromChildConditioned : NodeSet.union x w fromChild = true := by
    simp [NodeSet.union, fromChildInW]
  have fromChildTarget : targets fromChild = true := by
    simp [targets, NodeSet.union, fromChildInW]
  cases fromIncident : model.latent.incident root fromChild with
  | false =>
      have rootWitness :=
        rule1RootMoralLeftWitness_of_factor_parent_relevant_not_incident
          model G x y z w assignment fromChild root fromParent fromRelevant
          fromIncident
      exact rule1FactorMoralLeftParent_of_root_witness model G projected
        x y z w assignment toChild root rootWitness toRelevant
  | true =>
      cases toIncident : model.latent.incident root toChild with
      | false =>
          rcases rule1LocalConditionRootWalk_of_relevant model G x w
              assignment toChild root toRelevant with
            ⟨source, sourceIncident, sourceIncoming, length, route,
              routeProperOpen⟩
          have sourceDifferent : source ≠ toChild := by
            intro equal
            subst source
            rw [sourceIncident] at toIncident
            contradiction
          have sourceOpen := routeProperOpen source route.mem_source
            sourceDifferent
          have toChildTarget : targets toChild = true := by
            simp [targets, NodeSet.union, toChildInW]
          have sourceObservedAncestor := G.observedAncestorOf_of_mem_walk
            mutilation targets route toChildTarget route.mem_source
          have sourceAncestor :=
            FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
              targets source sourceObservedAncestor
          have sourceDifferentFromCurrent : source ≠ fromChild := by
            intro equal
            subst source
            have sourceOutside : NodeSet.union x w fromChild = false := by
              simpa [ObservedGraph.blockedBy] using sourceOpen
            rw [fromChildConditioned] at sourceOutside
            contradiction
          have bidirected := model.bidirected_of_shared_latent G projected
            root sourceDifferentFromCurrent.symm fromIncident sourceIncident
          let latent : SeparationNode S := .latentPair fromChild source
          have fromIncoming : mutilation.removeIncoming fromChild = false := by
            simpa [mutilation] using
              rule1_w_not_removeIncoming x y z w disjoint fromChild
                fromChildInW
          have sourceIncoming' : mutilation.removeIncoming source = false := by
            simpa [mutilation] using sourceIncoming
          have edgeFrom : G.expandedMutilatedEdge mutilation latent
              (.observed fromChild) = true := by
            have self : finBeq fromChild fromChild = true :=
              (finBeq_eq_true_iff fromChild fromChild).mpr rfl
            simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
              fromIncoming, self]
          have edgeSource : G.expandedMutilatedEdge mutilation latent
              (.observed source) = true := by
            have self : finBeq source source = true :=
              (finBeq_eq_true_iff source source).mpr rfl
            simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
              sourceIncoming', self]
          have latentAncestor : G.ancestorOf mutilation targets latent =
              true :=
            G.ancestorOf_prepend mutilation targets edgeSource sourceAncestor
          have latentSide := Rule1FactorMoralLeftParent.marries G x y z w
            fromChild fromParent fromChildConditioned latent edgeFrom
            latentAncestor (by dsimp [latent]; rfl)
          have latentSourceMoral : G.MoralOpenEdge mutilation targets
              (NodeSet.union x w) latent (.observed source) = true :=
            G.moralOpenEdge_of_ancestral mutilation targets
              (NodeSet.union x w) (by dsimp [latent]; rfl) sourceOpen
              (G.ancestralMoralEdge_of_adjacent mutilation targets
                latentAncestor sourceAncestor (Or.inl edgeSource))
          have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation
            y z (NodeSet.union x w) latentSourceMoral
          have sourceSide : G.moralLeftSide mutilation y z
              (NodeSet.union x w) (.observed source) = true := by
            rw [latentSide] at sameSide
            exact sameSide.symm
          have rootWitness : Rule1RootMoralLeftWitness model G x y z w
              root :=
            ⟨source, sourceIncident, sourceIncoming, sourceAncestor,
              sourceOpen, sourceSide⟩
          exact rule1FactorMoralLeftParent_of_root_witness model G projected
            x y z w assignment toChild root rootWitness toRelevant
      | true =>
          by_cases sameChild : fromChild = toChild
          · subst toChild
            exact fromParent
          · have bidirected := model.bidirected_of_shared_latent G
              projected root sameChild fromIncident toIncident
            let latent : SeparationNode S := .latentPair fromChild toChild
            have fromIncoming : mutilation.removeIncoming fromChild = false := by
              simpa [mutilation] using
                rule1_w_not_removeIncoming x y z w disjoint fromChild
                  fromChildInW
            have toIncoming : mutilation.removeIncoming toChild = false := by
              simpa [mutilation] using
                rule1_w_not_removeIncoming x y z w disjoint toChild
                  toChildInW
            have edgeFrom : G.expandedMutilatedEdge mutilation latent
                (.observed fromChild) = true := by
              have self : finBeq fromChild fromChild = true :=
                (finBeq_eq_true_iff fromChild fromChild).mpr rfl
              simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
                fromIncoming, self]
            have edgeTo : G.expandedMutilatedEdge mutilation latent
                (.observed toChild) = true := by
              have self : finBeq toChild toChild = true :=
                (finBeq_eq_true_iff toChild toChild).mpr rfl
              simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
                toIncoming, self]
            have fromAncestor : G.ancestorOf mutilation targets
                (.observed fromChild) = true :=
              G.ancestorOf_target mutilation targets fromChildTarget
            have latentAncestor : G.ancestorOf mutilation targets latent =
                true :=
              G.ancestorOf_prepend mutilation targets edgeFrom fromAncestor
            have latentSide := Rule1FactorMoralLeftParent.marries G x y z w
              fromChild fromParent fromChildConditioned latent edgeFrom
              latentAncestor (by dsimp [latent]; rfl)
            exact ⟨latent, edgeTo, latentAncestor,
              by dsimp [latent]; rfl, latentSide⟩

/-- Induction state at one latent root: the root affects a conditioned
rule-1 factor that already has a parent on the `Y` moral side. -/
def Rule1RootMoralLeftContact (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (root : Fin model.latent.count) : Prop :=
  Exists fun child : Fin S.count =>
    Rule1FactorMoralLeftParent G x y z w child /\
      rule1WConditionRootRelevant model G x w assignment child root = true

/-- Carry a factor-parent contact along an arbitrary exact walk in the
rule-1 root-adjacency graph, then route the terminal root into a requested
factor.  Every adjacency edge names a local factor affected by both adjacent
roots, so the single-root transfer theorem supplies the induction step. -/
theorem rule1FactorMoralLeftParent_of_contact_walk
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    {length : Nat} {source terminal : Fin model.latent.count}
    (walk : FiniteReachability.ExactWalk
      (rule1WConditionRootAdjacent model G x w assignment)
      length source terminal) :
    Rule1RootMoralLeftContact model G x y z w assignment source ->
      forall targetChild,
        rule1WConditionRootRelevant model G x w assignment
          targetChild terminal = true ->
        Rule1FactorMoralLeftParent G x y z w targetChild := by
  induction walk with
  | refl node =>
      intro contact targetChild targetRelevant
      rcases contact with
        ⟨fromChild, fromParent, fromRelevant⟩
      exact rule1FactorMoralLeftParent_transfer model G projected x y z w
        assignment disjoint fromChild targetChild node fromParent
        fromRelevant targetRelevant
  | @step restLength current next terminal first rest ih =>
      intro contact targetChild targetRelevant
      rcases contact with
        ⟨fromChild, fromParent, fromRelevant⟩
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule1WConditionRootAdjacent] using first) with
        ⟨bridgeChild, bridgeData⟩
      rcases Bool.and_eq_true_iff.mp bridgeData with
        ⟨currentRelevant, nextRelevant⟩
      have bridgeParent := rule1FactorMoralLeftParent_transfer model G
        projected x y z w assignment disjoint fromChild bridgeChild current
        fromParent fromRelevant currentRelevant
      have nextContact : Rule1RootMoralLeftContact model G x y z w
          assignment next := ⟨bridgeChild, bridgeParent, nextRelevant⟩
      exact ih nextContact targetChild targetRelevant

/-- Route a `Y`-side seed root through an arbitrary exact component walk and
obtain a left-side parent for any factor affected by the terminal root.  The
reflexive case uses the seed directly; a nontrivial walk initializes the
contact invariant at its first shared factor and recurses over the suffix. -/
theorem rule1FactorMoralLeftParent_of_root_walk
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    {length : Nat} {seed terminal : Fin model.latent.count}
    (walk : FiniteReachability.ExactWalk
      (rule1WConditionRootAdjacent model G x w assignment)
      length seed terminal)
    (seedWitness : Rule1RootMoralLeftWitness model G x y z w seed)
    (targetChild : Fin S.count)
    (targetRelevant : rule1WConditionRootRelevant model G x w assignment
      targetChild terminal = true) :
    Rule1FactorMoralLeftParent G x y z w targetChild := by
  cases walk with
  | refl =>
      exact rule1FactorMoralLeftParent_of_root_witness model G projected
        x y z w assignment targetChild seed seedWitness targetRelevant
  | @step restLength seed next terminal first rest =>
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule1WConditionRootAdjacent] using first) with
        ⟨bridgeChild, bridgeData⟩
      rcases Bool.and_eq_true_iff.mp bridgeData with
        ⟨seedRelevant, nextRelevant⟩
      have bridgeParent := rule1FactorMoralLeftParent_of_root_witness
        model G projected x y z w assignment bridgeChild seed seedWitness
        seedRelevant
      have nextContact : Rule1RootMoralLeftContact model G x y z w
          assignment next := ⟨bridgeChild, bridgeParent, nextRelevant⟩
      exact rule1FactorMoralLeftParent_of_contact_walk model G projected
        x y z w assignment disjoint rest nextContact targetChild
        targetRelevant

/-- A free ancestral observed representative showing that one concrete root
lies on the `Z` side of rule 1's moral separator in `G_{̅X}`. -/
def Rule1RootMoralRightWitness (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (root : Fin model.latent.count) : Prop :=
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      mutilation.removeIncoming source = false /\
        G.ancestorOf mutilation targets (.observed source) = true /\
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
              false /\
            G.moralLeftSide mutilation y z (NodeSet.union x w)
              (.observed source) = false

/-- Every root needed by the `Z` cylinder under `do(X ∪ W)` has a free
ancestral representative on the right moral side in `G_{̅X}`.

The ancestry route is first obtained in `G_{̅(X ∪ W)}` and then embedded
in `G_{̅X}`.  Every route vertex is open under `X ∪ W`; path separation
therefore assigns the terminal `Z` vertex, and hence the incident source, to
the complement of the canonical `Y` component. -/
theorem rule1RootMoralRightWitness_of_z_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true) :
    Rule1RootMoralRightWitness model G x y z w root := by
  let intervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let ancestors := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z
  rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
      root).mp (by simpa [intervention, ancestors] using relevant) with
    ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar (NodeSet.union x w)) z source (by
        simpa [FiniteLatentSCM.ancestralInBar, ancestors] using
          sourceAncestor) with
    ⟨zEnd, zEndInZ, length, walk, walkSimple, _minimal⟩
  have xSubset : NodeSet.Subset x (NodeSet.union x w) :=
    NodeSet.subset_union_left x w
  let mapped := FiniteLatentSCM.remapBarWalk_of_incoming_subset G xSubset
    walk
  have mappedNodes : mapped.nodes = walk.nodes := by
    simpa [mapped] using
      FiniteLatentSCM.remapBarWalk_of_incoming_subset_nodes G xSubset walk
  have walkOpen : forall node, node ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    by_cases atSource : node = source
    · subst node
      exact (FiniteLatentSCM.intervention_none_iff_unblocked
        (NodeSet.union x w) assignment source).mp (by
          simpa [intervention] using sourceFree)
    · have incoming :=
        PathSpecification.directed_walk_mem_not_removeIncoming G
          (GraphMutilation.bar (NodeSet.union x w)) walk member atSource
      simpa [GraphMutilation.bar, ObservedGraph.blockedBy] using incoming
  have mappedOpen : forall node, node ∈ mapped.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    rw [mappedNodes] at member
    exact walkOpen node member
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  have zEndTarget : targets zEnd = true := by
    simp [targets, NodeSet.union, zEndInZ]
  have mappedAncestor : forall node, node ∈ mapped.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      mapped zEndTarget member
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have sourceToZ := moralLeftSide_eq_of_open_observed_walk G mutilation
    y z (NodeSet.union x w) mapped mappedOpen (by
      simpa [targets] using mappedAncestor)
  have zOpen := FiniteLatentSCM.blockedBy_false_of_mem_z x y z w disjoint
    zEndInZ
  have zSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
      (.observed zEnd) = false :=
    G.moralLeftSide_not_of_right mutilation y z (NodeSet.union x w)
      (by simpa [mutilation] using separated) zEnd zEndInZ (by
        simpa [ObservedGraph.blockedBy] using zOpen)
  have sourceOutsideX : x source = false := by
    have sourceOpen := mappedOpen source mapped.mem_source
    have outside : NodeSet.union x w source = false := by
      simpa [ObservedGraph.blockedBy] using sourceOpen
    exact (Bool.or_eq_false_iff.mp (by
      simpa [NodeSet.union] using outside)).1
  have sourceIncoming : mutilation.removeIncoming source = false := by
    simpa [mutilation, GraphMutilation.bar] using sourceOutsideX
  exact ⟨source, sourceIncident, sourceIncoming,
    mappedAncestor source mapped.mem_source,
    mappedOpen source mapped.mem_source, sourceToZ.trans zSide⟩

/-- A concrete latent root cannot have free ancestral representatives on
opposite sides of the rule-1 moral separator.  Projection joins two distinct
representatives through the canonical latent-pair vertex; the shared-latent
side lemma also covers the reflexive case constructively. -/
theorem rule1RootMoralWitnesses_disjoint
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (root : Fin model.latent.count)
    (leftWitness : Rule1RootMoralLeftWitness model G x y z w root)
    (rightWitness : Rule1RootMoralRightWitness model G x y z w root) :
    False := by
  let mutilation := GraphMutilation.bar x
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases leftWitness with
    ⟨leftSource, leftIncident, leftIncoming, leftAncestor, leftOpen,
      leftSide⟩
  rcases rightWitness with
    ⟨rightSource, rightIncident, rightIncoming, rightAncestor, rightOpen,
      rightSide⟩
  have sameSide := FiniteLatentSCM.moralLeftSide_eq_of_shared_latent
    model G projected mutilation y z (NodeSet.union x w) root
    leftSource rightSource leftIncident rightIncident leftIncoming
    rightIncoming leftAncestor rightAncestor (by
      simpa [ObservedGraph.blockedBy] using leftOpen) (by
      simpa [ObservedGraph.blockedBy] using rightOpen)
  rw [leftSide, rightSide] at sameSide
  contradiction

/-- A factor already carrying a `Y`-side parent cannot be affected by a root
that is also needed by the `Z` cylinder.

For a nonincident root, its relevance route supplies an ordinary left-side
root witness.  For direct incidence, the projected latent-pair parent joins
the conditioned factor to the root's open `Z` representative; moralizing the
conditioned collider would put that representative on both sides. -/
theorem Rule1FactorMoralLeftParent.excludes_z_relevant_root
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (child : Fin S.count) (root : Fin model.latent.count)
    (factorParent : Rule1FactorMoralLeftParent G x y z w child)
    (factorRelevant : rule1WConditionRootRelevant model G x w assignment
      child root = true)
    (zRelevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true) :
    False := by
  have rightWitness := rule1RootMoralRightWitness_of_z_relevant model G
    x y z w assignment disjoint separated root zRelevant
  cases incident : model.latent.incident root child with
  | false =>
      have leftWitness :=
        rule1RootMoralLeftWitness_of_factor_parent_relevant_not_incident
          model G x y z w assignment child root factorParent factorRelevant
          incident
      exact rule1RootMoralWitnesses_disjoint model G projected x y z w root
        leftWitness rightWitness
  | true =>
      let mutilation := GraphMutilation.bar x
      let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
      rcases rightWitness with
        ⟨source, sourceIncident, sourceIncoming, sourceAncestor, sourceOpen,
          sourceSide⟩
      have childInW : w child = true :=
        (Bool.and_eq_true_iff.mp factorRelevant).1
      have childConditioned : NodeSet.union x w child = true := by
        simp [NodeSet.union, childInW]
      have sourceDifferent : child ≠ source := by
        intro equal
        subst source
        have childOpen : NodeSet.union x w child = false := by
          simpa [ObservedGraph.blockedBy] using sourceOpen
        rw [childConditioned] at childOpen
        contradiction
      have bidirected := model.bidirected_of_shared_latent G projected root
        sourceDifferent incident sourceIncident
      let latent : SeparationNode S := .latentPair child source
      have childIncoming : mutilation.removeIncoming child = false := by
        simpa [mutilation] using
          rule1_w_not_removeIncoming x y z w disjoint child childInW
      have sourceIncoming' : mutilation.removeIncoming source = false := by
        simpa [mutilation] using sourceIncoming
      have edgeChild : G.expandedMutilatedEdge mutilation latent
          (.observed child) = true := by
        have self : finBeq child child = true :=
          (finBeq_eq_true_iff child child).mpr rfl
        simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
          childIncoming, self]
      have edgeSource : G.expandedMutilatedEdge mutilation latent
          (.observed source) = true := by
        have self : finBeq source source = true :=
          (finBeq_eq_true_iff source source).mpr rfl
        simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
          sourceIncoming', self]
      have latentAncestor : G.ancestorOf mutilation targets latent = true :=
        G.ancestorOf_prepend mutilation targets edgeSource sourceAncestor
      have latentSide := Rule1FactorMoralLeftParent.marries G x y z w child
        factorParent childConditioned latent edgeChild latentAncestor
        (by dsimp [latent]; rfl)
      have latentSourceMoral : G.MoralOpenEdge mutilation targets
          (NodeSet.union x w) latent (.observed source) = true :=
        G.moralOpenEdge_of_ancestral mutilation targets
          (NodeSet.union x w) (by dsimp [latent]; rfl) sourceOpen
          (G.ancestralMoralEdge_of_adjacent mutilation targets
            latentAncestor sourceAncestor (Or.inl edgeSource))
      have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation
        y z (NodeSet.union x w) latentSourceMoral
      rw [latentSide, sourceSide] at sameSide
      contradiction

/-- Propagate the contact invariant itself to the terminal root of an exact
component walk.  This companion to the factor-target theorem is used when
the terminal root is tested against the `Z` cylinder rather than against a
preselected local factor. -/
theorem rule1RootMoralLeftContact_of_contact_walk
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    {length : Nat} {source terminal : Fin model.latent.count}
    (walk : FiniteReachability.ExactWalk
      (rule1WConditionRootAdjacent model G x w assignment)
      length source terminal) :
    Rule1RootMoralLeftContact model G x y z w assignment source ->
      Rule1RootMoralLeftContact model G x y z w assignment terminal := by
  induction walk with
  | refl node =>
      intro contact
      exact contact
  | @step restLength current next terminal first rest ih =>
      intro contact
      rcases contact with ⟨fromChild, fromParent, fromRelevant⟩
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule1WConditionRootAdjacent] using first) with
        ⟨bridgeChild, bridgeData⟩
      rcases Bool.and_eq_true_iff.mp bridgeData with
        ⟨currentRelevant, nextRelevant⟩
      have bridgeParent := rule1FactorMoralLeftParent_transfer model G
        projected x y z w assignment disjoint fromChild bridgeChild current
        fromParent fromRelevant currentRelevant
      have nextContact : Rule1RootMoralLeftContact model G x y z w
          assignment next := ⟨bridgeChild, bridgeParent, nextRelevant⟩
      exact ih nextContact

/-- No root in the latent component generated by the `Y` cylinder is needed
by the `Z` cylinder.  A reflexive component path contradicts the two root
witnesses directly.  A nontrivial path initializes a factor contact at its
first adjacency edge, propagates that contact over the exact suffix, and
contradicts `Z` relevance at the terminal factor. -/
theorem rule1YConditionLatentComponent_z_relevant_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w))
    (root : Fin model.latent.count)
    (selected : rule1YConditionLatentComponent model G x y w assignment
      root = true) :
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = false := by
  cases zRelevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root with
  | false => rfl
  | true =>
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule1YConditionLatentComponent] using selected) with
        ⟨seed, seedData⟩
      rcases Bool.and_eq_true_iff.mp seedData with
        ⟨seedRelevant, seedReaches⟩
      let roots := List.ofFn
        (fun latent : Fin model.latent.count => latent)
      let adjacent := rule1WConditionRootAdjacent model G x w assignment
      have complete : forall latent : Fin model.latent.count,
          latent ∈ roots :=
        fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
      have bounded : FiniteReachability.BoundedWalk adjacent roots.length
          seed root :=
        (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots
          adjacent finBeq_eq_true_iff complete roots.length seed root).mp
          (by simpa [roots, adjacent] using seedReaches)
      rcases bounded with ⟨length, _bound, exactWalk⟩
      rcases exactWalk with ⟨walk⟩
      have seedWitness := rule1RootMoralLeftWitness_of_y_relevant model G
        x y z w assignment disjoint seed seedRelevant
      cases walk with
      | refl =>
          have rightWitness := rule1RootMoralRightWitness_of_z_relevant
            model G x y z w assignment disjoint separated root zRelevant
          exact (rule1RootMoralWitnesses_disjoint model G projected
            x y z w root seedWitness rightWitness).elim
      | @step restLength seed next terminal first rest =>
          rcases (finAny_eq_true_iff _).mp (by
              simpa [adjacent, rule1WConditionRootAdjacent] using first) with
            ⟨bridgeChild, bridgeData⟩
          rcases Bool.and_eq_true_iff.mp bridgeData with
            ⟨seedFactorRelevant, nextRelevant⟩
          have bridgeParent := rule1FactorMoralLeftParent_of_root_witness
            model G projected x y z w assignment bridgeChild _
            seedWitness seedFactorRelevant
          have nextContact : Rule1RootMoralLeftContact model G x y z w
              assignment next :=
            ⟨bridgeChild, bridgeParent, nextRelevant⟩
          have terminalContact :=
            rule1RootMoralLeftContact_of_contact_walk model G projected
              x y z w assignment disjoint rest nextContact
          rcases terminalContact with
            ⟨terminalChild, terminalParent, terminalRelevant⟩
          exact (Rule1FactorMoralLeftParent.excludes_z_relevant_root model G
            projected x y z w assignment disjoint separated terminalChild
            root terminalParent terminalRelevant zRelevant).elim

/-- Two roots relevant to the same local rule-1 factor are adjacent in the
finite component graph. -/
theorem rule1WConditionRootAdjacent_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (left right : Fin model.latent.count)
    (leftRelevant : rule1WConditionRootRelevant model G x w assignment
      child left = true)
    (rightRelevant : rule1WConditionRootRelevant model G x w assignment
      child right = true) :
    rule1WConditionRootAdjacent model G x w assignment left right = true :=
  finAny_eq_true_of _ child
    (Bool.and_eq_true_iff.mpr ⟨leftRelevant, rightRelevant⟩)

/-- Every root needed by the `Y` cylinder is a seed of, and therefore lies
in, the generated rule-1 component. -/
theorem rule1YConditionLatentComponent_of_y_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y w : NodeSet S) (assignment : S.Assignment)
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true) :
    rule1YConditionLatentComponent model G x y w assignment root = true := by
  apply finAny_eq_true_of _ root
  apply Bool.and_eq_true_iff.mpr
  refine ⟨relevant, ?_⟩
  have complete : forall latent : Fin model.latent.count,
      latent ∈ List.ofFn (fun i : Fin model.latent.count => i) :=
    fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
    (List.ofFn (fun latent : Fin model.latent.count => latent))
    (rule1WConditionRootAdjacent model G x w assignment)
    finBeq_eq_true_iff complete
    (List.ofFn (fun latent : Fin model.latent.count => latent)).length
    root root).mpr
      (FiniteReachability.BoundedWalk.refl _ _ root)

/-- The generated rule-1 root family is closed across every local-factor
adjacency edge. -/
theorem rule1YConditionLatentComponent_closed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y w : NodeSet S) (assignment : S.Assignment)
    (left right : Fin model.latent.count)
    (leftIn : rule1YConditionLatentComponent model G x y w assignment
      left = true)
    (edge : rule1WConditionRootAdjacent model G x w assignment
      left right = true) :
    rule1YConditionLatentComponent model G x y w assignment right = true := by
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule1YConditionLatentComponent] using leftIn) with
    ⟨seed, seedData⟩
  rcases Bool.and_eq_true_iff.mp seedData with
    ⟨seedRelevant, seedReachesLeft⟩
  let roots := List.ofFn (fun latent : Fin model.latent.count => latent)
  let adjacent := rule1WConditionRootAdjacent model G x w assignment
  have complete : forall latent : Fin model.latent.count, latent ∈ roots :=
    fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
  have seedToLeft : FiniteReachability.BoundedWalk adjacent roots.length
      seed left :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots adjacent
      finBeq_eq_true_iff complete roots.length seed left).mp
      (by simpa [roots, adjacent] using seedReachesLeft)
  have leftToRight : FiniteReachability.BoundedWalk adjacent 1 left right :=
    ⟨1, Nat.le_refl _,
      ⟨FiniteReachability.ExactWalk.step (by simpa [adjacent] using edge)
        (FiniteReachability.ExactWalk.refl right)⟩⟩
  have seedToRightReachable : FiniteReachability.Reachable adjacent seed right :=
    FiniteReachability.Reachable.of_bounded
      (FiniteReachability.BoundedWalk.trans seedToLeft leftToRight)
  have seedToRight : FiniteReachability.BoundedWalk adjacent roots.length
      seed right :=
    FiniteReachability.boundedWalk_of_reachable finBeq roots adjacent
      finBeq_eq_true_iff complete seedToRightReachable
  have found : FiniteReachability.within finBeq roots adjacent roots.length
      seed right = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots adjacent
      finBeq_eq_true_iff complete roots.length seed right).mpr seedToRight
  apply (finAny_eq_true_iff _).mpr
  exact ⟨seed, Bool.and_eq_true_iff.mpr ⟨seedRelevant,
    by simpa [roots, adjacent] using found⟩⟩

/-- Every root relevant to a common rule-1 conditioning factor belongs to
the generated `Y` component. -/
theorem rule1WConditionCommon_root_selected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (common : rule1WConditionCommon model G x y w assignment child = true)
    (relevant : rule1WConditionRootRelevant model G x w assignment
      child root = true) :
    rule1YConditionLatentComponent model G x y w assignment root = true := by
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule1WConditionCommon] using common) with ⟨pivot, pivotData⟩
  rcases Bool.and_eq_true_iff.mp pivotData with
    ⟨pivotRelevant, pivotSelected⟩
  exact rule1YConditionLatentComponent_closed model G x y w assignment
    pivot root pivotSelected
    (rule1WConditionRootAdjacent_of_relevant model G x w assignment
      child pivot root pivotRelevant relevant)

/-- A residual rule-1 conditioning factor contains no root from the generated
`Y` component. -/
theorem rule1WConditionResidual_root_unselected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (residual : rule1WConditionResidual model G x y w assignment child =
      true)
    (relevant : rule1WConditionRootRelevant model G x w assignment
      child root = true) :
    rule1YConditionLatentComponent model G x y w assignment root = false := by
  have notCommon :
      rule1WConditionCommon model G x y w assignment child = false :=
    NodeSet.Disjoint.diff_right w
      (rule1WConditionCommon model G x y w assignment) child residual
  cases selected :
      rule1YConditionLatentComponent model G x y w assignment root with
  | false => rfl
  | true =>
      have common :
          rule1WConditionCommon model G x y w assignment child = true :=
        finAny_eq_true_of _ root
          (Bool.and_eq_true_iff.mpr ⟨relevant, selected⟩)
      rw [common] at notCommon
      contradiction

/-- Common rule-1 factors are genuine members of `W`. -/
theorem rule1WConditionCommon_subset_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.Subset (rule1WConditionCommon model G x y w assignment) w := by
  intro child common
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule1WConditionCommon] using common) with ⟨root, rootData⟩
  have relevant : rule1WConditionRootRelevant model G x w assignment
      child root = true := (Bool.and_eq_true_iff.mp rootData).1
  exact (Bool.and_eq_true_iff.mp relevant).1

/-- The connected common block and its complementary residual block cover
all of `W`. -/
theorem rule1WConditionSplit_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.union (rule1WConditionCommon model G x y w assignment)
      (rule1WConditionResidual model G x y w assignment) = w := by
  funext child
  have subset := rule1WConditionCommon_subset_w model G x y w assignment
    child
  simp [rule1WConditionResidual, NodeSet.union, NodeSet.diff]
  cases hw : w child with
  | false =>
      cases hc : rule1WConditionCommon model G x y w assignment child with
      | false => rfl
      | true =>
          have impossible := subset hc
          rw [hw] at impossible
          contradiction
  | true =>
      cases rule1WConditionCommon model G x y w assignment child <;> rfl

/-- Path d-separation and projection construct the full rule-1 latent
partition, with no auxiliary Boolean graph premises.

The selected coordinates are the complement of the finite component
generated by roots needed for `Y`.  The `Z` cylinder and residual local `W`
factors depend only on that complement.  The `Y` cylinder and common local
`W` factors depend only on the component itself.  Topological local factors
are essential here: they split the conditioning cylinder without pretending
that a conditioned vertex is an ordinary open output coordinate. -/
def rule1PartitionWitness_of_path_projected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x w)) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let unionIntervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let yRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  let zRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z
  let component :=
    rule1YConditionLatentComponent model G x y w assignment
  let selected := fun root : Fin model.latent.count => !(component root)
  let common := rule1WConditionCommon model G x y w assignment
  let residual := rule1WConditionResidual model G x y w assignment
  let zEvent : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder unionIntervention roots)
  let yEvent : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder unionIntervention roots)
  let residualEvent :=
    localConditionEvent model x w residual assignment
  let commonEvent :=
    localConditionEvent model x w common assignment
  have commonSubsetW : NodeSet.Subset common w := by
    simpa [common] using
      rule1WConditionCommon_subset_w model G x y w assignment
  have residualSubsetW : NodeSet.Subset residual w := by
    dsimp [residual]
    exact NodeSet.diff_subset_left w
      (rule1WConditionCommon model G x y w assignment)
  have covers : NodeSet.union common residual = w := by
    simpa [common, residual] using
      rule1WConditionSplit_union model G x y w assignment
  have coversReverse : NodeSet.union residual common = w := by
    rw [NodeSet.union_comm]
    exact covers
  have leftIntervention :
      (rule1Left x y z w).intervention assignment =
        (rule1Right x y z w).intervention assignment := by
    funext child
    simp [rule1Left, rule1Right, Kernel.intervention]
  have rightIntervention :
      (rule1Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
    funext child
    simp [rule1Right, Kernel.intervention]
  have yDependsOnComponent :
      CanonicalFactorization.DependsOnSelected model.latent.count
        model.latent.Value component yEvent := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder unionIntervention yRelevant)
      (selected' := component) yEvent ?_ ?_
    · intro root relevantRoot
      exact rule1YConditionLatentComponent_of_y_relevant model G x y w
        assignment root (by
          simpa [unionIntervention, yRelevant] using relevantRoot)
    · simpa [unionIntervention, yRelevant, yEvent] using
        agreesOn_rule1Y_dependsOnSelected_union model G x y z w assignment
  have zDependsOnComplement :
      CanonicalFactorization.DependsOnSelected model.latent.count
        model.latent.Value selected zEvent := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder unionIntervention zRelevant)
      (selected' := selected) zEvent ?_ ?_
    · intro root relevantRoot
      cases componentRoot : component root with
      | false => simp [selected, componentRoot]
      | true =>
          have impossible :=
            rule1YConditionLatentComponent_z_relevant_false model G
              projected x y z w assignment disjoint separated root (by
                simpa [component] using componentRoot)
          have relevantRoot' : model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment)
              (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z)
              root = true := by
            simpa [unionIntervention, zRelevant] using relevantRoot
          rw [relevantRoot'] at impossible
          contradiction
    · simpa [unionIntervention, zRelevant, zEvent] using
        agreesOn_rule1Z_dependsOnSelected_union model G x y z w assignment
  have residualDependsOnComplement :
      CanonicalFactorization.DependsOnSelected model.latent.count
        model.latent.Value selected residualEvent := by
    dsimp [residualEvent]
    apply localConditionEvent_dependsOnSelected model G
    intro child childResidual root relevantRoot
    have childInW := residualSubsetW child childResidual
    have combined : rule1WConditionRootRelevant model G x w assignment
        child root = true := by
      simp [rule1WConditionRootRelevant, childInW, relevantRoot]
    have outside := rule1WConditionResidual_root_unselected model G x y w
      assignment child root (by simpa [residual] using childResidual)
      combined
    simp [selected, component, outside]
  have commonDependsOnComponent :
      CanonicalFactorization.DependsOnUnselected model.latent.count
        model.latent.Value selected commonEvent := by
    dsimp [commonEvent]
    apply localConditionEvent_dependsOnUnselected model G
    intro child childCommon root relevantRoot
    have childInW := commonSubsetW child childCommon
    have combined : rule1WConditionRootRelevant model G x w assignment
        child root = true := by
      simp [rule1WConditionRootRelevant, childInW, relevantRoot]
    have inside := rule1WConditionCommon_root_selected model G x y w
      assignment child root (by simpa [common] using childCommon) combined
    simp [selected, component, inside]
  have wEventSplit : forall roots,
      Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule1Right x y z w).intervention assignment) roots) =
        (residualEvent roots && commonEvent roots) := by
    intro roots
    have full := agreesOn_evalUnder_eq_localConditionEvent model x w
      assignment roots
    have split := localConditionEvent_union model x w residual common
      assignment roots
    have selectedCover := congrArg
      (fun nodes => localConditionEvent model x w nodes assignment roots)
      coversReverse
    have splitFullRaw : localConditionEvent model x w w assignment roots =
        (localConditionEvent model x w residual assignment roots &&
          localConditionEvent model x w common assignment roots) :=
      selectedCover.symm.trans split
    have splitFull : localConditionEvent model x w w assignment roots =
        (residualEvent roots && commonEvent roots) := by
      simpa [residualEvent, commonEvent] using splitFullRaw
    rw [rightIntervention, full, splitFull]
  refine
    { selected := selected
      selectedOutcome := zEvent
      selectedCondition := residualEvent
      unselectedOutcome := yEvent
      unselectedCondition := commonEvent
      selectedOutcomeDepends := zDependsOnComplement
      selectedConditionDepends := residualDependsOnComplement
      unselectedOutcomeDepends := by
        exact CanonicalFactorization.DependsOnUnselected.of_selected_compl
          model.latent.count model.latent.Value component yEvent
          yDependsOnComponent
      unselectedConditionDepends := commonDependsOnComponent
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · funext roots
    have rewritten :=
      agreesOn_rule1_evalUnder_union_eq model x y z w assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      zEvent, yEvent]
    rw [show (rule1Left x y z w).outcome = y from rfl,
      show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      leftIntervention, Kernel.agreesOn_union, rewritten,
      wEventSplit roots]
    exact bool_and_four_pairs (residualEvent roots) (commonEvent roots)
      (yEvent roots) (zEvent roots)
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter]
    rw [show (rule1Right x y z w).condition = w from rfl,
      wEventSplit roots]
  · funext roots
    have yComposition :=
      agreesOn_and_evalUnder_union_eq model x w y assignment roots
    simp only [productPreimage, Kernel.numeratorEvent, Probability.inter,
      yEvent]
    rw [show (rule1Right x y z w).outcome = y from rfl,
      show (rule1Right x y z w).condition = w from rfl,
      rightIntervention, Bool.and_comm, yComposition,
      ← rightIntervention, wEventSplit roots]
    exact bool_and_mid_swap (residualEvent roots) (commonEvent roots)
      (yEvent roots)
  · funext roots
    have zComposition :=
      agreesOn_and_evalUnder_union_eq model x w z assignment roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter,
      zEvent]
    rw [show (rule1Left x y z w).condition = NodeSet.union z w from rfl,
      leftIntervention, Kernel.agreesOn_union, rightIntervention,
      Bool.and_comm, zComposition, ← rightIntervention,
      wEventSplit roots]
    exact bool_and_rot_left (residualEvent roots) (commonEvent roots)
      (zEvent roots)

/-- Build the rule-2 witness once the four cylinders have been assigned to a
common latent partition.  The cross-world event equalities are discharged by
SCM composition; only the dependence proofs remain graph-specific. -/
def rule2PartitionWitness (model : FiniteLatentSCM S)
    (x y z w wSelected wUnselected : NodeSet S)
    (assignment : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (wSplit : w = NodeSet.union wSelected wUnselected)
    (zDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule2Right x y z w).intervention assignment) roots)))
    (wSelectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn wSelected assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)))
    (yDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)))
    (wUnselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn wUnselected assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots))) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  let baseIntervention := (rule2Right x y z w).intervention assignment
  let extendedIntervention := (rule2Left x y z w).intervention assignment
  let baseCylinder := fun nodes : NodeSet S =>
    fun roots : model.latent.Assignment => Kernel.agreesOn nodes assignment
      (model.evalUnder baseIntervention roots)
  let extendedCylinder := fun nodes : NodeSet S =>
    fun roots : model.latent.Assignment => Kernel.agreesOn nodes assignment
      (model.evalUnder extendedIntervention roots)
  refine
    { selected := selected
      selectedOutcome := baseCylinder z
      selectedCondition := extendedCylinder wSelected
      unselectedOutcome := extendedCylinder y
      unselectedCondition := extendedCylinder wUnselected
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [baseCylinder, baseIntervention] using zDepends
  · simpa [extendedCylinder, extendedIntervention] using wSelectedDepends
  · simpa [extendedCylinder, extendedIntervention] using yDepends
  · simpa [extendedCylinder, extendedIntervention] using wUnselectedDepends
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.numeratorEvent,
      baseCylinder, extendedCylinder]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder baseIntervention roots) &&
        Kernel.agreesOn (NodeSet.union z w) assignment
          (model.evalUnder baseIntervention roots)) = _
    rw [Kernel.agreesOn_union z w]
    cases zHolds : Kernel.agreesOn z assignment
        (model.evalUnder baseIntervention roots) with
    | false => simp [Probability.inter, zHolds]
    | true =>
        have evaluationsEqual :
            model.evalUnder extendedIntervention roots =
              model.evalUnder baseIntervention roots := by
          simpa [baseIntervention, extendedIntervention, rule2Left,
            rule2Right] using
            evalUnder_union_intervention_eq_of_agreesOn model x z assignment
              roots zHolds
        simp only [Probability.inter]
        rw [evaluationsEqual]
        rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
        simp [zHolds]
        ac_rfl
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.conditionEvent,
      extendedCylinder]
    change Kernel.agreesOn w assignment
      (model.evalUnder extendedIntervention roots) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.numeratorEvent,
      extendedCylinder]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder extendedIntervention roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder extendedIntervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.conditionEvent,
      baseCylinder, extendedCylinder]
    change Kernel.agreesOn (NodeSet.union z w) assignment
      (model.evalUnder baseIntervention roots) = _
    rw [Kernel.agreesOn_union z w]
    cases zHolds : Kernel.agreesOn z assignment
        (model.evalUnder baseIntervention roots) with
    | false => simp [Probability.inter, zHolds]
    | true =>
        have evaluationsEqual :
            model.evalUnder extendedIntervention roots =
              model.evalUnder baseIntervention roots := by
          simpa [baseIntervention, extendedIntervention, rule2Left,
            rule2Right] using
            evalUnder_union_intervention_eq_of_agreesOn model x z assignment
              roots zHolds
        simp only [Probability.inter]
        rw [evaluationsEqual]
        rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
        simp [zHolds]

/-!
### Rule 2 through cross-intervention local factors

The older rule-2 split above fixes the raw `An(Z)` latent mask.  That mask is
too coarse in the general conditioned case: a root may affect both `Y` and
`Z` only through a conditioned `W` noncollider, while path separation remains
valid.  The general construction instead factors the joint `Z ∪ W`
cylinder topologically.  A local `Z` factor is read under `do(X ∪ W)` and a
local `W` factor under `do(X ∪ Z)`.  Together they are exactly the original
joint cylinder under `do(X)`.
-/

/-- A local joint factor for a `Z` vertex can intervene on every `W` vertex.
Only earlier vertices can influence the factor, and every earlier `W` vertex
already occurs in the joint topological prefix. -/
theorem rule2JointLocalConditionFactor_eq_z
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (child : Fin S.count) (childInZ : z child = true)
    (roots : model.latent.Assignment) :
    localConditionFactor model x (NodeSet.union z w) assignment child roots =
      localConditionFactor model (NodeSet.union x w) z assignment child
        roots := by
  let jointAction := localConditionAction x (NodeSet.union z w) child
  let zAction := localConditionAction (NodeSet.union x w) z child
  have interventionAgree : forall node, node.val <= child.val ->
      ((Kernel.mk NodeSet.empty jointAction NodeSet.empty).intervention
          assignment) node =
        ((Kernel.mk NodeSet.empty zAction NodeSet.empty).intervention
          assignment) node := by
    intro node through
    have actionEq : jointAction node = zAction node := by
      by_cases earlier : node.val < child.val
      · dsimp [jointAction, zAction]
        simp only [localConditionAction, conditioningPrefix, NodeSet.union,
          earlier, decide_true, Bool.and_true]
        ac_rfl
      · have sameValue : node.val = child.val :=
          Nat.le_antisymm through (Nat.le_of_not_gt earlier)
        have sameNode : node = child := Fin.ext sameValue
        subst node
        have childOutsideX : x child = false :=
          disjoint.xz.symm child childInZ
        have childOutsideW : w child = false :=
          disjoint.zw child childInZ
        simp [jointAction, zAction, localConditionAction,
          conditioningPrefix, NodeSet.union, childInZ, childOutsideX,
          childOutsideW]
    simp [Kernel.intervention, actionEq]
  have evaluated := model.evalNodeUnder_eq_of_intervention_agree_through
    ((Kernel.mk NodeSet.empty jointAction NodeSet.empty).intervention
      assignment)
    ((Kernel.mk NodeSet.empty zAction NodeSet.empty).intervention assignment)
    roots child interventionAgree
  simpa [localConditionFactor, jointAction, zAction,
    FiniteLatentSCM.evalUnder] using congrArg
      (fun value => decide (value = assignment child)) evaluated

/-- The symmetric local statement for a `W` vertex: intervening on every
`Z` vertex agrees with the joint topological prefix through that factor. -/
theorem rule2JointLocalConditionFactor_eq_w
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (child : Fin S.count) (childInW : w child = true)
    (roots : model.latent.Assignment) :
    localConditionFactor model x (NodeSet.union z w) assignment child roots =
      localConditionFactor model (NodeSet.union x z) w assignment child
        roots := by
  let jointAction := localConditionAction x (NodeSet.union z w) child
  let wAction := localConditionAction (NodeSet.union x z) w child
  have interventionAgree : forall node, node.val <= child.val ->
      ((Kernel.mk NodeSet.empty jointAction NodeSet.empty).intervention
          assignment) node =
        ((Kernel.mk NodeSet.empty wAction NodeSet.empty).intervention
          assignment) node := by
    intro node through
    have actionEq : jointAction node = wAction node := by
      by_cases earlier : node.val < child.val
      · dsimp [jointAction, wAction]
        simp only [localConditionAction, conditioningPrefix, NodeSet.union,
          earlier, decide_true, Bool.and_true]
        ac_rfl
      · have sameValue : node.val = child.val :=
          Nat.le_antisymm through (Nat.le_of_not_gt earlier)
        have sameNode : node = child := Fin.ext sameValue
        subst node
        have childOutsideX : x child = false :=
          disjoint.xw.symm child childInW
        have childOutsideZ : z child = false :=
          disjoint.zw.symm child childInW
        simp [jointAction, wAction, localConditionAction,
          conditioningPrefix, NodeSet.union, childInW, childOutsideX,
          childOutsideZ]
    simp [Kernel.intervention, actionEq]
  have evaluated := model.evalNodeUnder_eq_of_intervention_agree_through
    ((Kernel.mk NodeSet.empty jointAction NodeSet.empty).intervention
      assignment)
    ((Kernel.mk NodeSet.empty wAction NodeSet.empty).intervention assignment)
    roots child interventionAgree
  simpa [localConditionFactor, jointAction, wAction,
    FiniteLatentSCM.evalUnder] using congrArg
      (fun value => decide (value = assignment child)) evaluated

/-- The `Z` subfamily of the joint topological cylinder is the standalone
`Z` cylinder under `do(X ∪ W)`. -/
theorem rule2JointLocalConditionZ_eq
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (roots : model.latent.Assignment) :
    localConditionEvent model x (NodeSet.union z w) z assignment roots =
      localConditionEvent model (NodeSet.union x w) z z assignment roots := by
  unfold localConditionEvent
  apply finAll_congr
  intro child
  cases selected : z child with
  | false => simp
  | true =>
      simp only [↓reduceIte]
      exact rule2JointLocalConditionFactor_eq_z model x y z w assignment
        disjoint child selected roots

/-- The `W` subfamily of the same joint cylinder is the standalone `W`
cylinder under `do(X ∪ Z)`. -/
theorem rule2JointLocalConditionW_eq
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (roots : model.latent.Assignment) :
    localConditionEvent model x (NodeSet.union z w) w assignment roots =
      localConditionEvent model (NodeSet.union x z) w w assignment roots := by
  unfold localConditionEvent
  apply finAll_congr
  intro child
  cases selected : w child with
  | false => simp
  | true =>
      simp only [↓reduceIte]
      exact rule2JointLocalConditionFactor_eq_w model x y z w assignment
        disjoint child selected roots

/-- Cross-intervention factorization of the rule-2 conditioning cylinder.

For every latent assignment, observing `Z ∪ W` under `do(X)` is exactly
the conjunction of observing `Z` under `do(X ∪ W)` and observing `W`
under `do(X ∪ Z)`.  The proof is pointwise and constructive: all three
cylinders are expanded into their topological local factors, after which the
two preceding prefix lemmas identify the factors one by one. -/
theorem agreesOn_rule2_cross_condition_factorization
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (roots : model.latent.Assignment) :
    Kernel.agreesOn (NodeSet.union z w) assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          roots) =
      (Kernel.agreesOn z assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment) roots)) := by
  have joint := agreesOn_evalUnder_eq_localConditionEvent model x
    (NodeSet.union z w) assignment roots
  have split := localConditionEvent_union model x (NodeSet.union z w)
    z w assignment roots
  have zFactors := rule2JointLocalConditionZ_eq model x y z w assignment
    disjoint roots
  have wFactors := rule2JointLocalConditionW_eq model x y z w assignment
    disjoint roots
  have zCylinder := agreesOn_evalUnder_eq_localConditionEvent model
    (NodeSet.union x w) z assignment roots
  have wCylinder := agreesOn_evalUnder_eq_localConditionEvent model
    (NodeSet.union x z) w assignment roots
  rw [joint, split, zFactors, wFactors, ← zCylinder, ← wCylinder]

/-- One latent root can affect the local equality constraint for a
conditioned `W` vertex under `do(X ∪ Z)`. -/
def rule2WConditionRootRelevant (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (assignment : S.Assignment) (child : Fin S.count)
    (root : Fin model.latent.count) : Bool :=
  w child &&
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty
        (localConditionAction (NodeSet.union x z) w child)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G
        (localConditionAction (NodeSet.union x z) w child)
        (NodeSet.singleton child)) root

/-- Two latent roots are adjacent when the same local rule-2 conditioning
factor can observe both of them. -/
def rule2WConditionRootAdjacent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (assignment : S.Assignment)
    (left right : Fin model.latent.count) : Bool :=
  finAny S.count (fun child =>
    rule2WConditionRootRelevant model G x z w assignment child left &&
      rule2WConditionRootRelevant model G x z w assignment child right)

/-- The finite latent component generated by roots needed for the `Z`
cylinder under `do(X ∪ W)`, closed through local `W` factors read under
`do(X ∪ Z)`. -/
def rule2ZConditionLatentComponent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (assignment : S.Assignment) (root : Fin model.latent.count) : Bool :=
  finAny model.latent.count (fun seed =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) seed &&
      FiniteReachability.within finBeq
        (List.ofFn (fun latent : Fin model.latent.count => latent))
        (rule2WConditionRootAdjacent model G x z w assignment)
        (List.ofFn (fun latent : Fin model.latent.count => latent)).length
        seed root)

/-- A local `W` factor belongs to the selected rule-2 block when one of its
relevant roots lies in the component generated by `Z`. -/
def rule2WConditionSelected (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (assignment : S.Assignment) : NodeSet S :=
  fun child =>
    finAny model.latent.count (fun root =>
      rule2WConditionRootRelevant model G x z w assignment child root &&
        rule2ZConditionLatentComponent model G x z w assignment root)

/-- Every remaining local `W` factor belongs to the complementary rule-2
block. -/
def rule2WConditionResidual (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (assignment : S.Assignment) : NodeSet S :=
  NodeSet.diff w (rule2WConditionSelected model G x z w assignment)

theorem rule2WConditionRootAdjacent_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (left right : Fin model.latent.count)
    (leftRelevant : rule2WConditionRootRelevant model G x z w assignment
      child left = true)
    (rightRelevant : rule2WConditionRootRelevant model G x z w assignment
      child right = true) :
    rule2WConditionRootAdjacent model G x z w assignment left right = true :=
  finAny_eq_true_of _ child
    (Bool.and_eq_true_iff.mpr ⟨leftRelevant, rightRelevant⟩)

/-- Every `Z`-relevant seed root lies in the generated component by a
reflexive bounded walk. -/
theorem rule2ZConditionLatentComponent_of_z_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true) :
    rule2ZConditionLatentComponent model G x z w assignment root = true := by
  apply finAny_eq_true_of _ root
  apply Bool.and_eq_true_iff.mpr
  refine ⟨relevant, ?_⟩
  have complete : forall latent : Fin model.latent.count,
      latent ∈ List.ofFn (fun i : Fin model.latent.count => i) :=
    fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
    (List.ofFn (fun latent : Fin model.latent.count => latent))
    (rule2WConditionRootAdjacent model G x z w assignment)
    finBeq_eq_true_iff complete
    (List.ofFn (fun latent : Fin model.latent.count => latent)).length
    root root).mpr
      (FiniteReachability.BoundedWalk.refl _ _ root)

/-- The generated rule-2 component is closed across every local-factor
adjacency edge. -/
theorem rule2ZConditionLatentComponent_closed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (left right : Fin model.latent.count)
    (leftIn : rule2ZConditionLatentComponent model G x z w assignment
      left = true)
    (edge : rule2WConditionRootAdjacent model G x z w assignment
      left right = true) :
    rule2ZConditionLatentComponent model G x z w assignment right = true := by
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule2ZConditionLatentComponent] using leftIn) with
    ⟨seed, seedData⟩
  rcases Bool.and_eq_true_iff.mp seedData with
    ⟨seedRelevant, seedReachesLeft⟩
  let roots := List.ofFn (fun latent : Fin model.latent.count => latent)
  let adjacent := rule2WConditionRootAdjacent model G x z w assignment
  have complete : forall latent : Fin model.latent.count, latent ∈ roots :=
    fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
  have seedToLeft : FiniteReachability.BoundedWalk adjacent roots.length
      seed left :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots adjacent
      finBeq_eq_true_iff complete roots.length seed left).mp
      (by simpa [roots, adjacent] using seedReachesLeft)
  have leftToRight : FiniteReachability.BoundedWalk adjacent 1 left right :=
    ⟨1, Nat.le_refl _,
      ⟨FiniteReachability.ExactWalk.step (by simpa [adjacent] using edge)
        (FiniteReachability.ExactWalk.refl right)⟩⟩
  have seedToRightReachable : FiniteReachability.Reachable adjacent seed right :=
    FiniteReachability.Reachable.of_bounded
      (FiniteReachability.BoundedWalk.trans seedToLeft leftToRight)
  have seedToRight : FiniteReachability.BoundedWalk adjacent roots.length
      seed right :=
    FiniteReachability.boundedWalk_of_reachable finBeq roots adjacent
      finBeq_eq_true_iff complete seedToRightReachable
  have found : FiniteReachability.within finBeq roots adjacent roots.length
      seed right = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots adjacent
      finBeq_eq_true_iff complete roots.length seed right).mpr seedToRight
  apply (finAny_eq_true_iff _).mpr
  exact ⟨seed, Bool.and_eq_true_iff.mpr ⟨seedRelevant,
    by simpa [roots, adjacent] using found⟩⟩

/-- Every root of a selected rule-2 factor belongs to the generated
component. -/
theorem rule2WConditionSelected_root_in_component
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (selected : rule2WConditionSelected model G x z w assignment child =
      true)
    (relevant : rule2WConditionRootRelevant model G x z w assignment
      child root = true) :
    rule2ZConditionLatentComponent model G x z w assignment root = true := by
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule2WConditionSelected] using selected) with
    ⟨pivot, pivotData⟩
  rcases Bool.and_eq_true_iff.mp pivotData with
    ⟨pivotRelevant, pivotInComponent⟩
  exact rule2ZConditionLatentComponent_closed model G x z w assignment
    pivot root pivotInComponent
    (rule2WConditionRootAdjacent_of_relevant model G x z w assignment
      child pivot root pivotRelevant relevant)

/-- Every root of a residual rule-2 factor lies outside the generated
component. -/
theorem rule2WConditionResidual_root_outside_component
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (residual : rule2WConditionResidual model G x z w assignment child =
      true)
    (relevant : rule2WConditionRootRelevant model G x z w assignment
      child root = true) :
    rule2ZConditionLatentComponent model G x z w assignment root = false := by
  have notSelected :
      rule2WConditionSelected model G x z w assignment child = false :=
    NodeSet.Disjoint.diff_right w
      (rule2WConditionSelected model G x z w assignment) child residual
  cases component :
      rule2ZConditionLatentComponent model G x z w assignment root with
  | false => rfl
  | true =>
      have selected :
          rule2WConditionSelected model G x z w assignment child = true :=
        finAny_eq_true_of _ root
          (Bool.and_eq_true_iff.mpr ⟨relevant, component⟩)
      rw [selected] at notSelected
      contradiction

theorem rule2WConditionSelected_subset_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.Subset (rule2WConditionSelected model G x z w assignment) w := by
  intro child selected
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule2WConditionSelected] using selected) with ⟨root, rootData⟩
  have relevant : rule2WConditionRootRelevant model G x z w assignment
      child root = true := (Bool.and_eq_true_iff.mp rootData).1
  exact (Bool.and_eq_true_iff.mp relevant).1

/-- The selected and residual local-factor blocks cover all of `W`. -/
theorem rule2WConditionSplit_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.union (rule2WConditionSelected model G x z w assignment)
      (rule2WConditionResidual model G x z w assignment) = w := by
  funext child
  have subset := rule2WConditionSelected_subset_w model G x z w assignment
    child
  simp [rule2WConditionResidual, NodeSet.union, NodeSet.diff]
  cases hw : w child with
  | false =>
      cases hs : rule2WConditionSelected model G x z w assignment child with
      | false => rfl
      | true =>
          have impossible := subset hs
          rw [hw] at impossible
          contradiction
  | true =>
      cases rule2WConditionSelected model G x z w assignment child <;> rfl

/-- Assemble the full rule-2 conditional-independence witness from the local
`Z` component once graph separation has shown that every root needed by `Y`
lies outside that component.

All other routing facts are automatic: the `Z` cylinder seeds the component,
selected `W` factors are closed into it, and residual factors avoid it by
definition.  The four kernel-event equalities use the cross-intervention
factorization above plus SCM composition after the displayed conditioning
cylinders hold. -/
def rule2PartitionWitness_of_local_condition_component
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (yAvoids : forall root,
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty
            (NodeSet.union (NodeSet.union x z) w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G
            (NodeSet.union (NodeSet.union x z) w) y) root = true ->
        rule2ZConditionLatentComponent model G x z w assignment root =
          false) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  let baseIntervention :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  let extendedIntervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z)
      NodeSet.empty).intervention assignment
  let zIntervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let yIntervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union (NodeSet.union x z) w)
      NodeSet.empty).intervention assignment
  let zRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z
  let yRelevant :=
    FiniteLatentSCM.ancestralInBar G
      (NodeSet.union (NodeSet.union x z) w) y
  let component :=
    rule2ZConditionLatentComponent model G x z w assignment
  let selectedW := rule2WConditionSelected model G x z w assignment
  let residualW := rule2WConditionResidual model G x z w assignment
  let zEvent : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn z assignment (model.evalUnder zIntervention roots)
  let yEvent : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment (model.evalUnder yIntervention roots)
  let selectedConditionEvent :=
    localConditionEvent model (NodeSet.union x z) w selectedW assignment
  let residualConditionEvent :=
    localConditionEvent model (NodeSet.union x z) w residualW assignment
  have selectedWSubset : NodeSet.Subset selectedW w := by
    simpa [selectedW] using
      rule2WConditionSelected_subset_w model G x z w assignment
  have residualWSubset : NodeSet.Subset residualW w := by
    dsimp [residualW]
    exact NodeSet.diff_subset_left w
      (rule2WConditionSelected model G x z w assignment)
  have covers : NodeSet.union selectedW residualW = w := by
    simpa [selectedW, residualW] using
      rule2WConditionSplit_union model G x z w assignment
  have zDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value component zEvent := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder zIntervention zRelevant)
      (selected' := component) zEvent ?_ ?_
    · intro root relevantRoot
      exact rule2ZConditionLatentComponent_of_z_relevant model G x z w
        assignment root (by
          simpa [zIntervention, zRelevant] using relevantRoot)
    · exact agreesOn_evalUnder_dependsOnSelected model zIntervention
        zRelevant z assignment (by
          dsimp [zIntervention, zRelevant]
          exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
            model G (NodeSet.union x w) z assignment) (by
          dsimp [zRelevant]
          exact FiniteLatentSCM.ancestralInBar_contains_targets G
            (NodeSet.union x w) z)
  have selectedConditionDepends :
      CanonicalFactorization.DependsOnSelected model.latent.count
        model.latent.Value component selectedConditionEvent := by
    dsimp [selectedConditionEvent]
    apply localConditionEvent_dependsOnSelected model G
    intro child childSelected root relevantRoot
    have childInW := selectedWSubset child childSelected
    have combined : rule2WConditionRootRelevant model G x z w assignment
        child root = true := by
      simp [rule2WConditionRootRelevant, childInW, relevantRoot]
    exact rule2WConditionSelected_root_in_component model G x z w
      assignment child root (by simpa [selectedW] using childSelected)
      combined
  have yDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value component yEvent := by
    exact agreesOn_evalUnder_dependsOnUnselected_of_relevance_avoids model
      component yIntervention yRelevant y assignment (by
        dsimp [yIntervention, yRelevant]
        exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union (NodeSet.union x z) w) y assignment) (by
        dsimp [yRelevant]
        exact FiniteLatentSCM.ancestralInBar_contains_targets G
          (NodeSet.union (NodeSet.union x z) w) y) (by
        intro root relevantRoot
        exact yAvoids root (by
          simpa [yIntervention, yRelevant] using relevantRoot))
  have residualConditionDepends :
      CanonicalFactorization.DependsOnUnselected model.latent.count
        model.latent.Value component residualConditionEvent := by
    dsimp [residualConditionEvent]
    apply localConditionEvent_dependsOnUnselected model G
    intro child childResidual root relevantRoot
    have childInW := residualWSubset child childResidual
    have combined : rule2WConditionRootRelevant model G x z w assignment
        child root = true := by
      simp [rule2WConditionRootRelevant, childInW, relevantRoot]
    exact rule2WConditionResidual_root_outside_component model G x z w
      assignment child root (by simpa [residualW] using childResidual)
      combined
  have wEventSplit : forall roots,
      Kernel.agreesOn w assignment
          (model.evalUnder extendedIntervention roots) =
        (selectedConditionEvent roots && residualConditionEvent roots) := by
    intro roots
    have full := agreesOn_evalUnder_eq_localConditionEvent model
      (NodeSet.union x z) w assignment roots
    have split := localConditionEvent_union model (NodeSet.union x z) w
      selectedW residualW assignment roots
    have selectedCover := congrArg
      (fun nodes => localConditionEvent model (NodeSet.union x z) w nodes
        assignment roots) covers
    have splitFullRaw :
        localConditionEvent model (NodeSet.union x z) w w assignment roots =
          (localConditionEvent model (NodeSet.union x z) w selectedW
              assignment roots &&
            localConditionEvent model (NodeSet.union x z) w residualW
              assignment roots) :=
      selectedCover.symm.trans split
    have splitFull :
        localConditionEvent model (NodeSet.union x z) w w assignment roots =
          (selectedConditionEvent roots && residualConditionEvent roots) := by
      simpa [selectedConditionEvent, residualConditionEvent] using splitFullRaw
    rw [full, splitFull]
  refine
    { selected := component
      selectedOutcome := zEvent
      selectedCondition := selectedConditionEvent
      unselectedOutcome := yEvent
      unselectedCondition := residualConditionEvent
      selectedOutcomeDepends := zDepends
      selectedConditionDepends := selectedConditionDepends
      unselectedOutcomeDepends := yDepends
      unselectedConditionDepends := residualConditionDepends
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.numeratorEvent,
      Probability.inter]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder baseIntervention roots) &&
        Kernel.agreesOn (NodeSet.union z w) assignment
          (model.evalUnder baseIntervention roots)) = _
    have composition := agreesOn_and_evalUnder_union_eq model x
      (NodeSet.union z w) y assignment roots
    have cross := agreesOn_rule2_cross_condition_factorization model
      x y z w assignment disjoint roots
    calc
      _ = (Kernel.agreesOn (NodeSet.union z w) assignment
            (model.evalUnder baseIntervention roots) &&
          Kernel.agreesOn y assignment
            (model.evalUnder baseIntervention roots)) := Bool.and_comm _ _
      _ = (Kernel.agreesOn (NodeSet.union z w) assignment
            (model.evalUnder baseIntervention roots) && yEvent roots) := by
          simpa [baseIntervention, yIntervention, yEvent,
            NodeSet.union_assoc] using composition
      _ = ((zEvent roots &&
            Kernel.agreesOn w assignment
              (model.evalUnder extendedIntervention roots)) &&
          yEvent roots) := by
          rw [show Kernel.agreesOn (NodeSet.union z w) assignment
              (model.evalUnder baseIntervention roots) =
                (zEvent roots && Kernel.agreesOn w assignment
                  (model.evalUnder extendedIntervention roots)) by
            simpa [baseIntervention, extendedIntervention, zIntervention,
              zEvent] using cross]
      _ = ((zEvent roots && selectedConditionEvent roots) &&
          (yEvent roots && residualConditionEvent roots)) := by
          rw [wEventSplit roots]
          ac_rfl
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.conditionEvent,
      Probability.inter]
    change Kernel.agreesOn w assignment
      (model.evalUnder extendedIntervention roots) = _
    exact wEventSplit roots
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.numeratorEvent,
      Probability.inter]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder extendedIntervention roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder extendedIntervention roots)) = _
    have composition := agreesOn_and_evalUnder_union_eq model
      (NodeSet.union x z) w y assignment roots
    calc
      _ = (Kernel.agreesOn w assignment
            (model.evalUnder extendedIntervention roots) &&
          Kernel.agreesOn y assignment
            (model.evalUnder extendedIntervention roots)) := Bool.and_comm _ _
      _ = (Kernel.agreesOn w assignment
            (model.evalUnder extendedIntervention roots) && yEvent roots) := by
          simpa [extendedIntervention, yIntervention, yEvent] using composition
      _ = (selectedConditionEvent roots &&
          (yEvent roots && residualConditionEvent roots)) := by
          rw [wEventSplit roots]
          ac_rfl
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.conditionEvent,
      Probability.inter]
    change Kernel.agreesOn (NodeSet.union z w) assignment
      (model.evalUnder baseIntervention roots) = _
    have cross := agreesOn_rule2_cross_condition_factorization model
      x y z w assignment disjoint roots
    calc
      _ = (zEvent roots && Kernel.agreesOn w assignment
          (model.evalUnder extendedIntervention roots)) := by
            simpa [baseIntervention, extendedIntervention, zIntervention,
              zEvent] using cross
      _ = ((zEvent roots && selectedConditionEvent roots) &&
          residualConditionEvent roots) := by
            rw [wEventSplit roots]
            ac_rfl

/-- An observed route witnessing relevance of one concrete root to a local
rule-2 `W` factor.  The route is embedded in
`G_{̅X̲Z}`; every proper route vertex is open given `X ∪ W`, while the
terminal factor vertex may itself be conditioned. -/
def Rule2LocalConditionRootWalk (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (child : Fin S.count) (root : Fin model.latent.count) : Prop :=
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      (GraphMutilation.barUnderline x z).removeIncoming source = false /\
        Exists fun length : Nat =>
          Exists fun walk : FiniteReachability.ExactWalk
            (G.observedDirectedEdge (GraphMutilation.barUnderline x z))
            length source child =>
            forall node, node ∈ walk.nodes -> node ≠ child ->
              ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
                false

/-- Unpack local rule-2 factor relevance into its route in
`G_{̅X̲Z}`.

The original route cuts `X ∪ Z` and the earlier `W` prefix.  Removing only
`X ∪ Z` embeds it in `G_{̅(X ∪ Z)}`.  Its free source and every later
route vertex lie outside `Z`, so the route also survives the outgoing `Z`
cut.  Topological prefix arguments make every proper vertex open under the
published conditioner `X ∪ W`. -/
def rule2LocalConditionRootWalk_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (relevant : rule2WConditionRootRelevant model G x z w assignment
      child root = true) :
    Rule2LocalConditionRootWalk model G x z w child root := by
  have parts := Bool.and_eq_true_iff.mp relevant
  have childInW : w child = true := parts.1
  let baseAction := NodeSet.union x z
  let action := localConditionAction baseAction w child
  let intervention :=
    (Kernel.mk NodeSet.empty action NodeSet.empty).intervention assignment
  let ancestors := FiniteLatentSCM.ancestralInBar G action
    (NodeSet.singleton child)
  rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
      root).mp (by simpa [intervention, ancestors, action, baseAction] using
        parts.2) with
    ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
  rcases (G.observedAncestorOf_eq_true_iff (GraphMutilation.bar action)
      (NodeSet.singleton child) source).mp (by
        simpa [FiniteLatentSCM.ancestralInBar, ancestors, action] using
          sourceAncestor) with ⟨target, targetSelected, bounded⟩
  have targetEq : target = child :=
    (NodeSet.singleton_eq_true_iff child target).mp targetSelected
  subst target
  rcases bounded with ⟨length, _bound, exactWalk⟩
  rcases exactWalk with ⟨walk⟩
  have baseSubset : NodeSet.Subset baseAction action := by
    intro node selected
    simp [action, localConditionAction, NodeSet.union, selected]
  let barUnionWalk := FiniteLatentSCM.remapBarWalk_of_incoming_subset G
    baseSubset walk
  have barUnionNodes : barUnionWalk.nodes = walk.nodes := by
    simpa [barUnionWalk] using
      FiniteLatentSCM.remapBarWalk_of_incoming_subset_nodes G baseSubset walk
  have sourceOutsideAction : action source = false := by
    simpa [intervention, Kernel.intervention] using sourceFree
  have sourceOutsideBase : baseAction source = false := by
    cases selected : baseAction source with
    | false => rfl
    | true =>
        have inAction : action source = true := by
          simp [action, localConditionAction, NodeSet.union, selected]
        rw [inAction] at sourceOutsideAction
        contradiction
  have noZ : forall node, node ∈ barUnionWalk.nodes -> z node = false := by
    intro node member
    exact FiniteLatentSCM.barUnion_walk_vertices_not_in_z G x z
      barUnionWalk (by simpa [baseAction] using sourceOutsideBase) member
  let mapped := FiniteLatentSCM.remapBarUnionWalkToBarUnderline G x z
    barUnionWalk noZ
  have mappedNodes : mapped.nodes = walk.nodes := by
    calc
      mapped.nodes = barUnionWalk.nodes := by simp [mapped]
      _ = walk.nodes := barUnionNodes
  have sourceOutsideX : x source = false := by
    have outside := Bool.or_eq_false_iff.mp (by
      simpa [baseAction, NodeSet.union] using sourceOutsideBase)
    exact outside.1
  have sourceIncoming :
      (GraphMutilation.barUnderline x z).removeIncoming source = false := by
    simpa [GraphMutilation.barUnderline] using sourceOutsideX
  refine ⟨source, sourceIncident, sourceIncoming, length, mapped, ?_⟩
  intro node member notTarget
  have originalMember : node ∈ walk.nodes := by
    rw [mappedNodes] at member
    exact member
  by_cases atSource : node = source
  · subst node
    exact localConditionWalk_source_open_of_free G baseAction x w
      (NodeSet.subset_union_left x z) assignment child walk notTarget (by
        simpa [intervention, action] using sourceFree)
  · exact localConditionWalk_internal_open G baseAction x w
      (NodeSet.subset_union_left x z) child walk originalMember atSource
      notTarget

/-- A free ancestral observed representative showing that one concrete root
lies on the `Z` side of rule 2's moral separator in `G_{̅X̲Z}`. -/
def Rule2RootMoralZWitness (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (root : Fin model.latent.count) : Prop :=
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      mutilation.removeIncoming source = false /\
        G.ancestorOf mutilation targets (.observed source) = true /\
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
              false /\
            G.moralLeftSide mutilation z y (NodeSet.union x w)
              (.observed source) = true

/-- Every root needed by the `Z` cylinder under `do(X ∪ W)` has a free
representative on the `Z` moral side in `G_{̅X̲Z}`.

A minimal ancestry route into `Z` first embeds from `G_{̅(X ∪ W)}` into
`G_{̅X}`.  Minimality ensures that no proper route vertex belongs to `Z`,
so deleting arrows out of `Z` preserves the route. -/
theorem rule2RootMoralZWitness_of_z_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z) root = true) :
    Rule2RootMoralZWitness model G x y z w root := by
  let intervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let ancestors := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) z
  rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
      root).mp (by simpa [intervention, ancestors] using relevant) with
    ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar (NodeSet.union x w)) z source (by
        simpa [FiniteLatentSCM.ancestralInBar, ancestors] using
          sourceAncestor) with
    ⟨zEnd, zEndInZ, length, walk, walkSimple, minimal⟩
  have xSubset : NodeSet.Subset x (NodeSet.union x w) :=
    NodeSet.subset_union_left x w
  let barXWalk := FiniteLatentSCM.remapBarWalk_of_incoming_subset G xSubset
    walk
  have barXNodes : barXWalk.nodes = walk.nodes := by
    simpa [barXWalk] using
      FiniteLatentSCM.remapBarWalk_of_incoming_subset_nodes G xSubset walk
  have barXSimple : barXWalk.nodes.Nodup := by
    rw [barXNodes]
    exact walkSimple
  have barXAvoid : forall node, node ∈ barXWalk.nodes -> node ≠ zEnd ->
      z node = false := by
    intro node member different
    rw [barXNodes] at member
    exact FiniteReachability.ExactWalk.not_mem_targets_of_minimal_internal
      walk minimal member different
  let mapped := FiniteLatentSCM.remapMinimalBarWalkToBarUnderline G x z
    barXWalk barXSimple barXAvoid
  have mappedNodes : mapped.nodes = walk.nodes := by
    calc
      mapped.nodes = barXWalk.nodes := by simp [mapped]
      _ = walk.nodes := barXNodes
  have walkOpen : forall node, node ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    by_cases atSource : node = source
    · subst node
      exact (FiniteLatentSCM.intervention_none_iff_unblocked
        (NodeSet.union x w) assignment source).mp (by
          simpa [intervention] using sourceFree)
    · have incoming :=
        PathSpecification.directed_walk_mem_not_removeIncoming G
          (GraphMutilation.bar (NodeSet.union x w)) walk member atSource
      simpa [GraphMutilation.bar, ObservedGraph.blockedBy] using incoming
  have mappedOpen : forall node, node ∈ mapped.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    rw [mappedNodes] at member
    exact walkOpen node member
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  have zEndTarget : targets zEnd = true := by
    simp [targets, NodeSet.union, zEndInZ]
  have mappedAncestor : forall node, node ∈ mapped.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      mapped zEndTarget member
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have sourceToZ := moralLeftSide_eq_of_open_observed_walk G mutilation
    z y (NodeSet.union x w) mapped mappedOpen (by
      simpa [targets] using mappedAncestor)
  have zOpen := FiniteLatentSCM.blockedBy_false_of_mem_z x y z w disjoint
    zEndInZ
  have zSide := G.moralLeftSide_of_left mutilation z y
    (NodeSet.union x w) zEnd zEndInZ (by
      simpa [ObservedGraph.blockedBy] using zOpen)
  have sourceOutsideX : x source = false := by
    have sourceOpen := mappedOpen source mapped.mem_source
    have outside : NodeSet.union x w source = false := by
      simpa [ObservedGraph.blockedBy] using sourceOpen
    exact (Bool.or_eq_false_iff.mp (by
      simpa [NodeSet.union] using outside)).1
  have sourceIncoming : mutilation.removeIncoming source = false := by
    simpa [mutilation, GraphMutilation.barUnderline] using sourceOutsideX
  exact ⟨source, sourceIncident, sourceIncoming,
    mappedAncestor source mapped.mem_source,
    mappedOpen source mapped.mem_source, sourceToZ.trans zSide⟩

/-- An open ancestral parent of a local rule-2 conditioning factor on the
`Z` side of the canonical separator in `G_{̅X̲Z}`.

This is the factor-level invariant carried through the root component.  The
factor child is conditioned and therefore is not itself open; recording an
open parent is exactly what lets moralization transport the side label across
another root that affects the same local factor. -/
def Rule2FactorMoralZParent (G : ObservedGraph S)
    (x y z w : NodeSet S) (child : Fin S.count) : Prop :=
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  Exists fun parent : SeparationNode S =>
    G.expandedMutilatedEdge mutilation parent (.observed child) = true /\
      G.ancestorOf mutilation targets parent = true /\
        ObservedGraph.blockedBy (NodeSet.union x w) parent = false /\
          G.moralLeftSide mutilation z y (NodeSet.union x w) parent = true

/-- Moralization at a conditioned rule-2 factor transfers its stored `Z`-side
label to every other open ancestral parent of the same child.

`SeparationNode` equality is split through its explicit Boolean code.  This
keeps the argument constructive: no proposition-level decidable equality,
excluded middle, or choice is introduced. -/
theorem Rule2FactorMoralZParent.marries
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (child : Fin S.count)
    (witness : Rule2FactorMoralZParent G x y z w child)
    (childConditioned : NodeSet.union x w child = true)
    (other : SeparationNode S)
    (otherEdge : G.expandedMutilatedEdge
      (GraphMutilation.barUnderline x z) other (.observed child) = true)
    (otherAncestor : G.ancestorOf (GraphMutilation.barUnderline x z)
      (NodeSet.union z (NodeSet.union y (NodeSet.union x w))) other = true)
    (otherOpen : ObservedGraph.blockedBy (NodeSet.union x w) other = false) :
    G.moralLeftSide (GraphMutilation.barUnderline x z) z y
      (NodeSet.union x w) other = true := by
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  rcases witness with
    ⟨parent, parentEdge, parentAncestor, parentOpen, parentSide⟩
  have equalityCases : SeparationNode.beq parent other = true ∨
      SeparationNode.beq parent other = false := by
    cases value : SeparationNode.beq parent other with
    | false => exact Or.inr rfl
    | true => exact Or.inl rfl
  rcases equalityCases with sameValue | sameValue
  · have same := (SeparationNode.beq_eq_true_iff parent other).mp sameValue
    exact Eq.mp (congrArg (fun node =>
      G.moralLeftSide mutilation z y (NodeSet.union x w) node = true) same)
      parentSide
  · have different : parent ≠ other :=
      (SeparationNode.beq_eq_false_iff parent other).mp sameValue
    have conditionedPart : x child = true ∨ w child = true :=
      Bool.or_eq_true_iff.mp (by
        simpa [NodeSet.union] using childConditioned)
    have childTarget : targets child = true := by
      rcases conditionedPart with childInX | childInW
      · simp [targets, NodeSet.union, childInX]
      · simp [targets, NodeSet.union, childInW]
    have childAncestor : G.ancestorOf mutilation targets
        (.observed child) = true :=
      G.ancestorOf_target mutilation targets childTarget
    have collider : PathSpecification.IsCollider G mutilation parent
        (.observed child) other := ⟨parentEdge, otherEdge⟩
    have ancestralMoral := G.ancestralMoralEdge_of_collider mutilation
      targets parentAncestor childAncestor otherAncestor different collider
    have moral := G.moralOpenEdge_of_ancestral mutilation targets
      (NodeSet.union x w) parentOpen otherOpen ancestralMoral
    have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation z y
      (NodeSet.union x w) moral
    rw [parentSide] at sameSide
    exact sameSide.symm

/-- A rule-2 root already represented on the `Z` moral side supplies a
`Z`-side parent for every local `W` factor it affects.

For a nontrivial relevance route, the final directed predecessor is the
required factor parent.  If the route is reflexive, projection materializes
the shared concrete root as the canonical latent-pair vertex joining the
stored `Z` representative directly to the factor child. -/
theorem rule2FactorMoralZParent_of_root_witness
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (rootWitness : Rule2RootMoralZWitness model G x y z w root)
    (relevant : rule2WConditionRootRelevant model G x z w assignment
      child root = true) :
    Rule2FactorMoralZParent G x y z w child := by
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  rcases rootWitness with
    ⟨zSource, zIncident, zIncoming, zAncestor, zOpen, zSide⟩
  rcases rule2LocalConditionRootWalk_of_relevant model G x z w assignment
      child root relevant with
    ⟨routeSource, routeIncident, routeIncoming, routeLength, route,
      routeProperOpen⟩
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp relevant).1
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  by_cases routeReflexive : routeSource = child
  · subst routeSource
    have zDifferent : zSource ≠ child := by
      intro same
      subst zSource
      have childOpen : NodeSet.union x w child = false := by
        simpa [ObservedGraph.blockedBy] using zOpen
      rw [childConditioned] at childOpen
      contradiction
    have bidirected := model.bidirected_of_shared_latent G projected root
      zDifferent zIncident routeIncident
    let latent : SeparationNode S := .latentPair zSource child
    have zIncoming' : mutilation.removeIncoming zSource = false := by
      simpa [mutilation] using zIncoming
    have childIncoming' : mutilation.removeIncoming child = false := by
      simpa [mutilation] using routeIncoming
    have edgeZ : G.expandedMutilatedEdge mutilation latent
        (.observed zSource) = true := by
      have self : finBeq zSource zSource = true :=
        (finBeq_eq_true_iff zSource zSource).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        zIncoming', self]
    have edgeChild : G.expandedMutilatedEdge mutilation latent
        (.observed child) = true := by
      have self : finBeq child child = true :=
        (finBeq_eq_true_iff child child).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        childIncoming', self]
    have latentAncestor : G.ancestorOf mutilation targets latent = true :=
      G.ancestorOf_prepend mutilation targets edgeZ zAncestor
    have zLatentMoral : G.MoralOpenEdge mutilation targets
        (NodeSet.union x w) (.observed zSource) latent = true :=
      G.moralOpenEdge_of_ancestral mutilation targets (NodeSet.union x w)
        zOpen (by dsimp [latent]; rfl)
        (G.ancestralMoralEdge_of_adjacent mutilation targets zAncestor
          latentAncestor (Or.inr edgeZ))
    have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation z y
      (NodeSet.union x w) zLatentMoral
    have latentSide : G.moralLeftSide mutilation z y (NodeSet.union x w)
        latent = true := by
      rw [zSide] at sameSide
      exact sameSide.symm
    exact ⟨latent, edgeChild, latentAncestor, by dsimp [latent]; rfl,
      latentSide⟩
  · have routeOpen := routeProperOpen routeSource route.mem_source
      routeReflexive
    have routeObservedAncestor := G.observedAncestorOf_of_mem_walk
      mutilation targets route childTarget route.mem_source
    have routeAncestor := FiniteLatentSCM.ancestorOf_of_observedAncestorOf
      G mutilation targets routeSource routeObservedAncestor
    have routeSameSide :=
      FiniteLatentSCM.moralLeftSide_eq_of_shared_latent model G projected
        mutilation z y (NodeSet.union x w) root zSource routeSource
        zIncident routeIncident zIncoming routeIncoming zAncestor
        routeAncestor (by
          simpa [ObservedGraph.blockedBy] using zOpen) (by
          simpa [ObservedGraph.blockedBy] using routeOpen)
    have routeSide : G.moralLeftSide mutilation z y (NodeSet.union x w)
        (.observed routeSource) = true := by
      rw [zSide] at routeSameSide
      exact routeSameSide.symm
    rcases exists_observedDirectedWalk_prefix_last G mutilation route
        routeReflexive with
      ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
    have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
        node ≠ child := by
      intro node member equal
      have parentDirected : S.directed parent child = true :=
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
      have parentEarlier := S.directed_earlier parentDirected
      have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
        prefixWalk member
      subst node
      exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
    have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
        ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
          false := by
      intro node member
      exact routeProperOpen node (prefixSubset node member)
        (prefixNotChild node member)
    have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
        G.ancestorOf mutilation targets (.observed node) = true := by
      intro node member
      have observed := G.observedAncestorOf_of_mem_walk mutilation targets
        route childTarget (prefixSubset node member)
      exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
        targets node observed
    have routeToParent := moralLeftSide_eq_of_open_observed_walk G
      mutilation z y (NodeSet.union x w) prefixWalk prefixOpen (by
        simpa [targets] using prefixAncestor)
    have parentSide : G.moralLeftSide mutilation z y (NodeSet.union x w)
        (.observed parent) = true := by
      rw [routeSide] at routeToParent
      exact routeToParent.symm
    exact ⟨.observed parent, last,
      prefixAncestor parent prefixWalk.mem_target,
      prefixOpen parent prefixWalk.mem_target, parentSide⟩

/-- A nonincident root relevant to a rule-2 factor with a `Z`-side parent
obtains an ordinary observed `Z`-side representative from its nontrivial
relevance route. -/
theorem rule2RootMoralZWitness_of_factor_parent_relevant_not_incident
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (factorParent : Rule2FactorMoralZParent G x y z w child)
    (relevant : rule2WConditionRootRelevant model G x z w assignment
      child root = true)
    (notIncident : model.latent.incident root child = false) :
    Rule2RootMoralZWitness model G x y z w root := by
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  rcases rule2LocalConditionRootWalk_of_relevant model G x z w assignment
      child root relevant with
    ⟨source, sourceIncident, sourceIncoming, length, route,
      routeProperOpen⟩
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp relevant).1
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  have sourceDifferent : source ≠ child := by
    intro equal
    subst source
    rw [sourceIncident] at notIncident
    contradiction
  have sourceOpen := routeProperOpen source route.mem_source sourceDifferent
  have sourceObservedAncestor := G.observedAncestorOf_of_mem_walk
    mutilation targets route childTarget route.mem_source
  have sourceAncestor := FiniteLatentSCM.ancestorOf_of_observedAncestorOf
    G mutilation targets source sourceObservedAncestor
  rcases exists_observedDirectedWalk_prefix_last G mutilation route
      sourceDifferent with
    ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
  have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
      node ≠ child := by
    intro node member equal
    have parentDirected : S.directed parent child = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
    have parentEarlier := S.directed_earlier parentDirected
    have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
      prefixWalk member
    subst node
    exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
  have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) = false := by
    intro node member
    exact routeProperOpen node (prefixSubset node member)
      (prefixNotChild node member)
  have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      route childTarget (prefixSubset node member)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have parentSide := Rule2FactorMoralZParent.marries G x y z w child
    factorParent childConditioned (.observed parent) last
    (prefixAncestor parent prefixWalk.mem_target)
    (prefixOpen parent prefixWalk.mem_target)
  have sourceToParent := moralLeftSide_eq_of_open_observed_walk G
    mutilation z y (NodeSet.union x w) prefixWalk prefixOpen (by
      simpa [targets] using prefixAncestor)
  have sourceSide : G.moralLeftSide mutilation z y (NodeSet.union x w)
      (.observed source) = true := by
    rw [parentSide] at sourceToParent
    exact sourceToParent
  exact ⟨source, sourceIncident, sourceIncoming, sourceAncestor,
    sourceOpen, sourceSide⟩

/-- A free ancestral observed representative showing that one concrete root
lies on the `Y` side, i.e. outside the `Z` moral component, for rule 2. -/
def Rule2RootMoralYWitness (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (root : Fin model.latent.count) : Prop :=
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      mutilation.removeIncoming source = false /\
        G.ancestorOf mutilation targets (.observed source) = true /\
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
              false /\
            G.moralLeftSide mutilation z y (NodeSet.union x w)
              (.observed source) = false

/-- Every root needed by `Y` after intervening on `X ∪ Z ∪ W` has a
representative on the `Y` side of the rule-2 separator.  Its ancestry route
has no `Z` vertex because `Z` is in the incoming cut, and therefore embeds
into `G_{̅X̲Z}` edge for edge. -/
theorem rule2RootMoralYWitness_of_y_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty
        (NodeSet.union (NodeSet.union x z) w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G
        (NodeSet.union (NodeSet.union x z) w) y) root = true) :
    Rule2RootMoralYWitness model G x y z w root := by
  let fullAction := NodeSet.union (NodeSet.union x z) w
  let intervention :=
    (Kernel.mk NodeSet.empty fullAction NodeSet.empty).intervention assignment
  let ancestors := FiniteLatentSCM.ancestralInBar G fullAction y
  rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
      root).mp (by simpa [intervention, ancestors, fullAction] using relevant)
      with ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar fullAction) y source (by
        simpa [FiniteLatentSCM.ancestralInBar, ancestors] using
          sourceAncestor) with
    ⟨yEnd, yEndInY, length, walk, walkSimple, _minimal⟩
  have xzSubset : NodeSet.Subset (NodeSet.union x z) fullAction := by
    exact NodeSet.subset_union_left (NodeSet.union x z) w
  let barXZWalk := FiniteLatentSCM.remapBarWalk_of_incoming_subset G
    xzSubset walk
  have barXZNodes : barXZWalk.nodes = walk.nodes := by
    simpa [barXZWalk] using
      FiniteLatentSCM.remapBarWalk_of_incoming_subset_nodes G xzSubset walk
  have sourceOutsideFull : fullAction source = false := by
    simpa [intervention, Kernel.intervention] using sourceFree
  have sourceOutsideXZ : NodeSet.union x z source = false := by
    cases selected : NodeSet.union x z source with
    | false => rfl
    | true =>
        have inFull : fullAction source = true := by
          exact NodeSet.subset_union_left (NodeSet.union x z) w source
            selected
        rw [inFull] at sourceOutsideFull
        contradiction
  have noZ : forall node, node ∈ barXZWalk.nodes -> z node = false := by
    intro node member
    exact FiniteLatentSCM.barUnion_walk_vertices_not_in_z G x z barXZWalk
      sourceOutsideXZ member
  let mapped := FiniteLatentSCM.remapBarUnionWalkToBarUnderline G x z
    barXZWalk noZ
  have mappedNodes : mapped.nodes = walk.nodes := by
    calc
      mapped.nodes = barXZWalk.nodes := by simp [mapped]
      _ = walk.nodes := barXZNodes
  have walkOpen : forall node, node ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    have outsideFull : fullAction node = false := by
      by_cases atSource : node = source
      · subst node
        exact sourceOutsideFull
      · have incoming :=
          PathSpecification.directed_walk_mem_not_removeIncoming G
            (GraphMutilation.bar fullAction) walk member atSource
        simpa [GraphMutilation.bar] using incoming
    have outsideX : x node = false := by
      cases selected : x node with
      | false => rfl
      | true =>
          have inFull : fullAction node = true := by
            simp [fullAction, NodeSet.union, selected]
          rw [inFull] at outsideFull
          contradiction
    have outsideW : w node = false := by
      cases selected : w node with
      | false => rfl
      | true =>
          have inFull : fullAction node = true := by
            simp [fullAction, NodeSet.union, selected]
          rw [inFull] at outsideFull
          contradiction
    simp [ObservedGraph.blockedBy, NodeSet.union, outsideX, outsideW]
  have mappedOpen : forall node, node ∈ mapped.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    rw [mappedNodes] at member
    exact walkOpen node member
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  have yEndTarget : targets yEnd = true := by
    simp [targets, NodeSet.union, yEndInY]
  have mappedAncestor : forall node, node ∈ mapped.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      mapped yEndTarget member
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have sourceToY := moralLeftSide_eq_of_open_observed_walk G mutilation
    z y (NodeSet.union x w) mapped mappedOpen (by
      simpa [targets] using mappedAncestor)
  have yOpen := FiniteLatentSCM.blockedBy_false_of_mem_y x y z w disjoint
    yEndInY
  have ySide : G.moralLeftSide mutilation z y (NodeSet.union x w)
      (.observed yEnd) = false :=
    G.moralLeftSide_not_of_right mutilation z y (NodeSet.union x w)
      (PathSpecification.PathDSeparated.symm separated) yEnd yEndInY (by
        simpa [ObservedGraph.blockedBy] using yOpen)
  have sourceOutsideX : x source = false := by
    have sourceOpen := mappedOpen source mapped.mem_source
    have outside : NodeSet.union x w source = false := by
      simpa [ObservedGraph.blockedBy] using sourceOpen
    exact (Bool.or_eq_false_iff.mp (by
      simpa [NodeSet.union] using outside)).1
  have sourceIncoming : mutilation.removeIncoming source = false := by
    simpa [mutilation, GraphMutilation.barUnderline] using sourceOutsideX
  exact ⟨source, sourceIncident, sourceIncoming,
    mappedAncestor source mapped.mem_source,
    mappedOpen source mapped.mem_source, sourceToY.trans ySide⟩

/-- One concrete latent root cannot have free ancestral representatives on
opposite sides of the rule-2 moral separator.  Projection joins distinct
representatives through the canonical latent-pair vertex; the shared-root
side lemma also covers the reflexive case constructively. -/
theorem rule2RootMoralWitnesses_disjoint
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (root : Fin model.latent.count)
    (zWitness : Rule2RootMoralZWitness model G x y z w root)
    (yWitness : Rule2RootMoralYWitness model G x y z w root) :
    False := by
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  rcases zWitness with
    ⟨zSource, zIncident, zIncoming, zAncestor, zOpen, zSide⟩
  rcases yWitness with
    ⟨ySource, yIncident, yIncoming, yAncestor, yOpen, ySide⟩
  have sameSide := FiniteLatentSCM.moralLeftSide_eq_of_shared_latent
    model G projected mutilation z y (NodeSet.union x w) root
    zSource ySource zIncident yIncident zIncoming yIncoming zAncestor
    yAncestor (by simpa [ObservedGraph.blockedBy] using zOpen) (by
      simpa [ObservedGraph.blockedBy] using yOpen)
  rw [zSide, ySide] at sameSide
  contradiction

/-- Every conditioned `W` vertex survives the incoming cut of
`G_{̅X̲Z}`.  Rule 2 removes incoming arrows only at `X`; four-way
disjointness therefore supplies the fact directly. -/
theorem rule2_w_not_removeIncoming
    (x y z w : NodeSet S) (disjoint : FourWayDisjoint x y z w)
    (child : Fin S.count) (childInW : w child = true) :
    (GraphMutilation.barUnderline x z).removeIncoming child = false := by
  have outsideX : x child = false := disjoint.xw.symm child childInW
  simpa [GraphMutilation.barUnderline] using outsideX

/-- A local rule-2 factor carrying a `Z`-side parent cannot also be affected
by a root needed by the `Y` cylinder.

For a nonincident root, its relevance route gives an ordinary `Z`-side root
witness, contradicting the `Y` witness.  Under direct incidence, projection
creates a latent-pair parent from the factor child to the open `Y`
representative.  Moralizing at the conditioned child then assigns that
latent parent both Boolean side labels. -/
theorem Rule2FactorMoralZParent.excludes_y_relevant_root
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    (child : Fin S.count) (root : Fin model.latent.count)
    (factorParent : Rule2FactorMoralZParent G x y z w child)
    (factorRelevant : rule2WConditionRootRelevant model G x z w assignment
      child root = true)
    (yRelevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty
        (NodeSet.union (NodeSet.union x z) w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G
        (NodeSet.union (NodeSet.union x z) w) y) root = true) :
    False := by
  have yWitness := rule2RootMoralYWitness_of_y_relevant model G
    x y z w assignment disjoint separated root yRelevant
  cases incident : model.latent.incident root child with
  | false =>
      have zWitness :=
        rule2RootMoralZWitness_of_factor_parent_relevant_not_incident
          model G x y z w assignment child root factorParent factorRelevant
          incident
      exact rule2RootMoralWitnesses_disjoint model G projected x y z w root
        zWitness yWitness
  | true =>
      let mutilation := GraphMutilation.barUnderline x z
      let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
      rcases yWitness with
        ⟨source, sourceIncident, sourceIncoming, sourceAncestor, sourceOpen,
          sourceSide⟩
      have childInW : w child = true :=
        (Bool.and_eq_true_iff.mp factorRelevant).1
      have childConditioned : NodeSet.union x w child = true := by
        simp [NodeSet.union, childInW]
      have sourceDifferent : child ≠ source := by
        intro equal
        subst source
        have childOpen : NodeSet.union x w child = false := by
          simpa [ObservedGraph.blockedBy] using sourceOpen
        rw [childConditioned] at childOpen
        contradiction
      have bidirected := model.bidirected_of_shared_latent G projected root
        sourceDifferent incident sourceIncident
      let latent : SeparationNode S := .latentPair child source
      have childIncoming : mutilation.removeIncoming child = false := by
        simpa [mutilation] using
          rule2_w_not_removeIncoming x y z w disjoint child childInW
      have sourceIncoming' : mutilation.removeIncoming source = false := by
        simpa [mutilation] using sourceIncoming
      have edgeChild : G.expandedMutilatedEdge mutilation latent
          (.observed child) = true := by
        have self : finBeq child child = true :=
          (finBeq_eq_true_iff child child).mpr rfl
        simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
          childIncoming, self]
      have edgeSource : G.expandedMutilatedEdge mutilation latent
          (.observed source) = true := by
        have self : finBeq source source = true :=
          (finBeq_eq_true_iff source source).mpr rfl
        simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
          sourceIncoming', self]
      have latentAncestor : G.ancestorOf mutilation targets latent = true :=
        G.ancestorOf_prepend mutilation targets edgeSource sourceAncestor
      have latentSide := Rule2FactorMoralZParent.marries G x y z w child
        factorParent childConditioned latent edgeChild latentAncestor
        (by dsimp [latent]; rfl)
      have latentSourceMoral : G.MoralOpenEdge mutilation targets
          (NodeSet.union x w) latent (.observed source) = true :=
        G.moralOpenEdge_of_ancestral mutilation targets
          (NodeSet.union x w) (by dsimp [latent]; rfl) sourceOpen
          (G.ancestralMoralEdge_of_adjacent mutilation targets
            latentAncestor sourceAncestor (Or.inl edgeSource))
      have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation
        z y (NodeSet.union x w) latentSourceMoral
      rw [latentSide, sourceSide] at sameSide
      contradiction

/-- Transport a `Z`-side factor parent across one concrete latent root.

The four incidence cases are the local induction step for the finite Rule 2
root component.  A nonincident current factor exposes an observed `Z`-side
representative.  Direct incidence is represented by a projected latent-pair
parent, which transfers the side label either to the next route source or
directly to the next conditioned factor.  The statement has no depth bound
and extracts no data from an existential proposition. -/
theorem rule2FactorMoralZParent_transfer
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (fromChild toChild : Fin S.count) (root : Fin model.latent.count)
    (fromParent : Rule2FactorMoralZParent G x y z w fromChild)
    (fromRelevant : rule2WConditionRootRelevant model G x z w assignment
      fromChild root = true)
    (toRelevant : rule2WConditionRootRelevant model G x z w assignment
      toChild root = true) :
    Rule2FactorMoralZParent G x y z w toChild := by
  let mutilation := GraphMutilation.barUnderline x z
  let targets := NodeSet.union z (NodeSet.union y (NodeSet.union x w))
  have fromChildInW : w fromChild = true :=
    (Bool.and_eq_true_iff.mp fromRelevant).1
  have toChildInW : w toChild = true :=
    (Bool.and_eq_true_iff.mp toRelevant).1
  have fromChildConditioned : NodeSet.union x w fromChild = true := by
    simp [NodeSet.union, fromChildInW]
  have fromChildTarget : targets fromChild = true := by
    simp [targets, NodeSet.union, fromChildInW]
  cases fromIncident : model.latent.incident root fromChild with
  | false =>
      have rootWitness :=
        rule2RootMoralZWitness_of_factor_parent_relevant_not_incident
          model G x y z w assignment fromChild root fromParent fromRelevant
          fromIncident
      exact rule2FactorMoralZParent_of_root_witness model G projected
        x y z w assignment toChild root rootWitness toRelevant
  | true =>
      cases toIncident : model.latent.incident root toChild with
      | false =>
          rcases rule2LocalConditionRootWalk_of_relevant model G x z w
              assignment toChild root toRelevant with
            ⟨source, sourceIncident, sourceIncoming, length, route,
              routeProperOpen⟩
          have sourceDifferent : source ≠ toChild := by
            intro equal
            subst source
            rw [sourceIncident] at toIncident
            contradiction
          have sourceOpen := routeProperOpen source route.mem_source
            sourceDifferent
          have toChildTarget : targets toChild = true := by
            simp [targets, NodeSet.union, toChildInW]
          have sourceObservedAncestor := G.observedAncestorOf_of_mem_walk
            mutilation targets route toChildTarget route.mem_source
          have sourceAncestor :=
            FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
              targets source sourceObservedAncestor
          have sourceDifferentFromCurrent : source ≠ fromChild := by
            intro equal
            subst source
            have sourceOutside : NodeSet.union x w fromChild = false := by
              simpa [ObservedGraph.blockedBy] using sourceOpen
            rw [fromChildConditioned] at sourceOutside
            contradiction
          have bidirected := model.bidirected_of_shared_latent G projected
            root sourceDifferentFromCurrent.symm fromIncident sourceIncident
          let latent : SeparationNode S := .latentPair fromChild source
          have fromIncoming : mutilation.removeIncoming fromChild = false := by
            simpa [mutilation] using
              rule2_w_not_removeIncoming x y z w disjoint fromChild
                fromChildInW
          have sourceIncoming' : mutilation.removeIncoming source = false := by
            simpa [mutilation] using sourceIncoming
          have edgeFrom : G.expandedMutilatedEdge mutilation latent
              (.observed fromChild) = true := by
            have self : finBeq fromChild fromChild = true :=
              (finBeq_eq_true_iff fromChild fromChild).mpr rfl
            simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
              fromIncoming, self]
          have edgeSource : G.expandedMutilatedEdge mutilation latent
              (.observed source) = true := by
            have self : finBeq source source = true :=
              (finBeq_eq_true_iff source source).mpr rfl
            simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
              sourceIncoming', self]
          have latentAncestor : G.ancestorOf mutilation targets latent =
              true :=
            G.ancestorOf_prepend mutilation targets edgeSource sourceAncestor
          have latentSide := Rule2FactorMoralZParent.marries G x y z w
            fromChild fromParent fromChildConditioned latent edgeFrom
            latentAncestor (by dsimp [latent]; rfl)
          have latentSourceMoral : G.MoralOpenEdge mutilation targets
              (NodeSet.union x w) latent (.observed source) = true :=
            G.moralOpenEdge_of_ancestral mutilation targets
              (NodeSet.union x w) (by dsimp [latent]; rfl) sourceOpen
              (G.ancestralMoralEdge_of_adjacent mutilation targets
                latentAncestor sourceAncestor (Or.inl edgeSource))
          have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation
            z y (NodeSet.union x w) latentSourceMoral
          have sourceSide : G.moralLeftSide mutilation z y
              (NodeSet.union x w) (.observed source) = true := by
            rw [latentSide] at sameSide
            exact sameSide.symm
          have rootWitness : Rule2RootMoralZWitness model G x y z w root :=
            ⟨source, sourceIncident, sourceIncoming, sourceAncestor,
              sourceOpen, sourceSide⟩
          exact rule2FactorMoralZParent_of_root_witness model G projected
            x y z w assignment toChild root rootWitness toRelevant
      | true =>
          by_cases sameChild : fromChild = toChild
          · subst toChild
            exact fromParent
          · have bidirected := model.bidirected_of_shared_latent G
              projected root sameChild fromIncident toIncident
            let latent : SeparationNode S := .latentPair fromChild toChild
            have fromIncoming : mutilation.removeIncoming fromChild = false := by
              simpa [mutilation] using
                rule2_w_not_removeIncoming x y z w disjoint fromChild
                  fromChildInW
            have toIncoming : mutilation.removeIncoming toChild = false := by
              simpa [mutilation] using
                rule2_w_not_removeIncoming x y z w disjoint toChild
                  toChildInW
            have edgeFrom : G.expandedMutilatedEdge mutilation latent
                (.observed fromChild) = true := by
              have self : finBeq fromChild fromChild = true :=
                (finBeq_eq_true_iff fromChild fromChild).mpr rfl
              simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
                fromIncoming, self]
            have edgeTo : G.expandedMutilatedEdge mutilation latent
                (.observed toChild) = true := by
              have self : finBeq toChild toChild = true :=
                (finBeq_eq_true_iff toChild toChild).mpr rfl
              simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
                toIncoming, self]
            have fromAncestor : G.ancestorOf mutilation targets
                (.observed fromChild) = true :=
              G.ancestorOf_target mutilation targets fromChildTarget
            have latentAncestor : G.ancestorOf mutilation targets latent =
                true :=
              G.ancestorOf_prepend mutilation targets edgeFrom fromAncestor
            have latentSide := Rule2FactorMoralZParent.marries G x y z w
              fromChild fromParent fromChildConditioned latent edgeFrom
              latentAncestor (by dsimp [latent]; rfl)
            exact ⟨latent, edgeTo, latentAncestor,
              by dsimp [latent]; rfl, latentSide⟩

/-- Induction state at one Rule 2 latent root: the root affects a conditioned
local `W` factor that already carries a parent on the `Z` moral side. -/
def Rule2RootMoralZContact (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (root : Fin model.latent.count) : Prop :=
  Exists fun child : Fin S.count =>
    Rule2FactorMoralZParent G x y z w child /\
      rule2WConditionRootRelevant model G x z w assignment child root = true

/-- Propagate the Rule 2 factor contact through an arbitrary exact walk in
the local-factor root graph.  Each adjacency edge exposes a concrete `W`
factor affected by both endpoints, so the one-root transport theorem is the
inductive step. -/
theorem rule2RootMoralZContact_of_contact_walk
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    {length : Nat} {source terminal : Fin model.latent.count}
    (walk : FiniteReachability.ExactWalk
      (rule2WConditionRootAdjacent model G x z w assignment)
      length source terminal) :
    Rule2RootMoralZContact model G x y z w assignment source ->
      Rule2RootMoralZContact model G x y z w assignment terminal := by
  induction walk with
  | refl node =>
      intro contact
      exact contact
  | @step restLength current next terminal first rest ih =>
      intro contact
      rcases contact with ⟨fromChild, fromParent, fromRelevant⟩
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule2WConditionRootAdjacent] using first) with
        ⟨bridgeChild, bridgeData⟩
      rcases Bool.and_eq_true_iff.mp bridgeData with
        ⟨currentRelevant, nextRelevant⟩
      have bridgeParent := rule2FactorMoralZParent_transfer model G
        projected x y z w assignment disjoint fromChild bridgeChild current
        fromParent fromRelevant currentRelevant
      have nextContact : Rule2RootMoralZContact model G x y z w
          assignment next := ⟨bridgeChild, bridgeParent, nextRelevant⟩
      exact ih nextContact

/-- Every root needed by the `Y` cylinder lies outside the latent component
generated by `Z` and closed through Rule 2's local `W` factors.

Membership provides an exact finite walk from a `Z`-relevant seed.  A
reflexive walk contradicts the seed's `Z` witness and the terminal root's
`Y` witness directly.  A nontrivial walk initializes the factor-contact
invariant at its first shared factor, propagates it through the suffix, and
uses the terminal factor's `Z`-side parent to exclude `Y` relevance. -/
theorem rule2ZConditionLatentComponent_y_relevant_false
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    (root : Fin model.latent.count)
    (yRelevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty
        (NodeSet.union (NodeSet.union x z) w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G
        (NodeSet.union (NodeSet.union x z) w) y) root = true) :
    rule2ZConditionLatentComponent model G x z w assignment root = false := by
  cases selected :
      rule2ZConditionLatentComponent model G x z w assignment root with
  | false => rfl
  | true =>
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule2ZConditionLatentComponent] using selected) with
        ⟨seed, seedData⟩
      rcases Bool.and_eq_true_iff.mp seedData with
        ⟨seedRelevant, seedReaches⟩
      let roots := List.ofFn
        (fun latent : Fin model.latent.count => latent)
      let adjacent := rule2WConditionRootAdjacent model G x z w assignment
      have complete : forall latent : Fin model.latent.count,
          latent ∈ roots :=
        fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
      have bounded : FiniteReachability.BoundedWalk adjacent roots.length
          seed root :=
        (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots
          adjacent finBeq_eq_true_iff complete roots.length seed root).mp
          (by simpa [roots, adjacent] using seedReaches)
      rcases bounded with ⟨length, _bound, exactWalk⟩
      rcases exactWalk with ⟨walk⟩
      have seedWitness := rule2RootMoralZWitness_of_z_relevant model G
        x y z w assignment disjoint seed seedRelevant
      cases walk with
      | refl =>
          have terminalWitness := rule2RootMoralYWitness_of_y_relevant
            model G x y z w assignment disjoint separated root yRelevant
          exact (rule2RootMoralWitnesses_disjoint model G projected
            x y z w root seedWitness terminalWitness).elim
      | @step restLength seed next terminal first rest =>
          rcases (finAny_eq_true_iff _).mp (by
              simpa [adjacent, rule2WConditionRootAdjacent] using first) with
            ⟨bridgeChild, bridgeData⟩
          rcases Bool.and_eq_true_iff.mp bridgeData with
            ⟨seedFactorRelevant, nextRelevant⟩
          have bridgeParent := rule2FactorMoralZParent_of_root_witness
            model G projected x y z w assignment bridgeChild seed
            seedWitness seedFactorRelevant
          have nextContact : Rule2RootMoralZContact model G x y z w
              assignment next :=
            ⟨bridgeChild, bridgeParent, nextRelevant⟩
          have terminalContact :=
            rule2RootMoralZContact_of_contact_walk model G projected
              x y z w assignment disjoint rest nextContact
          rcases terminalContact with
            ⟨terminalChild, terminalParent, terminalRelevant⟩
          exact (Rule2FactorMoralZParent.excludes_y_relevant_root model G
            projected x y z w assignment disjoint separated terminalChild
            root terminalParent terminalRelevant yRelevant).elim

/-- The published Rule 2 path-separation condition now supplies the complete
conditional-independence partition for every compatible projected model.

The semantic factorization chooses the `Z`-generated root component.  The
preceding graph theorem proves exactly its sole remaining premise: every root
needed by `Y` after `do(X ∪ Z ∪ W)` lies in the complementary block. -/
def rule2PartitionWitness_of_path_projected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment :=
  rule2PartitionWitness_of_local_condition_component model G
    x y z w assignment disjoint (fun root yRelevant =>
      rule2ZConditionLatentComponent_y_relevant_false model G projected
        x y z w assignment disjoint separated root yRelevant)

/-- Empty-cylinder events are constant, so they depend on no coordinates. -/
theorem agreesOn_empty_eq_true
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (assignment : S.Assignment) (roots : model.latent.Assignment) :
    Kernel.agreesOn NodeSet.empty assignment
      (model.evalUnder intervention roots) = true := by
  unfold Kernel.agreesOn NodeSet.empty
  refine (finAll_eq_true_iff _).mpr ?_
  intro _i
  simp

/-- A latent is shared between `An(Z)` under `do(X)` and `An(W)` under
`do(X ∪ Z)`.  When this is false, the whole of `W` can sit with `Y` on
the unselected side of the rule-2 partition. -/
def rule2WMeetsZAncestral (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z) root &&
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root)

/-- Ancestral overlap with `W` is vacuous when `W` is empty. -/
theorem rule2WMeetsZAncestral_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true) :
    rule2WMeetsZAncestral model G x z w assignment = false := by
  have hw' : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  subst hw'
  refine (finAny_eq_false_iff _).mpr ?_
  intro root
  have hrel :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            NodeSet.empty) root = false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      model.latentRelevantUnder_empty
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        root
  simp [hrel]

/-- The displayed meet is exactly a shared latent of the two ancestral
families. -/
theorem rule2WMeetsZAncestral_eq_true_iff
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment) :
    rule2WMeetsZAncestral model G x z w assignment = true ↔
      Exists fun root : Fin model.latent.count =>
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true ∧
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root =
              true := by
  constructor
  · intro hmeet
    rcases (finAny_eq_true_iff _).mp (by
      simpa [rule2WMeetsZAncestral] using hmeet) with ⟨root, hroot⟩
    exact ⟨root, Bool.and_eq_true_iff.mp hroot⟩
  · rintro ⟨root, hZ, hW⟩
    apply (finAny_eq_true_iff _).mpr
    refine ⟨root, ?_⟩
    exact Bool.and_eq_true_iff.mpr ⟨hZ, hW⟩

/-- Rule 2 when `W` shares no latent with `An(Z)`: `W` under `do(X ∪ Z)`
depends only on coordinates complementary to those `An(Z)` latents. -/
theorem agreesOn_rule2W_dependsOnUnselected_of_avoids_z
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) w assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) w assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) w w
      (fun _i hi => hi))
    left right
  intro root hrelW
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hmeet :
          rule2WMeetsZAncestral model G x z w assignment = true := by
        refine (rule2WMeetsZAncestral_eq_true_iff model G x z w
            assignment).mpr ⟨root, ?_, ?_⟩
        · simpa [selected, rule2Right, Kernel.intervention] using hsel
        · simpa [heavier, rule2Left, Kernel.intervention] using hrelW
      rw [hmeet] at havoid
      cases havoid

/-- A `do(X)`-relevant `An(Z)` latent is already relevant to the rule-2
open `Z` core when `W` shares no such latent: its free incident child is
open given `X ∪ W`, and a shortest walk into `Z` never meets `W`. -/
theorem latentRelevantUnder_rule2ZOpenCore_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    {root : Fin model.latent.count}
    (hrel : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z) root = true) :
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.rule2ZOpenCore G x z w) root = true := by
  let doX :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  let doXZ :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z) NodeSet.empty).intervention
      assignment
  rcases (model.latentRelevantUnder_eq_true_iff doX
      (FiniteLatentSCM.ancestralInBar G x z) root).mp hrel with
    ⟨child, hsel, hnone, hinc⟩
  have hx : x child = false := by
    dsimp [doX, Kernel.intervention] at hnone
    cases hx : x child with
    | false =>
        rfl
    | true =>
        simp [hx] at hnone
  have hwChild : w child = false := by
    cases hw : w child with
    | false =>
        rfl
    | true =>
        have hz : z child = false := by
          cases hz : z child with
          | false =>
              rfl
          | true =>
              have hfalse := disjoint.zw child hz
              rw [hw] at hfalse
              cases hfalse
        have hfreeXZ : doXZ child = none := by
          simp [doXZ, Kernel.intervention, NodeSet.union, hx, hz]
        have hancW :
            FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w child =
              true :=
          FiniteLatentSCM.observedAncestorOf_self G
            (GraphMutilation.bar (NodeSet.union x z)) w hw
        have hW :=
          model.latentRelevantUnder_of_incident doXZ
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
            root child hancW hfreeXZ hinc
        have hmeet :
            rule2WMeetsZAncestral model G x z w assignment = true :=
          (rule2WMeetsZAncestral_eq_true_iff model G x z w assignment).mpr
            ⟨root, hrel, hW⟩
        rw [hmeet] at havoid
        cases havoid
  have hunion : NodeSet.union x w child = false :=
    Bool.or_eq_false_iff.mpr ⟨hx, hwChild⟩
  have hbar :=
    FiniteLatentSCM.observedAncestorOf_barUnderline_z_of_bar G x z child hsel
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.barUnderline x z) z child hbar with
    ⟨target, htarget, length, walk, simple, minimal⟩
  have hopen :
      forall n, n ∈ walk.nodes -> NodeSet.union x w n = false := by
    intro n hn
    have hxN : x n = false := by
      by_cases hsrc : n = child
      · subst n
        exact hx
      · have hin :=
          PathSpecification.directed_walk_mem_not_removeIncoming G
            (GraphMutilation.barUnderline x z) walk hn hsrc
        simpa [GraphMutilation.barUnderline] using hin
    have hwN : w n = false := by
      cases hw : w n with
      | false =>
          rfl
      | true =>
          have hzN : z n = false := by
            cases hz : z n with
            | false =>
                rfl
            | true =>
                have hfalse := disjoint.zw n hz
                rw [hw] at hfalse
                cases hfalse
          by_cases hsrc : n = child
          · subst n
            exact (Bool.false_ne_true (hwChild.symm.trans hw)).elim
          · rcases FiniteReachability.ExactWalk.exists_prefix_with_subset
                walk hn with
              ⟨_plen, preWalk, _bound, subset, rest, hsplit⟩
            have hnotZ :
                forall m, m ∈ preWalk.nodes -> z m = false := by
              intro m hm
              have hmWalk := subset m hm
              by_cases hmeq : m = target
              · subst m
                have hneN : n ≠ target := by
                  intro eq
                  subst n
                  exact Bool.false_ne_true (hzN.symm.trans htarget)
                cases hrest : rest with
                | nil =>
                    have heq : walk.nodes = preWalk.nodes := by
                      simpa [hrest] using hsplit
                    have wlast := walk.nodes_getLast
                    have plast := preWalk.nodes_getLast
                    have : n = target := by
                      simpa [heq, plast] using wlast
                    exact (hneN this).elim
                | cons head tail =>
                    have hwalkNodup := simple
                    rw [hsplit, hrest] at hwalkNodup
                    have hrestMem : target ∈ head :: tail := by
                      have wlast := walk.nodes_getLast
                      have hrestLast :
                          (head :: tail).getLast? = some target := by
                        rw [hsplit, hrest] at wlast
                        simpa [List.getLast?_append] using wlast
                      exact List.mem_of_mem_getLast? (by
                        simp [hrestLast])
                    have hne :=
                      (List.nodup_append.mp hwalkNodup).2.2 target hm target
                        hrestMem
                    exact (hne rfl).elim
              · have hfalse :=
                  FiniteReachability.ExactWalk.not_mem_targets_of_minimal_internal
                    walk minimal hmWalk hmeq
                cases hzm : z m with
                | false =>
                    rfl
                | true =>
                    rw [hzm] at hfalse
                    cases hfalse
            have hancW :
                FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w
                    child = true :=
              FiniteLatentSCM.observedAncestorOf_barUnion_of_barUnderline_walk
                G x z w preWalk hw hnotZ
            have hzChild : z child = false :=
              hnotZ child preWalk.mem_source
            have hfreeXZ : doXZ child = none := by
              simp [doXZ, Kernel.intervention, NodeSet.union, hx, hzChild]
            have hW :=
              model.latentRelevantUnder_of_incident doXZ
                (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
                root child hancW hfreeXZ hinc
            have hmeet :
                rule2WMeetsZAncestral model G x z w assignment = true :=
              (rule2WMeetsZAncestral_eq_true_iff model G x z w
                  assignment).mpr ⟨root, hrel, hW⟩
            rw [hmeet] at havoid
            cases havoid
    exact Bool.or_eq_false_iff.mpr ⟨hxN, hwN⟩
  have hancU :=
    FiniteLatentSCM.observedAncestorOf_unionBarUnderline_of_open_walk G x w z
      z walk htarget hopen
  have hblocked :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed child) =
        false := by
    simpa [ObservedGraph.blockedBy] using hunion
  have hcore : FiniteLatentSCM.rule2ZOpenCore G x z w child = true := by
    simp [FiniteLatentSCM.rule2ZOpenCore,
      FiniteLatentSCM.openAncestralInGraph, hblocked, hancU]
  exact model.latentRelevantUnder_of_incident doX
    (FiniteLatentSCM.rule2ZOpenCore G x z w) root child hcore hnone hinc

/-- A `do(X ∪ Z)`-relevant `An(Y)` latent that is also `do(X)`-relevant to
`An(Z)` is already relevant to the rule-2 open `Y` core when `W` shares
no `An(Z)` latent: its free incident child is open given `X ∪ W`, and a
shortest walk into `Y` in `G_{\overline{X}\underline{Z}}` never meets
`W`. -/
theorem latentRelevantUnder_rule2YOpenCore_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    {root : Fin model.latent.count}
    (hrelZ : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z) root = true)
    (hrelY : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root =
        true) :
    model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.rule2YOpenCore G x y z w) root = true := by
  let doX :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  let doXZ :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z) NodeSet.empty).intervention
      assignment
  rcases (model.latentRelevantUnder_eq_true_iff doXZ
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root).mp
      hrelY with
    ⟨child, hsel, hnone, hinc⟩
  have hfreeXZ : NodeSet.union x z child = false := by
    dsimp [doXZ, Kernel.intervention] at hnone
    cases hunion : NodeSet.union x z child with
    | false =>
        rfl
    | true =>
        simp [hunion] at hnone
  have hx : x child = false := (Bool.or_eq_false_iff.mp hfreeXZ).1
  have hzChild : z child = false := (Bool.or_eq_false_iff.mp hfreeXZ).2
  have hwChild : w child = false := by
    cases hw : w child with
    | false =>
        rfl
    | true =>
        have hancW :
            FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w child =
              true :=
          FiniteLatentSCM.observedAncestorOf_self G
            (GraphMutilation.bar (NodeSet.union x z)) w hw
        have hW :=
          model.latentRelevantUnder_of_incident doXZ
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
            root child hancW hnone hinc
        have hmeet :
            rule2WMeetsZAncestral model G x z w assignment = true :=
          (rule2WMeetsZAncestral_eq_true_iff model G x z w assignment).mpr
            ⟨root, hrelZ, hW⟩
        rw [hmeet] at havoid
        cases havoid
  have hunion : NodeSet.union x w child = false :=
    Bool.or_eq_false_iff.mpr ⟨hx, hwChild⟩
  have hbar :=
    FiniteLatentSCM.observedAncestorOf_barUnderline_y_of_barUnion G x y z
      child hsel hfreeXZ
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.barUnderline x z) y child hbar with
    ⟨target, htarget, length, walk, simple, minimal⟩
  have hnotZWalk :
      forall m, m ∈ walk.nodes -> z m = false := by
    intro m hm
    by_cases hsrc : m = child
    · subst m
      exact hzChild
    · by_cases hmt : m = target
      · subst m
        have hyfalse := disjoint.yz target htarget
        cases hz : z target with
        | false =>
            rfl
        | true =>
            rw [hz] at hyfalse
            cases hyfalse
      · rcases FiniteReachability.ExactWalk.exists_simple_suffix_of_mem
            walk simple hm with
          ⟨_slen, suffix, _ss, _pre, _hsplit⟩
        cases suffix with
        | refl =>
            exact (hmt rfl).elim
        | step first rest =>
            have hzParent : z m = false := by
              simp [ObservedGraph.observedDirectedEdge,
                GraphMutilation.barUnderline] at first
              exact first.1.2
            exact hzParent
  have hopen :
      forall n, n ∈ walk.nodes -> NodeSet.union x w n = false := by
    intro n hn
    have hxN : x n = false := by
      by_cases hsrc : n = child
      · subst n
        exact hx
      · have hin :=
          PathSpecification.directed_walk_mem_not_removeIncoming G
            (GraphMutilation.barUnderline x z) walk hn hsrc
        simpa [GraphMutilation.barUnderline] using hin
    have hwN : w n = false := by
      cases hw : w n with
      | false =>
          rfl
      | true =>
          by_cases hsrc : n = child
          · subst n
            exact (Bool.false_ne_true (hwChild.symm.trans hw)).elim
          · rcases FiniteReachability.ExactWalk.exists_prefix_with_subset
                walk hn with
              ⟨_plen, preWalk, _bound, subset, _rest, _hsplit⟩
            have hnotZ :
                forall m, m ∈ preWalk.nodes -> z m = false :=
              fun m hm => hnotZWalk m (subset m hm)
            have hancW :
                FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w
                    child = true :=
              FiniteLatentSCM.observedAncestorOf_barUnion_of_barUnderline_walk
                G x z w preWalk hw hnotZ
            have hW :=
              model.latentRelevantUnder_of_incident doXZ
                (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
                root child hancW hnone hinc
            have hmeet :
                rule2WMeetsZAncestral model G x z w assignment = true :=
              (rule2WMeetsZAncestral_eq_true_iff model G x z w
                  assignment).mpr ⟨root, hrelZ, hW⟩
            rw [hmeet] at havoid
            cases havoid
    exact Bool.or_eq_false_iff.mpr ⟨hxN, hwN⟩
  have hancU :=
    FiniteLatentSCM.observedAncestorOf_unionBarUnderline_of_open_walk G x w z
      y walk htarget hopen
  have hblocked :
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed child) =
        false := by
    simpa [ObservedGraph.blockedBy] using hunion
  have hcore : FiniteLatentSCM.rule2YOpenCore G x y z w child = true := by
    simp [FiniteLatentSCM.rule2YOpenCore,
      FiniteLatentSCM.openAncestralInGraph, hblocked, hancU]
  have hnoneX : doX child = none := by
    simp [doX, Kernel.intervention, hx]
  exact model.latentRelevantUnder_of_incident doX
    (FiniteLatentSCM.rule2YOpenCore G x y z w) root child hcore hnoneX hinc

/-- Rule 2 with empty `W`: `Z` under `do(X)` depends only on latents of
`An(Z)` in `G_{\overline{X}}`. -/
theorem agreesOn_rule2Z_dependsOnSelected_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x _y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule2Right x y z w).intervention assignment) roots)) :=
  agreesOn_evalUnder_dependsOnSelected model
    ((rule2Right x y z w).intervention assignment)
    (FiniteLatentSCM.ancestralInBar G x z) z assignment
    (by
      have hact :
          (rule2Right x y z w).intervention assignment =
            (fun i => if x i then some (assignment i) else none) := by
        funext i
        simp [rule2Right, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          x z assignment)
    (FiniteLatentSCM.subset_ancestralInBar G x z z (fun _i hi => hi))

/-- Rule 2 with empty `W`: `Y` under `do(X ∪ Z)` is independent of the
selected `An(Z)` latents, because those latents are separated from the
open `Y` core in `G_{\overline{X}\underline{Z}}`. -/
theorem agreesOn_rule2Y_dependsOnUnselected_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) y assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) y y
      (fun _i hi => hi))
    left right
  intro root hrelY
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hZopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2ZOpenCore G x z w) root = true := by
        have hrelZ : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true := by
          simpa [selected, rule2Right, Kernel.intervention] using hsel
        exact FiniteLatentSCM.latentRelevantUnder_rule2ZOpenCore_of_ancestral_of_empty_w
          model G x z w assignment hw hrelZ
      have hYopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2YOpenCore G x y z w) root = true := by
        have hrelY' : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root =
              true := by
          simpa [heavier, rule2Left, Kernel.intervention] using hrelY
        exact FiniteLatentSCM.latentRelevantUnder_rule2YOpenCore_of_barUnion_of_empty_w
          model G x y z w assignment hw hrelY'
      have hsep :=
        FiniteLatentSCM.rule2OpenCores_latentSeparated_of_empty_w model G
          projected x y z w assignment hw separated root hZopen
      rw [hYopen] at hsep
      cases hsep

/-- Rule 2 when `W` shares no `An(Z)` latent: `Y` under `do(X ∪ Z)` is
independent of the selected `An(Z)` latents, because those latents are
separated from the open `Y` core in `G_{\overline{X}\underline{Z}}`. -/
theorem agreesOn_rule2Y_dependsOnUnselected_of_avoids_z
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) y assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) y y
      (fun _i hi => hi))
    left right
  intro root hrelY
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hZopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2ZOpenCore G x z w) root = true := by
        have hrelZ : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true := by
          simpa [selected, rule2Right, Kernel.intervention] using hsel
        exact latentRelevantUnder_rule2ZOpenCore_of_avoids
          model G x y z w assignment disjoint havoid hrelZ
      have hYopen :
          model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.rule2YOpenCore G x y z w) root = true := by
        have hrelZ : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root = true := by
          simpa [selected, rule2Right, Kernel.intervention] using hsel
        have hrelY' : model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root =
              true := by
          simpa [heavier, rule2Left, Kernel.intervention] using hrelY
        exact latentRelevantUnder_rule2YOpenCore_of_avoids
          model G x y z w assignment disjoint havoid hrelZ hrelY'
      have hsep :=
        FiniteLatentSCM.rule2OpenCores_latentSeparated model G
          projected x y z w assignment separated root hZopen
      rw [hYopen] at hsep
      cases hsep

/-- Empty `W` supplies the four cylinder-dependence hypotheses of
`rule2PartitionWitness`: both `W` blocks are empty, `Z` depends on
`An(Z)` under `do(X)`, and `Y` is independent of those latents under
`do(X ∪ Z)`. -/
def rule2PartitionWitness_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    (hw : NodeSet.isEmpty w = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  have hact : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  have wSplit : w = NodeSet.union NodeSet.empty NodeSet.empty := by
    simp [hact, NodeSet.union_empty_right]
  exact rule2PartitionWitness model x y z w
    NodeSet.empty NodeSet.empty assignment
    (model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z))
    wSplit
    (agreesOn_rule2Z_dependsOnSelected_of_empty_w model G x y z w assignment)
    (by
      intro left right _agree
      have hL :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment left
      have hR :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment right
      simp [hL, hR])
    (agreesOn_rule2Y_dependsOnUnselected_of_empty_w model G projected
      x y z w assignment hw separated)
    (by
      intro left right _agree
      have hL :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment left
      have hR :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment right
      simp [hL, hR])

/-- When `W` shares no `An(Z)` latent, the whole of `W` is unselected:
`wSelected` is empty, `wUnselected` is `W`, `Z` depends on `An(Z)` under
`do(X)`, and `Y` is independent of those latents under `do(X ∪ Z)`. -/
def rule2PartitionWitness_of_w_avoids_z
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w)) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  have wSplit : w = NodeSet.union NodeSet.empty w :=
    (NodeSet.union_empty_left w).symm
  exact rule2PartitionWitness model x y z w
    NodeSet.empty w assignment
    (model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z))
    wSplit
    (agreesOn_rule2Z_dependsOnSelected_of_empty_w model G x y z w assignment)
    (by
      intro left right _agree
      have hL :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment left
      have hR :=
        agreesOn_empty_eq_true model
          ((rule2Left x y z w).intervention assignment) assignment right
      simp [hL, hR])
    (agreesOn_rule2Y_dependsOnUnselected_of_avoids_z model G projected
      x y z w assignment disjoint havoid separated)
    (agreesOn_rule2W_dependsOnUnselected_of_avoids_z model G
      x y z w assignment havoid)

/-- A `W` vertex that is free under `do(X ∪ Z)` and incident to a
`do(X)`-relevant `An(Z)` latent.  These are the observed children of the
rule-2 meet. -/
def rule2WVertexMeetsZ (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    (w i &&
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root &&
        model.latent.incident root i)

theorem rule2WVertexMeetsZ_subset_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.Subset (rule2WVertexMeetsZ model G x z w assignment) w := by
  intro i hi
  have hparts :
      (w i &&
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root &&
            model.latent.incident root i) = true := by
    simpa [rule2WVertexMeetsZ] using hi
  exact (Bool.and_eq_true_iff.mp hparts.1).1

/-- A `do(X ∪ Z)`-free ancestor of `W` incident to a `do(X)`-relevant
`An(Z)` latent.  Meeting `W` vertices are included, as are extra free
ancestors outside `W` that still feed the meet. -/
def rule2WZSideSeed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i &&
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root &&
        model.latent.incident root i)

theorem rule2WZSideSeed_of_vertex_meet
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {i : Fin S.count}
    (hi : rule2WVertexMeetsZ model G x z w assignment i = true) :
    rule2WZSideSeed model G x z w assignment i = true := by
  have hparts :
      (w i &&
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root &&
            model.latent.incident root i) = true := by
    simpa [rule2WVertexMeetsZ] using hi
  have hw : w i = true := (Bool.and_eq_true_iff.mp hparts.1).1
  have hself :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i = true :=
    FiniteLatentSCM.observedAncestorOf_self G
      (GraphMutilation.bar (NodeSet.union x z)) w hw
  refine Bool.and_eq_true_iff.mpr ⟨?_, hparts.2⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hself, (Bool.and_eq_true_iff.mp hparts.1).2⟩

/-- A `Z`-side seed already witnesses `rule2WMeetsZAncestral`. -/
theorem rule2WMeetsZAncestral_of_seed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {i : Fin S.count}
    (hi : rule2WZSideSeed model G x z w assignment i = true) :
    rule2WMeetsZAncestral model G x z w assignment = true := by
  have hparts :
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i &&
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment i).isNone) = true ∧
        finAny model.latent.count (fun root =>
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root &&
            model.latent.incident root i) = true := by
    simpa [rule2WZSideSeed] using hi
  have hancW :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i = true :=
    (Bool.and_eq_true_iff.mp hparts.1).1
  have hfree :
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i) = none :=
    Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hparts.1).2
  rcases (finAny_eq_true_iff _).mp hparts.2 with ⟨root, hroot⟩
  rcases Bool.and_eq_true_iff.mp hroot with ⟨hrelZ, hinc⟩
  have hW :=
    model.latentRelevantUnder_of_incident
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w)
      root i hancW hfree hinc
  exact (rule2WMeetsZAncestral_eq_true_iff model G x z w assignment).mpr
    ⟨root, hrelZ, hW⟩

/-- Avoiding the `An(Z)` meet empties the `Z`-side seed set. -/
theorem rule2WZSideSeed_eq_false_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (i : Fin S.count) :
    rule2WZSideSeed model G x z w assignment i = false := by
  cases hseed : rule2WZSideSeed model G x z w assignment i with
  | false =>
      rfl
  | true =>
      have hmeet :=
        rule2WMeetsZAncestral_of_seed model G x z w assignment hseed
      rw [hmeet] at havoid
      cases havoid

/--
`W` vertices that are directed descendants of a `Z`-side seed in
`G_{\overline{X ∪ Z}}`, including every `Z`-meeting `W` vertex.  Directed
`W_Z → W'` is absorbed into the selected block.
-/
def rule2WSplitSelectedClosed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    w i &&
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (NodeSet.singleton i))
        (rule2WZSideSeed model G x z w assignment)

def rule2WSplitUnselectedClosed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  NodeSet.diff w (rule2WSplitSelectedClosed model G x z w assignment)

theorem rule2WSplitClosed_disjoint (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.Disjoint
      (rule2WSplitSelectedClosed model G x z w assignment)
      (rule2WSplitUnselectedClosed model G x z w assignment) :=
  NodeSet.Disjoint.diff_left w
    (rule2WSplitSelectedClosed model G x z w assignment)

theorem rule2WSplitClosed_union (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.union
      (rule2WSplitSelectedClosed model G x z w assignment)
      (rule2WSplitUnselectedClosed model G x z w assignment) = w := by
  funext i
  simp [rule2WSplitSelectedClosed, rule2WSplitUnselectedClosed,
    NodeSet.union, NodeSet.diff]
  cases hw : w i with
  | false =>
      simp
  | true =>
      cases hm :
          NodeSet.meetsBool
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (NodeSet.singleton i))
            (rule2WZSideSeed model G x z w assignment) with
      | false =>
          simp
      | true =>
          simp

/-- Every `Z`-meeting `W` vertex is a descendant of itself, hence sits
in the closed selected block. -/
theorem rule2WSplitClosed_contains_meets
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {i : Fin S.count}
    (hi : rule2WVertexMeetsZ model G x z w assignment i = true) :
    rule2WSplitSelectedClosed model G x z w assignment i = true := by
  have hw : w i = true :=
    rule2WVertexMeetsZ_subset_w model G x z w assignment i hi
  have hseed :
      rule2WZSideSeed model G x z w assignment i = true :=
    rule2WZSideSeed_of_vertex_meet model G x z w assignment hi
  have hself :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (NodeSet.singleton i) i = true :=
    FiniteLatentSCM.observedAncestorOf_self G
      (GraphMutilation.bar (NodeSet.union x z)) (NodeSet.singleton i)
      ((NodeSet.singleton_eq_true_iff i i).mpr rfl)
  have hmeets :
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (NodeSet.singleton i))
        (rule2WZSideSeed model G x z w assignment) = true :=
    (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨i, hself, hseed⟩
  simp [rule2WSplitSelectedClosed, hw, hmeets]

/-- Avoiding the `An(Z)` meet empties the closed selected block. -/
theorem rule2WSplitSelectedClosed_eq_false_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false)
    (i : Fin S.count) :
    rule2WSplitSelectedClosed model G x z w assignment i = false := by
  simp [rule2WSplitSelectedClosed]
  cases hw : w i with
  | false =>
      simp
  | true =>
      cases hm :
          NodeSet.meetsBool
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (NodeSet.singleton i))
            (rule2WZSideSeed model G x z w assignment) with
      | false =>
          simp
      | true =>
          rcases (NodeSet.meetsBool_eq_true_iff _ _).mp hm with
            ⟨seed, _hanc, hseed⟩
          have hfalse :=
            rule2WZSideSeed_eq_false_of_avoids model G x z w assignment
              havoid seed
          rw [hfalse] at hseed
          cases hseed

/-- A `do(X ∪ Z)`-free ancestor of `W` incident to a `do(X ∪ Z)`-relevant
`An(Y)` latent.  This is the rule-2 analogue of a `Y`-side seed. -/
def rule2WYSideSeed (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet S :=
  fun i =>
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w i &&
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment i).isNone) &&
    finAny model.latent.count (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root &&
        model.latent.incident root i)

/-- A `Z`-side seed cannot ancestor an unselected `W` vertex: that
vertex would itself be a descendant of the seed, hence selected. -/
theorem rule2WSplitClosed_no_seed_in_unselected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    {seed : Fin S.count}
    (hseed : rule2WZSideSeed model G x z w assignment seed = true)
    (hanc : FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment) seed =
          true) :
    False := by
  have hany :
      (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
        rule2WSplitUnselectedClosed model G x z w assignment target &&
          FiniteReachability.within finBeq
            (List.ofFn (fun k : Fin S.count => k))
            (G.observedDirectedEdge
              (GraphMutilation.bar (NodeSet.union x z)))
            (List.ofFn (fun k : Fin S.count => k)).length seed target) =
        true := by
    simpa [FiniteLatentSCM.ancestralInBar, ObservedGraph.observedAncestorOf]
      using hanc
  rcases List.any_eq_true.mp hany with ⟨t, tMem, ht⟩
  have htParts := Bool.and_eq_true_iff.mp ht
  have hunsel :
      rule2WSplitUnselectedClosed model G x z w assignment t = true :=
    htParts.1
  have hseedT :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (NodeSet.singleton t) seed = true := by
    have hanyT :
        (List.ofFn (fun k : Fin S.count => k)).any (fun target =>
          NodeSet.singleton t target &&
            FiniteReachability.within finBeq
              (List.ofFn (fun k : Fin S.count => k))
              (G.observedDirectedEdge
                (GraphMutilation.bar (NodeSet.union x z)))
              (List.ofFn (fun k : Fin S.count => k)).length seed target) =
          true :=
      List.any_eq_true.mpr
        ⟨t, tMem,
          Bool.and_eq_true_iff.mpr
            ⟨(NodeSet.singleton_eq_true_iff t t).mpr rfl, htParts.2⟩⟩
    simpa [FiniteLatentSCM.ancestralInBar, ObservedGraph.observedAncestorOf]
      using hanyT
  have hwT : w t = true :=
    NodeSet.diff_subset_left w
      (rule2WSplitSelectedClosed model G x z w assignment) t hunsel
  have hsel :
      rule2WSplitSelectedClosed model G x z w assignment t = true := by
    have hmeetsT :
        NodeSet.meetsBool
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (NodeSet.singleton t))
          (rule2WZSideSeed model G x z w assignment) = true :=
      (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨seed, hseedT, hseed⟩
    simp [rule2WSplitSelectedClosed, hwT, hmeetsT]
  have hfalse :
      rule2WSplitUnselectedClosed model G x z w assignment t = false :=
    rule2WSplitClosed_disjoint model G x z w assignment t hsel
  exact Bool.false_ne_true (hfalse.symm.trans hunsel)

/-- The closed unselected slice of `W` observes only latents complementary
to the `do(X)`-relevant `An(Z)` family: a selected latent incident to an
unselected ancestor would be a `Z`-side seed in that ancestral set. -/
theorem agreesOn_rule2WSplitUnselectedClosed_dependsOnNotZ
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn
        (rule2WSplitUnselectedClosed model G x z w assignment) assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
      (rule2WSplitUnselectedClosed model G x z w assignment))
    (rule2WSplitUnselectedClosed model G x z w assignment) assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z)
          (rule2WSplitUnselectedClosed model G x z w assignment)
          assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z)
      (rule2WSplitUnselectedClosed model G x z w assignment)
      (rule2WSplitUnselectedClosed model G x z w assignment)
      (fun _i hi => hi))
    left right
  intro root hrelW
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hrelZ : model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root = true := by
        simpa [selected, rule2Right, Kernel.intervention] using hsel
      rcases (model.latentRelevantUnder_eq_true_iff heavier
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule2WSplitUnselectedClosed model G x z w assignment))
          root).mp (by
            simpa [heavier, rule2Left, Kernel.intervention] using hrelW) with
        ⟨child, hancU, hnone, hinc⟩
      have hancW :
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w child =
            true :=
        FiniteLatentSCM.ancestralInBar_mono G (NodeSet.union x z)
          (NodeSet.diff_subset_left w
            (rule2WSplitSelectedClosed model G x z w assignment))
          hancU
      have hseed :
          rule2WZSideSeed model G x z w assignment child = true := by
        have hfree :
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment child).isNone =
              true := by
          have hact :
              heavier =
                (Kernel.mk NodeSet.empty (NodeSet.union x z)
                  NodeSet.empty).intervention assignment := by
            funext i
            simp [heavier, rule2Left, Kernel.intervention]
          have : heavier child = none := hnone
          rw [hact] at this
          exact Option.isNone_iff_eq_none.mpr this
        have hincZ :
            finAny model.latent.count (fun r =>
              model.latentRelevantUnder
                  ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                    assignment)
                  (FiniteLatentSCM.ancestralInBar G x z) r &&
                model.latent.incident r child) = true :=
          (finAny_eq_true_iff _).mpr ⟨root,
            Bool.and_eq_true_iff.mpr ⟨hrelZ, hinc⟩⟩
        refine Bool.and_eq_true_iff.mpr ⟨?_, hincZ⟩
        exact Bool.and_eq_true_iff.mpr ⟨hancW, hfree⟩
      exact (rule2WSplitClosed_no_seed_in_unselected model G x z w
        assignment hseed hancU).elim

/-- The closed selected slice of `W` observes only latents of its own
ancestors in `G_{\overline{X ∪ Z}}`. -/
theorem agreesOn_rule2WSplitSelectedClosed_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Left x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule2WSplitSelectedClosed model G x z w assignment)))
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitSelectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((rule2Left x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule2Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule2Left, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule2WSplitSelectedClosed model G x z w assignment))
      (rule2WSplitSelectedClosed model G x z w assignment) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
        (NodeSet.union x z)
        (rule2WSplitSelectedClosed model G x z w assignment) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z)
        (rule2WSplitSelectedClosed model G x z w assignment)
        (rule2WSplitSelectedClosed model G x z w assignment)
        (fun _i hi => hi))

/-- The closed unselected slice of `W` observes only latents of its own
ancestors in `G_{\overline{X ∪ Z}}`. -/
theorem agreesOn_rule2WSplitUnselectedClosed_dependsOnAncestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Left x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule2WSplitUnselectedClosed model G x z w assignment)))
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitUnselectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((rule2Left x y z w).intervention assignment) roots)) := by
  have hinter :
      (rule2Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule2Left, Kernel.intervention]
  simpa [hinter] using
    agreesOn_evalUnder_dependsOnSelected model
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment))
      (rule2WSplitUnselectedClosed model G x z w assignment) assignment
      (FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
        (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment) assignment)
      (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z)
        (rule2WSplitUnselectedClosed model G x z w assignment)
        (rule2WSplitUnselectedClosed model G x z w assignment)
        (fun _i hi => hi))

/-- A selected-`W` ancestral latent under `do(X ∪ Z)` that is missing from
`An(Z)` under `do(X)`.  This is the extra-latent gap: the closed selected
block can see coordinates outside the rule-2 `An(Z)` mask. -/
def rule2WSplitSelectedClosedExtraLatent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S) (assignment : S.Assignment) :
    Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule2WSplitSelectedClosed model G x z w assignment)) root &&
      !(model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root))

/-- Avoiding the `An(Z)` meet empties the selected block, so it contributes
no extra ancestral latents. -/
theorem rule2WSplitSelectedClosedExtraLatent_eq_false_of_avoids
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (havoid : rule2WMeetsZAncestral model G x z w assignment = false) :
    rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
      false := by
  have hsel :
      rule2WSplitSelectedClosed model G x z w assignment = NodeSet.empty := by
    funext i
    exact rule2WSplitSelectedClosed_eq_false_of_avoids model G x z w
      assignment havoid i
  refine (finAny_eq_false_iff _).mpr ?_
  intro root
  have hrel :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule2WSplitSelectedClosed model G x z w assignment))
          root = false := by
    rw [hsel, FiniteLatentSCM.ancestralInBar_eq_empty]
    exact model.latentRelevantUnder_empty
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      root
  simp [hrel]

/-- When the extra-latent gap is empty, the closed selected slice of `W`
observes only the `do(X)`-relevant `An(Z)` latents. -/
theorem agreesOn_rule2WSplitSelectedClosed_dependsOnZ
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hextra :
      rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
        false) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitSelectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((rule2Left x y z w).intervention assignment) roots)) := by
  have hall :=
    (finAny_eq_false_iff (fun root =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule2WSplitSelectedClosed model G x z w assignment)) root &&
        !(model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
              assignment)
            (FiniteLatentSCM.ancestralInBar G x z) root))).mp
      (by simpa [rule2WSplitSelectedClosedExtraLatent] using hextra)
  have hsub :
      forall root,
        model.latentRelevantUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment)
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (rule2WSplitSelectedClosed model G x z w assignment))
            root = true ->
          model.latentRelevantUnder
              ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
                assignment)
              (FiniteLatentSCM.ancestralInBar G x z) root = true := by
    intro root hr
    have hroot := hall root
    cases hz :
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x z) root with
    | true =>
        rfl
    | false =>
        simp [hr, hz] at hroot
  have hinterL :
      (rule2Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule2Left, Kernel.intervention]
  have hinterR :
      (rule2Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment :=
      by
    funext i
    simp [rule2Right, Kernel.intervention]
  simpa [hinterL, hinterR] using
    CanonicalFactorization.DependsOnSelected.subset model.latent.count
      model.latent.Value
      (fun roots =>
        Kernel.agreesOn
          (rule2WSplitSelectedClosed model G x z w assignment) assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x z)
              NodeSet.empty).intervention assignment) roots))
      hsub
      (by
        simpa [hinterL] using
          agreesOn_rule2WSplitSelectedClosed_dependsOnAncestral model G
            x y z w assignment)

/-- A `do(X)`-relevant `An(Z)` latent that is also `do(X ∪ Z)`-relevant to
`An(Y)`.  When this is false, `Y` ignores the rule-2 selected mask. -/
def rule2SelectedMeetsYAncestral (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z _w : NodeSet S)
    (assignment : S.Assignment) :
    Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z) root &&
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) root)

/-- `Y` under `do(X ∪ Z)` is independent of the selected `An(Z)` latents
once those latents are not relevant to `An(Y)`. -/
theorem agreesOn_rule2Y_dependsOnUnselected_of_avoids_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (havoidY :
      rule2SelectedMeetsYAncestral model G x y z w assignment = false) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
      (model.latentRelevantUnder
        ((rule2Right x y z w).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x z))
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)) := by
  let selected :=
    model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z)
  let heavier := (rule2Left x y z w).intervention assignment
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model heavier
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y) y assignment
    (by
      have hact :
          heavier =
            (fun i =>
              if NodeSet.union x z i then some (assignment i)
              else none) := by
        funext i
        simp [heavier, rule2Left, Kernel.intervention]
      simpa [hact] using
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment)
    (FiniteLatentSCM.subset_ancestralInBar G (NodeSet.union x z) y y
      (fun _i hi => hi))
    left right
  intro root hrelY
  apply rootsAgree root
  cases hsel : selected root with
  | false =>
      exact hsel
  | true =>
      have hmeet :
          rule2SelectedMeetsYAncestral model G x y z w assignment = true := by
        refine (finAny_eq_true_iff _).mpr ⟨root, ?_⟩
        refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
        · simpa [selected, rule2Right, Kernel.intervention] using hsel
        · simpa [heavier, rule2Left, Kernel.intervention] using hrelY
      rw [hmeet] at havoidY
      cases havoidY

/-- When the extra-latent gap is empty and `Y` ignores the selected
`An(Z)` mask, the closed `Z`-side split inhabits the rule-2 partition. -/
def rule2PartitionWitness_of_w_split_closed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hextra :
      rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
        false)
    (havoidY :
      rule2SelectedMeetsYAncestral model G x y z w assignment = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment :=
  rule2PartitionWitness model x y z w
    (rule2WSplitSelectedClosed model G x z w assignment)
    (rule2WSplitUnselectedClosed model G x z w assignment) assignment
    (model.latentRelevantUnder
      ((rule2Right x y z w).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x z))
    (rule2WSplitClosed_union model G x z w assignment).symm
    (agreesOn_rule2Z_dependsOnSelected_of_empty_w model G x y z w assignment)
    (agreesOn_rule2WSplitSelectedClosed_dependsOnZ model G x y z w
      assignment hextra)
    (agreesOn_rule2Y_dependsOnUnselected_of_avoids_y model G x y z w
      assignment havoidY)
    (agreesOn_rule2WSplitUnselectedClosed_dependsOnNotZ model G x y z w
      assignment)

/-- A checked latent partition discharges the canonical-product cross-product
obligation. -/
theorem ProductConditionalIndependenceWitnessAt.toCrossProduct
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (witness : ProductConditionalIndependenceWitnessAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model left right assignment := by
  have conditional := productRecord_conditional_independence_cross model
    witness.selected witness.selectedOutcome witness.selectedCondition
    witness.unselectedOutcome witness.unselectedCondition
    witness.selectedOutcomeDepends witness.selectedConditionDepends
    witness.unselectedOutcomeDepends witness.unselectedConditionDepends
  constructor
  unfold productMass
  change QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.conditionEvent assignment))))
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.conditionEvent assignment))))
  rw [witness.leftNumerator, witness.rightCondition,
    witness.rightNumerator, witness.leftCondition]
  exact QProb.equiv_trans (QProb.equiv_symm conditional)
    (QProb.mul_comm _ _)

/-- A latent event factored across a selected/unselected partition of the
independent roots.  Unlike `ProductConditionalIndependenceWitnessAt`, this
does not require the four kernel events to share any of their two factors. -/
structure ProductEventRectangle (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (event : model.latent.Assignment -> Bool) where
  selectedPart : model.latent.Assignment -> Bool
  unselectedPart : model.latent.Assignment -> Bool
  selectedDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedPart
  unselectedDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedPart
  factorization : event = Probability.inter selectedPart unselectedPart

theorem ProductEventRectangle.probVal
    {model : FiniteLatentSCM S}
    {selected : Fin model.latent.count -> Bool}
    {event : model.latent.Assignment -> Bool}
    (rectangle : ProductEventRectangle model selected event) :
    QProb.Equiv ((productRecord model).probVal event)
      (QProb.mul
        ((productRecord model).probVal rectangle.selectedPart)
        ((productRecord model).probVal rectangle.unselectedPart)) := by
  cases rectangle with
  | mk selectedPart unselectedPart selectedDepends unselectedDepends
      factorization =>
      subst event
      exact productRecord_inter_equiv_mul model selected
        selectedPart unselectedPart selectedDepends unselectedDepends

/-- A general rectangular factorization of a kernel cross product.

The selected and unselected factors may differ in all four kernel events.
The two component cross identities are therefore expressive enough for
cross-world intervention arguments such as do-calculus Rule 3, without
imposing a pointwise inclusion between the two conditioning events. -/
structure ProductRectangularCrossProductWitnessAt
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  leftNumerator : ProductEventRectangle model selected
    (productPreimage model left assignment (left.numeratorEvent assignment))
  rightCondition : ProductEventRectangle model selected
    (productPreimage model right assignment (right.conditionEvent assignment))
  rightNumerator : ProductEventRectangle model selected
    (productPreimage model right assignment (right.numeratorEvent assignment))
  leftCondition : ProductEventRectangle model selected
    (productPreimage model left assignment (left.conditionEvent assignment))
  selectedCross : QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal leftNumerator.selectedPart)
      ((productRecord model).probVal rightCondition.selectedPart))
    (QProb.mul
      ((productRecord model).probVal rightNumerator.selectedPart)
      ((productRecord model).probVal leftCondition.selectedPart))
  unselectedCross : QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal leftNumerator.unselectedPart)
      ((productRecord model).probVal rightCondition.unselectedPart))
    (QProb.mul
      ((productRecord model).probVal rightNumerator.unselectedPart)
      ((productRecord model).probVal leftCondition.unselectedPart))

/--
Assemble a rectangular cross-product from factors shared in the only places
where the cross identity requires them to agree.

The two numerator events have the same selected-coordinate factor, and the
two conditioning events have the same selected-coordinate factor.  Their
unselected factors may differ between the left and right interventions.  The
selected cross identity is therefore reflexive, while the unselected identity
is commutativity of multiplication.

This shape is strictly more general than putting an entire conditioning
cylinder on the unselected side.  In particular, a rule-3 conditioner `W`
may legitimately share latent roots with `Y`: that common part belongs in
`selectedCondition`, while only the intervention-sensitive residuals need to
lie on the complementary coordinates.
-/
def ProductRectangularCrossProductWitnessAt.of_shared_factors
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (selectedNumerator selectedCondition leftResidual rightResidual :
      model.latent.Assignment -> Bool)
    (selectedNumeratorDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedNumerator)
    (selectedConditionDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedCondition)
    (leftResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected leftResidual)
    (rightResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected rightResidual)
    (leftNumerator :
      productPreimage model left assignment (left.numeratorEvent assignment) =
        Probability.inter selectedNumerator leftResidual)
    (rightCondition :
      productPreimage model right assignment (right.conditionEvent assignment) =
        Probability.inter selectedCondition rightResidual)
    (rightNumerator :
      productPreimage model right assignment
          (right.numeratorEvent assignment) =
        Probability.inter selectedNumerator rightResidual)
    (leftCondition :
      productPreimage model left assignment (left.conditionEvent assignment) =
        Probability.inter selectedCondition leftResidual) :
    ProductRectangularCrossProductWitnessAt model left right assignment where
  selected := selected
  leftNumerator :=
    { selectedPart := selectedNumerator
      unselectedPart := leftResidual
      selectedDepends := selectedNumeratorDepends
      unselectedDepends := leftResidualDepends
      factorization := leftNumerator }
  rightCondition :=
    { selectedPart := selectedCondition
      unselectedPart := rightResidual
      selectedDepends := selectedConditionDepends
      unselectedDepends := rightResidualDepends
      factorization := rightCondition }
  rightNumerator :=
    { selectedPart := selectedNumerator
      unselectedPart := rightResidual
      selectedDepends := selectedNumeratorDepends
      unselectedDepends := rightResidualDepends
      factorization := rightNumerator }
  leftCondition :=
    { selectedPart := selectedCondition
      unselectedPart := leftResidual
      selectedDepends := selectedConditionDepends
      unselectedDepends := leftResidualDepends
      factorization := leftCondition }
  selectedCross := QProb.equiv_refl _
  unselectedCross := QProb.mul_comm _ _

/-- Componentwise rectangular cross identities imply the kernel-level
canonical-product cross identity. -/
theorem ProductRectangularCrossProductWitnessAt.toCrossProduct
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (witness : ProductRectangularCrossProductWitnessAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model left right assignment := by
  have leftNumeratorFactor := witness.leftNumerator.probVal
  have rightConditionFactor := witness.rightCondition.probVal
  have rightNumeratorFactor := witness.rightNumerator.probVal
  have leftConditionFactor := witness.leftCondition.probVal
  constructor
  unfold productMass
  change QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.conditionEvent assignment))))
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.conditionEvent assignment))))
  exact QProb.equiv_trans
    (QProb.mul_congr leftNumeratorFactor rightConditionFactor)
    (QProb.equiv_trans (by
      simp only [QProb.Equiv, QProb.mul]
      ac_rfl)
      (QProb.equiv_trans
        (QProb.mul_congr witness.selectedCross witness.unselectedCross)
        (QProb.equiv_trans (by
          simp only [QProb.Equiv, QProb.mul]
          ac_rfl)
          (QProb.equiv_symm
            (QProb.mul_congr rightNumeratorFactor
              leftConditionFactor)))))

/-- A fully unselected mask makes every event a rectangle with constant
selected factor `true`. -/
def ProductEventRectangle.of_all_unselected (model : FiniteLatentSCM S)
    (event : model.latent.Assignment -> Bool) :
    ProductEventRectangle model (fun _ => false) event where
  selectedPart := fun _ => true
  unselectedPart := event
  selectedDepends :=
    CanonicalFactorization.DependsOnSelected.const _ _ _ true
  unselectedDepends := by
    intro left right agree
    have heq : left = right := funext fun i => agree i rfl
    subst heq
    rfl
  factorization := by
    funext roots
    simp [Probability.inter]

/-- Identical kernels have a rectangular cross-product: both sides share
the same numerator and condition, and a fully unselected mask makes the
two cross identities reflexive. -/
def ProductRectangularCrossProductWitnessAt.of_kernel_eq
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) (heq : left = right) :
    ProductRectangularCrossProductWitnessAt model left right assignment := by
  subst heq
  exact
    { selected := fun _ => false
      leftNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.numeratorEvent assignment))
      rightCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.conditionEvent assignment))
      rightNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.numeratorEvent assignment))
      leftCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model left assignment
            (left.conditionEvent assignment))
      selectedCross := QProb.equiv_refl _
      unselectedCross := QProb.equiv_refl _ }

/-- Identical kernels also inhabit the stronger CI shape: the selected
factors are constantly true, the unselected factors are the shared
numerator and condition, and `P(Y, W)` already implies `W`. -/
def ProductConditionalIndependenceWitnessAt.of_kernel_eq
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) (heq : left = right) :
    ProductConditionalIndependenceWitnessAt model left right assignment := by
  subst heq
  let num :=
    productPreimage model left assignment (left.numeratorEvent assignment)
  let cond :=
    productPreimage model left assignment (left.conditionEvent assignment)
  let numRect := ProductEventRectangle.of_all_unselected model num
  let condRect := ProductEventRectangle.of_all_unselected model cond
  refine
    { selected := fun _ => false
      selectedOutcome := fun _ => true
      selectedCondition := fun _ => true
      unselectedOutcome := num
      unselectedCondition := cond
      selectedOutcomeDepends :=
        CanonicalFactorization.DependsOnSelected.const _ _ _ true
      selectedConditionDepends :=
        CanonicalFactorization.DependsOnSelected.const _ _ _ true
      unselectedOutcomeDepends := numRect.unselectedDepends
      unselectedConditionDepends := condRect.unselectedDepends
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · funext roots
    simp [num, cond, productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter]
  · funext roots
    simp [cond, productPreimage, Probability.inter]
  · funext roots
    simp [num, cond, productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter]
  · funext roots
    simp [cond, productPreimage, Probability.inter]

/-- Empty `Z` makes rule 1 an identity of kernels.  The side condition
`Y ⊥ ∅ | X ∪ W` in `G_{\overline{X}}` is vacuous. -/
def rule1PartitionWitness_of_empty_z
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hz : NodeSet.isEmpty z = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment :=
  ProductConditionalIndependenceWitnessAt.of_kernel_eq model
    (rule1Left x y z w) (rule1Right x y z w) assignment
    (rule1Left_eq_rule1Right_of_empty_z x y z w hz)

/-- Empty `Z` makes rule 2 an identity of kernels, oriented as the
partition witness `(right, left)`. -/
def rule2PartitionWitness_of_empty_z
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hz : NodeSet.isEmpty z = true) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment :=
  ProductConditionalIndependenceWitnessAt.of_kernel_eq model
    (rule2Right x y z w) (rule2Left x y z w) assignment
    (rule2Left_eq_rule2Right_of_empty_z x y z w hz).symm

/--
Rule 2 from path d-separation.  Empty `Z` is a kernel identity; empty
`W` or a `W` that misses `An(Z)` uses the one-sided witnesses.  If `W`
meets `An(Z)`, the closed split still factorizes once the extra-latent
gap is empty and `Y` ignores the selected `An(Z)` mask.
-/
def rule2PartitionWitness_of_path
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z (NodeSet.union x w))
    (hextra :
      rule2WSplitSelectedClosedExtraLatent model G x z w assignment =
        false)
    (havoidY :
      rule2SelectedMeetsYAncestral model G x y z w assignment = false) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  cases hz : NodeSet.isEmpty z with
  | true =>
      exact rule2PartitionWitness_of_empty_z model x y z w assignment hz
  | false =>
      cases hw : NodeSet.isEmpty w with
      | true =>
          exact rule2PartitionWitness_of_empty_w model G projected
            x y z w assignment separated hw
      | false =>
          cases havoid :
              rule2WMeetsZAncestral model G x z w assignment with
          | false =>
              exact rule2PartitionWitness_of_w_avoids_z model G projected
                x y z w assignment disjoint havoid separated
          | true =>
              exact rule2PartitionWitness_of_w_split_closed model G
                x y z w assignment hextra havoidY

/-- Empty `Z` makes rule 3 an identity of kernels. -/
def rule3RectangularWitness_of_empty_z
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hz : NodeSet.isEmpty z = true) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  ProductRectangularCrossProductWitnessAt.of_kernel_eq model
    (rule3Left x y z w) (rule3Right x y z w) assignment
    (rule3Left_eq_rule3Right_of_empty_z x y z w hz)

/-- When `Z(W) = Z`, `Y` is evaluated the same under `do(X)` and
`do(X ∪ Z)`, because d-separation in `G_{\overline{X ∪ Z}}` forbids `Z`
from ancestoring `Y`. -/
theorem agreesOn_rule3Y_eq_of_z_avoids_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases hy : y child with
  | false =>
      rfl
  | true =>
      have hanc :
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y child =
            true :=
        FiniteLatentSCM.observedAncestorOf_self G
          (GraphMutilation.bar (NodeSet.union x z)) y hy
      have hclosed :=
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union x z) y assignment
      have hagree :
          forall i, FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y i =
              true ->
            ((rule3Left x y z w).intervention assignment i) =
              ((rule3Right x y z w).intervention assignment i) := by
        intro i hi
        have hz : z i = false := by
          cases hzi : z i with
          | false =>
              rfl
          | true =>
              have hfalse :=
                FiniteLatentSCM.rule3_z_not_ancestral_of_z_avoids_w G x y z w
                  disjoint hrem separated hzi
              simpa [FiniteLatentSCM.ancestralInBar] using
                (hfalse.symm.trans hi)
        have hinterL :
            (rule3Left x y z w).intervention assignment i =
              (if NodeSet.union x z i then some (assignment i)
                else none) := by
          simp [rule3Left, Kernel.intervention]
        have hinterR :
            (rule3Right x y z w).intervention assignment i =
              (if x i then some (assignment i) else none) := by
          simp [rule3Right, Kernel.intervention]
        have hxZ : NodeSet.union x z i = x i := by
          simp [NodeSet.union, hz]
        simp [hinterL, hinterR, hxZ]
      have heval :=
        FiniteLatentSCM.evalUnder_eq_on_of_intervention_agree_on_closed
          model
          ((rule3Left x y z w).intervention assignment)
          ((rule3Right x y z w).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) y)
          roots hclosed hagree child hanc
      simp [heval]

theorem agreesOn_rule3Y_eq_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) :=
  agreesOn_rule3Y_eq_of_z_avoids_w model G x y z w assignment disjoint
    (ObservedGraph.nonAncestorsOf_of_isEmpty G (GraphMutilation.bar x) z w hw)
    separated roots

/-- Evaluation agrees nodewise after adding `do(Z)` whenever no selected
`Z` vertex reaches the observed family in `G_{\overline{X ∪ Z}}`. -/
theorem evalUnder_bar_union_eq_on_of_z_not_ancestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z nodes : NodeSet S) (assignment : S.Assignment)
    (zAvoids : forall i, z i = true ->
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes i = false)
    (roots : model.latent.Assignment) :
    forall child, nodes child = true ->
      model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment) roots child =
        model.evalUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          roots child := by
  intro child childInNodes
  have childAncestor :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes child =
        true :=
    FiniteLatentSCM.observedAncestorOf_self G
      (GraphMutilation.bar (NodeSet.union x z)) nodes childInNodes
  have closed :=
    FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x z) nodes assignment
  have interventionsAgree : forall i,
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes i = true ->
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment i) =
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
            i) := by
    intro i ancestor
    have outsideZ : z i = false := by
      cases selected : z i with
      | false => rfl
      | true =>
          have impossible := zAvoids i selected
          rw [ancestor] at impossible
          contradiction
    have unionAtI : NodeSet.union x z i = x i := by
      simp [NodeSet.union, outsideZ]
    simp [Kernel.intervention, unionAtI]
  exact FiniteLatentSCM.evalUnder_eq_on_of_intervention_agree_on_closed
    model
    ((Kernel.mk NodeSet.empty (NodeSet.union x z)
      NodeSet.empty).intervention assignment)
    ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
    (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes)
    roots closed interventionsAgree child childAncestor

/--
A cylinder is invariant under adding `do(Z)` whenever no `Z` vertex reaches
its nodes in `G_{\overline{X ∪ Z}}`.

The ancestral set is backward-closed for the heavier intervention.  On that
set the two interventions agree, because a selected `Z` coordinate would
contradict the supplied non-ancestry fact.  This lemma is stated independently
of rule 3 so a future common block of `W` can use it directly.
-/
theorem agreesOn_evalUnder_bar_union_eq_of_z_not_ancestral
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z nodes : NodeSet S) (assignment : S.Assignment)
    (zAvoids : forall i, z i = true ->
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) nodes i = false)
    (roots : model.latent.Assignment) :
    Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment) roots) =
      Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          roots) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases hnodes : nodes child with
  | false => rfl
  | true =>
      have evaluated :=
        evalUnder_bar_union_eq_on_of_z_not_ancestral model G x z nodes
          assignment zAvoids roots child hnodes
      simp [evaluated]

/--
The conditioned `W` vertices that can be reached from `Z` in
`G_{\overline{X ∪ Z}}`.  These are exactly the vertices whose agreement
cylinder may change when `do(Z)` is added; they form the residual block of the
rule-3 node split.
-/
def rule3WInterventionSensitive (G : ObservedGraph S)
    (x z w : NodeSet S) : NodeSet S :=
  fun child =>
    w child &&
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (NodeSet.singleton child)) z

/-- The complementary `W` block is pointwise invariant under adding
`do(Z)`. -/
def rule3WInterventionInvariant (G : ObservedGraph S)
    (x z w : NodeSet S) : NodeSet S :=
  NodeSet.diff w (rule3WInterventionSensitive G x z w)

/--
Latent coordinates used by the common side of the rule-3 factorization: the
ancestors of `Y` after fixing `X ∪ W`, together with the ancestors of the
intervention-invariant `W` block under `do(X ∪ Z)`.
-/
def rule3YInvariantLatentMask (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) : Fin model.latent.count -> Bool :=
  fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root ||
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
          (rule3WInterventionInvariant G x z w)) root

theorem rule3WInterventionSensitive_subset_w (G : ObservedGraph S)
    (x z w : NodeSet S) :
    NodeSet.Subset (rule3WInterventionSensitive G x z w) w := by
  intro child selected
  exact (Bool.and_eq_true_iff.mp selected).1

/-- The invariant and sensitive blocks are disjoint by construction. -/
theorem rule3WInterventionSplit_disjoint (G : ObservedGraph S)
    (x z w : NodeSet S) :
    NodeSet.Disjoint (rule3WInterventionInvariant G x z w)
      (rule3WInterventionSensitive G x z w) :=
  NodeSet.Disjoint.diff_right w (rule3WInterventionSensitive G x z w)

/-- The invariant and sensitive blocks cover all conditioned vertices. -/
theorem rule3WInterventionSplit_union (G : ObservedGraph S)
    (x z w : NodeSet S) :
    NodeSet.union (rule3WInterventionInvariant G x z w)
      (rule3WInterventionSensitive G x z w) = w := by
  funext child
  have subset := rule3WInterventionSensitive_subset_w G x z w child
  simp [rule3WInterventionInvariant, NodeSet.union, NodeSet.diff]
  cases hw : w child with
  | false =>
      cases hs : rule3WInterventionSensitive G x z w child with
      | false => simp
      | true => exact (Bool.false_ne_true (hw.symm.trans (subset hs))).elim
  | true =>
      cases hs : rule3WInterventionSensitive G x z w child <;> simp

/-- No `Z` vertex ancestors the invariant block: any such walk would make
its endpoint intervention-sensitive by definition. -/
theorem rule3_z_not_ancestral_invariant_w
    (G : ObservedGraph S) (x z w : NodeSet S)
    {source : Fin S.count} (sourceInZ : z source = true) :
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
      (rule3WInterventionInvariant G x z w) source = false := by
  cases hanc :
      FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
        (rule3WInterventionInvariant G x z w) source with
  | false => rfl
  | true =>
      rcases (G.observedAncestorOf_eq_true_iff
          (GraphMutilation.bar (NodeSet.union x z))
          (rule3WInterventionInvariant G x z w) source).mp hanc with
        ⟨target, targetInvariant, walk⟩
      have targetInW : w target = true :=
        NodeSet.diff_subset_left w
          (rule3WInterventionSensitive G x z w) target targetInvariant
      have targetNotSensitive :
          rule3WInterventionSensitive G x z w target = false := by
        have disjoint := rule3WInterventionSplit_disjoint G x z w
          target targetInvariant
        exact disjoint
      have sourceAncestorsTarget :
          FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (NodeSet.singleton target) source = true :=
        (G.observedAncestorOf_eq_true_iff
          (GraphMutilation.bar (NodeSet.union x z))
          (NodeSet.singleton target) source).mpr
          ⟨target, (NodeSet.singleton_eq_true_iff target target).mpr rfl,
            walk⟩
      have meetsZ :
          NodeSet.meetsBool
            (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
              (NodeSet.singleton target)) z = true :=
        (NodeSet.meetsBool_eq_true_iff _ _).mpr
          ⟨source, sourceAncestorsTarget, sourceInZ⟩
      have targetSensitive :
          rule3WInterventionSensitive G x z w target = true :=
        Bool.and_eq_true_iff.mpr ⟨targetInW, meetsZ⟩
      rw [targetSensitive] at targetNotSensitive
      contradiction

/-- The invariant `W` block has the same agreement cylinder under
`do(X ∪ Z)` and `do(X)`. -/
theorem agreesOn_rule3WInterventionInvariant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (roots : model.latent.Assignment) :
    Kernel.agreesOn (rule3WInterventionInvariant G x z w) assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn (rule3WInterventionInvariant G x z w) assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) := by
  have invariant :=
    agreesOn_evalUnder_bar_union_eq_of_z_not_ancestral model G x z
      (rule3WInterventionInvariant G x z w) assignment
      (fun source sourceInZ =>
        rule3_z_not_ancestral_invariant_w G x z w sourceInZ)
      roots
  simpa [rule3Left, rule3Right, Kernel.intervention] using invariant

/-!
### The `Y`-connected component of the rule-3 conditioner

The intervention split above is useful but too coarse for the general rule:
an invariant `W` vertex need not share any dependency with `Y`, and two
conditioned vertices can couple latent coordinates that were otherwise on
different sides.  The finite component below therefore works at the level
of the actual latent product.  Two roots are adjacent when they can both
affect the same `W` cylinder under either rule-3 intervention.  Starting from
the roots needed by `Y`, finite reachability then closes the selected family
under every conditioning factor.

This is the constructive factor-graph analogue of taking the `Y` component
of the ancestral moral graph.  It uses only bounded Boolean reachability on
the explicitly enumerated latent roots.
-/

/-- A latent root can affect the agreement constraint for one conditioned
`W` vertex under at least one of the two rule-3 interventions. -/
def rule3WConditionRootRelevant (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (assignment : S.Assignment) (child : Fin S.count)
    (root : Fin model.latent.count) : Bool :=
  w child &&
    (model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty
          (localConditionAction (NodeSet.union x z) w child)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G
          (localConditionAction (NodeSet.union x z) w child)
          (NodeSet.singleton child)) root ||
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (localConditionAction x w child)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (localConditionAction x w child)
          (NodeSet.singleton child)) root)

/-- A checked observed route witnessing that one concrete latent root can
affect a local conditioning factor.  The route has already been embedded in
the graph of rule 3's path side condition.  Its endpoint may be conditioned,
but every proper route vertex is open given `X ∪ W`.

Keeping the incident source as data is important: a relevance witness can
start at the factor vertex itself, in which case that source is conditioned
and `properOpen` is deliberately vacuous there. -/
def Rule3LocalConditionRootWalk (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (child : Fin S.count) (root : Fin model.latent.count) : Prop :=
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      (GraphMutilation.bar
        (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w))).removeIncoming
          source = false /\
      Exists fun length : Nat =>
        Exists fun walk : FiniteReachability.ExactWalk
          (G.observedDirectedEdge
            (GraphMutilation.bar
              (NodeSet.union x
                (G.nonAncestorsOf (GraphMutilation.bar x) z w))))
          length source child =>
          forall node, node ∈ walk.nodes -> node ≠ child ->
            ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
              false

/-- Unpack a root-relevance Boolean into a route in the rule-3 graph.
Left-factor ancestry maps by incoming-cut inclusion.  Right-factor ancestry
uses `remapRule3RightLocalConditionWalk`, whose suffix argument excludes the
additional `Z(W)` cut constructively. -/
def rule3LocalConditionRootWalk_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true) :
    Rule3LocalConditionRootWalk model G x z w child root := by
  have relevantParts := Bool.and_eq_true_iff.mp relevant
  have childInW : w child = true := relevantParts.1
  cases leftRelevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty
        (localConditionAction (NodeSet.union x z) w child)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G
        (localConditionAction (NodeSet.union x z) w child)
        (NodeSet.singleton child)) root with
  | true =>
    let action := localConditionAction (NodeSet.union x z) w child
    let intervention :=
      (Kernel.mk NodeSet.empty action NodeSet.empty).intervention assignment
    let ancestors := FiniteLatentSCM.ancestralInBar G action
      (NodeSet.singleton child)
    rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
        root).mp (by
          simpa [intervention, ancestors, action] using leftRelevant) with
      ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
    rcases (G.observedAncestorOf_eq_true_iff (GraphMutilation.bar action)
        (NodeSet.singleton child) source).mp (by
          simpa [FiniteLatentSCM.ancestralInBar, ancestors, action] using
            sourceAncestor) with ⟨target, targetSelected, bounded⟩
    have targetEq : target = child :=
      (NodeSet.singleton_eq_true_iff child target).mp targetSelected
    subst target
    rcases bounded with ⟨length, _bound, exactWalk⟩
    rcases exactWalk with ⟨walk⟩
    have sourceOutsideAction : action source = false := by
      simpa [intervention, Kernel.intervention] using sourceFree
    have sourceOutsideX : x source = false := by
      cases selected : x source with
      | false => rfl
      | true =>
          have inAction : action source = true := by
            simp [action, localConditionAction, NodeSet.union, selected]
          rw [inAction] at sourceOutsideAction
          contradiction
    have sourceOutsideRemovable :
        G.nonAncestorsOf (GraphMutilation.bar x) z w source = false := by
      cases removable :
          G.nonAncestorsOf (GraphMutilation.bar x) z w source with
      | false => rfl
      | true =>
          have sourceInZ := ObservedGraph.nonAncestorsOf_subset_actions G
            (GraphMutilation.bar x) z w source removable
          have inAction : action source = true := by
            simp [action, localConditionAction, NodeSet.union, sourceInZ]
          rw [inAction] at sourceOutsideAction
          contradiction
    have sourceIncoming : (GraphMutilation.bar
        (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w))).removeIncoming
        source = false := by
      change NodeSet.union x
        (G.nonAncestorsOf (GraphMutilation.bar x) z w) source = false
      simp [NodeSet.union, sourceOutsideX, sourceOutsideRemovable]
    let mapped := remapRule3LeftLocalConditionWalk G x z w child walk
    refine ⟨source, sourceIncident, sourceIncoming, length, mapped, ?_⟩
    intro node member notTarget
    have originalMember : node ∈ walk.nodes := by
      simpa [mapped] using member
    by_cases atSource : node = source
    · subst node
      exact localConditionWalk_source_open_of_free G
        (NodeSet.union x z) x w (NodeSet.subset_union_left x z)
        assignment child walk notTarget (by
          simpa [intervention, action] using sourceFree)
    · exact localConditionWalk_internal_open G
        (NodeSet.union x z) x w (NodeSet.subset_union_left x z)
        child walk originalMember atSource notTarget
  | false =>
    have rightRelevant : model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (localConditionAction x w child)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G
          (localConditionAction x w child) (NodeSet.singleton child)) root =
          true := by
      simpa [leftRelevant] using relevantParts.2
    let action := localConditionAction x w child
    let intervention :=
      (Kernel.mk NodeSet.empty action NodeSet.empty).intervention assignment
    let ancestors := FiniteLatentSCM.ancestralInBar G action
      (NodeSet.singleton child)
    rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
        root).mp (by
          simpa [intervention, ancestors, action] using rightRelevant) with
      ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
    rcases (G.observedAncestorOf_eq_true_iff (GraphMutilation.bar action)
        (NodeSet.singleton child) source).mp (by
          simpa [FiniteLatentSCM.ancestralInBar, ancestors, action] using
            sourceAncestor) with ⟨target, targetSelected, bounded⟩
    have targetEq : target = child :=
      (NodeSet.singleton_eq_true_iff child target).mp targetSelected
    subst target
    rcases bounded with ⟨length, _bound, exactWalk⟩
    rcases exactWalk with ⟨walk⟩
    have sourceOutsideAction : action source = false := by
      simpa [intervention, Kernel.intervention] using sourceFree
    have sourceOutsideX : x source = false := by
      cases selected : x source with
      | false => rfl
      | true =>
          have inAction : action source = true := by
            simp [action, localConditionAction, NodeSet.union, selected]
          rw [inAction] at sourceOutsideAction
          contradiction
    have xSubset : NodeSet.Subset x action := by
      intro node selected
      simp [action, localConditionAction, NodeSet.union, selected]
    have walkInBarX :=
      FiniteLatentSCM.remapBarWalk_of_incoming_subset G xSubset walk
    have sourceAncestorsW :
        G.observedAncestorOf (GraphMutilation.bar x) w source = true :=
      G.observedAncestorOf_of_mem_walk (GraphMutilation.bar x) w
        walkInBarX childInW walkInBarX.mem_source
    have sourceOutsideRemovable :
        G.nonAncestorsOf (GraphMutilation.bar x) z w source = false := by
      cases removable :
          G.nonAncestorsOf (GraphMutilation.bar x) z w source with
      | false => rfl
      | true =>
          simp [ObservedGraph.nonAncestorsOf, sourceAncestorsW] at removable
    have sourceIncoming : (GraphMutilation.bar
        (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w))).removeIncoming
        source = false := by
      change NodeSet.union x
        (G.nonAncestorsOf (GraphMutilation.bar x) z w) source = false
      simp [NodeSet.union, sourceOutsideX, sourceOutsideRemovable]
    let mapped := remapRule3RightLocalConditionWalk G x z w child childInW
      walk
    refine ⟨source, sourceIncident, sourceIncoming, length, mapped, ?_⟩
    intro node member notTarget
    have originalMember : node ∈ walk.nodes := by
      simpa [mapped] using member
    by_cases atSource : node = source
    · subst node
      exact localConditionWalk_source_open_of_free G x x w
        (fun _node selected => selected) assignment child walk notTarget
        (by simpa [intervention, action] using sourceFree)
    · exact localConditionWalk_internal_open G x x w
        (fun _node selected => selected) child walk originalMember atSource
        notTarget

/-- Two latent coordinates are joined when one conditioned `W` equation can
observe both of them under the left or right rule-3 intervention. -/
def rule3WConditionRootAdjacent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x z w : NodeSet S)
    (assignment : S.Assignment)
    (left right : Fin model.latent.count) : Bool :=
  finAny S.count (fun child =>
    rule3WConditionRootRelevant model G x z w assignment child left &&
      rule3WConditionRootRelevant model G x z w assignment child right)

/-- The latent component generated by the `Y` cylinder and closed through
all rule-3 conditioning factors. -/
def rule3YConditionLatentComponent (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (root : Fin model.latent.count) : Bool :=
  finAny model.latent.count (fun seed =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) seed &&
      FiniteReachability.within finBeq
        (List.ofFn (fun latent : Fin model.latent.count => latent))
        (rule3WConditionRootAdjacent model G x z w assignment)
        (List.ofFn (fun latent : Fin model.latent.count => latent)).length
        seed root)

/-- A conditioned vertex belongs to the common block exactly when one of
its relevant roots lies in the `Y`-connected component. -/
def rule3WConditionCommon (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) : NodeSet S :=
  fun child =>
    finAny model.latent.count (fun root =>
      rule3WConditionRootRelevant model G x z w assignment child root &&
        rule3YConditionLatentComponent model G x y z w assignment root)

/-- Every other conditioned vertex is assigned to the complementary
residual block. -/
def rule3WConditionResidual (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) : NodeSet S :=
  NodeSet.diff w (rule3WConditionCommon model G x y z w assignment)

/-- A conditioned vertex whose *local* equation can still be reached from
`Z` after earlier conditioned coordinates have been fixed. -/
def rule3WLocalInterventionSensitive (G : ObservedGraph S)
    (x z w : NodeSet S) : NodeSet S :=
  fun child =>
    w child &&
      NodeSet.meetsBool
        (FiniteLatentSCM.ancestralInBar G
          (localConditionAction (NodeSet.union x z) w child)
          (NodeSet.singleton child)) z

/-- The complementary local factors are pointwise invariant under adding
`do(Z)`.  This is finer than `rule3WInterventionInvariant`: fixing earlier
conditioned vertices can block a directed `Z` path before it reaches the
current local equation. -/
def rule3WLocalInterventionInvariant (G : ObservedGraph S)
    (x z w : NodeSet S) : NodeSet S :=
  NodeSet.diff w (rule3WLocalInterventionSensitive G x z w)

/-- An exact rule-3-graph route from a selected `Z` endpoint into one locally
sensitive conditioning factor.  All proper vertices are open given `X ∪ W`;
the terminal `W` vertex is retained as the activated collider at which this
route will meet the factor-component side. -/
def Rule3LocalSensitivityWalk (G : ObservedGraph S)
    (x z w : NodeSet S) (child : Fin S.count) : Prop :=
  Exists fun source : Fin S.count =>
    z source = true /\
      Exists fun length : Nat =>
        Exists fun walk : FiniteReachability.ExactWalk
          (G.observedDirectedEdge
            (GraphMutilation.bar
              (NodeSet.union x
                (G.nonAncestorsOf (GraphMutilation.bar x) z w))))
          length source child =>
          forall node, node ∈ walk.nodes -> node ≠ child ->
            ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
              false

/-- Unpack local intervention sensitivity into its open route from `Z`.
The caller supplies only the elementary endpoint fact that `Z` is open under
the conditioning family; `FourWayDisjoint` provides exactly this fact in the
published rule-3 application. -/
def rule3LocalSensitivityWalk_of_sensitive
    (G : ObservedGraph S) (x z w : NodeSet S)
    (child : Fin S.count)
    (sensitive : rule3WLocalInterventionSensitive G x z w child = true)
    (zOpen : forall source, z source = true ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
        false) :
    Rule3LocalSensitivityWalk G x z w child := by
  have parts := Bool.and_eq_true_iff.mp sensitive
  have childInW : w child = true := parts.1
  rcases (NodeSet.meetsBool_eq_true_iff _ _).mp parts.2 with
    ⟨source, sourceAncestor, sourceInZ⟩
  let action := localConditionAction (NodeSet.union x z) w child
  rcases (G.observedAncestorOf_eq_true_iff (GraphMutilation.bar action)
      (NodeSet.singleton child) source).mp (by
        simpa [FiniteLatentSCM.ancestralInBar, action] using
          sourceAncestor) with ⟨target, targetSelected, bounded⟩
  have targetEq : target = child :=
    (NodeSet.singleton_eq_true_iff child target).mp targetSelected
  subst target
  rcases bounded with ⟨length, _bound, exactWalk⟩
  rcases exactWalk with ⟨walk⟩
  let mapped := remapRule3LeftLocalConditionWalk G x z w child walk
  refine ⟨source, sourceInZ, length, mapped, ?_⟩
  intro node member notTarget
  have originalMember : node ∈ walk.nodes := by
    simpa [mapped] using member
  by_cases atSource : node = source
  · subst node
    exact zOpen source sourceInZ
  · exact localConditionWalk_internal_open G
      (NodeSet.union x z) x w (NodeSet.subset_union_left x z)
      child walk originalMember atSource notTarget

/-- A free ancestral observed representative showing that a concrete latent
root lies on the `Z` side of rule 3's canonical moral separator.

The incoming-cut and ancestry fields are retained alongside openness.  They
are precisely the hypotheses needed to compare two representatives of the
same concrete root through the projected bidirected graph; storing them here
keeps that later comparison independent of how either route was obtained. -/
def Rule3RootMoralRightWitness (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (root : Fin model.latent.count) : Prop :=
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      mutilation.removeIncoming source = false /\
        G.ancestorOf mutilation targets (.observed source) = true /\
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
            false /\
            G.moralLeftSide mutilation y z (NodeSet.union x w)
              (.observed source) = false

/-- A free ancestral observed representative showing that a concrete latent
root lies in the `Y` component of rule 3's canonical moral separator.  Its
field order mirrors `Rule3RootMoralRightWitness`, so the two packages can be
compared without reconstructing route-specific invariants. -/
def Rule3RootMoralLeftWitness (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (root : Fin model.latent.count) : Prop :=
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  Exists fun source : Fin S.count =>
    model.latent.incident root source = true /\
      mutilation.removeIncoming source = false /\
        G.ancestorOf mutilation targets (.observed source) = true /\
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
            false /\
            G.moralLeftSide mutilation y z (NodeSet.union x w)
              (.observed source) = true

/-- An open ancestral parent of one conditioned `W` factor that already lies
on the `Y` side of rule 3's canonical moral separator.

The parent may be observed or a canonical latent-pair vertex.  This is the
right induction invariant for the finite factor/root component: moralizing at
the conditioned child transfers the side label to every other open ancestral
parent without retaining the route that originally reached the factor. -/
def Rule3FactorMoralLeftParent (G : ObservedGraph S)
    (x y z w : NodeSet S) (child : Fin S.count) : Prop :=
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  Exists fun parent : SeparationNode S =>
    G.expandedMutilatedEdge mutilation parent (.observed child) = true /\
      G.ancestorOf mutilation targets parent = true /\
        ObservedGraph.blockedBy (NodeSet.union x w) parent = false /\
          G.moralLeftSide mutilation y z (NodeSet.union x w) parent = true

/-- At a conditioned collider, any second open ancestral parent inherits the
`Y` moral side from a stored factor parent.  Equality of the two parents is
handled directly; otherwise the two incoming edges generate the moral edge
that marries them. -/
theorem Rule3FactorMoralLeftParent.marries
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (child : Fin S.count)
    (witness : Rule3FactorMoralLeftParent G x y z w child)
    (childConditioned : NodeSet.union x w child = true)
    (other : SeparationNode S)
    (otherEdge : G.expandedMutilatedEdge
      (GraphMutilation.bar
        (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w)))
      other (.observed child) = true)
    (otherAncestor : G.ancestorOf
      (GraphMutilation.bar
        (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w)))
      (NodeSet.union y (NodeSet.union z (NodeSet.union x w))) other = true)
    (otherOpen : ObservedGraph.blockedBy (NodeSet.union x w) other = false) :
    G.moralLeftSide
      (GraphMutilation.bar
        (NodeSet.union x
          (G.nonAncestorsOf (GraphMutilation.bar x) z w)))
      y z (NodeSet.union x w) other = true := by
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases witness with
    ⟨parent, parentEdge, parentAncestor, parentOpen, parentSide⟩
  have equalityCases : SeparationNode.beq parent other = true ∨
      SeparationNode.beq parent other = false := by
    cases value : SeparationNode.beq parent other with
    | false => exact Or.inr rfl
    | true => exact Or.inl rfl
  rcases equalityCases with sameValue | sameValue
  · have same := (SeparationNode.beq_eq_true_iff parent other).mp sameValue
    exact Eq.mp (congrArg (fun node =>
      G.moralLeftSide mutilation y z (NodeSet.union x w) node = true) same)
      parentSide
  · have different : parent ≠ other :=
      (SeparationNode.beq_eq_false_iff parent other).mp sameValue
    have childTarget : targets child = true := by
      have conditionedPart : x child = true ∨ w child = true :=
        Bool.or_eq_true_iff.mp (by
          simpa [NodeSet.union] using childConditioned)
      rcases conditionedPart with childInX | childInW
      · simp [targets, NodeSet.union, childInX]
      · simp [targets, NodeSet.union, childInW]
    have childAncestor : G.ancestorOf mutilation targets
        (.observed child) = true :=
      G.ancestorOf_target mutilation targets childTarget
    have collider : PathSpecification.IsCollider G mutilation parent
        (.observed child) other := ⟨parentEdge, otherEdge⟩
    have ancestralMoral := G.ancestralMoralEdge_of_collider mutilation
      targets parentAncestor childAncestor otherAncestor different collider
    have moral := G.moralOpenEdge_of_ancestral mutilation targets
      (NodeSet.union x w) parentOpen otherOpen ancestralMoral
    have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation y z
      (NodeSet.union x w) moral
    rw [parentSide] at sameSide
    exact sameSide.symm

/-- A root already represented on the `Y` moral side supplies a left-side
parent for every local conditioning factor it can affect.

If the relevance route is nontrivial, its open source shares the concrete
root with the stored representative; the route is then followed to its final
observed parent.  If the root is incident to the factor vertex itself, the
projected latent-pair vertex between that child and the stored representative
is the required parent.  Thus both the ordinary and zero-length relevance
routes inhabit the same factor-level induction invariant. -/
theorem rule3FactorMoralLeftParent_of_root_witness
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (rootWitness : Rule3RootMoralLeftWitness model G x y z w root)
    (relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true) :
    Rule3FactorMoralLeftParent G x y z w child := by
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases rootWitness with
    ⟨leftSource, leftIncident, leftIncoming, leftAncestor, leftOpen,
      leftSide⟩
  rcases rule3LocalConditionRootWalk_of_relevant model G x z w assignment
      child root relevant with
    ⟨routeSource, routeIncident, routeIncoming, routeLength, route,
      routeProperOpen⟩
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp relevant).1
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  by_cases routeReflexive : routeSource = child
  · subst routeSource
    have leftDifferent : leftSource ≠ child := by
      intro same
      subst leftSource
      have childOpen : NodeSet.union x w child = false := by
        simpa [ObservedGraph.blockedBy] using leftOpen
      rw [childConditioned] at childOpen
      contradiction
    have bidirected := model.bidirected_of_shared_latent G projected root
      leftDifferent leftIncident routeIncident
    let latent : SeparationNode S := .latentPair leftSource child
    have leftIncoming' : mutilation.removeIncoming leftSource = false := by
      simpa [mutilation] using leftIncoming
    have childIncoming' : mutilation.removeIncoming child = false := by
      simpa [mutilation] using routeIncoming
    have edgeLeft : G.expandedMutilatedEdge mutilation latent
        (.observed leftSource) = true := by
      have self : finBeq leftSource leftSource = true :=
        (finBeq_eq_true_iff leftSource leftSource).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        leftIncoming', self]
    have edgeChild : G.expandedMutilatedEdge mutilation latent
        (.observed child) = true := by
      have self : finBeq child child = true :=
        (finBeq_eq_true_iff child child).mpr rfl
      simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
        childIncoming', self]
    have latentAncestor : G.ancestorOf mutilation targets latent = true :=
      G.ancestorOf_prepend mutilation targets edgeLeft leftAncestor
    have leftLatentMoral : G.MoralOpenEdge mutilation targets
        (NodeSet.union x w) (.observed leftSource) latent = true :=
      G.moralOpenEdge_of_ancestral mutilation targets (NodeSet.union x w)
        leftOpen (by dsimp [latent]; rfl)
        (G.ancestralMoralEdge_of_adjacent mutilation targets leftAncestor
          latentAncestor (Or.inr edgeLeft))
    have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation y z
      (NodeSet.union x w) leftLatentMoral
    have latentSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
        latent = true := by
      rw [leftSide] at sameSide
      exact sameSide.symm
    exact ⟨latent, edgeChild, latentAncestor, by dsimp [latent]; rfl,
      latentSide⟩
  · have routeOpen := routeProperOpen routeSource route.mem_source
      routeReflexive
    have routeObservedAncestor := G.observedAncestorOf_of_mem_walk
      mutilation targets route childTarget route.mem_source
    have routeAncestor := FiniteLatentSCM.ancestorOf_of_observedAncestorOf
      G mutilation targets routeSource routeObservedAncestor
    have routeSameSide :=
      FiniteLatentSCM.moralLeftSide_eq_of_shared_latent model G projected
        mutilation y z (NodeSet.union x w) root leftSource routeSource
        leftIncident routeIncident leftIncoming routeIncoming leftAncestor
        routeAncestor (by
          simpa [ObservedGraph.blockedBy] using leftOpen) (by
          simpa [ObservedGraph.blockedBy] using routeOpen)
    have routeSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
        (.observed routeSource) = true := by
      rw [leftSide] at routeSameSide
      exact routeSameSide.symm
    rcases exists_observedDirectedWalk_prefix_last G mutilation route
        routeReflexive with
      ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
    have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
        node ≠ child := by
      intro node member equal
      have parentDirected : S.directed parent child = true :=
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
      have parentEarlier := S.directed_earlier parentDirected
      have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
        prefixWalk member
      subst node
      exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
    have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
        ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
          false := by
      intro node member
      exact routeProperOpen node (prefixSubset node member)
        (prefixNotChild node member)
    have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
        G.ancestorOf mutilation targets (.observed node) = true := by
      intro node member
      have observed := G.observedAncestorOf_of_mem_walk mutilation targets
        route childTarget (prefixSubset node member)
      exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
        targets node observed
    have routeToParent := moralLeftSide_eq_of_open_observed_walk G
      mutilation y z (NodeSet.union x w) prefixWalk prefixOpen (by
        simpa [targets] using prefixAncestor)
    have parentSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
        (.observed parent) = true := by
      rw [routeSide] at routeToParent
      exact routeToParent.symm
    exact ⟨.observed parent, last,
      prefixAncestor parent prefixWalk.mem_target,
      prefixOpen parent prefixWalk.mem_target, parentSide⟩

/-- A locally sensitive factor cannot have a parent on the `Y` moral side.
The open route from `Z` supplies a second parent of the conditioned factor;
moralization marries its final parent to the stored left parent, and the open
prefix transports that label back to `Z`, contradicting path separation. -/
theorem Rule3FactorMoralLeftParent.excludes_sensitive
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (child : Fin S.count)
    (witness : Rule3FactorMoralLeftParent G x y z w child)
    (sensitive : rule3WLocalInterventionSensitive G x z w child = true) :
    False := by
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp sensitive).1
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  have zOpen : forall source, z source = true ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
        false := by
    intro source sourceInZ
    exact FiniteLatentSCM.blockedBy_false_of_mem_z x y z w disjoint
      sourceInZ
  rcases rule3LocalSensitivityWalk_of_sensitive G x z w child sensitive
      zOpen with
    ⟨zSource, zSourceInZ, zLength, zWalk, zProperOpen⟩
  have zSourceDifferent : zSource ≠ child := by
    intro equal
    subst zSource
    have impossible := disjoint.zw child zSourceInZ
    rw [childInW] at impossible
    contradiction
  rcases exists_observedDirectedWalk_prefix_last G mutilation zWalk
      zSourceDifferent with
    ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
  have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
      node ≠ child := by
    intro node member equal
    have parentDirected : S.directed parent child = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
    have parentEarlier := S.directed_earlier parentDirected
    have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
      prefixWalk member
    subst node
    exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
  have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) = false := by
    intro node member
    exact zProperOpen node (prefixSubset node member)
      (prefixNotChild node member)
  have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      zWalk childTarget (prefixSubset node member)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have parentSide := Rule3FactorMoralLeftParent.marries G x y z w child
    witness childConditioned (.observed parent) last
    (prefixAncestor parent prefixWalk.mem_target)
    (prefixOpen parent prefixWalk.mem_target)
  have sourceToParent := moralLeftSide_eq_of_open_observed_walk G
    mutilation y z (NodeSet.union x w) prefixWalk prefixOpen (by
      simpa [targets] using prefixAncestor)
  have sourceSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
      (.observed zSource) = true := by
    rw [parentSide] at sourceToParent
    exact sourceToParent
  have separated' : PathSpecification.PathDSeparated G mutilation y z
      (NodeSet.union x w) := by
    simpa [mutilation, GraphMutilation.bar] using separated
  have zSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
      (.observed zSource) = false :=
    G.moralLeftSide_not_of_right mutilation y z (NodeSet.union x w)
      separated' zSource zSourceInZ (zOpen zSource zSourceInZ)
  rw [zSide] at sourceSide
  contradiction

/-- A nonincident root relevant to a factor with a stored left parent obtains
an ordinary observed left-side representative.  Its relevance route has a
genuine final edge into the conditioned child; moralizing that collider puts
the final route parent on the left, and the open prefix transports the label
back to the route source incident to the root. -/
theorem rule3RootMoralLeftWitness_of_factor_parent_relevant_not_incident
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (factorParent : Rule3FactorMoralLeftParent G x y z w child)
    (relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true)
    (notIncident : model.latent.incident root child = false) :
    Rule3RootMoralLeftWitness model G x y z w root := by
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases rule3LocalConditionRootWalk_of_relevant model G x z w assignment
      child root relevant with
    ⟨source, sourceIncident, sourceIncoming, length, route,
      routeProperOpen⟩
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp relevant).1
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  have sourceDifferent : source ≠ child := by
    intro equal
    subst source
    rw [sourceIncident] at notIncident
    contradiction
  have sourceOpen := routeProperOpen source route.mem_source sourceDifferent
  have sourceObservedAncestor := G.observedAncestorOf_of_mem_walk
    mutilation targets route childTarget route.mem_source
  have sourceAncestor := FiniteLatentSCM.ancestorOf_of_observedAncestorOf
    G mutilation targets source sourceObservedAncestor
  rcases exists_observedDirectedWalk_prefix_last G mutilation route
      sourceDifferent with
    ⟨prefixLength, parent, prefixWalk, last, prefixSubset⟩
  have prefixNotChild : forall node, node ∈ prefixWalk.nodes ->
      node ≠ child := by
    intro node member equal
    have parentDirected : S.directed parent child = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp last).1).1
    have parentEarlier := S.directed_earlier parentDirected
    have nodeLe := observedDirectedWalk_node_le_target_of_mem G mutilation
      prefixWalk member
    subst node
    exact (Nat.not_lt_of_ge nodeLe parentEarlier).elim
  have prefixOpen : forall node, node ∈ prefixWalk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) = false := by
    intro node member
    exact routeProperOpen node (prefixSubset node member)
      (prefixNotChild node member)
  have prefixAncestor : forall node, node ∈ prefixWalk.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      route childTarget (prefixSubset node member)
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have parentSide := Rule3FactorMoralLeftParent.marries G x y z w child
    factorParent childConditioned (.observed parent) last
    (prefixAncestor parent prefixWalk.mem_target)
    (prefixOpen parent prefixWalk.mem_target)
  have sourceToParent := moralLeftSide_eq_of_open_observed_walk G
    mutilation y z (NodeSet.union x w) prefixWalk prefixOpen (by
      simpa [targets] using prefixAncestor)
  have sourceSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
      (.observed source) = true := by
    rw [parentSide] at sourceToParent
    exact sourceToParent
  exact ⟨source, sourceIncident, sourceIncoming, sourceAncestor,
    sourceOpen, sourceSide⟩

/-- A conditioned `W` vertex survives rule 3's incoming cut.  It is outside
`X` by four-way disjointness and outside `Z(W)` because that removable family
is a subset of `Z`, which is disjoint from `W`. -/
theorem rule3_w_not_removeIncoming
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (disjoint : FourWayDisjoint x y z w)
    (child : Fin S.count) (childInW : w child = true) :
    (GraphMutilation.bar
      (NodeSet.union x
        (G.nonAncestorsOf (GraphMutilation.bar x) z w))).removeIncoming
      child = false := by
  have outsideX : x child = false := disjoint.xw.symm child childInW
  have outsideZ : z child = false := disjoint.zw.symm child childInW
  have outsideRemovable :
      G.nonAncestorsOf (GraphMutilation.bar x) z w child = false := by
    cases removable :
        G.nonAncestorsOf (GraphMutilation.bar x) z w child with
    | false => rfl
    | true =>
        have childInZ := ObservedGraph.nonAncestorsOf_subset_actions G
          (GraphMutilation.bar x) z w child removable
        rw [outsideZ] at childInZ
        contradiction
  change NodeSet.union x
    (G.nonAncestorsOf (GraphMutilation.bar x) z w) child = false
  simp [NodeSet.union, outsideX, outsideRemovable]

/-- Transport a left-side factor parent across one concrete latent root.

The root affects both the current and next local factors.  If it is not
directly incident to the current child, the current collider produces an
ordinary observed root witness, which the generic constructor routes into
the next factor.  If it is directly incident to the current child, projection
materializes the root as a canonical latent-pair parent using either the open
source of the next relevance route or the next child itself.  The latter is
the direct/direct case: the same latent-pair vertex is married to the stored
parent at the current child and is already a parent of the next child.

This single transfer lemma is the inductive step needed for arbitrary finite
root-component walks; it does not enumerate walk depths. -/
theorem rule3FactorMoralLeftParent_transfer
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (fromChild toChild : Fin S.count) (root : Fin model.latent.count)
    (fromParent : Rule3FactorMoralLeftParent G x y z w fromChild)
    (fromRelevant : rule3WConditionRootRelevant model G x z w assignment
      fromChild root = true)
    (toRelevant : rule3WConditionRootRelevant model G x z w assignment
      toChild root = true) :
    Rule3FactorMoralLeftParent G x y z w toChild := by
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  have fromChildInW : w fromChild = true :=
    (Bool.and_eq_true_iff.mp fromRelevant).1
  have toChildInW : w toChild = true :=
    (Bool.and_eq_true_iff.mp toRelevant).1
  have fromChildConditioned : NodeSet.union x w fromChild = true := by
    simp [NodeSet.union, fromChildInW]
  have fromChildTarget : targets fromChild = true := by
    simp [targets, NodeSet.union, fromChildInW]
  cases fromIncident : model.latent.incident root fromChild with
  | false =>
      have rootWitness :=
        rule3RootMoralLeftWitness_of_factor_parent_relevant_not_incident
          model G x y z w assignment fromChild root fromParent fromRelevant
          fromIncident
      exact rule3FactorMoralLeftParent_of_root_witness model G projected
        x y z w assignment toChild root rootWitness toRelevant
  | true =>
      cases toIncident : model.latent.incident root toChild with
      | false =>
          rcases rule3LocalConditionRootWalk_of_relevant model G x z w
              assignment toChild root toRelevant with
            ⟨source, sourceIncident, sourceIncoming, length, route,
              routeProperOpen⟩
          have sourceDifferent : source ≠ toChild := by
            intro equal
            subst source
            rw [sourceIncident] at toIncident
            contradiction
          have sourceOpen := routeProperOpen source route.mem_source
            sourceDifferent
          have toChildTarget : targets toChild = true := by
            simp [targets, NodeSet.union, toChildInW]
          have sourceObservedAncestor := G.observedAncestorOf_of_mem_walk
            mutilation targets route toChildTarget route.mem_source
          have sourceAncestor :=
            FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
              targets source sourceObservedAncestor
          have sourceDifferentFromCurrent : source ≠ fromChild := by
            intro equal
            subst source
            have sourceOutside : NodeSet.union x w fromChild = false := by
              simpa [ObservedGraph.blockedBy] using sourceOpen
            rw [fromChildConditioned] at sourceOutside
            contradiction
          have bidirected := model.bidirected_of_shared_latent G projected
            root sourceDifferentFromCurrent.symm fromIncident sourceIncident
          let latent : SeparationNode S := .latentPair fromChild source
          have fromIncoming : mutilation.removeIncoming fromChild = false := by
            simpa [mutilation] using
              rule3_w_not_removeIncoming G x y z w disjoint fromChild
                fromChildInW
          have sourceIncoming' : mutilation.removeIncoming source = false := by
            simpa [mutilation] using sourceIncoming
          have edgeFrom : G.expandedMutilatedEdge mutilation latent
              (.observed fromChild) = true := by
            have self : finBeq fromChild fromChild = true :=
              (finBeq_eq_true_iff fromChild fromChild).mpr rfl
            simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
              fromIncoming, self]
          have edgeSource : G.expandedMutilatedEdge mutilation latent
              (.observed source) = true := by
            have self : finBeq source source = true :=
              (finBeq_eq_true_iff source source).mpr rfl
            simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
              sourceIncoming', self]
          have latentAncestor : G.ancestorOf mutilation targets latent =
              true :=
            G.ancestorOf_prepend mutilation targets edgeSource sourceAncestor
          have latentSide := Rule3FactorMoralLeftParent.marries G x y z w
            fromChild fromParent fromChildConditioned latent edgeFrom
            latentAncestor (by dsimp [latent]; rfl)
          have latentSourceMoral : G.MoralOpenEdge mutilation targets
              (NodeSet.union x w) latent (.observed source) = true :=
            G.moralOpenEdge_of_ancestral mutilation targets
              (NodeSet.union x w) (by dsimp [latent]; rfl) sourceOpen
              (G.ancestralMoralEdge_of_adjacent mutilation targets
                latentAncestor sourceAncestor (Or.inl edgeSource))
          have sameSide := moralLeftSide_eq_of_moralOpenEdge G mutilation
            y z (NodeSet.union x w) latentSourceMoral
          have sourceSide : G.moralLeftSide mutilation y z
              (NodeSet.union x w) (.observed source) = true := by
            rw [latentSide] at sameSide
            exact sameSide.symm
          have rootWitness : Rule3RootMoralLeftWitness model G x y z w
              root :=
            ⟨source, sourceIncident, sourceIncoming, sourceAncestor,
              sourceOpen, sourceSide⟩
          exact rule3FactorMoralLeftParent_of_root_witness model G projected
            x y z w assignment toChild root rootWitness toRelevant
      | true =>
          by_cases sameChild : fromChild = toChild
          · subst toChild
            exact fromParent
          · have bidirected := model.bidirected_of_shared_latent G
              projected root sameChild fromIncident toIncident
            let latent : SeparationNode S := .latentPair fromChild toChild
            have fromIncoming : mutilation.removeIncoming fromChild = false := by
              simpa [mutilation] using
                rule3_w_not_removeIncoming G x y z w disjoint fromChild
                  fromChildInW
            have toIncoming : mutilation.removeIncoming toChild = false := by
              simpa [mutilation] using
                rule3_w_not_removeIncoming G x y z w disjoint toChild
                  toChildInW
            have edgeFrom : G.expandedMutilatedEdge mutilation latent
                (.observed fromChild) = true := by
              have self : finBeq fromChild fromChild = true :=
                (finBeq_eq_true_iff fromChild fromChild).mpr rfl
              simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
                fromIncoming, self]
            have edgeTo : G.expandedMutilatedEdge mutilation latent
                (.observed toChild) = true := by
              have self : finBeq toChild toChild = true :=
                (finBeq_eq_true_iff toChild toChild).mpr rfl
              simp [latent, ObservedGraph.expandedMutilatedEdge, bidirected,
                toIncoming, self]
            have fromAncestor : G.ancestorOf mutilation targets
                (.observed fromChild) = true :=
              G.ancestorOf_target mutilation targets fromChildTarget
            have latentAncestor : G.ancestorOf mutilation targets latent =
                true :=
              G.ancestorOf_prepend mutilation targets edgeFrom fromAncestor
            have latentSide := Rule3FactorMoralLeftParent.marries G x y z w
              fromChild fromParent fromChildConditioned latent edgeFrom
              latentAncestor (by dsimp [latent]; rfl)
            exact ⟨latent, edgeTo, latentAncestor,
              by dsimp [latent]; rfl, latentSide⟩

/-- Induction state at one latent root: the root is relevant to a conditioned
factor that already has a parent on the `Y` moral side. -/
def Rule3RootMoralLeftContact (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (root : Fin model.latent.count) : Prop :=
  Exists fun child : Fin S.count =>
    Rule3FactorMoralLeftParent G x y z w child /\
      rule3WConditionRootRelevant model G x z w assignment child root = true

/-- Carry a factor-parent contact along an arbitrary exact walk in the
root-adjacency graph, then route the terminal root into a requested factor.

Each adjacency edge names one local factor relevant to both consecutive
roots.  `rule3FactorMoralLeftParent_transfer` moves the stored factor parent
through the current root to that edge factor; the second relevance witness
then becomes the contact for the next root.  Recursion is on the exact walk
itself, so this covers every finite engine-computed component path without a
depth bound or a family of nested special cases. -/
theorem rule3FactorMoralLeftParent_of_contact_walk
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    {length : Nat} {source terminal : Fin model.latent.count}
    (walk : FiniteReachability.ExactWalk
      (rule3WConditionRootAdjacent model G x z w assignment)
      length source terminal) :
    Rule3RootMoralLeftContact model G x y z w assignment source ->
      forall targetChild,
        rule3WConditionRootRelevant model G x z w assignment
          targetChild terminal = true ->
        Rule3FactorMoralLeftParent G x y z w targetChild := by
  induction walk with
  | refl node =>
      intro contact targetChild targetRelevant
      rcases contact with
        ⟨fromChild, fromParent, fromRelevant⟩
      exact rule3FactorMoralLeftParent_transfer model G projected x y z w
        assignment disjoint fromChild targetChild node fromParent
        fromRelevant targetRelevant
  | @step restLength current next terminal first rest ih =>
      intro contact targetChild targetRelevant
      rcases contact with
        ⟨fromChild, fromParent, fromRelevant⟩
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule3WConditionRootAdjacent] using first) with
        ⟨bridgeChild, bridgeData⟩
      rcases Bool.and_eq_true_iff.mp bridgeData with
        ⟨currentRelevant, nextRelevant⟩
      have bridgeParent := rule3FactorMoralLeftParent_transfer model G
        projected x y z w assignment disjoint fromChild bridgeChild current
        fromParent fromRelevant currentRelevant
      have nextContact : Rule3RootMoralLeftContact model G x y z w
          assignment next := ⟨bridgeChild, bridgeParent, nextRelevant⟩
      exact ih nextContact targetChild targetRelevant

/-- Route a `Y`-side seed root through an arbitrary exact component walk and
obtain a left-side parent of any factor relevant to the terminal root.  The
reflexive walk is the direct seed case; a nontrivial walk initializes the
contact invariant from its first adjacency edge and delegates the remaining
suffix to `rule3FactorMoralLeftParent_of_contact_walk`. -/
theorem rule3FactorMoralLeftParent_of_root_walk
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    {length : Nat} {seed terminal : Fin model.latent.count}
    (walk : FiniteReachability.ExactWalk
      (rule3WConditionRootAdjacent model G x z w assignment)
      length seed terminal)
    (seedWitness : Rule3RootMoralLeftWitness model G x y z w seed)
    (targetChild : Fin S.count)
    (targetRelevant : rule3WConditionRootRelevant model G x z w assignment
      targetChild terminal = true) :
    Rule3FactorMoralLeftParent G x y z w targetChild := by
  cases walk with
  | refl =>
      exact rule3FactorMoralLeftParent_of_root_witness model G projected
        x y z w assignment targetChild seed seedWitness targetRelevant
  | @step restLength seed next terminal first rest =>
      rcases (finAny_eq_true_iff _).mp (by
          simpa [rule3WConditionRootAdjacent] using first) with
        ⟨bridgeChild, bridgeData⟩
      rcases Bool.and_eq_true_iff.mp bridgeData with
        ⟨seedRelevant, nextRelevant⟩
      have bridgeParent := rule3FactorMoralLeftParent_of_root_witness
        model G projected x y z w assignment bridgeChild seed seedWitness
        seedRelevant
      have nextContact : Rule3RootMoralLeftContact model G x y z w
          assignment next := ⟨bridgeChild, bridgeParent, nextRelevant⟩
      exact rule3FactorMoralLeftParent_of_contact_walk model G projected
        x y z w assignment disjoint rest nextContact targetChild
        targetRelevant

/-- Every seed root of the local conditioning component has an open
representative on the `Y` moral side.

The seed relevance walk initially lives in `G_{̅(X ∪ W)}`.  If it met
`Z`, choose its last `Z` vertex constructively; the remaining suffix contains
no `Z`, embeds in the rule-3 graph, and would be an active path from `Z` to
`Y`.  Separation therefore excludes every such meeting, after which the
complete seed walk embeds and transports the `Y`-side label back to its
incident source. -/
theorem rule3RootMoralLeftWitness_of_y_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true) :
    Rule3RootMoralLeftWitness model G x y z w root := by
  let intervention :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let ancestors := FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  rcases (model.latentRelevantUnder_eq_true_iff intervention ancestors
      root).mp (by simpa [intervention, ancestors] using relevant) with
    ⟨source, sourceAncestor, sourceFree, sourceIncident⟩
  rcases G.exists_minimal_walk_of_observedAncestorOf
      (GraphMutilation.bar (NodeSet.union x w)) y source (by
        simpa [FiniteLatentSCM.ancestralInBar, ancestors] using
          sourceAncestor) with
    ⟨yEnd, yEndInY, length, walk, walkSimple, _minimal⟩
  have walkOpen : forall node, node ∈ walk.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    by_cases atSource : node = source
    · subst node
      exact (FiniteLatentSCM.intervention_none_iff_unblocked
        (NodeSet.union x w) assignment source).mp (by
          simpa [intervention] using sourceFree)
    · have incoming :=
        PathSpecification.directed_walk_mem_not_removeIncoming G
          (GraphMutilation.bar (NodeSet.union x w)) walk member atSource
      simpa [GraphMutilation.bar, ObservedGraph.blockedBy] using incoming
  have noZ : forall node, node ∈ walk.nodes -> z node = false := by
    have noneSelected : walk.nodes.any z = false := by
      cases some : walk.nodes.any z with
      | false => rfl
      | true =>
          rcases exists_last_selected_observedDirectedWalk_suffix G
              (GraphMutilation.bar (NodeSet.union x w)) z walk walkSimple
              some with
            ⟨pivot, suffixLength, suffixWalk, pivotInZ, suffixSimple,
              suffixLast, suffixSubset⟩
          cases suffixWalk with
          | refl =>
              have impossible := disjoint.yz yEnd yEndInY
              rw [pivotInZ] at impossible
              contradiction
          | @step restLength pivot middle endNode first rest =>
              have simpleParts : pivot ∉ rest.nodes ∧ rest.nodes.Nodup := by
                simpa [FiniteReachability.ExactWalk.nodes] using
                  (List.nodup_cons.mp (by
                    simpa [FiniteReachability.ExactWalk.nodes] using
                      suffixSimple))
              have restNoZ : forall node, node ∈ rest.nodes ->
                  z node = false := by
                intro node member
                have notPivot : node ≠ pivot := by
                  intro equal
                  subst node
                  exact simpleParts.1 member
                exact suffixLast node (by
                  simp [FiniteReachability.ExactWalk.nodes]
                  exact Or.inr member) notPivot
              let mappedRest := remapRule3ConditionedWalk_of_no_z G x z w
                rest restNoZ
              have middleNotZ : z middle = false :=
                restNoZ middle rest.mem_source
              let mappedSuffix : FiniteReachability.ExactWalk
                  (G.observedDirectedEdge
                    (GraphMutilation.bar
                      (NodeSet.union x
                        (G.nonAncestorsOf (GraphMutilation.bar x) z w))))
                  (restLength + 1) pivot yEnd :=
                FiniteReachability.ExactWalk.step
                  (observedDirectedEdge_rule3_of_bar_union_of_child_not_z
                    G x z w first middleNotZ)
                  mappedRest
              have mappedNodes : mappedSuffix.nodes =
                  (FiniteReachability.ExactWalk.step first rest).nodes := by
                simp only [mappedSuffix,
                  FiniteReachability.ExactWalk.nodes]
                change pivot ::
                    (remapRule3ConditionedWalk_of_no_z G x z w rest
                      restNoZ).nodes =
                  pivot :: rest.nodes
                rw [remapRule3ConditionedWalk_of_no_z_nodes G x z w rest
                  restNoZ]
              have mappedSimple : mappedSuffix.nodes.Nodup := by
                rw [mappedNodes]
                exact suffixSimple
              have mappedOpen : forall node, node ∈ mappedSuffix.nodes ->
                  ObservedGraph.blockedBy (NodeSet.union x w)
                    (.observed node) = false := by
                intro node member
                rw [mappedNodes] at member
                exact walkOpen node (suffixSubset node member)
              let mutilation := GraphMutilation.bar
                (NodeSet.union x
                  (G.nonAncestorsOf (GraphMutilation.bar x) z w))
              have separated' : PathSpecification.PathDSeparated G
                  mutilation y z (NodeSet.union x w) := by
                simpa [mutilation, GraphMutilation.bar] using separated
              have active := PathSpecification.ActivePath.ofOpenDirectedWalk
                G mutilation (NodeSet.union x w) mappedSuffix mappedSimple
                mappedOpen
              exact (separated'
                ⟨yEnd, pivot, yEndInY, pivotInZ, ⟨active.reverse⟩⟩).elim
    intro node member
    have notTrue := (List.any_eq_false.mp noneSelected) node member
    exact (by
      cases value : z node with
      | false => rfl
      | true => exact (notTrue value).elim)
  let mapped := remapRule3ConditionedWalk_of_no_z G x z w walk noZ
  have mappedNodes : mapped.nodes = walk.nodes := by
    simp [mapped]
  have mappedSimple : mapped.nodes.Nodup := by
    rw [mappedNodes]
    exact walkSimple
  have mappedOpen : forall node, node ∈ mapped.nodes ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed node) =
        false := by
    intro node member
    rw [mappedNodes] at member
    exact walkOpen node member
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  have yEndTarget : targets yEnd = true := by
    simp [targets, NodeSet.union, yEndInY]
  have mappedAncestor : forall node, node ∈ mapped.nodes ->
      G.ancestorOf mutilation targets (.observed node) = true := by
    intro node member
    have observed := G.observedAncestorOf_of_mem_walk mutilation targets
      mapped yEndTarget member
    exact FiniteLatentSCM.ancestorOf_of_observedAncestorOf G mutilation
      targets node observed
  have sourceToY := moralLeftSide_eq_of_open_observed_walk G mutilation
    y z (NodeSet.union x w) mapped mappedOpen (by
      simpa [targets] using mappedAncestor)
  have yOpen := FiniteLatentSCM.blockedBy_false_of_mem_y x y z w disjoint
    yEndInY
  have ySide := G.moralLeftSide_of_left mutilation y z
    (NodeSet.union x w) yEnd yEndInY (by
      simpa [ObservedGraph.blockedBy] using yOpen)
  have sourceOpen := mappedOpen source mapped.mem_source
  have sourceOutsideX : x source = false := by
    have outside : NodeSet.union x w source = false := by
      simpa [ObservedGraph.blockedBy] using sourceOpen
    exact (Bool.or_eq_false_iff.mp (by
      simpa [NodeSet.union] using outside)).1
  have sourceOutsideRemovable :
      G.nonAncestorsOf (GraphMutilation.bar x) z w source = false := by
    cases removable :
        G.nonAncestorsOf (GraphMutilation.bar x) z w source with
    | false => rfl
    | true =>
        have sourceInZ := ObservedGraph.nonAncestorsOf_subset_actions G
          (GraphMutilation.bar x) z w source removable
        rw [noZ source walk.mem_source] at sourceInZ
        contradiction
  have sourceIncoming : mutilation.removeIncoming source = false := by
    change NodeSet.union x
      (G.nonAncestorsOf (GraphMutilation.bar x) z w) source = false
    simp [NodeSet.union, sourceOutsideX, sourceOutsideRemovable]
  have sourceAncestor := mappedAncestor source mapped.mem_source
  refine ⟨source, sourceIncident, sourceIncoming, sourceAncestor,
    sourceOpen, ?_⟩
  exact sourceToY.trans ySide

/-- If a root affects a locally sensitive factor without being directly
incident to that factor vertex, its open relevance route meets the open `Z`
route at the conditioned collider.  Path d-separation therefore places the
root's incident source outside the `Y` moral component.

The excluded direct-incidence case is intentional and exact.  It is the case
where the root itself supplies a latent parent of the conditioned collider;
the subsequent component proof handles it using projected bidirected
incidence rather than pretending that the blocked factor vertex is open. -/
theorem rule3RootMoralRightWitness_of_sensitive_relevant_not_incident
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (child : Fin S.count) (root : Fin model.latent.count)
    (relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true)
    (sensitive : rule3WLocalInterventionSensitive G x z w child = true)
    (notIncident : model.latent.incident root child = false) :
    Rule3RootMoralRightWitness model G x y z w root := by
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp sensitive).1
  have zOpen : forall source, z source = true ->
      ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
        false := by
    intro source sourceInZ
    exact FiniteLatentSCM.blockedBy_false_of_mem_z x y z w disjoint
      sourceInZ
  have rootRoute := rule3LocalConditionRootWalk_of_relevant model G
    x z w assignment child root relevant
  have zRoute := rule3LocalSensitivityWalk_of_sensitive G x z w child
    sensitive zOpen
  rcases rootRoute with
    ⟨rootSource, rootIncident, rootIncoming, rootLength, rootWalk,
      rootProperOpen⟩
  rcases zRoute with
    ⟨zSource, zSourceInZ, zLength, zWalk, zProperOpen⟩
  have rootSourceDifferent : rootSource ≠ child := by
    intro equal
    subst rootSource
    rw [rootIncident] at notIncident
    contradiction
  have zSourceDifferent : zSource ≠ child := by
    intro equal
    subst zSource
    have impossible := disjoint.zw child zSourceInZ
    rw [childInW] at impossible
    contradiction
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  have separated' : PathSpecification.PathDSeparated G mutilation y z
      (NodeSet.union x w) := by
    simpa [mutilation, GraphMutilation.bar] using separated
  have childConditioned : NodeSet.union x w child = true := by
    simp [NodeSet.union, childInW]
  have sameSide := moralLeftSide_eq_of_open_observed_walks_to_conditioned
    G mutilation y z (NodeSet.union x w) rootWalk zWalk
    rootSourceDifferent zSourceDifferent childConditioned rootProperOpen
    zProperOpen
  have zSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
      (.observed zSource) = false :=
    G.moralLeftSide_not_of_right mutilation y z (NodeSet.union x w)
      separated' zSource zSourceInZ (zOpen zSource zSourceInZ)
  have rootOpen := rootProperOpen rootSource rootWalk.mem_source
    rootSourceDifferent
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  have childTarget : targets child = true := by
    simp [targets, NodeSet.union, childInW]
  have rootObservedAncestor := G.observedAncestorOf_of_mem_walk
    mutilation targets rootWalk childTarget rootWalk.mem_source
  have rootAncestor := FiniteLatentSCM.ancestorOf_of_observedAncestorOf
    G mutilation targets rootSource rootObservedAncestor
  refine ⟨rootSource, rootIncident, rootIncoming, rootAncestor,
    rootOpen, ?_⟩
  exact sameSide.trans zSide

/-- One concrete latent root cannot have free ancestral representatives on
opposite sides of rule 3's canonical moral separator.

The representatives need not be the same observed vertex.  If they differ,
compatibility projects their shared concrete root to a bidirected edge of
`G`; if they coincide, the same lemma closes the reflexive case directly.
Because both representatives survive the incoming cut, are ancestral to the
rule-3 cylinders, and are open under `X ∪ W`, the intervening canonical
latent-pair vertex lies in the open ancestral moral graph.  Moral-side
membership must therefore agree, contradicting the stored `true` and
`false` labels. -/
theorem rule3RootMoralWitnesses_disjoint
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (root : Fin model.latent.count)
    (leftWitness : Rule3RootMoralLeftWitness model G x y z w root)
    (rightWitness : Rule3RootMoralRightWitness model G x y z w root) :
    False := by
  let mutilation := GraphMutilation.bar
    (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
  let targets := NodeSet.union y (NodeSet.union z (NodeSet.union x w))
  rcases leftWitness with
    ⟨leftSource, leftIncident, leftIncoming, leftAncestor, leftOpen,
      leftSide⟩
  rcases rightWitness with
    ⟨rightSource, rightIncident, rightIncoming, rightAncestor, rightOpen,
      rightSide⟩
  have sameSide := FiniteLatentSCM.moralLeftSide_eq_of_shared_latent
    model G projected
    mutilation y z (NodeSet.union x w) root leftSource rightSource
    leftIncident rightIncident leftIncoming rightIncoming leftAncestor
    rightAncestor (by
      simpa [ObservedGraph.blockedBy] using leftOpen) (by
      simpa [ObservedGraph.blockedBy] using rightOpen)
  rw [leftSide, rightSide] at sameSide
  contradiction

/-- A root already represented on the `Y` moral side cannot be relevant to a
locally `Z`-sensitive conditioning factor.

There are two exhaustive Boolean incidence cases.  A nonincident root has an
ordinary open relevance route and therefore obtains a right-side witness.
For direct incidence, projection turns the concrete root into the canonical
latent parent of the conditioned factor; moralizing that collider joins the
left representative to the open `Z` route.  Both cases contradict path
separation without deciding a proposition or selecting an existential
witness into data. -/
theorem rule3RootMoralLeftWitness_excludes_sensitive_relevance
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (child : Fin S.count) (root : Fin model.latent.count)
    (leftWitness : Rule3RootMoralLeftWitness model G x y z w root)
    (relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true)
    (sensitive : rule3WLocalInterventionSensitive G x z w child = true) :
    False := by
  cases incident : model.latent.incident root child with
  | false =>
      have rightWitness :=
        rule3RootMoralRightWitness_of_sensitive_relevant_not_incident
          model G x y z w assignment disjoint separated child root relevant
          sensitive incident
      exact rule3RootMoralWitnesses_disjoint model G projected x y z w root
        leftWitness rightWitness
  | true =>
      let mutilation := GraphMutilation.bar
        (NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w))
      rcases leftWitness with
        ⟨leftSource, leftIncident, leftIncoming, leftAncestor, leftOpen,
          leftSide⟩
      have childInW : w child = true :=
        (Bool.and_eq_true_iff.mp sensitive).1
      have childConditioned : NodeSet.union x w child = true := by
        simp [NodeSet.union, childInW]
      have zOpen : forall source, z source = true ->
          ObservedGraph.blockedBy (NodeSet.union x w) (.observed source) =
            false := by
        intro source sourceInZ
        exact FiniteLatentSCM.blockedBy_false_of_mem_z x y z w disjoint
          sourceInZ
      rcases rule3LocalSensitivityWalk_of_sensitive G x z w child sensitive
          zOpen with
        ⟨zSource, zSourceInZ, zLength, zWalk, zProperOpen⟩
      have zSourceDifferent : zSource ≠ child := by
        intro equal
        subst zSource
        have impossible := disjoint.zw child zSourceInZ
        rw [childInW] at impossible
        contradiction
      have sameSide :=
        moralLeftSide_eq_of_shared_latent_and_open_walk_to_conditioned
          model G projected mutilation y z (NodeSet.union x w) root
          leftSource child zSource leftIncident incident leftIncoming
          leftAncestor leftOpen zWalk zSourceDifferent childConditioned
          zProperOpen
      have separated' : PathSpecification.PathDSeparated G mutilation y z
          (NodeSet.union x w) := by
        simpa [mutilation, GraphMutilation.bar] using separated
      have zSide : G.moralLeftSide mutilation y z (NodeSet.union x w)
          (.observed zSource) = false :=
        G.moralLeftSide_not_of_right mutilation y z (NodeSet.union x w)
          separated' zSource zSourceInZ (zOpen zSource zSourceInZ)
      rw [leftSide, zSide] at sameSide
      contradiction

/-- A latent root needed by the `Y` cylinder cannot also affect a locally
`Z`-sensitive conditioning factor.  The seed route supplies the canonical
left-side representative; the preceding theorem handles both ordinary and
direct incidence at the factor. -/
theorem rule3_y_relevant_root_excludes_sensitive_relevance
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (child : Fin S.count) (root : Fin model.latent.count)
    (yRelevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true)
    (factorRelevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true)
    (sensitive : rule3WLocalInterventionSensitive G x z w child = true) :
    False :=
  rule3RootMoralLeftWitness_excludes_sensitive_relevance model G projected
    x y z w assignment disjoint separated child root
    (rule3RootMoralLeftWitness_of_y_relevant model G x y z w assignment
      disjoint separated root yRelevant)
    factorRelevant sensitive

/-- A local conditioning factor touched directly by a `Y`-relevant root is
invariant under adding `do(Z)`.  This is the zero-edge case of the finite
root-component argument: if the factor were sensitive, the preceding
separator theorem would produce the forbidden `Y`--`Z` connection. -/
theorem rule3WLocalInterventionInvariant_of_y_relevant_root
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (child : Fin S.count) (root : Fin model.latent.count)
    (yRelevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true)
    (factorRelevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true) :
    rule3WLocalInterventionInvariant G x z w child = true := by
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp factorRelevant).1
  cases sensitive : rule3WLocalInterventionSensitive G x z w child with
  | false =>
      simp [rule3WLocalInterventionInvariant, NodeSet.diff, childInW,
        sensitive]
  | true =>
      exact (rule3_y_relevant_root_excludes_sensitive_relevance model G
        projected x y z w assignment disjoint separated child root yRelevant
        factorRelevant sensitive).elim

/-- No selected `Z` vertex reaches a locally invariant conditioning factor. -/
theorem rule3_z_not_ancestral_local_invariant_w
    (G : ObservedGraph S) (x z w : NodeSet S)
    {child source : Fin S.count}
    (childInvariant : rule3WLocalInterventionInvariant G x z w child = true)
    (sourceInZ : z source = true) :
    FiniteLatentSCM.ancestralInBar G
      (localConditionAction (NodeSet.union x z) w child)
      (NodeSet.singleton child) source = false := by
  have childNotSensitive :
      rule3WLocalInterventionSensitive G x z w child = false :=
    NodeSet.Disjoint.diff_right w
      (rule3WLocalInterventionSensitive G x z w) child childInvariant
  cases ancestor : FiniteLatentSCM.ancestralInBar G
      (localConditionAction (NodeSet.union x z) w child)
      (NodeSet.singleton child) source with
  | false => rfl
  | true =>
      have meetsZ : NodeSet.meetsBool
          (FiniteLatentSCM.ancestralInBar G
            (localConditionAction (NodeSet.union x z) w child)
            (NodeSet.singleton child)) z = true :=
        (NodeSet.meetsBool_eq_true_iff _ _).mpr
          ⟨source, ancestor, sourceInZ⟩
      have childInW : w child = true :=
        NodeSet.diff_subset_left w
          (rule3WLocalInterventionSensitive G x z w) child childInvariant
      have childSensitive :
          rule3WLocalInterventionSensitive G x z w child = true := by
        simp [rule3WLocalInterventionSensitive, childInW, meetsZ]
      rw [childSensitive] at childNotSensitive
      contradiction

theorem rule3WConditionRootAdjacent_of_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (left right : Fin model.latent.count)
    (leftRelevant : rule3WConditionRootRelevant model G x z w assignment
      child left = true)
    (rightRelevant : rule3WConditionRootRelevant model G x z w assignment
      child right = true) :
    rule3WConditionRootAdjacent model G x z w assignment left right = true :=
  finAny_eq_true_of _ child
    (Bool.and_eq_true_iff.mpr ⟨leftRelevant, rightRelevant⟩)

/-- Every seed root is in the component, via the reflexive bounded walk. -/
theorem rule3YConditionLatentComponent_of_y_relevant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (root : Fin model.latent.count)
    (relevant : model.latentRelevantUnder
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root = true) :
    rule3YConditionLatentComponent model G x y z w assignment root = true := by
  apply finAny_eq_true_of _ root
  apply Bool.and_eq_true_iff.mpr
  refine ⟨relevant, ?_⟩
  have complete : forall latent : Fin model.latent.count,
      latent ∈ List.ofFn (fun i : Fin model.latent.count => i) :=
    fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
    (List.ofFn (fun latent : Fin model.latent.count => latent))
    (rule3WConditionRootAdjacent model G x z w assignment)
    finBeq_eq_true_iff complete
    (List.ofFn (fun latent : Fin model.latent.count => latent)).length
    root root).mpr
      (FiniteReachability.BoundedWalk.refl _ _ root)

/-- The generated root family is closed across every conditioning-factor
edge. -/
theorem rule3YConditionLatentComponent_closed
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (left right : Fin model.latent.count)
    (leftIn : rule3YConditionLatentComponent model G x y z w assignment
      left = true)
    (edge : rule3WConditionRootAdjacent model G x z w assignment
      left right = true) :
    rule3YConditionLatentComponent model G x y z w assignment right = true := by
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule3YConditionLatentComponent] using leftIn) with
    ⟨seed, seedData⟩
  rcases Bool.and_eq_true_iff.mp seedData with
    ⟨seedRelevant, seedReachesLeft⟩
  let roots := List.ofFn (fun latent : Fin model.latent.count => latent)
  let adjacent := rule3WConditionRootAdjacent model G x z w assignment
  have complete : forall latent : Fin model.latent.count, latent ∈ roots :=
    fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
  have seedToLeft : FiniteReachability.BoundedWalk adjacent roots.length
      seed left :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots adjacent
      finBeq_eq_true_iff complete roots.length seed left).mp
      (by simpa [roots, adjacent] using seedReachesLeft)
  have leftToRight : FiniteReachability.BoundedWalk adjacent 1 left right :=
    ⟨1, Nat.le_refl _,
      ⟨FiniteReachability.ExactWalk.step (by simpa [adjacent] using edge)
        (FiniteReachability.ExactWalk.refl right)⟩⟩
  have seedToRightReachable : FiniteReachability.Reachable adjacent seed right :=
    FiniteReachability.Reachable.of_bounded
      (FiniteReachability.BoundedWalk.trans seedToLeft leftToRight)
  have seedToRight : FiniteReachability.BoundedWalk adjacent roots.length
      seed right :=
    FiniteReachability.boundedWalk_of_reachable finBeq roots adjacent
      finBeq_eq_true_iff complete seedToRightReachable
  have found : FiniteReachability.within finBeq roots adjacent roots.length
      seed right = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots adjacent
      finBeq_eq_true_iff complete roots.length seed right).mpr seedToRight
  apply (finAny_eq_true_iff _).mpr
  exact ⟨seed, Bool.and_eq_true_iff.mpr ⟨seedRelevant,
    by simpa [roots, adjacent] using found⟩⟩

/-- Structural route carried by a common rule-3 conditioning factor.

The start root affects the `Y` cylinder, the end root affects the displayed
local factor, and the bounded walk alternates through factors on which two
roots are simultaneously relevant.  Keeping this package Prop-valued permits
constructive elimination of the finite witnesses while avoiding any choice
of roots in executable data. -/
def Rule3WConditionCommonRoute (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (child : Fin S.count) : Prop :=
  Exists fun seed : Fin model.latent.count =>
    Exists fun terminal : Fin model.latent.count =>
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) seed =
            true /\
        rule3WConditionRootRelevant model G x z w assignment child terminal =
          true /\
        FiniteReachability.BoundedWalk
          (rule3WConditionRootAdjacent model G x z w assignment)
          (List.ofFn
            (fun latent : Fin model.latent.count => latent)).length
          seed terminal

/-- Unpack membership in the common block into its generic bounded root
route.  This replaces branch-depth enumeration with the exact reachability
witness already computed by `rule3YConditionLatentComponent`. -/
def rule3WConditionCommonRoute_of_common
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count)
    (common : rule3WConditionCommon model G x y z w assignment child = true) :
    Rule3WConditionCommonRoute model G x y z w assignment child := by
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule3WConditionCommon] using common) with
    ⟨terminal, terminalData⟩
  rcases Bool.and_eq_true_iff.mp terminalData with
    ⟨terminalRelevant, terminalSelected⟩
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule3YConditionLatentComponent] using terminalSelected) with
    ⟨seed, seedData⟩
  rcases Bool.and_eq_true_iff.mp seedData with
    ⟨seedRelevant, seedReaches⟩
  let roots := List.ofFn
    (fun latent : Fin model.latent.count => latent)
  let adjacent := rule3WConditionRootAdjacent model G x z w assignment
  have complete : forall latent : Fin model.latent.count, latent ∈ roots :=
    fun latent => List.mem_ofFn.mpr ⟨latent, rfl⟩
  have route : FiniteReachability.BoundedWalk adjacent roots.length seed
      terminal :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq roots adjacent
      finBeq_eq_true_iff complete roots.length seed terminal).mp (by
        simpa [roots, adjacent] using seedReaches)
  exact ⟨seed, terminal, seedRelevant, terminalRelevant, by
    simpa [roots, adjacent] using route⟩

/-- Path separation places every factor in the `Y`-connected conditioning
component inside the locally intervention-invariant block.

Membership in the common block yields a bounded root path from a root needed
by `Y` to a root needed by the factor.  The path's exact witness is consumed
by `rule3FactorMoralLeftParent_of_root_walk`, producing a `Y`-side parent of
the factor for every possible path length.  Local sensitivity would provide
an open `Z`-side parent of the same conditioned collider, contradicting the
canonical moral separator.  Therefore the sensitivity Boolean is false and
the factor belongs to the complementary invariant block.

All witness extraction remains in `Prop`: no root, path, or factor is chosen
into executable data, and the proof uses neither choice nor excluded middle. -/
theorem rule3WConditionCommon_subset_local_invariant_of_path
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x
            (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w)) :
    NodeSet.Subset
      (rule3WConditionCommon model G x y z w assignment)
      (rule3WLocalInterventionInvariant G x z w) := by
  intro child common
  rcases rule3WConditionCommonRoute_of_common model G x y z w assignment
      child common with
    ⟨seed, terminal, seedRelevant, terminalRelevant, bounded⟩
  rcases bounded with ⟨length, _bound, exactWalk⟩
  rcases exactWalk with ⟨walk⟩
  have seedWitness := rule3RootMoralLeftWitness_of_y_relevant model G
    x y z w assignment disjoint separated seed seedRelevant
  have factorParent := rule3FactorMoralLeftParent_of_root_walk model G
    projected x y z w assignment disjoint walk seedWitness child
    terminalRelevant
  have childInW : w child = true :=
    (Bool.and_eq_true_iff.mp terminalRelevant).1
  cases sensitive : rule3WLocalInterventionSensitive G x z w child with
  | false =>
      simp [rule3WLocalInterventionInvariant, NodeSet.diff, childInW,
        sensitive]
  | true =>
      exact (Rule3FactorMoralLeftParent.excludes_sensitive G x y z w
        disjoint separated child factorParent sensitive).elim

/-- Every root relevant to a common conditioning factor belongs to the
generated component. -/
theorem rule3WConditionCommon_root_selected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (common : rule3WConditionCommon model G x y z w assignment child = true)
    (relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true) :
    rule3YConditionLatentComponent model G x y z w assignment root = true := by
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule3WConditionCommon] using common) with ⟨pivot, pivotData⟩
  rcases Bool.and_eq_true_iff.mp pivotData with
    ⟨pivotRelevant, pivotSelected⟩
  exact rule3YConditionLatentComponent_closed model G x y z w assignment
    pivot root pivotSelected
    (rule3WConditionRootAdjacent_of_relevant model G x z w assignment
      child pivot root pivotRelevant relevant)

/-- A residual factor contains no root from the generated component. -/
theorem rule3WConditionResidual_root_unselected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count) (root : Fin model.latent.count)
    (residual : rule3WConditionResidual model G x y z w assignment child =
      true)
    (relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true) :
    rule3YConditionLatentComponent model G x y z w assignment root = false := by
  have notCommon :
      rule3WConditionCommon model G x y z w assignment child = false :=
    NodeSet.Disjoint.diff_right w
      (rule3WConditionCommon model G x y z w assignment) child residual
  cases selected :
      rule3YConditionLatentComponent model G x y z w assignment root with
  | false => rfl
  | true =>
      have common :
          rule3WConditionCommon model G x y z w assignment child = true :=
        finAny_eq_true_of _ root
          (Bool.and_eq_true_iff.mpr ⟨relevant, selected⟩)
      rw [common] at notCommon
      contradiction

theorem rule3WConditionCommon_subset_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.Subset (rule3WConditionCommon model G x y z w assignment) w := by
  intro child common
  rcases (finAny_eq_true_iff _).mp (by
      simpa [rule3WConditionCommon] using common) with ⟨root, rootData⟩
  have relevant : rule3WConditionRootRelevant model G x z w assignment
      child root = true := (Bool.and_eq_true_iff.mp rootData).1
  exact (Bool.and_eq_true_iff.mp relevant).1

/-- The connected common block and its complement cover all of `W`. -/
theorem rule3WConditionSplit_union
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) :
    NodeSet.union (rule3WConditionCommon model G x y z w assignment)
      (rule3WConditionResidual model G x y z w assignment) = w := by
  funext child
  have subset := rule3WConditionCommon_subset_w model G x y z w assignment
    child
  simp [rule3WConditionResidual, NodeSet.union, NodeSet.diff]
  cases hw : w child with
  | false =>
      cases hc : rule3WConditionCommon model G x y z w assignment child with
      | false => simp
      | true => exact (Bool.false_ne_true (hw.symm.trans (subset hc))).elim
  | true =>
      cases hc : rule3WConditionCommon model G x y z w assignment child <;>
        simp

/-- A local `W` factor is unchanged by adding `do(Z)` when its vertex lies
in the local intervention-invariant block. -/
theorem rule3LocalConditionFactor_eq_of_local_invariant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x z w : NodeSet S) (assignment : S.Assignment)
    (child : Fin S.count)
    (invariant : rule3WLocalInterventionInvariant G x z w child = true)
    (roots : model.latent.Assignment) :
    localConditionFactor model (NodeSet.union x z) w assignment child roots =
      localConditionFactor model x w assignment child roots := by
  let base := localConditionAction x w child
  have actionEq : NodeSet.union base z =
      localConditionAction (NodeSet.union x z) w child := by
    funext node
    simp only [base, localConditionAction, NodeSet.union]
    cases hx : x node <;> cases hz : z node <;>
      cases hp : conditioningPrefix w child node <;> rfl
  have zAvoids : forall source, z source = true ->
      FiniteLatentSCM.ancestralInBar G (NodeSet.union base z)
        (NodeSet.singleton child) source = false := by
    intro source sourceInZ
    have localAvoids := rule3_z_not_ancestral_local_invariant_w G x z w
      invariant sourceInZ
    simpa [actionEq] using localAvoids
  have evaluated :=
    evalUnder_bar_union_eq_on_of_z_not_ancestral model G base z
      (NodeSet.singleton child) assignment zAvoids roots child
      ((NodeSet.singleton_eq_true_iff child child).mpr rfl)
  unfold localConditionFactor
  have evaluated' :
      model.evalUnder
          ((Kernel.mk NodeSet.empty
            (localConditionAction (NodeSet.union x z) w child)
            NodeSet.empty).intervention assignment) roots child =
        model.evalUnder
          ((Kernel.mk NodeSet.empty (localConditionAction x w child)
            NodeSet.empty).intervention assignment) roots child := by
    simpa [base, actionEq] using evaluated
  exact congrArg (fun value => decide (value = assignment child)) evaluated'

/-- The conjunction of all connected common factors is therefore identical
under the left and right rule-3 interventions. -/
theorem rule3LocalConditionCommon_eq_of_subset_local_invariant
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (subsetInvariant : NodeSet.Subset
      (rule3WConditionCommon model G x y z w assignment)
      (rule3WLocalInterventionInvariant G x z w))
    (roots : model.latent.Assignment) :
    localConditionEvent model (NodeSet.union x z) w
        (rule3WConditionCommon model G x y z w assignment) assignment roots =
      localConditionEvent model x w
        (rule3WConditionCommon model G x y z w assignment) assignment
        roots := by
  unfold localConditionEvent
  apply finAll_congr
  intro child
  cases common : rule3WConditionCommon model G x y z w assignment child with
  | false => rfl
  | true =>
      simp only [↓reduceIte]
      exact rule3LocalConditionFactor_eq_of_local_invariant model G
        x z w assignment child (subsetInvariant child common) roots

/-- When no `Z` vertex ancestors `W` in `G_{\overline{X}}`, the `W`
cylinders under `do(X ∪ Z)` and `do(X)` coincide: intervening on `Z`
cannot reach `W`. -/
theorem agreesOn_rule3W_eq_of_z_avoids_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    (roots : model.latent.Assignment) :
    Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots) =
      Kernel.agreesOn w assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots) := by
  have invariant :=
    agreesOn_evalUnder_bar_union_eq_of_z_not_ancestral model G x z w
      assignment
      (fun i hzi =>
        FiniteLatentSCM.rule3_z_not_ancestral_w_of_z_avoids_w G x z w
          hrem hzi)
      roots
  simpa [rule3Left, rule3Right, Kernel.intervention] using invariant

/-- `Y` under `do(X ∪ W ∪ Z)` equals `Y` under `do(X ∪ W)`: d-separation
in the rule-3 side graph forbids `Z` from ancestoring `Y` after incoming
arrows to `W` are cut. -/
theorem agreesOn_rule3Y_eq_of_union_xw
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty
            (NodeSet.union (NodeSet.union x w) z)
            NodeSet.empty).intervention assignment) roots) =
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases hy : y child with
  | false =>
      rfl
  | true =>
      have hanc :
          FiniteLatentSCM.ancestralInBar G
            (NodeSet.union (NodeSet.union x w) z) y child = true :=
        FiniteLatentSCM.observedAncestorOf_self G
          (GraphMutilation.bar (NodeSet.union (NodeSet.union x w) z)) y hy
      have hclosed :=
        FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
          (NodeSet.union (NodeSet.union x w) z) y assignment
      have hagree :
          forall i,
            FiniteLatentSCM.ancestralInBar G
                (NodeSet.union (NodeSet.union x w) z) y i = true ->
              ((Kernel.mk NodeSet.empty
                  (NodeSet.union (NodeSet.union x w) z)
                  NodeSet.empty).intervention assignment i) =
                ((Kernel.mk NodeSet.empty (NodeSet.union x w)
                  NodeSet.empty).intervention assignment i) := by
        intro i hi
        have hz : z i = false := by
          cases hzi : z i with
          | false =>
              rfl
          | true =>
              have hfalse :=
                FiniteLatentSCM.rule3_z_not_ancestral_of_union_xw G x y z w
                  disjoint separated hzi
              simpa [FiniteLatentSCM.ancestralInBar] using
                (hfalse.symm.trans hi)
        have hinterL :
            (Kernel.mk NodeSet.empty
                (NodeSet.union (NodeSet.union x w) z)
                NodeSet.empty).intervention assignment i =
              (if NodeSet.union (NodeSet.union x w) z i
                then some (assignment i) else none) := by
          simp [Kernel.intervention]
        have hinterR :
            (Kernel.mk NodeSet.empty (NodeSet.union x w)
                NodeSet.empty).intervention assignment i =
              (if NodeSet.union x w i then some (assignment i)
                else none) := by
          simp [Kernel.intervention]
        have hxZ : NodeSet.union (NodeSet.union x w) z i =
            NodeSet.union x w i := by
          simp [NodeSet.union, hz]
        simp [hinterL, hinterR, hxZ]
      have heval :=
        FiniteLatentSCM.evalUnder_eq_on_of_intervention_agree_on_closed
          model
          ((Kernel.mk NodeSet.empty
            (NodeSet.union (NodeSet.union x w) z)
            NodeSet.empty).intervention assignment)
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G
            (NodeSet.union (NodeSet.union x w) z) y)
          roots hclosed hagree child hanc
      simp [heval]

/-- Rule-3 left numerator `Y ∧ W` under `do(X ∪ Z)` rewrites as the `W`
cylinder times `Y` under `do(X ∪ Z ∪ W)`. -/
theorem agreesOn_rule3Left_evalUnder_union_eq
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (roots : model.latent.Assignment) :
    (Kernel.agreesOn y assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots)) =
      (Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty
            (NodeSet.union (NodeSet.union x z) w)
            NodeSet.empty).intervention assignment) roots)) := by
  have hinter :
      (rule3Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule3Left, Kernel.intervention]
  rw [hinter]
  conv =>
    lhs
    rw [Bool.and_comm]
  exact agreesOn_and_evalUnder_union_eq model (NodeSet.union x z) w y
    assignment roots

/-- Rule-3 right numerator `Y ∧ W` under `do(X)` rewrites as the `W`
cylinder times `Y` under `do(X ∪ W)`. -/
theorem agreesOn_rule3Right_evalUnder_union_eq
    (model : FiniteLatentSCM S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (roots : model.latent.Assignment) :
    (Kernel.agreesOn y assignment
        (model.evalUnder ((rule3Right x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Right x y z w).intervention assignment)
          roots)) =
      (Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Right x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots)) := by
  have hinter :
      (rule3Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment := by
    funext i
    simp [rule3Right, Kernel.intervention]
  rw [hinter]
  conv =>
    lhs
    rw [Bool.and_comm]
  exact agreesOn_and_evalUnder_union_eq model x w y assignment roots

/-- Combined given-`W` rewrite of the rule-3 left numerator onto
`Y` under `do(X ∪ W)`. -/
theorem agreesOn_rule3Left_numerator_eq_given_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (roots : model.latent.Assignment) :
    (Kernel.agreesOn y assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots)) =
      (Kernel.agreesOn w assignment
        (model.evalUnder ((rule3Left x y z w).intervention assignment)
          roots) &&
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots)) := by
  have hunion :
      NodeSet.union (NodeSet.union x z) w =
        NodeSet.union (NodeSet.union x w) z := by
    rw [NodeSet.union_assoc, NodeSet.union_comm z w, ← NodeSet.union_assoc]
  rw [agreesOn_rule3Left_evalUnder_union_eq]
  rw [hunion]
  have hy :=
    agreesOn_rule3Y_eq_of_union_xw model G x y z w assignment disjoint
      separated roots
  rw [hy]

/-- A `do(X ∪ W)`-relevant ancestor of `Y` that is also relevant to `W`
under `do(X ∪ Z)` or `do(X)`.  When this is false, the given-`W` cylinders
factor across the `Y` mask. -/
def rule3YWLatentOverlap (model : FiniteLatentSCM S)
    (G : ObservedGraph S) (x y z w : NodeSet S)
    (assignment : S.Assignment) : Bool :=
  finAny model.latent.count (fun root =>
    model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) root &&
      (model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root ||
        model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x w) root))

/-- Empty `W` has no ancestral latents, so it cannot overlap the `Y` mask. -/
theorem rule3YWLatentOverlap_eq_false_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hw : NodeSet.isEmpty w = true) :
    rule3YWLatentOverlap model G x y z w assignment = false := by
  have hw' : w = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hw
  subst hw'
  refine (finAny_eq_false_iff _).mpr fun root => ?_
  have hL :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            NodeSet.empty) root = false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      FiniteLatentSCM.latentRelevantUnder_empty model
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment) root
  have hR :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
            assignment)
          (FiniteLatentSCM.ancestralInBar G x NodeSet.empty) root =
            false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      FiniteLatentSCM.latentRelevantUnder_empty model
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment) root
  simp [hL, hR]

/-- Empty `Y` has no ancestral latents, so the given-`W` overlap is false. -/
theorem rule3YWLatentOverlap_eq_false_of_empty_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hy : NodeSet.isEmpty y = true) :
    rule3YWLatentOverlap model G x y z w assignment = false := by
  have hy' : y = NodeSet.empty := NodeSet.eq_empty_of_isEmpty hy
  subst hy'
  refine (finAny_eq_false_iff _).mpr fun root => ?_
  have hY :
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w)
            NodeSet.empty) root = false := by
    simpa [FiniteLatentSCM.ancestralInBar_eq_empty] using
      FiniteLatentSCM.latentRelevantUnder_empty model
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment) root
  simp [hY]

theorem rule3YWLatentSeparatedAcross_left_of_overlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    model.LatentSeparatedAcross
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
      ((Kernel.mk NodeSet.empty (NodeSet.union x z)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) := by
  intro root hyRel
  have hall := (finAny_eq_false_iff _).mp hoverlap root
  cases hL :
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) root with
  | false =>
      rfl
  | true =>
      simp [hyRel, hL] at hall

theorem rule3YWLatentSeparatedAcross_right_of_overlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    model.LatentSeparatedAcross
      ((Kernel.mk NodeSet.empty (NodeSet.union x w)
        NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
      ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
      (FiniteLatentSCM.ancestralInBar G x w) := by
  intro root hyRel
  have hall := (finAny_eq_false_iff _).mp hoverlap root
  cases hR :
      model.latentRelevantUnder
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G x w) root with
  | false =>
      rfl
  | true =>
      simp [hyRel, hR] at hall

/--
The factorization actually needed by the nontrivial given-`W` case of rule 3.

After conditioning is rewritten as intervention on `W`, the `Y` cylinder is
the same on both sides by the rule-3 path condition.  The two original `W`
cylinders may nevertheless share latent roots with that common `Y` cylinder.
Such shared dependence is represented by `commonCondition`, while the parts
of `W` that differ between `do(X ∪ Z)` and `do(X)` are kept in the two
residual events on unselected roots.

Unlike `rule3YWLatentOverlap = false`, this interface does not demand that
`Y` and `W` be independent.  It records only the common/residual decomposition
needed for cancellation in the conditional cross product.
-/
structure Rule3GivenWFactorization
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  commonCondition : model.latent.Assignment -> Bool
  leftResidual : model.latent.Assignment -> Bool
  rightResidual : model.latent.Assignment -> Bool
  yDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected
    (fun roots =>
      Kernel.agreesOn y assignment
        (model.evalUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x w)
            NodeSet.empty).intervention assignment) roots))
  commonConditionDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected commonCondition
  leftResidualDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected leftResidual
  rightResidualDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected rightResidual
  leftCondition :
    productPreimage model (rule3Left x y z w) assignment
        ((rule3Left x y z w).conditionEvent assignment) =
      Probability.inter commonCondition leftResidual
  rightCondition :
    productPreimage model (rule3Right x y z w) assignment
        ((rule3Right x y z w).conditionEvent assignment) =
      Probability.inter commonCondition rightResidual

/--
Build the rule-3 common/residual event factorization from an actual split of
the conditioned vertices.

The `common` block may depend on the same selected latent roots as `Y`, but
its agreement cylinder must be unchanged by adding the `Z` intervention.
The complementary `residual` block may have different cylinders on the two
sides, provided both depend only on unselected roots.  This is the graph-level
shape expected from a moral separator: dependence shared by `Y` and `W` is
retained and cancelled, rather than incorrectly ruled out.
-/
def Rule3GivenWFactorization.of_node_split
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (common residual : NodeSet S)
    (covers : NodeSet.union common residual = w)
    (commonInvariant : forall roots,
      Kernel.agreesOn common assignment
          (model.evalUnder
            ((rule3Left x y z w).intervention assignment) roots) =
        Kernel.agreesOn common assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots))
    (yDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((Kernel.mk NodeSet.empty (NodeSet.union x w)
              NodeSet.empty).intervention assignment) roots)))
    (commonDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn common assignment
          (model.evalUnder
            ((rule3Left x y z w).intervention assignment) roots)))
    (leftResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn residual assignment
          (model.evalUnder
            ((rule3Left x y z w).intervention assignment) roots)))
    (rightResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots =>
        Kernel.agreesOn residual assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots))) :
    Rule3GivenWFactorization model G x y z w assignment where
  selected := selected
  commonCondition := fun roots =>
    Kernel.agreesOn common assignment
      (model.evalUnder
        ((rule3Left x y z w).intervention assignment) roots)
  leftResidual := fun roots =>
    Kernel.agreesOn residual assignment
      (model.evalUnder
        ((rule3Left x y z w).intervention assignment) roots)
  rightResidual := fun roots =>
    Kernel.agreesOn residual assignment
      (model.evalUnder
        ((rule3Right x y z w).intervention assignment) roots)
  yDepends := yDepends
  commonConditionDepends := commonDepends
  leftResidualDepends := leftResidualDepends
  rightResidualDepends := rightResidualDepends
  leftCondition := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter]
    rw [show (rule3Left x y z w).condition = w from rfl]
    have split := congrArg
      (fun nodes => Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((rule3Left x y z w).intervention assignment) roots)) covers
    have split' :
        Kernel.agreesOn (NodeSet.union common residual) assignment
            (model.evalUnder
              ((rule3Left x y z w).intervention assignment) roots) =
          Kernel.agreesOn w assignment
            (model.evalUnder
              ((rule3Left x y z w).intervention assignment) roots) := by
      simpa using split
    rw [← split', Kernel.agreesOn_union]
  rightCondition := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter]
    rw [show (rule3Right x y z w).condition = w from rfl]
    have split := congrArg
      (fun nodes => Kernel.agreesOn nodes assignment
        (model.evalUnder
          ((rule3Right x y z w).intervention assignment) roots)) covers
    have split' :
        Kernel.agreesOn (NodeSet.union common residual) assignment
            (model.evalUnder
              ((rule3Right x y z w).intervention assignment) roots) =
          Kernel.agreesOn w assignment
            (model.evalUnder
              ((rule3Right x y z w).intervention assignment) roots) := by
      simpa using split
    rw [← split', Kernel.agreesOn_union, ← commonInvariant roots]

/--
Build the rule-3 common/residual factorization from topological local
conditioning factors.

The selected mask is the finite component generated by the `Y` roots and by
roots co-occurring in one local `W` factor.  Component closure therefore puts
every common factor wholly on selected roots and every residual factor wholly
on unselected roots.  The one graph-shaped premise says that the connected
common nodes lie in the locally intervention-invariant block; the preceding
local invariance theorem then identifies their left and right factors
pointwise.
-/
def Rule3GivenWFactorization.of_local_condition_component
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (commonSubsetLocalInvariant : NodeSet.Subset
      (rule3WConditionCommon model G x y z w assignment)
      (rule3WLocalInterventionInvariant G x z w)) :
    Rule3GivenWFactorization model G x y z w assignment := by
  let yInt :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let yRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  let selected :=
    rule3YConditionLatentComponent model G x y z w assignment
  let common := rule3WConditionCommon model G x y z w assignment
  let residual := rule3WConditionResidual model G x y z w assignment
  let commonEvent := localConditionEvent model (NodeSet.union x z) w
    common assignment
  let leftResidualEvent := localConditionEvent model (NodeSet.union x z) w
    residual assignment
  let rightResidualEvent := localConditionEvent model x w residual assignment
  have commonSubsetW : NodeSet.Subset common w := by
    simpa [common] using
      rule3WConditionCommon_subset_w model G x y z w assignment
  have residualSubsetW : NodeSet.Subset residual w := by
    dsimp [residual]
    exact NodeSet.diff_subset_left w
      (rule3WConditionCommon model G x y z w assignment)
  have covers : NodeSet.union common residual = w := by
    simpa [common, residual] using
      rule3WConditionSplit_union model G x y z w assignment
  have yDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder yInt yRelevant)
      (selected' := selected)
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) ?_ ?_
    · intro root relevantRoot
      exact rule3YConditionLatentComponent_of_y_relevant model G x y z w
        assignment root (by simpa [yInt, yRelevant] using relevantRoot)
    · exact agreesOn_evalUnder_dependsOnSelected model yInt yRelevant y
        assignment
        (by
          dsimp [yInt, yRelevant]
          exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
            model G (NodeSet.union x w) y assignment)
        (by
          dsimp [yRelevant]
          exact FiniteLatentSCM.ancestralInBar_contains_targets G
            (NodeSet.union x w) y)
  have commonDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected commonEvent := by
    dsimp [commonEvent]
    apply localConditionEvent_dependsOnSelected model G
    intro child childCommon root relevantRoot
    have childInW := commonSubsetW child childCommon
    have combined : rule3WConditionRootRelevant model G x z w assignment
        child root = true := by
      simp [rule3WConditionRootRelevant, childInW, relevantRoot]
    exact rule3WConditionCommon_root_selected model G x y z w assignment
      child root (by simpa [common] using childCommon) combined
  have leftResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected leftResidualEvent := by
    dsimp [leftResidualEvent]
    apply localConditionEvent_dependsOnUnselected model G
    intro child childResidual root relevantRoot
    have childInW := residualSubsetW child childResidual
    have combined : rule3WConditionRootRelevant model G x z w assignment
        child root = true := by
      simp [rule3WConditionRootRelevant, childInW, relevantRoot]
    exact rule3WConditionResidual_root_unselected model G x y z w assignment
      child root (by simpa [residual] using childResidual) combined
  have rightResidualDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected rightResidualEvent := by
    dsimp [rightResidualEvent]
    apply localConditionEvent_dependsOnUnselected model G
    intro child childResidual root relevantRoot
    have childInW := residualSubsetW child childResidual
    have combined : rule3WConditionRootRelevant model G x z w assignment
        child root = true := by
      simp [rule3WConditionRootRelevant, childInW, relevantRoot]
    exact rule3WConditionResidual_root_unselected model G x y z w assignment
      child root (by simpa [residual] using childResidual) combined
  have commonInvariant : forall roots,
      commonEvent roots =
        localConditionEvent model x w common assignment roots := by
    intro roots
    dsimp [commonEvent, common]
    exact rule3LocalConditionCommon_eq_of_subset_local_invariant model G
      x y z w assignment commonSubsetLocalInvariant roots
  refine
    { selected := selected
      commonCondition := commonEvent
      leftResidual := leftResidualEvent
      rightResidual := rightResidualEvent
      yDepends := by simpa [yInt] using yDepends
      commonConditionDepends := commonDepends
      leftResidualDepends := leftResidualDepends
      rightResidualDepends := rightResidualDepends
      leftCondition := ?_
      rightCondition := ?_ }
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter]
    rw [show (rule3Left x y z w).condition = w from rfl]
    have full := agreesOn_evalUnder_eq_localConditionEvent model
      (NodeSet.union x z) w assignment roots
    have split := localConditionEvent_union model (NodeSet.union x z) w
      common residual assignment roots
    have selectedCover := congrArg
      (fun nodes => localConditionEvent model (NodeSet.union x z) w nodes
        assignment roots) covers
    have splitFullRaw : localConditionEvent model (NodeSet.union x z) w w
        assignment roots =
          (localConditionEvent model (NodeSet.union x z) w common assignment
              roots &&
            localConditionEvent model (NodeSet.union x z) w residual
              assignment roots) :=
      selectedCover.symm.trans split
    have splitFull : localConditionEvent model (NodeSet.union x z) w w
        assignment roots = (commonEvent roots && leftResidualEvent roots) := by
      simpa [commonEvent, leftResidualEvent] using splitFullRaw
    have interventionEq :
        (rule3Left x y z w).intervention assignment =
          (Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment := by
      funext child
      simp [rule3Left, Kernel.intervention]
    rw [interventionEq, full, splitFull]
  · funext roots
    simp only [productPreimage, Kernel.conditionEvent, Probability.inter]
    rw [show (rule3Right x y z w).condition = w from rfl]
    have full := agreesOn_evalUnder_eq_localConditionEvent model x w
      assignment roots
    have split := localConditionEvent_union model x w common residual
      assignment roots
    have selectedCover := congrArg
      (fun nodes => localConditionEvent model x w nodes assignment roots)
      covers
    have splitFullRaw : localConditionEvent model x w w assignment roots =
        (localConditionEvent model x w common assignment roots &&
          localConditionEvent model x w residual assignment roots) :=
      selectedCover.symm.trans split
    have splitFull : localConditionEvent model x w w assignment roots =
        (localConditionEvent model x w common assignment roots &&
          rightResidualEvent roots) := by
      simpa [rightResidualEvent] using splitFullRaw
    have interventionEq :
        (rule3Right x y z w).intervention assignment =
          (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment := by
      funext child
      simp [rule3Right, Kernel.intervention]
    rw [interventionEq, full, splitFull, ← commonInvariant roots]

/--
Instantiate the rule-3 node split with the part of `W` that is pointwise
invariant under adding `do(Z)` and its intervention-sensitive complement.

The selected latent mask contains every coordinate needed by `Y` under
`do(X ∪ W)` and by the invariant `W` cylinder under `do(X ∪ Z)`.
Consequently all dependency and intervention-invariance fields of
`Rule3GivenWFactorization` are automatic.  The only remaining hypotheses say
that the sensitive `W` cylinder, under each of its two interventions, avoids
that selected mask.

These two avoidance statements are deliberately explicit.  They are valid
in an important rule-3 subcase, but path d-separation alone need not put *all*
intervention-invariant `W` vertices on the `Y` side of the moral separator.
The fully general construction must refine the invariant block by moral side
rather than silently treating these hypotheses as universal consequences.
-/
def Rule3GivenWFactorization.of_intervention_split
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (leftResidualAvoids : forall root,
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty (NodeSet.union x z)
            NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z)
            (rule3WInterventionSensitive G x z w)) root = true ->
        rule3YInvariantLatentMask model G x y z w assignment root = false)
    (rightResidualAvoids : forall root,
      model.latentRelevantUnder
          ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
          (FiniteLatentSCM.ancestralInBar G x
            (rule3WInterventionSensitive G x z w)) root = true ->
        rule3YInvariantLatentMask model G x y z w assignment root = false) :
    Rule3GivenWFactorization model G x y z w assignment := by
  let yInt :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let leftInt :=
    (Kernel.mk NodeSet.empty (NodeSet.union x z)
      NodeSet.empty).intervention assignment
  let rightInt :=
    (Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment
  let yRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y
  let common := rule3WInterventionInvariant G x z w
  let residual := rule3WInterventionSensitive G x z w
  let commonRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) common
  let leftResidualRelevant :=
    FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) residual
  let rightResidualRelevant :=
    FiniteLatentSCM.ancestralInBar G x residual
  let selected := rule3YInvariantLatentMask model G x y z w assignment
  have yDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder yInt yRelevant)
      (selected' := selected)
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) ?_ ?_
    · intro root relevantRoot
      simp [selected, rule3YInvariantLatentMask, yInt, yRelevant,
        relevantRoot]
    · exact agreesOn_evalUnder_dependsOnSelected model yInt yRelevant y
        assignment
        (by
          dsimp [yInt, yRelevant]
          exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
            model G (NodeSet.union x w) y assignment)
        (by
          dsimp [yRelevant]
          exact FiniteLatentSCM.ancestralInBar_contains_targets G
            (NodeSet.union x w) y)
  have commonDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn common assignment
        (model.evalUnder leftInt roots)) := by
    refine CanonicalFactorization.DependsOnSelected.subset
      model.latent.count model.latent.Value
      (selected := model.latentRelevantUnder leftInt commonRelevant)
      (selected' := selected)
      (fun roots => Kernel.agreesOn common assignment
        (model.evalUnder leftInt roots)) ?_ ?_
    · intro root relevantRoot
      simp [selected, rule3YInvariantLatentMask, leftInt, common,
        commonRelevant, relevantRoot]
    · exact agreesOn_evalUnder_dependsOnSelected model leftInt
        commonRelevant common assignment
        (by
          dsimp [leftInt, commonRelevant, common]
          exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
            model G (NodeSet.union x z)
              (rule3WInterventionInvariant G x z w) assignment)
        (by
          dsimp [commonRelevant, common]
          exact FiniteLatentSCM.ancestralInBar_contains_targets G
            (NodeSet.union x z)
              (rule3WInterventionInvariant G x z w))
  have leftResidualDepends :
      CanonicalFactorization.DependsOnUnselected
        model.latent.count model.latent.Value selected
        (fun roots => Kernel.agreesOn residual assignment
          (model.evalUnder leftInt roots)) :=
    agreesOn_evalUnder_dependsOnUnselected_of_relevance_avoids model
      selected leftInt leftResidualRelevant residual assignment
      (by
        dsimp [leftInt, leftResidualRelevant, residual]
        exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
          model G (NodeSet.union x z)
            (rule3WInterventionSensitive G x z w) assignment)
      (by
        dsimp [leftResidualRelevant, residual]
        exact FiniteLatentSCM.ancestralInBar_contains_targets G
          (NodeSet.union x z)
            (rule3WInterventionSensitive G x z w))
      (by
        intro root relevantRoot
        exact leftResidualAvoids root (by
          simpa [leftInt, leftResidualRelevant, residual] using relevantRoot))
  have rightResidualDepends :
      CanonicalFactorization.DependsOnUnselected
        model.latent.count model.latent.Value selected
        (fun roots => Kernel.agreesOn residual assignment
          (model.evalUnder rightInt roots)) :=
    agreesOn_evalUnder_dependsOnUnselected_of_relevance_avoids model
      selected rightInt rightResidualRelevant residual assignment
      (by
        dsimp [rightInt, rightResidualRelevant, residual]
        exact FiniteLatentSCM.observedAncestorOf_backwardClosedUnder
          model G x (rule3WInterventionSensitive G x z w) assignment)
      (by
        dsimp [rightResidualRelevant, residual]
        exact FiniteLatentSCM.ancestralInBar_contains_targets G x
          (rule3WInterventionSensitive G x z w))
      (by
        intro root relevantRoot
        exact rightResidualAvoids root (by
          simpa [rightInt, rightResidualRelevant, residual]
            using relevantRoot))
  apply Rule3GivenWFactorization.of_node_split model G x y z w assignment
    selected common residual
    (by
      dsimp [common, residual]
      exact rule3WInterventionSplit_union G x z w)
    (by
      intro roots
      dsimp [common]
      exact agreesOn_rule3WInterventionInvariant model G x y z w assignment
        roots)
  · simpa [yInt] using yDepends
  · simpa [leftInt, rule3Left, Kernel.intervention] using commonDepends
  · simpa [leftInt, rule3Left, Kernel.intervention]
      using leftResidualDepends
  · simpa [rightInt, rule3Right, Kernel.intervention]
      using rightResidualDepends

/--
Compile the common/residual `W` decomposition into the rectangular rule-3
cross product.  The proof uses the path condition only to rewrite both
numerators onto the same `Y`-under-`do(X ∪ W)` cylinder; factor independence
then follows from the supplied coordinate dependencies.
-/
def rule3RectangularWitness_of_given_w_factorization
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (factorization : Rule3GivenWFactorization model G x y z w assignment) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment := by
  let yCyl : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment
      (model.evalUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union x w)
          NodeSet.empty).intervention assignment) roots)
  let leftCondition :=
    productPreimage model (rule3Left x y z w) assignment
      ((rule3Left x y z w).conditionEvent assignment)
  let rightCondition :=
    productPreimage model (rule3Right x y z w) assignment
      ((rule3Right x y z w).conditionEvent assignment)
  have leftConditionFactor :
      leftCondition = Probability.inter factorization.commonCondition
        factorization.leftResidual := by
    simpa [leftCondition] using factorization.leftCondition
  have rightConditionFactor :
      rightCondition = Probability.inter factorization.commonCondition
        factorization.rightResidual := by
    simpa [rightCondition] using factorization.rightCondition
  have leftNumeratorGivenW :
      productPreimage model (rule3Left x y z w) assignment
          ((rule3Left x y z w).numeratorEvent assignment) =
        Probability.inter leftCondition yCyl := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter, leftCondition, yCyl]
    exact agreesOn_rule3Left_numerator_eq_given_w model G x y z w
      assignment disjoint separated roots
  have rightNumeratorGivenW :
      productPreimage model (rule3Right x y z w) assignment
          ((rule3Right x y z w).numeratorEvent assignment) =
        Probability.inter rightCondition yCyl := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent,
      Kernel.conditionEvent, Probability.inter, rightCondition, yCyl]
    exact agreesOn_rule3Right_evalUnder_union_eq model x y z w assignment
      roots
  apply ProductRectangularCrossProductWitnessAt.of_shared_factors model
    (rule3Left x y z w) (rule3Right x y z w) assignment
    factorization.selected
    (Probability.inter yCyl factorization.commonCondition)
    factorization.commonCondition factorization.leftResidual
    factorization.rightResidual
  · exact CanonicalFactorization.DependsOnSelected.inter
      model.latent.count model.latent.Value factorization.selected
      yCyl factorization.commonCondition (by
        simpa [yCyl] using factorization.yDepends)
      factorization.commonConditionDepends
  · exact factorization.commonConditionDepends
  · exact factorization.leftResidualDepends
  · exact factorization.rightResidualDepends
  · rw [leftNumeratorGivenW, leftConditionFactor]
    funext roots
    exact bool_and_rot_left (factorization.commonCondition roots)
      (factorization.leftResidual roots) (yCyl roots)
  · exact rightConditionFactor
  · rw [rightNumeratorGivenW, rightConditionFactor]
    funext roots
    exact bool_and_rot_left (factorization.commonCondition roots)
      (factorization.rightResidual roots) (yCyl roots)
  · exact leftConditionFactor

/--
The earlier no-overlap argument is the degenerate common/residual
factorization whose common `W` factor is `true`.  Keeping it as an explicit
constructor both preserves the useful special case and documents precisely
what the stronger hypothesis buys: every left and right `W` cylinder can be
placed wholly on the coordinates complementary to the `Y` mask.
-/
def Rule3GivenWFactorization.of_no_overlap
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    Rule3GivenWFactorization model G x y z w assignment := by
  let yInt :=
    (Kernel.mk NodeSet.empty (NodeSet.union x w)
      NodeSet.empty).intervention assignment
  let yMask :=
    model.latentRelevantUnder yInt
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
  let wLeft : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule3Left x y z w).intervention assignment) roots)
  let wRight : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule3Right x y z w).intervention assignment) roots)
  have hinterL :
      (rule3Left x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment := by
    funext i
    simp [rule3Left, Kernel.intervention]
  have hinterR :
      (rule3Right x y z w).intervention assignment =
        (Kernel.mk NodeSet.empty x NodeSet.empty).intervention
          assignment := by
    funext i
    simp [rule3Right, Kernel.intervention]
  have yClosed :=
    FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x w) y assignment
  have yContained :=
    FiniteLatentSCM.ancestralInBar_contains_targets G (NodeSet.union x w) y
  have wContainedL :=
    FiniteLatentSCM.ancestralInBar_contains_targets G (NodeSet.union x z) w
  have wContainedR :=
    FiniteLatentSCM.ancestralInBar_contains_targets G x w
  have wClosedL :=
    FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G
      (NodeSet.union x z) w assignment
  have wClosedR :=
    FiniteLatentSCM.observedAncestorOf_backwardClosedUnder model G x w
      assignment
  have yDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value yMask
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder yInt roots)) :=
    agreesOn_evalUnder_dependsOnSelected model yInt
      (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y) y
      assignment yClosed yContained
  have wLeftDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value yMask wLeft := by
    simpa [wLeft, hinterL] using
      agreesOn_evalUnder_dependsOnUnselected_across model yInt
        ((Kernel.mk NodeSet.empty (NodeSet.union x z)
          NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x z) w) w
        assignment wClosedL wContainedL
        (rule3YWLatentSeparatedAcross_left_of_overlap model G x y z w
          assignment hoverlap)
  have wRightDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value yMask wRight := by
    simpa [wRight, hinterR] using
      agreesOn_evalUnder_dependsOnUnselected_across model yInt
        ((Kernel.mk NodeSet.empty x NodeSet.empty).intervention assignment)
        (FiniteLatentSCM.ancestralInBar G (NodeSet.union x w) y)
        (FiniteLatentSCM.ancestralInBar G x w) w assignment wClosedR
        wContainedR
        (rule3YWLatentSeparatedAcross_right_of_overlap model G x y z w
          assignment hoverlap)
  exact
    { selected := yMask
      commonCondition := fun _ => true
      leftResidual := wLeft
      rightResidual := wRight
      yDepends := by simpa [yInt] using yDepends
      commonConditionDepends :=
        CanonicalFactorization.DependsOnSelected.const _ _ _ true
      leftResidualDepends := wLeftDepends
      rightResidualDepends := wRightDepends
      leftCondition := by
        funext roots
        simp [productPreimage, Kernel.conditionEvent, rule3Left, wLeft,
          Probability.inter]
      rightCondition := by
        funext roots
        simp [productPreimage, Kernel.conditionEvent, rule3Right, wRight,
          Probability.inter] }

/-- Given-`W` rule 3: if the `Y` mask under `do(X ∪ W)` shares no latent
with `W` under either kernel intervention, the four events are rectangles
on that mask.  The extra overlap Bool is not a theorem of path
d-separation (`U → Y` and `U → W` remain). -/
def rule3RectangularWitness_of_given_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (hoverlap : rule3YWLatentOverlap model G x y z w assignment = false) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_given_w_factorization model G x y z w assignment
    disjoint separated
    (Rule3GivenWFactorization.of_no_overlap model G x y z w assignment
      hoverlap)

/-- Empty-outcome rule 3: the `Y` mask is vacant, so given-`W` overlap
is false and the rectangle inhabits. -/
def rule3RectangularWitness_of_empty_y
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (hy : NodeSet.isEmpty y = true) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_given_w model G x y z w assignment disjoint
    separated
    (rule3YWLatentOverlap_eq_false_of_empty_y model G x y z w assignment
      hy)

/-- When no `Z` vertex ancestors `W` in `G_{\overline{X}}`, and path
d-separation forbids `Z` from ancestoring `Y` in `G_{\overline{X ∪ Z}}`,
the two rule-3 kernels share `Y` and `W` cylinders.  The selected mask is
vacuous: intervening on `Z` is invisible to both families. -/
def rule3RectangularWitness_of_z_avoids_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hrem : G.nonAncestorsOf (GraphMutilation.bar x) z w = z)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w)) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment := by
  let yLeft : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn y assignment
      (model.evalUnder ((rule3Left x y z w).intervention assignment) roots)
  let wLeft : model.latent.Assignment -> Bool := fun roots =>
    Kernel.agreesOn w assignment
      (model.evalUnder ((rule3Left x y z w).intervention assignment) roots)
  have yEq : forall roots,
      yLeft roots =
        Kernel.agreesOn y assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots) :=
    fun roots =>
      agreesOn_rule3Y_eq_of_z_avoids_w model G x y z w assignment
        disjoint hrem separated roots
  have wEq : forall roots,
      wLeft roots =
        Kernel.agreesOn w assignment
          (model.evalUnder
            ((rule3Right x y z w).intervention assignment) roots) :=
    fun roots =>
      agreesOn_rule3W_eq_of_z_avoids_w model G x y z w assignment hrem roots
  have hnumL :
      productPreimage model (rule3Left x y z w) assignment
          ((rule3Left x y z w).numeratorEvent assignment) =
        fun roots => yLeft roots && wLeft roots := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent, rule3Left]
    simp [yLeft, wLeft, rule3Left]
  have hnumR :
      productPreimage model (rule3Right x y z w) assignment
          ((rule3Right x y z w).numeratorEvent assignment) =
        fun roots => yLeft roots && wLeft roots := by
    funext roots
    simp only [productPreimage, Kernel.numeratorEvent]
    have hout : (rule3Right x y z w).outcome = y := rfl
    have hcondn : (rule3Right x y z w).condition = w := rfl
    rw [hout, hcondn]
    rw [← yEq roots, ← wEq roots]
  have hcondL :
      productPreimage model (rule3Left x y z w) assignment
          ((rule3Left x y z w).conditionEvent assignment) =
        wLeft := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent, rule3Left]
    simp [wLeft, rule3Left]
  have hcondR :
      productPreimage model (rule3Right x y z w) assignment
          ((rule3Right x y z w).conditionEvent assignment) =
        wLeft := by
    funext roots
    simp only [productPreimage, Kernel.conditionEvent]
    have hcondn : (rule3Right x y z w).condition = w := rfl
    rw [hcondn]
    rw [← wEq roots]
  exact
    { selected := fun _ => false
      leftNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Left x y z w) assignment
            ((rule3Left x y z w).numeratorEvent assignment))
      rightCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Right x y z w) assignment
            ((rule3Right x y z w).conditionEvent assignment))
      rightNumerator :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Right x y z w) assignment
            ((rule3Right x y z w).numeratorEvent assignment))
      leftCondition :=
        ProductEventRectangle.of_all_unselected model
          (productPreimage model (rule3Left x y z w) assignment
            ((rule3Left x y z w).conditionEvent assignment))
      selectedCross := QProb.equiv_refl _
      unselectedCross := by
        change QProb.Equiv
          (QProb.mul
            ((productRecord model).probVal
              (productPreimage model (rule3Left x y z w)
                assignment
                ((rule3Left x y z w).numeratorEvent assignment)))
            ((productRecord model).probVal
              (productPreimage model (rule3Right x y z w)
                assignment
                ((rule3Right x y z w).conditionEvent assignment))))
          (QProb.mul
            ((productRecord model).probVal
              (productPreimage model (rule3Right x y z w)
                assignment
                ((rule3Right x y z w).numeratorEvent assignment)))
            ((productRecord model).probVal
              (productPreimage model (rule3Left x y z w)
                assignment
                ((rule3Left x y z w).conditionEvent assignment))))
        rw [hnumL, hnumR, hcondL, hcondR]
        exact QProb.equiv_refl _ }

/-- Empty `W` is given-`W` rule 3 with a vacuous overlap: `W` has no
ancestral latents. -/
def rule3RectangularWitness_of_empty_w
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (hw : NodeSet.isEmpty w = true)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w)) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_given_w model G x y z w assignment disjoint
    separated
    (rule3YWLatentOverlap_eq_false_of_empty_w model G x y z w assignment hw)

/--
Rule 3 from path d-separation and the common/residual factorization of its
genuinely cross-interventional case.  Empty `Z`, empty `Y`, empty `W`, and
`Z(W) = Z` retain their direct constructions; only the remaining branch uses
the supplied factorization.
-/
def rule3RectangularWitness_of_path_factorization
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (factorization : Rule3GivenWFactorization model G x y z w assignment) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment := by
  cases hz : NodeSet.isEmpty z with
  | true =>
      exact rule3RectangularWitness_of_empty_z model x y z w assignment hz
  | false =>
      cases hy : NodeSet.isEmpty y with
      | true =>
          exact rule3RectangularWitness_of_empty_y model G x y z w
            assignment disjoint separated hy
      | false =>
          cases hw : NodeSet.isEmpty w with
          | true =>
              exact rule3RectangularWitness_of_empty_w model G x y z w
                assignment disjoint hw separated
          | false =>
              cases hrem :
                  NodeSet.equal
                    (G.nonAncestorsOf (GraphMutilation.bar x) z w) z with
              | true =>
                  exact rule3RectangularWitness_of_z_avoids_w model G
                    x y z w assignment disjoint
                    ((NodeSet.equal_eq_true_iff _ _).mp hrem)
                    separated
              | false =>
                  exact rule3RectangularWitness_of_given_w_factorization
                    model G x y z w assignment disjoint separated
                    factorization

/--
Rule 3 reduced to the graph statement exposed by the topological local
conditioning component: every `Y`-connected `W` factor is unchanged by
adding `do(Z)`.  Once that subset is known, the local factorization supplies
all selected/unselected coordinate judgements automatically.
-/
def rule3RectangularWitness_of_path_local_condition_component
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (commonSubsetLocalInvariant : NodeSet.Subset
      (rule3WConditionCommon model G x y z w assignment)
      (rule3WLocalInterventionInvariant G x z w)) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_path_factorization model G x y z w assignment
    disjoint separated
    (Rule3GivenWFactorization.of_local_condition_component model G x y z w
      assignment commonSubsetLocalInvariant)

/-- Rule 3 from path d-separation and projected-graph compatibility, with no
remaining graph premise.

The finite common-component theorem proves that every selected conditioning
factor is locally invariant; the established common/residual factorization
then supplies the rectangular latent-product witness for the two kernels. -/
def rule3RectangularWitness_of_path_projected
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w)) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_path_local_condition_component model G
    x y z w assignment disjoint separated
    (rule3WConditionCommon_subset_local_invariant_of_path model G projected
      x y z w assignment disjoint separated)

/--
Backward-compatible rule-3 assembler for the stronger no-overlap premise.
The premise is first embedded into the general common/residual
factorization; downstream cross-product algebra no longer relies on the
misleading idea that all valid rule-3 queries must satisfy it.
-/
def rule3RectangularWitness_of_path
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (x y z w : NodeSet S) (assignment : S.Assignment)
    (disjoint : FourWayDisjoint x y z w)
    (separated : PathSpecification.PathDSeparated G
      { removeIncoming :=
          NodeSet.union x (G.nonAncestorsOf (GraphMutilation.bar x) z w),
        removeOutgoing := NodeSet.empty }
      y z (NodeSet.union x w))
    (hoverlap :
      rule3YWLatentOverlap model G x y z w assignment = false) :
    ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment :=
  rule3RectangularWitness_of_path_factorization model G x y z w assignment
    disjoint separated
    (Rule3GivenWFactorization.of_no_overlap model G x y z w assignment
      hoverlap)

theorem ProductCrossProductEquivalentAt.toDistribution
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : ProductCrossProductEquivalentAt
      model left right assignment) :
    CrossProductEquivalentAt model left right assignment := by
  let leftNumerator := left.distribution_probVal_productRecord model assignment
    (left.numeratorEvent assignment)
  let leftDenominator := left.distribution_probVal_productRecord model assignment
    (left.conditionEvent assignment)
  let rightNumerator := right.distribution_probVal_productRecord model assignment
    (right.numeratorEvent assignment)
  let rightDenominator := right.distribution_probVal_productRecord model assignment
    (right.conditionEvent assignment)
  refine ⟨QProb.equiv_trans
    (QProb.mul_congr leftNumerator rightDenominator)
    (QProb.equiv_trans equivalent.cross
      (QProb.equiv_symm
        (QProb.mul_congr rightNumerator leftDenominator)))⟩

/-- A cross-product identity yields equality of both supported partial ratios. -/
noncomputable def CrossProductEquivalentAt.denote
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : CrossProductEquivalentAt model left right assignment)
    (leftSupported : ProbabilityTerm.SupportedAt model (.kernel left) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model (.kernel right) assignment) :
    ProbabilityResult.Equivalent
      (left.denote model assignment) (right.denote model assignment) := by
  let leftNumerator := (left.distribution model assignment).probVal
    (left.numeratorEvent assignment)
  let leftDenominator := (left.distribution model assignment).probVal
    (left.conditionEvent assignment)
  let rightNumerator := (right.distribution model assignment).probVal
    (right.numeratorEvent assignment)
  let rightDenominator := (right.distribution model assignment).probVal
    (right.conditionEvent assignment)
  have leftPositive : 0 < leftDenominator.num := by
    by_cases positive : 0 < leftDenominator.num
    · exact positive
    · change ProbabilityResult.Supported (left.denote model assignment)
        at leftSupported
      simp only [Kernel.denote, leftDenominator,
        ProbabilityResult.divide, dif_neg positive] at leftSupported
      rcases leftSupported with ⟨_, impossible⟩
      cases impossible
  have rightPositive : 0 < rightDenominator.num := by
    by_cases positive : 0 < rightDenominator.num
    · exact positive
    · change ProbabilityResult.Supported (right.denote model assignment)
        at rightSupported
      simp only [Kernel.denote, rightDenominator,
        ProbabilityResult.divide, dif_neg positive] at rightSupported
      rcases rightSupported with ⟨_, impossible⟩
      cases impossible
  simp only [Kernel.denote, leftDenominator, rightDenominator,
    ProbabilityResult.divide,
    dif_pos leftPositive, dif_pos rightPositive]
  exact .value (QProb.div_equiv_of_cross leftPositive rightPositive
    equivalent.cross)

end Kernel
end Causality
end Thesis
