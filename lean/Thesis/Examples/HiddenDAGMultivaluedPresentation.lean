import Thesis.CausalTransport.HiddenDAGFinitePresentation
import Thesis.CausalTransport.HiddenDAGSoundness
import Thesis.Probability.Distros.FinitePresentation
import Thesis.Probability.Distros.MultivariateHypergeometric

namespace Thesis.Causality.Examples.HiddenDAGMultivaluedPresentation

open Probability Probability.Distros

/-!
# A native three-valued observed domain retaining a null value

Sample one item from two colours with one item each. Its first-colour count
has probabilities one half at zero and one, and zero at two. Declare all
three counts as permitted observed values nonetheless. The node's native
values are the declared-domain subtype, while its observed values are finite
codes. The actual two-sided conversion is `ValueEquivalence.ofFiniteWitness`,
not an identity map or an occurrence decoder mistaken for a bijection.

There are two independent observed nodes. `X` is factually zero; `Y` reads
the decoded finite-population count. The all-event and supported-conditional
theorems concern the actual native evaluator and product prior. Intervening
on the null value two of `X` leaves the entire multivalued `Y` law unchanged,
as the graph-derived native rule-3 theorem also certifies.

For a second boundary check, forcing `Y` itself to its null value gives that
value with probability one. This last statement is structural evaluation in
the supplied model, not observational identification of an unsupported effect.
No continuous law, positive-support-only domain, or default null conditional
is introduced by this fixture.
-/

def domain : List Nat := [0, 1, 2]

abbrev DeclaredValue := {value : Nat // value ∈ domain}

def witness : FiniteWitness DeclaredValue := FiniteProbRecord.domainWitness domain

def conversion : ValueEquivalence DeclaredValue (Fin witness.card) :=
  .ofFiniteWitness witness

def zeroValue : DeclaredValue := ⟨0, by decide⟩
def nullValue : DeclaredValue := ⟨2, by decide⟩
def zeroCode : Fin witness.card := witness.encode zeroValue
def nullCode : Fin witness.card := witness.encode nullValue

def readValue (code : Fin witness.card) : Nat := (witness.decode code).val

theorem domain_card : witness.card = 3 := by decide +kernel

theorem read_zero : readValue zeroCode = 0 :=
  congrArg Subtype.val (witness.decode_encode zeroValue)

theorem read_null : readValue nullCode = 2 :=
  congrArg Subtype.val (witness.decode_encode nullValue)

/-- The actual newer distribution, mapped to its first-colour count. -/
def counts : Distro Nat :=
  (multivariateHypergeometricDistro 1 [1, 1] (by decide)).map (fun values => values.getD 0 0)

private theorem covered : ∀ atom, atom ∈ counts.record.atoms → atom.1 ∈ domain := by
  intro atom member
  change atom ∈ (multivariateHypergeometricAtoms 1 [1, 1]).map
    (fun original => (original.1.getD 0 0, original.2)) at member
  rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
  have bounded := multivariateHypergeometric_coordinate_bound 1 [1, 1] original originalMember 0
  simp only [domain, List.mem_cons, List.not_mem_nil, or_false]
  omega

def coded := counts.finiteDomainPresentation domain covered

theorem decoded_record_recovered : coded.record.map coded.decode = counts.record := coded.recovered

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Fin witness.card
  valueEnumeration := fun _ => List.finRange witness.card
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := by intro _; rw [domain_card]; decide
  defaultValue := fun _ => zeroCode
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

/-- Richness concerns permitted values, not positive probability in this
particular distribution. The declared null value is a legitimate second value. -/
def rich : ObservedSignature.ValueRich signature where
  first := fun _ => zeroCode
  second := fun _ => nullCode
  first_enumerated := fun _ => List.mem_finRange zeroCode
  second_enumerated := fun _ => List.mem_finRange nullCode
  different := by
    intro _ same
    have impossible := congrArg readValue same
    rw [read_zero, read_null] at impossible
    cases impossible

def fullGraph : FiniteHiddenDAG signature where
  count := 2
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := fun _ => rfl
  node_classified := fun node => Or.inr ⟨node, rfl⟩
  edge := fun _ _ => false
  rank := Fin.val
  edge_rank_lt := by intro _ _ impossible; cases impossible

private theorem no_path {first second : Fin fullGraph.count}
    (path : fullGraph.HiddenInternalPath first second) : False := by
  cases path with
  | direct impossible => cases impossible
  | tail _ _ impossible => cases impossible

def projection : FiniteLatentProjection signature where
  hiddenDAG := fullGraph
  directed_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · intro path; exact False.elim (no_path path)
  bidirected := fun _ _ => false
  bidirected_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · rintro ⟨_, _, impossible, _, _⟩; cases impossible

/-- Native node values and observed codes are genuinely different types.
Every declared value, including two, remains in both finite enumerations. -/
def model : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => DeclaredValue
  nodeEnumeration := fun _ => domain.attach
  node_complete := fun _ value => List.mem_attach domain value
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => conversion
  observedIndex := some
  observedIndex_observed := fun _ => rfl
  observedIndex_sound := fun _ _ same => (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ impossible; cases impossible
  Noise := fun _ => Fin witness.card
  noiseEnumeration := fun _ => List.finRange witness.card
  noise_complete := fun _ value => List.mem_finRange value
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => coded.record
  prior := FiniteProduct.record 2 (fun _ => Fin witness.card) (fun _ => coded.record)
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Fin witness.card) (fun _ => coded.record)
  mechanism := fun child _parents noise => if child.val = 0 then zeroValue else witness.decode noise

theorem eval_y (intervention : HardIntervention signature) (unforced : intervention.value y = none)
    (noise : model.NoiseAssignment) : model.evalObserved intervention noise y = noise y := by
  change witness.encode (model.evalNode intervention noise y) = noise y
  rw [FiniteHiddenDAGSCM.evalNode]
  have absent : model.interventionValueAt intervention y = none := by
    change model.interventionValueAt intervention (projection.hiddenDAG.observedNode y) = none
    rw [FiniteHiddenDAGSCM.interventionValueAt_observed_eq_map, unforced]
    rfl
  rw [absent]
  exact witness.encode_decode (noise y)

/-- All multivalued events, not only one Boolean summary, retain the actual
finite-population distribution under interventions away from `Y`. -/
theorem interventional_y_event (intervention : HardIntervention signature)
    (unforced : intervention.value y = none) (event : Event Nat) :
    QProb.Equiv (model.interventionalValue intervention (fun values => event (readValue (values y))))
      (counts.record.probVal event) := by
  apply QProb.equiv_trans (model.prior.map_probVal _ _)
  apply QProb.equiv_trans (model.prior.probVal_congr _ _
    (fun noise => congrArg (fun code => event (readValue code)) (eval_y intervention unforced noise)))
  exact QProb.equiv_trans
    (FiniteProduct.record_coordinate_probVal_dependent 2 (fun _ => Fin witness.card)
      (fun _ => coded.record) y (fun code => event (readValue code)))
    (coded.probVal event)

theorem observational_y_event (event : Event Nat) :
    QProb.Equiv (model.observationalValue (fun values => event (readValue (values y))))
      (counts.record.probVal event) :=
  interventional_y_event (HardIntervention.empty signature) rfl event

/-- Support transports from the original law to the native marginal.
No support for the null count is manufactured by the value conversion. -/
theorem native_evidence_positive (evidence : Event Nat) (supported : counts.record.EventPositive evidence) :
    model.observationalDist.EventPositive (fun values => evidence (readValue (values y))) :=
  (QProb.equiv_num_pos_iff (observational_y_event evidence)).mpr supported

theorem observational_y_conditional (evidence event : Event Nat)
    (supported : counts.record.EventPositive evidence) :
    QProb.Equiv
      ((model.observationalDist.conditionOn (fun values => evidence (readValue (values y)))
        (native_evidence_positive evidence supported)).probVal (fun values => event (readValue (values y))))
      ((counts.record.conditionOn evidence supported).probVal event) := by
  exact QProb.equiv_trans (model.observationalDist.conditionOn_probVal _ _ (native_evidence_positive evidence supported))
    (QProb.equiv_trans
      (QProb.div_congr (observational_y_event (fun value => evidence value && event value))
        (observational_y_event evidence) (native_evidence_positive evidence supported) supported)
      (QProb.equiv_symm (counts.record.conditionOn_probVal evidence event supported)))

theorem null_observed_y :
    QProb.Equiv (model.observationalValue (fun values => decide (readValue (values y) = 2))) QProb.zero :=
  QProb.equiv_trans (observational_y_event (fun value => decide (value = 2))) (by decide +kernel)

theorem do_x_null_preserves_y (event : Event Nat) :
    QProb.Equiv (model.interventionalValue ((HardIntervention.empty signature).set x nullCode)
      (fun values => event (readValue (values y)))) (counts.record.probVal event) :=
  interventional_y_event _ (HardIntervention.set_away_from_target _ x y nullCode (by decide)) event

def rule3Application : DoRuleApplication projection.observedGraph
    (rule3Left NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty)
    (rule3Right NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty) :=
  .rule3 NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty
    (FourWayDisjoint.emptyAction _ _ NodeSet.empty
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _))
    (by
      change projection.observedGraph.dSeparated
        { removeIncoming := NodeSet.union NodeSet.empty
            (projection.observedGraph.nonAncestorsOf (.bar NodeSet.empty) (NodeSet.singleton x) NodeSet.empty),
          removeOutgoing := NodeSet.empty }
        (NodeSet.singleton y) (NodeSet.singleton x) (NodeSet.union NodeSet.empty NodeSet.empty) = true
      decide +kernel)

/-- The native do-rule checks the actual three-valued observed signature.
Its unconditional endpoints require no factual action-positivity assumption. -/
noncomputable def rule3_sound (reference : signature.Assignment) : model.TermEquivalentAt
    (.kernel (rule3Left NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty))
    (.kernel (rule3Right NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty)) reference :=
  model.doRule_soundAt reference rule3Application
    (model.kernelSupportedAt_unconditional (NodeSet.singleton y)
      (NodeSet.union NodeSet.empty (NodeSet.singleton x)) reference)
    (model.kernelSupportedAt_unconditional (NodeSet.singleton y) NodeSet.empty reference)

/-- Forcing the declared null value is a valid structural operation. This
is a statement about this model's evaluator, not a claim that observations
identify arbitrary effects at unsupported action cells. -/
theorem eval_y_forced_null (noise : model.NoiseAssignment) :
    model.evalObserved ((HardIntervention.empty signature).set y nullCode) noise y = nullCode := by
  change witness.encode (model.evalNode ((HardIntervention.empty signature).set y nullCode) noise y) = nullCode
  rw [FiniteHiddenDAGSCM.evalNode]
  have forced : model.interventionValueAt ((HardIntervention.empty signature).set y nullCode) y =
      some (witness.decode nullCode) := by
    change model.interventionValueAt ((HardIntervention.empty signature).set y nullCode)
      (projection.hiddenDAG.observedNode y) = some (witness.decode nullCode)
    rw [FiniteHiddenDAGSCM.interventionValueAt_observed_eq_map, HardIntervention.set_at_target]
    rfl
  rw [forced]
  exact witness.encode_decode nullCode

theorem do_y_null_probability_one :
    QProb.Equiv (model.interventionalValue ((HardIntervention.empty signature).set y nullCode)
      (fun values => decide (readValue (values y) = 2))) QProb.one := by
  apply QProb.equiv_trans (model.prior.map_probVal _ _)
  exact QProb.equiv_trans (model.prior.probVal_congr _ (fun _ => true) (fun noise => by
    rw [eval_y_forced_null noise, read_null]
    decide)) model.prior.normalization

end Thesis.Causality.Examples.HiddenDAGMultivaluedPresentation
