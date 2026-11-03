import Thesis.Probability.Distros.NodeLawRecipe
import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.Construction

namespace Thesis.Examples.NodeLawRecipe
open Probability Probability.Distros Causality

/-- A supplied two-cell alphabet and exact success probability. -/
def bitConstraints (target : SignedRatio) : NodeLawConstraints Bool := {
  problem := {
    cells := [false, true]
    default := false
    nonempty := by decide
    distinct := by decide
    intervals := [.exact (fun x => if x then 1 else 0) target] } }

def rootRecipe : Distros.NodeLawRecipe Bool := .named (.bernoulli 2 1 (by decide) id)
def childRecipe : Distros.NodeLawRecipe Bool := .constraints (bitConstraints ⟨1, 4, by decide⟩)

private theorem childSuccess : childRecipe.compile.succeeded = true := by decide +kernel

def rootFactor : FiniteProbRecord Bool := rootRecipe.compile.table (by decide +kernel)
def childFactor : FiniteProbRecord Bool := childRecipe.compile.table childSuccess

example : (bitConstraints ⟨1, 4, by decide⟩).Accepts ⟨childFactor⟩ := childRecipe.compile.table_accepts childSuccess
example : QProb.Equiv (childFactor.probVal id) ⟨1, 4, by decide⟩ := by decide +kernel

/-- An actual supplied orbit equality conflicts with this moment; neither
input alone is inconsistent. Compilation returns a refutation, not a table. -/
def conflicting : NodeLawConstraints Bool := {
  bitConstraints ⟨1, 4, by decide⟩ with partition := some (fun _ => 0) }
example : (Distros.NodeLawRecipe.constraints conflicting).compile.table? = none := by decide +kernel

/-- A genuine moment interval is enforced without completing it to a
single specified mean or silently claiming that its feasible law is unique. -/
def intervalSpec : NodeLawConstraints Bool := {
  bitConstraints SignedRatio.zero with
  problem.intervals := [⟨fun x => if x then 1 else 0, ⟨1, 4, by decide⟩, ⟨3, 4, by decide⟩⟩] }
example : (match (Distros.NodeLawRecipe.constraints intervalSpec).compile with
    | .success table _ => decide (SignedRatio.LE ⟨1, 4, by decide⟩ (table.probVal id).toSignedRatio ∧
        SignedRatio.LE (table.probVal id).toSignedRatio ⟨3, 4, by decide⟩)
    | .infeasible _ => false) = true := by decide +kernel

/-- The null third cell stays in the table while the first two singleton
masses are constrained equal by an explicitly supplied partition. -/
def withNull : NodeLawConstraints Nat := {
  problem := {
    cells := [0, 1, 2]
    default := 0
    nonempty := by decide
    distinct := by decide
    intervals := [.exact (fun x => if x = 2 then 1 else 0) SignedRatio.zero] }
  partition := some (fun x => if x < 2 then 0 else 1) }
example : (match (Distros.NodeLawRecipe.constraints withNull).compile with
    | .success table _ => decide (QProb.Equiv ((⟨table⟩ : Distro Nat).pmf 0) ⟨1, 2, by decide⟩ ∧
        QProb.Equiv ((⟨table⟩ : Distro Nat).pmf 1) ⟨1, 2, by decide⟩ ∧ (2, 0) ∈ table.atoms)
    | .infeasible _ => false) = true := by decide +kernel

/-- One moment on three cells is underdetermined. Both witnesses are valid,
and an extra zero-weight label outside the grid is harmless. -/
def ambiguous : NodeLawConstraints Nat := { problem := scalarPartialMomentProblem 2 [MomentInterval.exact (fun n => (n : Int)) SignedRatio.one] }
def middleLaw : Distro Nat := ⟨{
  atoms := [(1, 1), (99, 0)]
  den := 1
  den_pos := by decide
  total_mass := rfl }⟩
def endpointsLaw : Distro Nat := ⟨{
  atoms := [(0, 1), (2, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl }⟩
private theorem ambiguous_accepts (law : Distro Nat)
    (support : law.AlmostSurely (fun x => x ∈ ambiguous.problem.cells))
    (moment : (MomentInterval.exact (fun n : Nat => (n : Int)) SignedRatio.one).LawHolds law) :
    ambiguous.Accepts law := by
  refine ⟨support, ?_, ?_⟩
  · intro interval member
    have same := List.mem_singleton.mp member
    cases same
    exact moment
  · intro label impossible
    cases impossible

example : ambiguous.Accepts middleLaw ∧ ambiguous.Accepts endpointsLaw ∧
    ¬ QProb.Equiv (middleLaw.pmf 1) (endpointsLaw.pmf 1) :=
  ⟨ambiguous_accepts middleLaw (by decide +kernel) (by unfold MomentInterval.LawHolds; decide +kernel),
    ambiguous_accepts endpointsLaw (by decide +kernel) (by unfold MomentInterval.LawHolds; decide +kernel), by decide +kernel⟩
example : (Distros.NodeLawRecipe.ofDistro middleLaw).compile.table? = some middleLaw.record := rfl

/-- Named adapters use the existing constructors with explicit parameters. -/
example : QProb.Equiv ((NamedNodeLaw.categorical 3
    (fun i => if i = 0 then 1 else if i = 1 then 2 else 0)
    (by decide) (fun i => decide (i.val < 2))).distro.pmf true) QProb.one ∧
    QProb.Equiv ((NamedNodeLaw.categorical 3
      (fun i => if i = 0 then 1 else if i = 1 then 2 else 0)
      (by decide) (fun i => decide (i.val < 2))).distro.pmf false) QProb.zero := by decide +kernel
example : QProb.Equiv ((NamedNodeLaw.polya 2 [1, 1] (by decide) id).distro.pmf [0, 0])
    ⟨1, 3, by decide⟩ := by decide +kernel
example : QProb.Equiv ((NamedNodeLaw.rationalPolya 2 [⟨1, 2, by decide⟩, ⟨1, 2, by decide⟩]
    (by decide) id).distro.pmf [0, 0]) ⟨3, 8, by decide⟩ := by decide +kernel
example : QProb.Equiv ((NamedNodeLaw.hypergeometric 1 2 2 (by decide) (by decide) id).distro.pmf 1)
    QProb.one := by decide +kernel
example : QProb.Equiv ((NamedNodeLaw.bernoulli 0 1 (by decide) id).distro.pmf true) QProb.zero := by decide +kernel

/-- An observed edge X -> Y, without hidden vertices. -/
def signature : ObservedSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by decide +kernel

def graph : FiniteHiddenDAG signature where
  count := 2
  observedNode := id
  observedNode_injective _ _ same := same
  hidden _ := false
  observed_not_hidden _ := rfl
  node_classified node := Or.inr ⟨node, rfl⟩
  edge := signature.directed
  rank := Fin.val
  edge_rank_lt := by decide +kernel

def projection : FiniteLatentProjection signature where
  hiddenDAG := graph
  directed_matches := by
    intro first second
    constructor
    · exact fun edge => .direct edge
    · intro path
      cases path with
      | direct edge => exact edge
      | tail _ hidden _ => cases hidden
  bidirected _ _ := false
  bidirected_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · rintro ⟨_, _, hidden, _, _⟩; cases hidden

def factors (node : Fin 2) : FiniteProbRecord Bool := if node = 0 then rootFactor else childFactor

def handFactors (node : Fin 2) : FiniteProbRecord Bool :=
  if node = 0 then {
    atoms := [(false, 1), (true, 2)]
    den := 3
    den_pos := by decide
    total_mass := rfl }
  else {
    atoms := [(false, 3), (true, 1)]
    den := 4
    den_pos := by decide
    total_mass := rfl }

/-- The same structural equations with either recipe-generated or hand-written
private-noise factors: X=U_X and Y=X xor U_Y. The prior is their actual
independent product, so the SCM product-law obligation is proved. -/
def model (tables : Fin 2 → FiniteProbRecord Bool) : FiniteHiddenDAGSCM signature projection where
  NodeValue _ := Bool
  nodeEnumeration _ := [false, true]
  node_complete := by intro _ value; cases value <;> simp
  nodeDecidableEq _ := inferInstance
  observedEquiv _ := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := some
  observedIndex_observed _ := rfl
  observedIndex_sound _ _ same := (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ hidden; cases hidden
  Noise _ := Bool
  noiseEnumeration _ := [false, true]
  noise_complete := by intro _ value; cases value <;> simp
  noiseDecidableEq _ := inferInstance
  factor := tables
  prior := FiniteProduct.record 2 (fun _ => Bool) tables
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism node parents seed :=
    if atRoot : node.val = 0 then seed
    else Bool.xor (parents (0 : Fin 2) (by
      have atChild : node.val = 1 := by have bounded : node.val < 2 := node.isLt; omega
      change decide (0 = 0 ∧ node.val = 1) = true
      simp only [atChild, and_self, decide_true])) seed

def recipeModel := model factors
def handModel := model handFactors

def setX (value : Bool) : HardIntervention signature := (HardIntervention.empty signature).set (0 : Fin 2) value

def yTrue : signature.Assignment → Bool := fun assignment => assignment (1 : Fin 2)

/-- All four observed cells agree with the independently written tables. -/
example : ∀ x y : Bool, QProb.Equiv
    (recipeModel.observationalValue (fun assignment => (assignment (0 : Fin 2) == x) && (assignment (1 : Fin 2) == y)))
    (handModel.observationalValue (fun assignment => (assignment (0 : Fin 2) == x) && (assignment (1 : Fin 2) == y))) := by decide +kernel

/-- Interventions evaluate the same structural equations with the recipe
factors; they are not a second update of a CPT or an identification call. -/
example : ∀ x : Bool, QProb.Equiv (recipeModel.interventionalValue (setX x) yTrue)
    (handModel.interventionalValue (setX x) yTrue) := by decide +kernel
example : QProb.Equiv (recipeModel.observationalValue yTrue) ⟨7, 12, by decide⟩ := by decide +kernel
example : QProb.Equiv (recipeModel.interventionalValue (setX false) yTrue) ⟨1, 4, by decide⟩ := by decide +kernel
example : QProb.Equiv (recipeModel.interventionalValue (setX true) yTrue) ⟨3, 4, by decide⟩ := by decide +kernel

end Thesis.Examples.NodeLawRecipe
