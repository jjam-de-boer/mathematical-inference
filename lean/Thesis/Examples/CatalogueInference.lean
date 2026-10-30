import Thesis.CausalTransport.CatalogueInference
import Thesis.CausalTransport.CataloguePartition
import Thesis.Causality.BinaryBowEndpoints

namespace Thesis
namespace Causality
namespace Examples
namespace CatalogueInference

open Probability Probability.Distros
open BinaryBow
open Causality.CatalogueInference
open Causality.CataloguePartition

/-!
# Two-graph Bayesian catalogue: chain vs bow, plus an independence restriction

Shared host signature is `BinaryBow.signature` (directed `X → Y`). The three
atoms are:

* independence: mechanism restriction `X ⊥ Y`, formula `P(Y)` (not ID on a
  different directed graph — competing directed edges would need another
  signature);
* chain: bidirected-free host graph, ID of `P(Y | do(X))`;
* bow: the native bow graph, sharp bounds.

Correlated observational data zero the independence atom in Regime A.
Regime B keeps a positive Dirichlet–multinomial weight on every atom, so
the mixture can disagree between two identified values. Layer 3 is a
depth-capped Boolean `W` tree on four cells, wired to an identified
conditional-difference formula.
-/

def xy (xv yv : Bool) : signature.Assignment :=
  fun i => if i.val = 0 then xv else yv

def correlated : FiniteProbRecord signature.Assignment where
  atoms := [(xy false false, 1), (xy true true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def chainGraph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ h; cases h
  bidirected_irreflexive := fun _ => rfl

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  action_outcome_disjoint := by
    intro i hx
    have : i = x := (NodeSet.singleton_eq_true_iff x i).mp hx
    subst this
    simp [NodeSet.singleton, x, y]

def independenceFormula : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.empty⟩

def productCompatible (law : FiniteProbRecord signature.Assignment) : Bool :=
  [false, true].all fun xv =>
    [false, true].all fun yv =>
      let joint := law.probVal (fun a => decide (a x = xv) && decide (a y = yv))
      let px := law.probVal (fun a => decide (a x = xv))
      let py := law.probVal (fun a => decide (a y = yv))
      decide (QProb.Equiv joint (QProb.mul px py))

structure Item where
  graph : ObservedGraph signature
  override : Option (ProbabilityTerm signature)
  bow : Bool
  product : Bool

def independenceItem : Item :=
  ⟨chainGraph, some independenceFormula, false, true⟩

def chainItem : Item :=
  ⟨chainGraph, none, false, false⟩

def bowItem : Item :=
  ⟨graph, none, true, false⟩

def items : List Item := [independenceItem, chainItem, bowItem]

theorem items_length : items.length = 3 := rfl

def catalogue : Catalogue items.length Item :=
  uniformOfList items (by decide)

def reference : signature.Assignment := xy true true

def lawWeight (item : Item) : Nat :=
  boolWeight (if item.product then productCompatible correlated else true)

def lawWeights : Fin 3 → Nat :=
  fun i => lawWeight (catalogue.item i)

def lawBounds (item : Item) : Option (QProb × QProb) :=
  if item.bow then some (BinaryBow.lower correlated true, BinaryBow.upper correlated true)
  else none

def lawAnswer (i : Fin 3) : TemplateAnswer signature :=
  let item := catalogue.item i
  answerOf item.graph query (.law correlated) reference (lawBounds item) item.override

def lawReport : Report 3 Item signature :=
  match infer catalogue lawWeights lawAnswer with
  | some r => r
  | none =>
      reportOf catalogue catalogue.prior lawWeights lawAnswer

theorem independence_law_weight_zero : lawWeights ⟨0, by decide⟩ = 0 := by
  native_decide

theorem chain_law_weight_one : lawWeights ⟨1, by decide⟩ = 1 := by
  native_decide

theorem bow_law_weight_one : lawWeights ⟨2, by decide⟩ = 1 := by
  native_decide

set_option maxRecDepth 100000

def chainFormula : ProbabilityTerm signature :=
  match identifyJointKernel chainGraph query with
  | .identified term => term
  | _ => .zero

theorem chain_identified :
    identifyJointKernel chainGraph query = .identified chainFormula := by
  rfl

def bowFailed : Bool :=
  match identifyJointKernel graph query with
  | .failed _ => true
  | _ => false

theorem bow_failed : bowFailed = true := by
  rfl

theorem law_posterior_exists :
    (posterior? catalogue.prior lawWeights).isSome = true := by
  native_decide

def lawPosterior : Distro (Fin 3) :=
  match posterior? catalogue.prior lawWeights with
  | some μ => μ
  | none => catalogue.prior

theorem independence_posterior_zero :
    (lawPosterior.pmf ⟨0, by decide⟩).num = 0 := by
  native_decide

theorem chain_posterior_pos :
    0 < (lawPosterior.pmf ⟨1, by decide⟩).num := by
  native_decide

theorem bow_posterior_pos :
    0 < (lawPosterior.pmf ⟨2, by decide⟩).num := by
  native_decide

def chainValue : ProbabilityResult.Result :=
  match lawAnswer ⟨1, by decide⟩ with
  | .identified _ value => value
  | _ => none

def bowInterval : Option (QProb × QProb) :=
  match lawAnswer ⟨2, by decide⟩ with
  | .bounded lo hi => some (lo, hi)
  | _ => none

def isIdentified : TemplateAnswer signature → Bool
  | .identified _ _ => true
  | _ => false

def isBounded : TemplateAnswer signature → Bool
  | .bounded _ _ => true
  | _ => false

def isSpread {S : ObservedSignature} : Mixture S → Bool
  | .spread _ => true
  | _ => false

def keepsDisagreement {S : ObservedSignature} : Mixture S → Bool
  | .disagree _ _ _ _ => true
  | .spread _ => true
  | _ => false

def isIdentifiedLeaf : LeafAnswer → Bool
  | .identified _ => true
  | _ => false

theorem chain_identified_answer : isIdentified (lawAnswer ⟨1, by decide⟩) = true := by
  native_decide

theorem bow_bounded_answer : isBounded (lawAnswer ⟨2, by decide⟩) = true := by
  native_decide

theorem law_mixture_spread : isSpread lawReport.mixture = true := by
  native_decide

/-- Existing bow endpoint models are the bound witnesses. -/
def bowLowerModel := BinaryBow.model correlated false
def bowUpperModel := BinaryBow.model correlated true

def C : Nat := 2

def lawOddsChainBow : Option (QProb × QProb) :=
  posteriorOddsInterval C (by decide)
    ⟨lawWeights ⟨1, by decide⟩, 1, Nat.succ_pos 0⟩
    ⟨lawWeights ⟨2, by decide⟩, 1, Nat.succ_pos 0⟩

theorem law_odds_defined : lawOddsChainBow.isSome = true := by
  native_decide

/-! ## Regime B: Dirichlet–multinomial on the observed table -/

def labels : List signature.Assignment := signature.assignmentEnumeration

def countOf (a : signature.Assignment) : Nat :=
  if decide (a x = a y) then 3 else 0

def bins : List Nat := labels.map countOf

def uniformAlphas : List QProb := [QProb.one, QProb.one, QProb.one, QProb.one]

theorem uniformAlphas_pos : 0 < (QProb.listSum uniformAlphas).num := by
  decide

def saturatedMass : QProb :=
  dirichletMultinomialMass bins.sum uniformAlphas uniformAlphas_pos bins

def marginFalse (node : Fin signature.count) : Nat :=
  (labels.zip bins).foldl (fun acc p =>
    acc + if decide (p.1 node = false) then p.2 else 0) 0

def marginTrue (node : Fin signature.count) : Nat :=
  (labels.zip bins).foldl (fun acc p =>
    acc + if decide (p.1 node = true) then p.2 else 0) 0

def twoAlphas : List QProb := [QProb.one, QProb.one]

theorem twoAlphas_pos : 0 < (QProb.listSum twoAlphas).num := by
  decide

/-- v1 product-of-marginal Dirichlet–multinomials for the independence
atom. The extra multinomial coefficient of the joint given its margins is
omitted; hidden-sum over native source tables is `sumHiddenCompletions`. -/
def independenceMass : QProb :=
  QProb.mul
    (dirichletMultinomialMass (marginFalse x + marginTrue x) twoAlphas twoAlphas_pos
      [marginFalse x, marginTrue x])
    (dirichletMultinomialMass (marginFalse y + marginTrue y) twoAlphas twoAlphas_pos
      [marginFalse y, marginTrue y])

def countLikelihood : Fin 3 → QProb
  | ⟨0, _⟩ => independenceMass
  | ⟨1, _⟩ => saturatedMass
  | ⟨2, _⟩ => saturatedMass

def countWeights : Fin 3 → Nat :=
  qprobWeights 3 countLikelihood

def countLaw : FiniteProbRecord signature.Assignment :=
  recordOfCounts labels bins
    (by simp [bins, labels, List.length_map])
    (by native_decide)

def countAnswer (i : Fin 3) : TemplateAnswer signature :=
  let item := catalogue.item i
  answerOf item.graph query (.law countLaw) reference (lawBounds item) item.override

def countReport : Report 3 Item signature :=
  match infer catalogue countWeights countAnswer with
  | some r => r
  | none => reportOf catalogue catalogue.prior countWeights countAnswer

theorem count_posterior_exists :
    (posterior? catalogue.prior countWeights).isSome = true := by
  native_decide

theorem count_independence_pos :
    0 < (countReport.mass ⟨0, by decide⟩).num := by
  native_decide

theorem count_mixture_keeps_disagreement :
    keepsDisagreement countReport.mixture = true := by
  native_decide

/-! ## Layer 3: depth-capped Boolean `W`, identified leaf formula -/

def pooled : TyTable :=
  addCount (addCount emptyTable true true 3) false false 3

def leafIdentified : LeafAnswer :=
  leafAnswer true pooled none

theorem leaf_tau_defined : isIdentifiedLeaf leafIdentified = true := by
  native_decide

def cap1Trees : List SplitTree := treesUpTo 1

theorem cap1_nonempty : 0 < cap1Trees.length :=
  treesUpTo_length_pos 1

def stumpTables (_idx : Nat) : TyTable := pooled

def stumpLikelihood (tree : SplitTree) : QProb :=
  treeLikelihood tree stumpTables uniformAlphas uniformAlphas_pos

def stumpWeights : Fin (treesUpTo 1).length → Nat :=
  qprobWeights (treesUpTo 1).length (fun i =>
    stumpLikelihood ((treesUpTo 1).get i))

theorem stump_posterior_exists :
    (posterior? (treePrior 1) stumpWeights).isSome = true := by
  native_decide

def stumpPosterior : Distro (Fin (treesUpTo 1).length) :=
  match posterior? (treePrior 1) stumpWeights with
  | some μ => μ
  | none => treePrior 1

def stumpTau (cell : Cell) : Option SignedRatio :=
  mixTau 1 stumpPosterior (fun _ _ => leafIdentified) cell

theorem stump_tau_cell0 :
    (stumpTau ⟨0, by decide⟩).isSome = true := by
  native_decide

def refinement : ObservationChain (discreteUniformDistro 4 (by decide)) 1 :=
  firstBitChain _

end CatalogueInference
end Examples
end Causality
end Thesis
