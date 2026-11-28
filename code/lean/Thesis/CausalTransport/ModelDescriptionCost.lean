import Init.Data.Rat.Lemmas
import Thesis.CausalTransport.CatalogueSymmetry
import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.FiniteFunctionTables
import Thesis.Probability.Reindexing

/-!
# Costs for declared finite model descriptions

The structural score counts the slots in an explicit description with
one table row for every assignment of allowed parents and incident
latent sources. The rational-law score counts the binary digits of
reduced singleton masses on a declared alphabet. Neither score claims
to be a decodable bit code for a whole graph or a minimum over all
possible representations. Adding an edge, repacking the latent sources,
or changing the alphabet can change the description that is scored.
-/

namespace Thesis.Causality.ModelDescriptionCost

open Probability Probability.Distros FiniteSymmetry CatalogueInference

/-- The dense-table layout retains the size of each separate input
alphabet. The mechanisms themselves may use fewer inputs than declared. -/
structure Layout (vertices sources : Nat) where
  values : Fin vertices → Nat
  latentValues : Fin sources → Nat
  directed : Fin vertices → Fin vertices → Bool
  incident : Fin sources → Fin vertices → Bool

def Layout.ofModel {S : ObservedSignature.{0}} (model : ExactModel S) :
    Layout S.count model.latent.count where
  values node := (S.valueEnumeration node).length
  latentValues source := by
    letI : DecidableEq (model.latent.Value source) := model.latent.valueDecidableEq source
    exact (deduplicate (model.latent.valueEnumeration source)).length
  directed := S.directed
  incident := model.latent.incident

private def total (n : Nat) (term : Fin n → Nat) : Nat :=
  AdditiveCarrier.nat.finSum n term

private def product (n : Nat) (term : Fin n → Nat) : Nat :=
  ((List.finRange n).map term).foldr (· * ·) 1

/-- One output cell is stored for every configuration of the declared
inputs. Inactive coordinates have one possible input, the empty one. -/
def Layout.mechanismCells (layout : Layout vertices sources) (child : Fin vertices) : Nat :=
  product vertices (fun parent => if layout.directed parent child then layout.values parent else 1) *
    product sources (fun source => if layout.incident source child then layout.latentValues source else 1)

/-- Each observed vertex, latent source, directed edge, latent incidence
and mechanism cell contributes one unit. A node with no inputs stores one
constant mechanism cell. -/
def Layout.cost (layout : Layout vertices sources) : Nat :=
  vertices + sources + total vertices fun child =>
    total vertices (fun parent => if layout.directed parent child then 1 else 0) +
    total sources (fun source => if layout.incident source child then 1 else 0) +
    layout.mechanismCells child

/-- A relabelling carries vertices and latent coordinates separately and
preserves their alphabet cardinalities and incidences. It can change the
enumeration of rows and the actual names of all values. -/
structure Layout.Relabel (left right : Layout vertices sources) where
  vertex : ValueEquivalence (Fin vertices) (Fin vertices)
  source : ValueEquivalence (Fin sources) (Fin sources)
  values : ∀ node, right.values (vertex.forward node) = left.values node
  latentValues : ∀ root, right.latentValues (source.forward root) = left.latentValues root
  directed : ∀ parent child, right.directed (vertex.forward parent) (vertex.forward child) =
    left.directed parent child
  incident : ∀ root child, right.incident (source.forward root) (vertex.forward child) =
    left.incident root child

private theorem total_relabel (rename : ValueEquivalence (Fin n) (Fin n))
    (left right : Fin n → Nat) (agrees : ∀ i, right (rename.forward i) = left i) :
    total n left = total n right := by
  calc
    _ = total n (right ∘ rename.forward) := congrArg (total n) (funext fun i => (agrees i).symm)
    _ = _ := nat_finSum_reindex n right rename.forward rename.backward
      rename.backward_forward rename.forward_backward

private theorem foldProduct_perm {left right : List Nat} (perm : left.Perm right) :
    left.foldr (· * ·) 1 = right.foldr (· * ·) 1 := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldr_cons, ih]
  | swap _ _ _ => simp only [List.foldr_cons, Nat.mul_left_comm]
  | trans _ _ ih ih' => exact ih.trans ih'

private theorem product_relabel (rename : ValueEquivalence (Fin n) (Fin n))
    (left right : Fin n → Nat) (agrees : ∀ i, right (rename.forward i) = left i) :
    product n left = product n right := by
  have permutation := (AdditiveCarrier.finRange_map_bijective_perm rename.forward rename.backward
    rename.backward_forward rename.forward_backward).map right
  rw [List.map_map] at permutation
  show ((List.finRange n).map left).foldr (· * ·) 1 = ((List.finRange n).map right).foldr (· * ·) 1
  rw [show left = right ∘ rename.forward from funext fun i => (agrees i).symm]
  exact foldProduct_perm permutation

theorem Layout.Relabel.cost_eq {left right : Layout vertices sources} (rename : left.Relabel right) :
    left.cost = right.cost := by
  unfold Layout.cost
  apply congrArg (fun subtotal => vertices + sources + subtotal)
  apply total_relabel rename.vertex
  intro child
  have edges := total_relabel rename.vertex
    (fun parent => if left.directed parent child then 1 else 0)
    (fun parent => if right.directed parent (rename.vertex.forward child) then 1 else 0)
    (fun parent => by simp only [rename.directed])
  have incidences := total_relabel rename.source
    (fun source => if left.incident source child then 1 else 0)
    (fun source => if right.incident source (rename.vertex.forward child) then 1 else 0)
    (fun source => by simp only [rename.incident])
  have parentRows := product_relabel rename.vertex
    (fun parent => if left.directed parent child then left.values parent else 1)
    (fun parent => if right.directed parent (rename.vertex.forward child) then right.values parent else 1)
    (fun parent => by simp only [rename.directed, rename.values])
  have latentRows := product_relabel rename.source
    (fun source => if left.incident source child then left.latentValues source else 1)
    (fun source => if right.incident source (rename.vertex.forward child) then right.latentValues source else 1)
    (fun source => by simp only [rename.incident, rename.latentValues])
  simp only [Layout.mechanismCells, ← edges, ← incidences, ← parentRows, ← latentRows]

/-- Canonicalize the numerator and denominator by their common divisor. -/
def reducedMass (mass : QProb) : Rat :=
  Rat.normalize mass.num mass.den (Nat.ne_of_gt mass.den_pos)

theorem reducedMass_eq {left right : QProb} (same : QProb.Equiv left right) :
    reducedMass left = reducedMass right := by
  apply (Rat.normalize_eq_iff (Nat.ne_of_gt left.den_pos) (Nat.ne_of_gt right.den_pos)).mpr
  change left.num * right.den = right.num * left.den at same
  simpa only [← Int.natCast_mul, Int.ofNat_inj] using same

private def digitCost (mass : Rat) : Nat :=
  (mass.num.natAbs.log2 + 1) + (mass.den.log2 + 1)

/-- One slot per declared label and the digits of the reduced fraction in
that slot. Zero uses one numerator digit and the denominator one. Reading
the singleton first merges repeated atoms and keeps declared zero cells. -/
def distributionCost (alphabet : FiniteWitness X) (law : Distro X) : Nat :=
  letI : DecidableEq X := alphabet.decidableEq
  alphabet.card + AdditiveCarrier.nat.listSum (alphabet.enumeration.map fun label =>
    digitCost (reducedMass (law.pmf label)))

theorem distributionCost_sameLaw (alphabet : FiniteWitness X) {left right : Distro X}
    (same : left.SameLaw right) : distributionCost alphabet left = distributionCost alphabet right := by
  letI : DecidableEq X := alphabet.decidableEq
  have entries : (fun label => digitCost (reducedMass (left.pmf label))) =
      (fun label => digitCost (reducedMass (right.pmf label))) := by
    funext label
    exact congrArg digitCost (reducedMass_eq (same (FiniteProbRecord.singletonEvent label)))
  unfold distributionCost
  rw [entries]

private theorem enumeration_nodup (alphabet : FiniteWitness X) : alphabet.enumeration.Nodup := by
  apply List.pairwise_map.mpr
  apply (finRange_nodup alphabet.card).imp
  intro left right different same
  apply different
  simpa only [alphabet.encode_decode] using congrArg alphabet.encode same

/-- Any bijection of the declared alphabet preserves the cost. Each
side may use its own order and equality decision for singleton events. -/
theorem distributionCost_relabel (source : FiniteWitness X) (target : FiniteWitness Y)
    (rename : ValueEquivalence X Y) (law : Distro X) :
    distributionCost source law = distributionCost target (law.map rename.forward) := by
  letI : DecidableEq X := source.decidableEq
  letI : DecidableEq Y := target.decidableEq
  have perm : (source.enumeration.map rename.forward).Perm target.enumeration := by
    apply AdditiveCarrier.perm_of_count_eq_constructive
    intro label
    have distinct : (source.enumeration.map rename.forward).Nodup := by
      apply List.pairwise_map.mpr
      apply (enumeration_nodup source).imp
      intro left right different same
      apply different
      simpa only [rename.backward_forward] using congrArg rename.backward same
    have member : label ∈ source.enumeration.map rename.forward :=
      List.mem_map.mpr ⟨rename.backward label, source.enumeration_complete _, rename.forward_backward _⟩
    rw [distinct.count, (enumeration_nodup target).count, if_pos member,
      if_pos (target.enumeration_complete label)]
  have card : source.card = target.card := by
    simpa only [FiniteWitness.enumeration, List.length_map, List.length_finRange] using perm.length_eq
  let targetEntry := fun label => digitCost (reducedMass ((law.map rename.forward).pmf label))
  have values : (fun label => digitCost (reducedMass (law.pmf label))) =
      targetEntry ∘ rename.forward := by
    funext label
    apply congrArg digitCost
    apply reducedMass_eq
    apply QProb.equiv_symm
    apply QProb.equiv_trans (law.map_pmf rename.forward (rename.forward label))
    apply law.record.probVal_congr
    intro other
    apply Bool.eq_iff_iff.mpr
    simp only [FiniteProbRecord.singletonEvent, decide_eq_true_eq]
    constructor
    · intro equal
      simpa only [rename.backward_forward] using congrArg rename.backward equal
    · exact congrArg rename.forward
  unfold distributionCost
  rw [card, values]
  apply congrArg (target.card + ·)
  apply AdditiveCarrier.nat.listSum_perm
  simpa only [List.map_map] using perm.map targetEntry

/-- Complexity reweights the declared law on classes. Only then are the
class masses split among the catalogue's encodings. Every class remains
represented, even if the budget assigns it zero probability. -/
def classComplexityCatalogue [DecidableEq Class] (item : Fin n → Hypothesis)
    (classPrior : Distro Class) (cost : Class → Nat) (budget : Nat)
    (positive : 0 < natIntegral classPrior.record.atoms (fun c => complexityWeight budget (cost c)))
    (classOf : Fin n → Class) (represented : ∀ label, ∃ i, classOf i = label) :
    Catalogue n Hypothesis :=
  catalogueOfClassPrior item
    (classPrior.reweightNat (fun c => complexityWeight budget (cost c)) positive) classOf represented

theorem classComplexityCatalogue_aggregate [DecidableEq Class] (item : Fin n → Hypothesis)
    (classPrior : Distro Class) (cost : Class → Nat) (budget : Nat)
    (positive : 0 < natIntegral classPrior.record.atoms (fun c => complexityWeight budget (cost c)))
    (classOf : Fin n → Class) (represented : ∀ label, ∃ i, classOf i = label) :
    (aggregateClasses (classComplexityCatalogue item classPrior cost budget positive classOf represented).prior
      classOf).SameLaw (classPrior.reweightNat (fun c => complexityWeight budget (cost c)) positive) :=
  splitClassPrior_aggregate _ classOf represented

end Thesis.Causality.ModelDescriptionCost
