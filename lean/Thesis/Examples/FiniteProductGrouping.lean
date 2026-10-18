import Thesis.Probability.FiniteProductGrouping

namespace Thesis.Probability.Examples.FiniteProductGrouping

/-!
# Joint-law checks for merged, empty and separate source groups

Sources zero and one share a block but remain separate independent coordinates
inside it. Source two occupies another block; the middle block is empty. The
old factors have unequal denominators, a zero-weight occurrence and repeated
labels. Agreement of every decoded event tests the complete law, not merely
the source marginals. A separate empty-family case exercises both zero counts
without selecting a source, group or value by a nonemptiness argument.
-/

def first : FiniteProbRecord Bool := ⟨[(false, 0), (true, 1), (true, 1), (false, 2)], 4, by decide, rfl⟩
def second : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩
def third : FiniteProbRecord Bool := ⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩

def factors (source : Fin 3) : FiniteProbRecord Bool :=
  if source.val = 0 then first else if source.val = 1 then second else third

def owner (source : Fin 3) : Fin 3 := if source.val < 2 then 0 else 2

def original := FiniteProduct.record 3 (fun _ => Bool) factors
def grouped := Thesis.Probability.FiniteProductGrouping.prior owner factors

theorem every_joint_event (event : Event (FiniteProduct.Assignment 3 (fun _ => Bool))) :
    QProb.Equiv (grouped.probVal (fun blocks => event (Thesis.Probability.FiniteProductGrouping.decode owner blocks)))
      (original.probVal event) :=
  Thesis.Probability.FiniteProductGrouping.decoded_probVal owner factors original
    (FiniteProduct.record_rectangular_probVal 3 _ factors)
    (fun _ => [false, true]) (fun _ value => by cases value <;> simp) (fun _ => inferInstance) event

theorem two_sources_one_owner : owner 0 = owner 1 := rfl

theorem empty_block_one_atom :
    (Thesis.Probability.FiniteProductGrouping.factor owner factors 1).atoms.length = 1 := by decide +kernel

/-- Merging the owners does not identify their random values: the joint
true event still has mass `(1/2) * (1/3) = 1/6`, not either marginal. -/
theorem merged_joint_mass :
    QProb.Equiv (grouped.probVal (fun blocks =>
      let sample := Thesis.Probability.FiniteProductGrouping.decode owner blocks
      sample 0 && sample 1)) ⟨1, 6, by decide⟩ :=
  QProb.equiv_trans (every_joint_event (fun sample => sample 0 && sample 1)) (by decide +kernel)

theorem all_typed_blocks_recovered (blocks : Thesis.Probability.FiniteProductGrouping.GroupedAssignment (fun _ : Fin 3 => Bool) owner) :
    Thesis.Probability.FiniteProductGrouping.encode owner
      (Thesis.Probability.FiniteProductGrouping.decode owner blocks) = blocks :=
  Thesis.Probability.FiniteProductGrouping.encode_decode owner blocks

def noOwner (source : Fin 0) : Fin 0 := Fin.elim0 source
def noFactors (source : Fin 0) : FiniteProbRecord Bool := Fin.elim0 source

theorem empty_family (event : Event (FiniteProduct.Assignment 0 (fun _ => Bool))) :
    QProb.Equiv ((Thesis.Probability.FiniteProductGrouping.prior noOwner noFactors).probVal
      (fun blocks => event (Thesis.Probability.FiniteProductGrouping.decode noOwner blocks)))
      ((FiniteProduct.record 0 (fun _ => Bool) noFactors).probVal event) :=
  Thesis.Probability.FiniteProductGrouping.decoded_probVal noOwner noFactors _
    (FiniteProduct.record_rectangular_probVal 0 _ noFactors)
    (fun _ => [false, true]) (fun _ value => by cases value <;> simp) (fun _ => inferInstance) event

end Thesis.Probability.Examples.FiniteProductGrouping
