import Thesis.Probability.FiniteProductReplacement
import Thesis.Probability.FiniteSourceCompression

namespace Thesis
namespace Probability
namespace FiniteProductSourceCompression

open FiniteProduct

universe u
variable {n count : Nat} {Value : Fin n → Type u}

/-!
# Compress every source of an independent finite law

For one chosen coordinate, pull the requested events back through explicit
coordinate replacement.  The previous one-source compressor integrates the
unchanged background and constructs a bounded replacement factor.  Finite
whole-law extensionality proves that reinserting the original factor gives
the original prior, so the new prior preserves the actual requested events.

The coordinate types stay fixed.  Each step rebuilds the canonical product
of the updated factors, avoiding repeated unused copies of overwritten
coordinates in later priors.  This is a presentation change, with arbitrary
event equivalence proved rather than assumed.

Iteration follows a supplied finite coordinate list.  An unvisited factor
remains literally unchanged; visited bounds and positivity survive later
steps, including repeated visits.  Compressing `finRange n` therefore bounds
every independent source by `count + 1` positive atom occurrences while
preserving every supplied joint-event probability.  The recursion is on list
length, never on a probability denominator or total number of unit weights.
-/

structure CompressedAt (original : IndependentLaw Value) (chosen : Fin n)
    (events : Fin count → Event (Assignment n Value)) where
  law : IndependentLaw Value
  bound : (law.factor chosen).atoms.length ≤ count + 1
  positive : forall atom, atom ∈ (law.factor chosen).atoms → 0 < atom.2
  unchanged : forall index, index ≠ chosen → law.factor index = original.factor index
  preserved : forall index, QProb.Equiv (law.prior.probVal (events index)) (original.prior.probVal (events index))

def compressAt (original : IndependentLaw Value)
    (values : (index : Fin n) → List (Value index)) (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index)) (chosen : Fin n)
    (events : Fin count → Event (Assignment n Value)) : CompressedAt original chosen events := by
  let pulled : Fin count → Event (Value chosen × Assignment n Value) :=
    fun index pair => events index (replaceCoordinate chosen pair.1 pair.2)
  let made := FiniteSourceCompression.compress (original.factor chosen) original.prior pulled
  let raw := original.replace chosen made.factor
  refine ⟨raw.canonical, ?_, ?_, ?_, ?_⟩
  · change (replaceFactor original.factor chosen made.factor chosen).atoms.length ≤ count + 1
    rw [replaceFactor_chosen]
    exact made.bound
  · intro atom member
    change atom ∈ (replaceFactor original.factor chosen made.factor chosen).atoms at member
    rw [replaceFactor_chosen] at member
    exact made.positive atom member
  · intro index different
    exact replaceFactor_other original.factor chosen made.factor index different
  · intro index
    have newMap := (made.factor.product original.prior).map_probVal
      (fun pair => replaceCoordinate chosen pair.1 pair.2) (events index)
    have oldMap := ((original.factor chosen).product original.prior).map_probVal
      (fun pair => replaceCoordinate chosen pair.1 pair.2) (events index)
    exact QProb.equiv_trans (canonical_probVal raw values complete decEq (events index))
      (QProb.equiv_trans newMap (QProb.equiv_trans (made.preserved index)
        (QProb.equiv_trans (QProb.equiv_symm oldMap)
          (replace_original_probVal original values complete decEq chosen (events index)))))

structure CompressedOn (original : IndependentLaw Value) (coordinates : List (Fin n))
    (events : Fin count → Event (Assignment n Value)) where
  law : IndependentLaw Value
  bounded : forall index, index ∈ coordinates → (law.factor index).atoms.length ≤ count + 1
  positive : forall index, index ∈ coordinates → forall atom, atom ∈ (law.factor index).atoms → 0 < atom.2
  unchanged : forall index, index ∉ coordinates → law.factor index = original.factor index
  preserved : forall index, QProb.Equiv (law.prior.probVal (events index)) (original.prior.probVal (events index))

/-- Every recursive output retains proofs about the entire processed list,
not just its last coordinate.  Later updates cannot invalidate an earlier
bound: they either revisit that coordinate and re-establish it, or leave its
factor literally unchanged. -/
def compressOn (original : IndependentLaw Value)
    (values : (index : Fin n) → List (Value index)) (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index))
    (coordinates : List (Fin n)) (events : Fin count → Event (Assignment n Value)) : CompressedOn original coordinates events :=
  match coordinates with
  | [] => by
      refine ⟨original, ?_, ?_, ?_, fun _ => QProb.equiv_refl _⟩
      · intro _ member
        cases member
      · intro _ member
        cases member
      · intro _ _
        rfl
  | chosen :: rest => by
      let made := compressAt original values complete decEq chosen events
      let solved := compressOn made.law values complete decEq rest events
      refine ⟨solved.law, ?_, ?_, ?_, ?_⟩
      · intro index listed
        rcases List.mem_cons.mp listed with atHead | inTail
        · subst index
          by_cases repeated : chosen ∈ rest
          · exact solved.bounded chosen repeated
          · rw [solved.unchanged chosen repeated]
            exact made.bound
        · exact solved.bounded index inTail
      · intro index listed atom member
        rcases List.mem_cons.mp listed with atHead | inTail
        · subst index
          by_cases repeated : chosen ∈ rest
          · exact solved.positive chosen repeated atom member
          · rw [solved.unchanged chosen repeated] at member
            exact made.positive atom member
        · exact solved.positive index inTail atom member
      · intro index absent
        have outside : index ∉ rest := fun member => absent (List.mem_cons.mpr (Or.inr member))
        have different : index ≠ chosen := fun same => absent (List.mem_cons.mpr (Or.inl same))
        exact (solved.unchanged index outside).trans (made.unchanged index different)
      · intro index
        exact QProb.equiv_trans (solved.preserved index) (made.preserved index)
termination_by coordinates.length
decreasing_by simp only [List.length_cons]; omega

structure Compressed (original : IndependentLaw Value) (events : Fin count → Event (Assignment n Value)) where
  law : IndependentLaw Value
  bounded : forall index, (law.factor index).atoms.length ≤ count + 1
  positive : forall index atom, atom ∈ (law.factor index).atoms → 0 < atom.2
  preserved : forall index, QProb.Equiv (law.prior.probVal (events index)) (original.prior.probVal (events index))

def compress (original : IndependentLaw Value)
    (values : (index : Fin n) → List (Value index)) (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index))
    (events : Fin count → Event (Assignment n Value)) : Compressed original events :=
  let solved := compressOn original values complete decEq (List.finRange n) events
  ⟨solved.law, fun index => solved.bounded index (List.mem_finRange index),
    fun index => solved.positive index (List.mem_finRange index), solved.preserved⟩

end FiniteProductSourceCompression
end Probability
end Thesis
