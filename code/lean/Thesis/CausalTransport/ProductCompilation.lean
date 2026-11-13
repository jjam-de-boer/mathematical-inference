import Thesis.CausalTransport.KernelCompilation

namespace Thesis
namespace Causality

open Probability

/-!
# Inspectable regrouping of finite probability products

The current-kernel ID engine groups a product by c-component.  Its chain
compiler instead visits vertices in reverse topological order.  Components
can interleave in that order, so equality of the two displayed expressions
must be witnessed by probability algebra, not by `ProbabilityTerm` equality.

The two new derivation leaves are ordinary multiplication commutativity and
associativity.  Their partial-result laws are proved in `Semantics`, including
undefined factors, and their support transports below use those laws directly.
No do-calculus soundness, positivity, independence, or completeness interface
is assumed.  Every derived rearrangement retains its complete support tree.

Permutation evidence is a proposition, but a certificate is data.  The
permutation compiler therefore searches the supplied finite lists using their
explicit decidable index equality.  It never chooses a derivation from an
existence proposition.  Factors themselves need not have decidable equality:
distinct indices may denote equal terms, and repeated indices retain their
multiplicity.
-/

/-! ## Elementary multiplication certificates -/

/-- Exchange two action-free factors, preserving local partial support. -/
noncomputable def PublishedIdentificationCertificate.multiplyComm
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    (left right : ProbabilityTerm S)
    (leftFree : left.ActionFree) (rightFree : right.ActionFree) :
    PublishedIdentificationCertificate C correct (.multiply left right) where
  formula := .multiply right left
  actionFree := ⟨rightFree, leftFree⟩
  derivation := DoCalculusDerivation.multiplyComm
    (G := G) (separation := pathRuleSeparation G) left right
  supported := fun model _member reference sourceSupported => by
    let targetSupported := ProbabilityResult.Supported.transport
      (ProbabilityResult.multiply_comm (left.denote model reference)
        (right.denote model reference)) sourceSupported
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨sourceSupported, targetSupported, ()⟩

/-- Associate a left-nested product to the right.  No artificial unit
factor is inserted, and zero-valued supported factors remain admissible. -/
noncomputable def PublishedIdentificationCertificate.multiplyAssoc
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    (first second third : ProbabilityTerm S)
    (firstFree : first.ActionFree) (secondFree : second.ActionFree)
    (thirdFree : third.ActionFree) :
    PublishedIdentificationCertificate C correct
      (.multiply (.multiply first second) third) where
  formula := .multiply first (.multiply second third)
  actionFree := ⟨firstFree, secondFree, thirdFree⟩
  derivation := DoCalculusDerivation.multiplyAssoc
    (G := G) (separation := pathRuleSeparation G) first second third
  supported := fun model _member reference sourceSupported => by
    let targetSupported := ProbabilityResult.Supported.transport
      (ProbabilityResult.multiply_assoc (first.denote model reference)
        (second.denote model reference) (third.denote model reference)) sourceSupported
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨sourceSupported, targetSupported, ()⟩

/-- The reverse association retains the original algebra leaf beneath
`symm`; its intermediate support is transported by the proved partial law. -/
noncomputable def PublishedIdentificationCertificate.multiplyAssocReverse
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    (first second third : ProbabilityTerm S)
    (firstFree : first.ActionFree) (secondFree : second.ActionFree)
    (thirdFree : third.ActionFree) :
    PublishedIdentificationCertificate C correct
      (.multiply first (.multiply second third)) where
  formula := .multiply (.multiply first second) third
  actionFree := ⟨⟨firstFree, secondFree⟩, thirdFree⟩
  derivation := DoCalculusDerivation.symm
    (G := G) (separation := pathRuleSeparation G)
    (DoCalculusDerivation.multiplyAssoc
      (G := G) (separation := pathRuleSeparation G) first second third)
  supported := fun model _member reference sourceSupported => by
    let targetSupported := ProbabilityResult.Supported.transport
      (ProbabilityResult.symm
        (ProbabilityResult.multiply_assoc (first.denote model reference)
          (second.denote model reference) (third.denote model reference))) sourceSupported
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    exact ⟨sourceSupported, targetSupported,
      ⟨targetSupported, sourceSupported, ()⟩⟩

/-- Exchange adjacent leading factors in a right-nested product.  This
is derived from the two elementary leaves, not an additional assumed law. -/
noncomputable def PublishedIdentificationCertificate.multiplyLeftComm
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    (first second third : ProbabilityTerm S)
    (firstFree : first.ActionFree) (secondFree : second.ActionFree)
    (thirdFree : third.ActionFree) :
    PublishedIdentificationCertificate C correct
      (.multiply first (.multiply second third)) :=
  (PublishedIdentificationCertificate.multiplyAssocReverse
    first second third firstFree secondFree thirdFree).trans
    (((PublishedIdentificationCertificate.multiplyComm first second firstFree secondFree).multiply
      (PublishedIdentificationCertificate.refl third thirdFree)).trans
      (PublishedIdentificationCertificate.multiplyAssoc second first third
        secondFree firstFree thirdFree))

/-! ## Splitting and grouping nonempty finite blocks -/

/-- A finite product compilation with its target syntax recorded explicitly.
The equality is syntactic: all rearrangement work lives in the certificate's
inspectable derivation.  Returning this package lets a recursive fold carry
the exact target without unfolding a recursively constructed certificate. -/
structure PublishedProductCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (source target : ProbabilityTerm S) where
  certificate : PublishedIdentificationCertificate C correct source
  formula_eq : certificate.formula = target

/-- Make the package's target definitionally visible to the next fold step.
The reindexing equality does not add a probability-algebra assumption. -/
noncomputable def PublishedProductCompilation.alignedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {source target : ProbabilityTerm S}
    (compiled : PublishedProductCompilation C correct source target) :
    PublishedIdentificationCertificate C correct source :=
  compiled.certificate.reindex rfl compiled.formula_eq.symm

/-- Split the exact engine product at a nonempty block boundary.

Both blocks must be nonempty because the engine omits the multiplication
node for a singleton list.  Actual c-components satisfy this condition;
the empty outer family is handled separately by the grouping fold below.
No semantic normalization of an empty product is needed. -/
noncomputable def productTerms_appendPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    (left right : List (ProbabilityTerm S))
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (free : forall term, term ∈ left ++ right -> term.ActionFree) :
    PublishedProductCompilation C correct (productTerms (left ++ right))
      (.multiply (productTerms left) (productTerms right)) := by
  induction left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons head tail inductionHypothesis =>
      have headFree := free head (List.mem_append.mpr
        (Or.inl (List.mem_cons.mpr (Or.inl rfl))))
      have rightFree : (productTerms right).ActionFree := productTerms_actionFree right
        (fun term member => free term (List.mem_append.mpr (Or.inr member)))
      cases tail with
      | nil =>
          let certificate := (PublishedIdentificationCertificate.refl
            (C := C) (correct := correct)
            (.multiply head (productTerms right)) ⟨headFree, rightFree⟩).reindex
            (show productTerms ((head :: []) ++ right) =
                .multiply head (productTerms right) from
              productTerms_cons head right rightNonempty) rfl
          exact ⟨certificate, rfl⟩
      | cons next rest =>
          have tailFree : (productTerms (next :: rest)).ActionFree :=
            productTerms_actionFree _ (fun term member => free term
              (List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr member)))))
          let tailCompiled := inductionHypothesis (by intro impossible; cases impossible)
            (fun term member => free term (by
              rcases List.mem_append.mp member with before | after
              · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr before)))
              · exact List.mem_append.mpr (Or.inr after)))
          let tailCertificate := tailCompiled.alignedCertificate
          let combined := (PublishedIdentificationCertificate.refl head headFree).multiply
            tailCertificate
          let certificate := (combined.reindex
            (show productTerms ((head :: next :: rest) ++ right) =
                .multiply head (productTerms ((next :: rest) ++ right)) from rfl)
            rfl).trans
            (PublishedIdentificationCertificate.multiplyAssocReverse head
              (productTerms (next :: rest)) (productTerms right)
              headFree tailFree rightFree)
          exact ⟨certificate, rfl⟩

/-! ## Constructive permutation of indexed factors -/

/-- Erasure preserves a permutation without importing the library proof's
classical dependency.  This induction produces only a proposition; later
certificate construction still follows the concrete list data. -/
private theorem permutation_erase_constructive {X : Type} [DecidableEq X]
    (selected : X) {left right : List X} (permutation : left.Perm right) :
    (left.erase selected).Perm (right.erase selected) := by
  induction permutation with
  | nil => exact .nil
  | cons head permutation inductionHypothesis =>
      by_cases equal : head = selected
      · subst head
        simpa only [List.erase_cons_head] using permutation
      · have notEqual : ¬ (head == selected) = true := by
          simpa only [beq_iff_eq] using equal
        simpa only [List.erase_cons_tail notEqual] using
          List.Perm.cons head inductionHypothesis
  | swap first second tail =>
      by_cases firstEqual : first = selected
      · subst first
        by_cases secondEqual : second = selected
        · subst second
          simp only [List.erase_cons_head]
          exact List.Perm.refl _
        · have notEqual : ¬ (second == selected) = true := by
            simpa only [beq_iff_eq] using secondEqual
          simp only [List.erase_cons_head, List.erase_cons_tail notEqual]
          exact List.Perm.refl _
      · have firstNotEqual : ¬ (first == selected) = true := by
          simpa only [beq_iff_eq] using firstEqual
        by_cases secondEqual : second = selected
        · subst second
          simp only [List.erase_cons_head, List.erase_cons_tail firstNotEqual]
          exact List.Perm.refl _
        · have secondNotEqual : ¬ (second == selected) = true := by
            simpa only [beq_iff_eq] using secondEqual
          simp only [List.erase_cons_tail firstNotEqual,
            List.erase_cons_tail secondNotEqual]
          exact .swap _ _ _
  | trans first second firstIH secondIH => exact firstIH.trans secondIH

/-- A nonempty index list has a nonempty mapped factor list.  Constructor
inspection avoids a generic empty-list characterization with hidden axioms. -/
private theorem map_nonempty_constructive (values : List X) (term : X -> Y)
    (nonempty : values ≠ []) : values.map term ≠ [] := by
  cases values with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => intro impossible; cases impossible

/-- Move the first occurrence of an index to the front of the product.
The list search is explicit and terminating.  Erasing only that occurrence
is essential: permutations of repeated factors must preserve multiplicity. -/
private noncomputable def productTermsMapMoveFrontCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {X : Type} [DecidableEq X]
    (values : List X) (selected : X) (member : selected ∈ values)
    (term : X -> ProbabilityTerm S)
    (free : forall value, value ∈ values -> (term value).ActionFree) :
    PublishedProductCompilation C correct (productTerms (values.map term))
      (productTerms ((selected :: values.erase selected).map term)) := by
  induction values with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail inductionHypothesis =>
      have headFree := free head (List.mem_cons.mpr (Or.inl rfl))
      by_cases equal : head = selected
      · subst head
        exact ⟨PublishedIdentificationCertificate.refl _
          (productTerms_actionFree _ (by
            intro factor factorMember
            rcases List.mem_map.mp factorMember with ⟨value, valueMember, equality⟩
            subst factor
            exact free value valueMember)), by rw [List.erase_cons_head]; rfl⟩
      · have selectedLater : selected ∈ tail :=
          (List.mem_cons.mp member).resolve_left (Ne.symm equal)
        have tailNonempty : tail ≠ [] := by
          intro empty
          rw [empty] at selectedLater
          exact List.not_mem_nil selectedLater
        have selectedFree := free selected member
        have tailFree : forall value, value ∈ tail -> (term value).ActionFree :=
          fun value later => free value (List.mem_cons.mpr (Or.inr later))
        let moved := inductionHypothesis selectedLater tailFree
        let combined := (PublishedIdentificationCertificate.refl (term head) headFree).multiply
          moved.alignedCertificate
        let started := combined.reindex
          (show productTerms ((head :: tail).map term) =
              .multiply (term head) (productTerms (tail.map term)) by
            rw [List.map_cons, productTerms_cons _ _
              (map_nonempty_constructive tail term tailNonempty)]) rfl
        have notEqual : ¬ (head == selected) = true := by
          simpa only [beq_iff_eq] using equal
        cases erased : tail.erase selected with
        | nil =>
            let normalized := started.reindex rfl
              (show ProbabilityTerm.multiply (term head) (term selected) = started.formula by
                change ProbabilityTerm.multiply (term head) (term selected) =
                  ProbabilityTerm.multiply (term head)
                  (productTerms ((selected :: tail.erase selected).map term))
                rw [erased]; rfl)
            let certificate := normalized.trans
              (PublishedIdentificationCertificate.multiplyComm (term head) (term selected)
                headFree selectedFree)
            exact ⟨certificate, by rw [List.erase_cons_tail notEqual, erased]; rfl⟩
        | cons next rest =>
            have restFree : (productTerms ((next :: rest).map term)).ActionFree :=
              productTerms_actionFree _ (by
                intro factor factorMember
                rcases List.mem_map.mp factorMember with ⟨value, valueMember, equality⟩
                subst factor
                apply tailFree value
                apply List.mem_of_mem_erase (b := selected)
                rw [erased]
                exact valueMember)
            let normalized := started.reindex rfl
              (show ProbabilityTerm.multiply (term head)
                  (.multiply (term selected) (productTerms ((next :: rest).map term))) =
                  started.formula by
                change ProbabilityTerm.multiply (term head)
                    (.multiply (term selected) (productTerms ((next :: rest).map term))) =
                  ProbabilityTerm.multiply (term head)
                  (productTerms ((selected :: tail.erase selected).map term))
                rw [erased]; rfl)
            let certificate := normalized.trans
              (PublishedIdentificationCertificate.multiplyLeftComm (term head) (term selected)
                (productTerms ((next :: rest).map term)) headFree selectedFree restFree)
            exact ⟨certificate, by rw [List.erase_cons_tail notEqual, erased]; rfl⟩

/-- Compile any permutation of an indexed finite factor list.

There are no ordering or nonemptiness restrictions: the empty product stays
the explicit unit, a singleton stays its sole factor, and duplicate indices
are handled one occurrence at a time.  Equality is tested only on indices,
so probability terms with functional node-set fields need no equality oracle.
The proposition `permutation` validates the finite search; it is never
eliminated into certificate data. -/
noncomputable def productTermsMapPermutationCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {X : Type} [DecidableEq X]
    (source target : List X) (permutation : source.Perm target)
    (term : X -> ProbabilityTerm S)
    (free : forall value, value ∈ source -> (term value).ActionFree) :
    PublishedProductCompilation C correct (productTerms (source.map term))
      (productTerms (target.map term)) := by
  induction target generalizing source with
  | nil =>
      have empty : source = [] := by
        have length := permutation.length_eq
        cases source with
        | nil => rfl
        | cons head tail => simp only [List.length_cons, List.length_nil] at length; omega
      subst source
      exact ⟨PublishedIdentificationCertificate.refl _ (unitProbabilityTerm_actionFree S), rfl⟩
  | cons head tail inductionHypothesis =>
      have member : head ∈ source := permutation.mem_iff.mpr
        (List.mem_cons.mpr (Or.inl rfl))
      have headFree := free head member
      let moved := productTermsMapMoveFrontCompilation (C := C) (correct := correct)
        source head member term free
      have tailPermutation : (source.erase head).Perm tail := by
        simpa only [List.erase_cons_head] using
          permutation_erase_constructive head permutation
      cases tail with
      | nil =>
          have erasedEmpty : source.erase head = [] := by
            have length := tailPermutation.length_eq
            cases erased : source.erase head with
            | nil => rfl
            | cons next rest => rw [erased] at length; simp only [List.length_cons,
                List.length_nil] at length; omega
          exact ⟨moved.certificate, by rw [moved.formula_eq, erasedEmpty]⟩
      | cons next rest =>
          have erasedNonempty : source.erase head ≠ [] := by
            intro empty
            have length := tailPermutation.length_eq
            rw [empty] at length
            simp only [List.length_nil, List.length_cons] at length
            omega
          let tailCompiled := inductionHypothesis (source.erase head) tailPermutation
            (fun value later => free value (List.mem_of_mem_erase later))
          let tailCertificate := tailCompiled.alignedCertificate
          let normalized := moved.certificate.reindex rfl
            (show ProbabilityTerm.multiply (term head)
                (productTerms ((source.erase head).map term)) = moved.certificate.formula by
              rw [moved.formula_eq, List.map_cons, productTerms_cons _ _
                (map_nonempty_constructive _ term erasedNonempty)])
          let certificate := normalized.trans
            ((PublishedIdentificationCertificate.refl (term head) headFree).multiply tailCertificate)
          exact ⟨certificate, rfl⟩

/-! ## Regrouping a partition and compiling its factors -/

/-- Group a flattened finite family of nonempty factor blocks.

The outer family may be empty.  Each nonempty block is kept in its original
order; only parentheses change in this fold.  The preceding permutation
compiler handles the genuinely different vertex/component orders. -/
noncomputable def productTermsGroupingCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    (blocks : List (List (ProbabilityTerm S)))
    (nonempty : forall block, block ∈ blocks -> block ≠ [])
    (free : forall term, term ∈ blocks.flatten -> term.ActionFree) :
    PublishedProductCompilation C correct (productTerms blocks.flatten)
      (productTerms (blocks.map productTerms)) := by
  induction blocks with
  | nil =>
      exact ⟨PublishedIdentificationCertificate.refl _ (unitProbabilityTerm_actionFree S), rfl⟩
  | cons block rest inductionHypothesis =>
      have blockNonempty := nonempty block (List.mem_cons.mpr (Or.inl rfl))
      have blockFree : (productTerms block).ActionFree := productTerms_actionFree block
        (fun term member => free term (List.mem_append.mpr (Or.inl member)))
      cases rest with
      | nil =>
          let certificate := (PublishedIdentificationCertificate.refl
            (C := C) (correct := correct) (productTerms block) blockFree).reindex
            (show productTerms ([block].flatten) = productTerms block by
              simp only [List.flatten_cons, List.flatten_nil, List.append_nil]) rfl
          exact ⟨certificate, rfl⟩
      | cons next rest =>
          have nextNonempty := nonempty next (List.mem_cons.mpr
            (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
          have restNonempty : (next :: rest).flatten ≠ [] := by
            cases next with
            | nil => exact False.elim (nextNonempty rfl)
            | cons head tail => intro impossible; cases impossible
          let restCompiled := inductionHypothesis
            (fun value member => nonempty value (List.mem_cons.mpr (Or.inr member)))
            (fun term member => free term (List.mem_append.mpr (Or.inr member)))
          let split := productTerms_appendPublishedCertificate (C := C) (correct := correct)
            block (next :: rest).flatten blockNonempty restNonempty free
          let product := (PublishedIdentificationCertificate.refl (productTerms block) blockFree).multiply
            restCompiled.alignedCertificate
          let certificate := split.alignedCertificate.trans product
          exact ⟨certificate, rfl⟩

/-- Mapping indices commutes syntactically with flattening their blocks.
This is list syntax only, not a rearrangement of probability expressions. -/
private theorem map_flatten_constructive (blocks : List (List X)) (term : X -> Y) :
    (blocks.map (fun block => block.map term)).flatten = blocks.flatten.map term := by
  induction blocks with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      simp only [List.map_cons, List.flatten_cons, List.map_append, inductionHypothesis]

/-- Regroup an arbitrary indexed product into a finite partition.

The supplied permutation records exactly the factors and their multiplicity.
It does not require consecutive blocks or a component-compatible topological
order.  Empty outer families are admitted; individual blocks are nonempty,
as are all components returned by the graph's partition algorithm. -/
noncomputable def productTermsRegroupingCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {X : Type} [DecidableEq X]
    (source : List X) (blocks : List (List X))
    (permutation : source.Perm blocks.flatten)
    (nonempty : forall block, block ∈ blocks -> block ≠ [])
    (term : X -> ProbabilityTerm S)
    (free : forall value, value ∈ source -> (term value).ActionFree) :
    PublishedProductCompilation C correct (productTerms (source.map term))
      (productTerms (blocks.map (fun block => productTerms (block.map term)))) := by
  let reordered := productTermsMapPermutationCompilation (C := C) (correct := correct)
    source blocks.flatten permutation term free
  have flatFree : forall factor,
      factor ∈ (blocks.map (fun block => block.map term)).flatten -> factor.ActionFree := by
    intro factor member
    rw [map_flatten_constructive] at member
    rcases List.mem_map.mp member with ⟨value, valueMember, equality⟩
    subst factor
    exact free value (permutation.mem_iff.mpr valueMember)
  let grouped := productTermsGroupingCompilation (C := C) (correct := correct)
    (blocks.map (fun block => block.map term))
    (by
      intro block member
      rcases List.mem_map.mp member with ⟨indices, indexMember, equality⟩
      subst block
      exact map_nonempty_constructive indices term (nonempty indices indexMember)) flatFree
  let aligned := grouped.alignedCertificate.reindex
    (show productTerms (blocks.flatten.map term) =
        productTerms ((blocks.map (fun block => block.map term)).flatten) by
      rw [map_flatten_constructive])
    (show productTerms (blocks.map (fun block => productTerms (block.map term))) =
        grouped.alignedCertificate.formula by
      change _ = productTerms ((blocks.map (fun block => block.map term)).map productTerms)
      rw [List.map_map]; rfl)
  exact ⟨reordered.alignedCertificate.trans aligned, rfl⟩

/-- Substitute a family of certified reductions into an engine product.

The target function is supplied explicitly, and each certificate is aligned
with it on the actual finite index list.  Proofs of list membership validate
the supplied reductions but are not searched to choose certificates.  This
fold is the bridge from regrouped chain factors to recursively identified
whole-component expressions. -/
noncomputable def productTermsMapPublishedCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    (values : List X) (source target : X -> ProbabilityTerm S)
    (factors : forall value, value ∈ values ->
      PublishedIdentificationCertificate C correct (source value))
    (aligned : forall value member, (factors value member).formula = target value) :
    PublishedProductCompilation C correct (productTerms (values.map source))
      (productTerms (values.map target)) := by
  induction values with
  | nil =>
      exact ⟨PublishedIdentificationCertificate.refl _ (unitProbabilityTerm_actionFree S), rfl⟩
  | cons head tail inductionHypothesis =>
      let factor := factors head (List.mem_cons.mpr (Or.inl rfl))
      cases tail with
      | nil => exact ⟨factor, aligned head _⟩
      | cons next rest =>
          let tailCompiled := inductionHypothesis
            (fun value member => factors value (List.mem_cons.mpr (Or.inr member)))
            (fun value member => aligned value (List.mem_cons.mpr (Or.inr member)))
          let alignedFactor := factor.reindex rfl (aligned head _).symm
          exact ⟨alignedFactor.multiply tailCompiled.alignedCertificate, rfl⟩

end Causality
end Thesis
