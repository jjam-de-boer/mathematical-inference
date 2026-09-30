import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

/-!
# Current-kernel formulation of recursive ID

This is the replacement engine used for the continuing completeness proof.
Its recursion follows Figure 3 of Shpitser--Pearl's joint-identification
paper (2006, UCLA technical report R-327).  It addresses the two semantic
defects isolated by the positive front-door regression:

* ordinary ancestral pruning uses the *uncut* induced host graph;
* a chain factor is extracted from the current input expression, including
  after a previous c-component restriction, rather than fetched afresh from
  the original observational distribution.

The incoming-cut ancestor test has its own role: it supplies the additional
action block `W` in line 3.  That block is added to the action while the host
and its current distribution are retained; it is not used to marginalize
the input distribution.

The old `identifyFuel` and its exact trace library remain available while
the structural compiler is migrated.  Their front-door counterexample is
retained as a baseline, not accepted as a sound implementation.  The new
engine is general over hosts and input terms, not a front-door shortcut.
The definitions here assert neither global semantic correctness nor an
inhabitant of `PublishedCompleteness`; those require support-carrying
compilation of every recursive branch and the general hedge countermodel.
-/

/-! ## Chain factors of the current input kernel -/

/-- The factor of `node` in the current host kernel.  Numerator and
denominator marginalize *the same current expression* onto the prefix with
and without `node`.  External coordinates of a previously identified
c-component kernel remain fixed parameters, not new random host vertices.

Even the first selected vertex has an explicit denominator: the total host
mass of `current`.  For a normalized input kernel this is one, but retaining
the quotient avoids an unproved syntactic normalization or cancellation. -/
def chainFactorFrom (remaining : NodeSet S) (current : ProbabilityTerm S)
    (node : Fin S.count) : ProbabilityTerm S :=
  let earlier := chainCondition remaining node
  .divide
    (.marginalize
      (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node) earlier))
      current)
    (.marginalize (NodeSet.diff remaining earlier) current)

/-- Tian's component factor, computed from the current recursive input.
Later vertices appear first, consistently with `chainProduct`, the primitive
chain derivation, and the exact-output certificate convention. -/
def chainProductFrom (remaining : NodeSet S) (current : ProbabilityTerm S)
    (component : NodeSet S) : ProbabilityTerm S :=
  productTerms ((NodeSet.members component).reverse.map
    (fun node => chainFactorFrom remaining current node))

/-- Prefix quotients introduce no actions when their input is action-free. -/
theorem chainFactorFrom_actionFree (remaining : NodeSet S)
    (current : ProbabilityTerm S) (node : Fin S.count)
    (inputFree : current.ActionFree) :
    (chainFactorFrom remaining current node).ActionFree :=
  ⟨inputFree, inputFree⟩

/-- Every component product preserves the action-free input invariant. -/
theorem chainProductFrom_actionFree (remaining : NodeSet S)
    (current : ProbabilityTerm S) (component : NodeSet S)
    (inputFree : current.ActionFree) :
    (chainProductFrom remaining current component).ActionFree :=
  productTerms_actionFree _ (fun factor member => by
    rcases List.mem_map.mp member with ⟨node, _, rfl⟩
    exact chainFactorFrom_actionFree remaining current node inputFree)

/-! ## Separate ancestral pruning and action augmentation -/

/-- Vertices outside the action that are not ancestors of the outcome in
the incoming-cut host graph.  The published ID algorithm adds this entire
block to the action before splitting the free host into c-components. -/
def identificationAdditionalAction (G : ObservedGraph S)
    (remaining outcome action : NodeSet S) : NodeSet S :=
  let localAction := NodeSet.inter action remaining
  let localOutcome := NodeSet.inter outcome remaining
  NodeSet.diff (NodeSet.diff remaining localAction)
    (G.ancestralSet remaining (GraphMutilation.bar localAction) localOutcome)

/-- The additional action never leaves the current host. -/
theorem identificationAdditionalAction_subset_remaining (G : ObservedGraph S)
    (remaining outcome action : NodeSet S) :
    NodeSet.Subset (identificationAdditionalAction G remaining outcome action)
      remaining := by
  intro node selected
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp selected).1).1

/-- The additional block contains no already selected local action vertex. -/
theorem identificationAdditionalAction_disjoint_action (G : ObservedGraph S)
    (remaining outcome action : NodeSet S) :
    NodeSet.Disjoint
      (identificationAdditionalAction G remaining outcome action)
      (NodeSet.inter action remaining) := by
  intro node selected
  have free := (Bool.and_eq_true_iff.mp selected).1
  have notSelected := (Bool.and_eq_true_iff.mp free).2
  cases localSelected : NodeSet.inter action remaining node with
  | false => rfl
  | true =>
      rw [localSelected] at notSelected
      cases notSelected

/-- The additional action also misses the local outcome.  Every outcome
vertex is an ancestor of itself even after incoming arrows are cut, whereas
the extra-action definition explicitly excludes that entire ancestral set. -/
theorem identificationAdditionalAction_disjoint_outcome (G : ObservedGraph S)
    (remaining outcome action : NodeSet S) :
    NodeSet.Disjoint (identificationAdditionalAction G remaining outcome action)
      (NodeSet.inter outcome remaining) := by
  intro node selected
  cases outcomeSelected : NodeSet.inter outcome remaining node with
  | false => rfl
  | true =>
      have nodeRemaining := (Bool.and_eq_true_iff.mp outcomeSelected).2
      have ancestor := ancestralSet_contains_targets G remaining
        (GraphMutilation.bar (NodeSet.inter action remaining))
        (NodeSet.inter outcome remaining) nodeRemaining outcomeSelected
      have excluded := (Bool.and_eq_true_iff.mp selected).2
      rw [ancestor] at excluded
      cases excluded

/-! ## The corrected fuel-bounded recursion -/

/-- One generic current-kernel ID invocation.

The branch order is significant.  First prune ordinary non-ancestors,
then add the incoming-cut non-ancestor block to the action, then split
c-components.  Both maximal-component extraction and restriction to a
containing component use `chainProductFrom ... current ...`.

`unfinished` retains the existing explicit sentinel for insufficient fuel
or a missing containing component.  Removing it from public calls requires
the new recursion's rank and branch-exhaustiveness proofs; totality of the
old engine is not silently reused for a changed program. -/
def identifyKernelFuel (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S) : IdentificationOutcome S :=
  match fuel with
  | 0 => .unfinished
  | fuel + 1 =>
      let identifyNext := identifyKernelFuel fuel
      let y := NodeSet.inter outcome remaining
      let x := NodeSet.inter action remaining
      if NodeSet.isEmpty x then
        .identified (.marginalize (NodeSet.diff remaining y) current)
      else
        let kept := G.ancestralSet remaining (GraphMutilation.none S) y
        if NodeSet.equal kept remaining then
          let additional := identificationAdditionalAction G remaining outcome action
          if NodeSet.isEmpty additional then
            let free := NodeSet.diff remaining x
            match G.cComponents free with
            | [] =>
                .identified (.marginalize remaining current)
            | [component] =>
                if G.isSingleCComponent remaining then
                  .failed ⟨remaining, component⟩
                else if (G.cComponents remaining).any
                    (fun piece => NodeSet.equal piece component) then
                  .identified (.marginalize (NodeSet.diff component y)
                    (chainProductFrom remaining current component))
                else
                  match G.containingCComponent remaining component with
                  | some larger =>
                      identifyNext G larger outcome (NodeSet.inter x larger)
                        (chainProductFrom remaining current larger)
                  | none => .unfinished
            | _ :: _ :: _ =>
                IdentificationOutcome.combine
                  ((G.cComponents free).map (fun component =>
                    identifyNext G remaining component
                      (NodeSet.diff remaining component) current))
                  (fun terms => .marginalize
                    (NodeSet.diff remaining (NodeSet.union y x))
                    (productTerms terms))
          else
            identifyNext G remaining outcome (NodeSet.union x additional) current
        else
          identifyNext G kept outcome (NodeSet.inter x kept)
            (.marginalize (NodeSet.diff remaining kept) current)

/-- A quadratic allowance for the current-kernel recursion.  Its proof
counts strict host decreases, strict free-set decreases during action
augmentation, and the single product split at each such pair of sets.
The extra two units cover the terminal invocation and the empty signature. -/
def kernelIdentificationFuel (S : ObservedSignature) : Nat :=
  2 * S.count * (S.count + 2) + 2

/-- Current-kernel joint ID on the full observed graph.  This is the
replacement entry point for the completeness development; its result is
still a candidate formula until the corresponding supported derivation is
compiled. -/
def identifyJointKernel (G : ObservedGraph S) (q : JointKernelQuery S) :
    IdentificationOutcome S :=
  identifyKernelFuel (kernelIdentificationFuel S) G NodeSet.full q.outcome q.action
    (observationalJointTerm S)

/-! ## Invariants of candidate output syntax -/

/-- All successful replacement-engine formulas remain action-free when the
input is action-free.  This is the syntactic certificate invariant, not a
claim of denotational correctness or of support for the new quotients. -/
theorem identifyKernelFuel_identified_actionFree
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S) (current : ProbabilityTerm S)
    (inputFree : current.ActionFree) {term : ProbabilityTerm S}
    (result : identifyKernelFuel fuel G remaining outcome action current =
      .identified term) : term.ActionFree := by
  induction fuel generalizing remaining outcome action current term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      simp only [identifyKernelFuel] at result
      split at result
      · cases result
        exact inputFree
      · split at result
        · split at result
          · split at result
            · cases result
              exact inputFree
            · split at result
              · cases result
              · split at result
                · cases result
                  exact chainProductFrom_actionFree _ _ _ inputFree
                · split at result
                  · exact inductionHypothesis _ _ _ _
                      (chainProductFrom_actionFree _ _ _ inputFree) result
                  · cases result
            · apply IdentificationOutcome.combine_identified_actionFree
                _ (fun terms => .marginalize
                  (NodeSet.diff remaining
                    (NodeSet.union (NodeSet.inter outcome remaining)
                      (NodeSet.inter action remaining))) (productTerms terms))
                (fun terms free => productTerms_actionFree terms free)
                _ result
              intro factor member
              rcases List.mem_map.mp member with ⟨piece, _, pieceResult⟩
              exact inductionHypothesis _ _ _ _ inputFree pieceResult
          · exact inductionHypothesis _ _ _ _ inputFree result
        · exact inductionHypothesis _ _ _ (.marginalize _ current) inputFree result

/-- Public current-kernel joint ID starts from the action-free observational
joint, so the preceding invariant applies to every identified result. -/
theorem identifyJointKernel_identified_actionFree (G : ObservedGraph S)
    (q : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel G q = .identified term) : term.ActionFree :=
  identifyKernelFuel_identified_actionFree _ _ _ _ _ _
    (observationalJointTerm_actionFree S) result

end Causality
end Thesis
