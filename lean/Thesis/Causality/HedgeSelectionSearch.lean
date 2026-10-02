import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

/-!
# Finite hedge selection with an additional checked requirement

The ordinary extractor stops at its first valid hedge.  A countermodel
construction may need a further geometric property, however, and testing
only that first hedge would miss later valid choices of vertices or kept
edges.  This module puts the additional Boolean requirement *inside* the
search.  A rejected candidate does not prevent the scan from continuing.

Both forest vertex sets and every kept child are searched.  The large set
may be any subset of the supplied host; the small set may be any child-closed
subset of `large \ action`.  In particular it need not contain all outcome
ancestors, and the child map need not be the map of an earlier witness.

The two continuation-based scans below reuse `ExtendsAcc`, `ChildExtends`,
and the finite option lists of `IdentificationSearch`.  They visit candidates
without materialising powersets or families of functions.  Their completeness
lemmas follow a *supplied* candidate through the scan, not a choice of data
from an existential proposition.  The public result is complete for every
contained selection that passes both the hedge tests and the additional
requirement.  This is search completeness, not a theorem that such a
selection exists for every abstract hedge.
-/

variable {S : ObservedSignature}

/-! ## Finite scans with a continuation at each completed assignment -/

/-- Include a pending vertex first, then skip it if the complete continuation
returns `none`.  Unlike `findSubset`, the continuation may itself perform a
further finite search and return data of an arbitrary type. -/
def findSubsetMap {α : Type _} (pending : List (Fin S.count))
    (acc : NodeSet S) (finish : NodeSet S -> Option α) : Option α :=
  match pending with
  | [] => finish acc
  | node :: rest =>
      match findSubsetMap rest (NodeSet.insert acc node) finish with
      | some found => some found
      | none => findSubsetMap rest acc finish

/-- Every returned value came from a completed vertex assignment. -/
theorem findSubsetMap_eq_some {α : Type _}
    (pending : List (Fin S.count)) (acc : NodeSet S)
    (finish : NodeSet S -> Option α) {value : α}
    (result : findSubsetMap pending acc finish = some value) :
    Exists fun nodes => finish nodes = some value := by
  induction pending generalizing acc with
  | nil => exact ⟨acc, result⟩
  | cons node rest ih =>
      cases included : findSubsetMap rest (NodeSet.insert acc node) finish with
      | some found =>
          have same : found = value := by
            simpa [findSubsetMap, included] using result
          subst found
          exact ih (NodeSet.insert acc node) included
      | none =>
          apply ih acc
          simpa [findSubsetMap, included] using result

/-- A supplied contained assignment with a successful continuation guarantees
some search result.  An earlier successful assignment may be returned instead;
no equality with the supplied candidate is asserted. -/
theorem findSubsetMap_eq_some_of_extends {α : Type _}
    (pending : List (Fin S.count)) (acc target : NodeSet S)
    (finish : NodeSet S -> Option α) {value : α}
    (extension : ExtendsAcc pending acc target)
    (accepted : finish target = some value) :
    Exists fun found => findSubsetMap pending acc finish = some found := by
  induction pending generalizing acc with
  | nil =>
      exact ⟨value, by simpa [findSubsetMap, extendsAcc_nil extension] using accepted⟩
  | cons node rest ih =>
      cases selected : target node with
      | true =>
          rcases ih (NodeSet.insert acc node)
            (extendsAcc_cons_insert extension selected) with ⟨found, result⟩
          exact ⟨found, by simp [findSubsetMap, result]⟩
      | false =>
          cases included : findSubsetMap rest (NodeSet.insert acc node) finish with
          | some found => exact ⟨found, by simp [findSubsetMap, included]⟩
          | none =>
              rcases ih acc (extendsAcc_cons_skip extension selected) with ⟨found, result⟩
              exact ⟨found, by simp [findSubsetMap, included, result]⟩

/-- Enumerate kept-child maps on a fixed large set, trying `none` and then
each genuine directed child in that set.  The continuation runs only after
every pending parent has been assigned. -/
def findChildMap {α : Type _} (large : NodeSet S)
    (pending : List (Fin S.count)) (acc : ForestChild S)
    (finish : ForestChild S -> Option α) : Option α :=
  match pending with
  | [] => finish acc
  | parent :: rest =>
      firstSome (childOptions large parent) (fun value =>
        findChildMap large rest (setChild acc parent value) finish)

/-- Every returned value came from a completed kept-child assignment. -/
theorem findChildMap_eq_some {α : Type _}
    (large : NodeSet S) (pending : List (Fin S.count)) (acc : ForestChild S)
    (finish : ForestChild S -> Option α) {value : α}
    (result : findChildMap large pending acc finish = some value) :
    Exists fun child => finish child = some value := by
  induction pending generalizing acc with
  | nil => exact ⟨acc, result⟩
  | cons parent rest ih =>
      rcases firstSome_eq_some _ _ result with ⟨childValue, childResult⟩
      exact ih (setChild acc parent childValue) childResult

/-- A known well-formed branch with a successful continuation is visited.
The finite child-option completeness is carried by `ChildExtends`, so this
argument does not decide equality of arbitrary functions. -/
theorem findChildMap_eq_some_of_extends {α : Type _}
    (large : NodeSet S) (pending : List (Fin S.count)) (acc target : ForestChild S)
    (finish : ForestChild S -> Option α) {value : α}
    (extension : ChildExtends large pending acc target)
    (accepted : finish target = some value) :
    Exists fun found => findChildMap large pending acc finish = some found := by
  induction pending generalizing acc with
  | nil =>
      have same : acc = target := by
        funext node
        exact extension.1 node (fun member => by cases member)
      exact ⟨value, by simpa [findChildMap, same] using accepted⟩
  | cons parent rest ih =>
      have member : target parent ∈ childOptions large parent :=
        extension.2 parent List.mem_cons_self
      rcases ih (setChild acc parent (target parent))
        (childExtends_setChild extension) with ⟨found, childResult⟩
      rcases firstSome_eq_some_of_mem (childOptions large parent)
        (fun childValue => findChildMap large rest (setChild acc parent childValue) finish)
        member childResult with ⟨result, foundResult⟩
      exact ⟨result, foundResult⟩

/-! ## Hedge tests and the additional requirement are checked together -/

/-- Search all small sets for fixed large vertices and kept children.  The
additional requirement is tested at the same leaf as `smallForestReady`, not
after the ordinary small-set search has already stopped. -/
def findHedgeSmallWhere (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S)
    (accept : HedgeSelection S -> Bool) : Option (HedgeSelection S) :=
  match findSubset (NodeSet.members (NodeSet.diff large q.action)) NodeSet.empty
      (fun small => smallForestReady G q large child small && accept ⟨large, small, child⟩) with
  | none => none
  | some small => some ⟨large, small, child⟩

/-- Exhaustive finite hedge selection inside `host`, with an additional
Boolean requirement.  Early large-side and child-map tests prune invalid
branches; failure of `accept` continues the complete vertex/edge search. -/
def findHedgeSelectionWhere (G : ObservedGraph S) (q : JointKernelQuery S)
    (host : NodeSet S) (accept : HedgeSelection S -> Bool) : Option (HedgeSelection S) :=
  findSubsetMap (NodeSet.members host) NodeSet.empty (fun large =>
    if largeVerticesReady G q large then
      findChildMap large (NodeSet.members large) (emptyChild S) (fun child =>
        if largeChildReady G q large child then
          findHedgeSmallWhere G q large child accept
        else none)
    else none)

/-- Every small-side result retains the fixed large set and child map and
passes both the small-forest test and the additional requirement. -/
theorem findHedgeSmallWhere_tests
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S) (accept : HedgeSelection S -> Bool)
    {selection : HedgeSelection S}
    (result : findHedgeSmallWhere G q large child accept = some selection) :
    selection.large = large ∧ selection.child = child ∧
      smallForestReady G q large child selection.small = true ∧ accept selection = true := by
  unfold findHedgeSmallWhere at result
  cases found : findSubset (NodeSet.members (NodeSet.diff large q.action)) NodeSet.empty
    (fun small => smallForestReady G q large child small && accept ⟨large, small, child⟩) with
  | none => simp [found] at result
  | some small =>
      have same : (⟨large, small, child⟩ : HedgeSelection S) = selection := by
        simpa [found] using result
      subst selection
      have tests := Bool.and_eq_true_iff.mp (findSubset_spec _ _ _ found)
      exact ⟨rfl, rfl, tests.1, tests.2⟩

/-- Every public search result is a valid hedge selection meeting the
requested extra property.  This theorem checks all accepted branches,
not merely the particular candidate used to prove search success. -/
theorem findHedgeSelectionWhere_tests
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (host : NodeSet S) (accept : HedgeSelection S -> Bool)
    {selection : HedgeSelection S}
    (result : findHedgeSelectionWhere G q host accept = some selection) :
    hedgeTestsHold G q selection = true ∧ accept selection = true := by
  rcases findSubsetMap_eq_some _ _ _ result with ⟨large, largeResult⟩
  split at largeResult
  · rename_i vertices
    rcases findChildMap_eq_some _ _ _ _ largeResult with ⟨child, childResult⟩
    split at childResult
    · rename_i children
      have tests := findHedgeSmallWhere_tests G q large child accept childResult
      refine ⟨(hedgeTestsHold_iff G q selection).mpr ?_, tests.2.2.2⟩
      exact ⟨by simpa [tests.1] using vertices,
        by simpa [tests.1, tests.2.1] using children,
        by simpa [tests.1, tests.2.1] using tests.2.2.1⟩
    · cases childResult
  · cases largeResult

/-- The search cannot miss any supplied contained candidate that passes
the hedge tests and the additional requirement.  This is independent of
the order of earlier failed candidates and permits entirely different
large/small sets, common roots, and kept edges from an original witness. -/
theorem findHedgeSelectionWhere_eq_some_of_selection
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (host : NodeSet S) (accept : HedgeSelection S -> Bool) (selection : HedgeSelection S)
    (contained : NodeSet.Subset selection.large host)
    (tests : hedgeTestsHold G q selection = true) (accepted : accept selection = true) :
    Exists fun found => findHedgeSelectionWhere G q host accept = some found := by
  have parts := (hedgeTestsHold_iff G q selection).mp tests
  have well := largeChildReady_wellFormed G q selection.large selection.child parts.2.1
  rcases findSubset_eq_some_of_extends
    (NodeSet.members (NodeSet.diff selection.large q.action)) NodeSet.empty selection.small
    (fun small => smallForestReady G q selection.large selection.child small &&
      accept ⟨selection.large, small, selection.child⟩)
    (extendsAcc_of_smallForestReady G q selection.large selection.child selection.small parts.2.2)
    (Bool.and_eq_true_iff.mpr ⟨parts.2.2, accepted⟩) with ⟨small, smallResult⟩
  have smallSuccess : findHedgeSmallWhere G q selection.large selection.child accept =
      some ⟨selection.large, small, selection.child⟩ := by
    simp [findHedgeSmallWhere, smallResult]
  rcases findChildMap_eq_some_of_extends selection.large (NodeSet.members selection.large)
    (emptyChild S) selection.child
    (fun child => if largeChildReady G q selection.large child then
      findHedgeSmallWhere G q selection.large child accept else none)
    (childExtends_members_empty selection.large selection.child well)
    (by simpa [parts.2.1] using smallSuccess) with ⟨childSelection, childResult⟩
  exact findSubsetMap_eq_some_of_extends (NodeSet.members host) NodeSet.empty selection.large
    (fun large => if largeVerticesReady G q large then
      findChildMap large (NodeSet.members large) (emptyChild S) (fun child =>
        if largeChildReady G q large child then findHedgeSmallWhere G q large child accept
        else none) else none)
    (extendsAcc_empty_of_subset contained) (by simpa [parts.1] using childResult)

/-- Returning `none` rules out every contained selection meeting these
particular tests.  It does not rule out all semantic countermodels or all
other possible countermodel constructions. -/
theorem findHedgeSelectionWhere_none_excludes_selection
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (host : NodeSet S) (accept : HedgeSelection S -> Bool)
    (absent : findHedgeSelectionWhere G q host accept = none)
    (selection : HedgeSelection S) (contained : NodeSet.Subset selection.large host)
    (tests : hedgeTestsHold G q selection = true) : accept selection = false := by
  cases accepted : accept selection with
  | false => rfl
  | true =>
      rcases findHedgeSelectionWhere_eq_some_of_selection G q host accept selection
        contained tests accepted with ⟨found, result⟩
      rw [absent] at result
      cases result

end Causality
end Thesis
