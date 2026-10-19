import Thesis.CausalTransport.CompletenessLegacyProductFailures

namespace Thesis
namespace Causality

open Probability

/-!
# Historical deeper failure cases and the immediate-query boundary

Retains every already-proved deeper legacy failure case and the immediate-query
hedge interface. It does not extend the family with another branch-name stack.

Every extracted declaration keeps its original namespace, statement, proof
script and order. The new boundary only lets later work import a completed
artifact instead of retaining this section's elaboration state. Existing
clients may still import Completeness for the entire historical interface.
No theorem is dropped, weakened or replaced by an assumption.

Historical branch-specific unpackers remain historical facts: their quantity
is not evidence that a published semantic completeness theorem has been
inhabited. Current-engine compilation and hedge semantics retain their
existing independently checked assembly boundaries.
-/

/--
After a first ancestral shrink, nested product, nested 4.3 restriction,
and nested product split, a further 4.3 restriction unpacks as the ID
run on the containing c-component of the failing subpiece, with action
`(larger \ subpiece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_restrict_product_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept larger subpiece host2 : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) larger) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        larger = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter (NodeSet.diff larger subpiece) larger)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent larger = false)
    (hany2 :
      (G.cComponents larger).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 : G.containingCComponent larger subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
          (chainProduct kept larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff larger subpiece) larger) host2)
        (chainProduct larger host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G larger subpiece
    (chainProduct kept larger) hexP2 hnestedKept2 hnestedFc2 hsingle2
    hany2 hcont2 hinner

/--
A first ancestral shrink, nested product, nested 4.3 restriction, nested
product split, then 4.3 onto the containing c-component of the failing
subpiece, with remaining that inner host and free side the subpiece,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        piece = some larger)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)
                piece)
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept (NodeSet.inter q.action kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept (NodeSet.inter q.action kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)) := by
    have hfcL' :
        G.cComponents
          (NodeSet.diff larger
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcL
    rw [hfcL']
    exact hmemS
  have hhost : NodeSet.Subset larger kept :=
    containingCComponent_subset_host G kept piece
      (by simpa [kept] using hcont)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff kept (NodeSet.inter q.action kept) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : larger i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : kept i = true := hhost i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested product, nested 4.3 restriction,
and nested product split, a further ancestral shrink unpacks as the ID
run on `An(subpiece)` inside that nested host, with action
`larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_restrict_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept larger subpiece : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) larger) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        larger = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
          (chainProduct kept larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        subpiece (NodeSet.diff larger subpiece)
        (.marginalize
          (NodeSet.diff larger
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff larger subpiece) larger))
              (NodeSet.inter subpiece larger)))
          (chainProduct kept larger)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G larger subpiece
    (chainProduct kept larger) hexP2 hnestedKept2 hinner

/--
A first ancestral shrink, nested product, nested 4.3 restriction, nested
product split, then ancestral shrink onto `An(subpiece)` inside that
host, with remaining that ancestral set and free side the subpiece,
yields a hedge for the original query once that remaining set meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        piece = some larger)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)
                piece)
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept (NodeSet.inter q.action kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept (NodeSet.inter q.action kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)) := by
    have hfcL' :
        G.cComponents
          (NodeSet.diff larger
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcL
    rw [hfcL']
    exact hmemS
  have hhost : NodeSet.Subset larger kept :=
    containingCComponent_subset_host G kept piece
      (by simpa [kept] using hcont)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff kept (NodeSet.inter q.action kept) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : larger i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : kept i = true := hhost i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested product, nested ancestral shrink,
and nested product split, a further 4.3 restriction unpacks as the ID
run on the containing c-component of the failing subpiece, with action
`(nestedAn \ subpiece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_shrink_product_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {nestedAn subpiece host2 : NodeSet S}
    {current : ProbabilityTerm S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent nestedAn = false)
    (hany2 :
      (G.cComponents nestedAn).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 : G.containingCComponent nestedAn subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff nestedAn subpiece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) host2)
        (chainProduct nestedAn host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G nestedAn subpiece
    current hexP2 hnestedKept2 hnestedFc2 hsingle2 hany2 hcont2 hinner

/--
A first ancestral shrink, nested product, nested ancestral shrink, nested
product split, then 4.3 onto the containing c-component of the failing
subpiece, with remaining that inner host and free side the subpiece,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcP :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.diff
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)
                  piece)
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)))
            (NodeSet.inter piece
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.diff
                    (G.ancestralSet NodeSet.full
                      (GraphMutilation.bar q.action) q.outcome)
                    piece)
                  (G.ancestralSet NodeSet.full
                    (GraphMutilation.bar q.action) q.outcome)))
              (NodeSet.inter piece
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  let nestedAn :=
    G.ancestralSet kept
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff kept piece) kept))
      (NodeSet.inter piece kept)
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept (NodeSet.inter q.action kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept (NodeSet.inter q.action kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) := by
    have hfcP' :
        G.cComponents
          (NodeSet.diff nestedAn
            (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) =
          inner :: inner2 :: innerRest := by
      simpa [nestedAn, kept] using hfcP
    rw [hfcP']
    exact hmemS
  have hhost : NodeSet.Subset nestedAn kept :=
    ancestralSet_subset G kept
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff kept piece) kept))
      (NodeSet.inter piece kept)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff kept (NodeSet.inter q.action kept) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : nestedAn i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : kept i = true := hhost i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested product, nested ancestral shrink,
and nested product split, a further ancestral shrink unpacks as the ID
run on `An(subpiece)` inside that nested ancestral remaining set, with
action `nestedAn \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_shrink_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {nestedAn subpiece : NodeSet S}
    {current : ProbabilityTerm S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff nestedAn subpiece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        subpiece (NodeSet.diff nestedAn subpiece)
        (.marginalize
          (NodeSet.diff nestedAn
            (G.ancestralSet nestedAn
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
              (NodeSet.inter subpiece nestedAn)))
          current) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G nestedAn subpiece
    current hexP2 hnestedKept2 hinner

/--
A first ancestral shrink, nested product, nested ancestral shrink, nested
product split, then ancestral shrink onto `An(subpiece)` inside that
remaining set, with remaining that ancestral set and free side the
subpiece, yields a hedge for the original query once that remaining set
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcP :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.diff
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)
                  piece)
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)))
            (NodeSet.inter piece
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.diff
                    (G.ancestralSet NodeSet.full
                      (GraphMutilation.bar q.action) q.outcome)
                    piece)
                  (G.ancestralSet NodeSet.full
                    (GraphMutilation.bar q.action) q.outcome)))
              (NodeSet.inter piece
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet
          (G.ancestralSet
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.diff
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)
                  piece)
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)))
            (NodeSet.inter piece
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)
                  (GraphMutilation.bar
                    (NodeSet.inter
                      (NodeSet.diff
                        (G.ancestralSet NodeSet.full
                          (GraphMutilation.bar q.action) q.outcome)
                        piece)
                      (G.ancestralSet NodeSet.full
                        (GraphMutilation.bar q.action) q.outcome)))
                  (NodeSet.inter piece
                    (G.ancestralSet NodeSet.full
                      (GraphMutilation.bar q.action) q.outcome)))
                subpiece)
              (G.ancestralSet
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)
                (GraphMutilation.bar
                  (NodeSet.inter
                    (NodeSet.diff
                      (G.ancestralSet NodeSet.full
                        (GraphMutilation.bar q.action) q.outcome)
                      piece)
                    (G.ancestralSet NodeSet.full
                      (GraphMutilation.bar q.action) q.outcome)))
                (NodeSet.inter piece
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)))))
          (NodeSet.inter subpiece
            (G.ancestralSet
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.diff
                    (G.ancestralSet NodeSet.full
                      (GraphMutilation.bar q.action) q.outcome)
                    piece)
                  (G.ancestralSet NodeSet.full
                    (GraphMutilation.bar q.action) q.outcome)))
              (NodeSet.inter piece
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))))) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  let nestedAn :=
    G.ancestralSet kept
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff kept piece) kept))
      (NodeSet.inter piece kept)
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept (NodeSet.inter q.action kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept (NodeSet.inter q.action kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) := by
    have hfcP' :
        G.cComponents
          (NodeSet.diff nestedAn
            (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) =
          inner :: inner2 :: innerRest := by
      simpa [nestedAn, kept] using hfcP
    rw [hfcP']
    exact hmemS
  have hhost : NodeSet.Subset nestedAn kept :=
    ancestralSet_subset G kept
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff kept piece) kept))
      (NodeSet.inter piece kept)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff kept (NodeSet.inter q.action kept) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : nestedAn i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : kept i = true := hhost i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, nested product
split, and nested 4.3 restriction, a further product split unpacks as
the ID run of a free-list piece of that nested host, with action
`larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_restrict_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host larger piece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff host piece) host)
                larger)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            larger)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)
          (chainProduct host larger) =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G larger subpiece
            (NodeSet.diff larger subpiece)
            (chainProduct host larger) =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G larger piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff host piece) host)
      larger)
    (chainProduct host larger) hexN hkeptN hfcN hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
nested 4.3 restriction, then a product split, with remaining that nested
host and free side the failing subpiece, yields a hedge for the original
query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hhostL : NodeSet.Subset larger host)
    (hhostK :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff host
            (NodeSet.inter (NodeSet.inter q.action kept) host)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            larger)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              have hh : host i = true := hhostL i hl
              simp [hp, hl, hh] at hcut
    have hfree :
        NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host) i = true :=
      cComponents_subset G _ hmem' i hp
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            simp [hh] at hfree
        | true =>
            have hk : kept i = true := hhostK i hh
            simp [hh, hk] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, nested product
split, and nested 4.3 restriction, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the failing piece, with
action `((host \ piece) ∩ larger) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_restrict_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host larger piece host2 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff host piece) host)
                larger)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            larger)) =
        [piece])
    (hsingleN : G.isSingleCComponent larger = false)
    (hanyN :
      (G.cComponents larger).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontN : G.containingCComponent larger piece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)
          (chainProduct host larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            larger)
          host2)
        (chainProduct larger host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G larger piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff host piece) host)
      larger)
    (chainProduct host larger) hexN hkeptN hfcN hsingleN hanyN hcontN
    hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
nested 4.3 restriction, then 4.3 onto the containing c-component of the
failing piece, with remaining that inner host and free side the piece,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_restrict_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hhostK :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff host
            (NodeSet.inter (NodeSet.inter q.action kept) host)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            simp [hh] at hfree
        | true =>
            have hk : kept i = true := hhostK i hh
            simp [hh, hk] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, nested product
split, and nested 4.3 restriction, a further ancestral shrink unpacks as
the ID run on `An(piece)` inside that nested host, with action
`(host \ piece) ∩ larger`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_restrict_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host larger piece : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff host piece) host)
                larger)
              larger))
          (NodeSet.inter piece larger))
        larger = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)
          (chainProduct host larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff host piece) host)
                larger)
              larger))
          (NodeSet.inter piece larger))
        piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff host piece) host)
          larger)
        (.marginalize
          (NodeSet.diff larger
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff host piece) host)
                    larger)
                  larger))
              (NodeSet.inter piece larger)))
          (chainProduct host larger)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G larger piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff host piece) host)
      larger)
    (chainProduct host larger) hexN hkeptN hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
nested 4.3 restriction, then ancestral shrink onto `An(piece)` inside
that nested host, with remaining that ancestral set and free side the
piece, yields a hedge for the original query once that remaining set
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece nestedAn : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hhostK :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff host
            (NodeSet.inter (NodeSet.inter q.action kept) host)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            simp [hh] at hfree
        | true =>
            have hk : kept i = true := hhostK i hh
            simp [hh, hk] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, nested product
split, and nested ancestral shrink, a further product split unpacks as
the ID run of a free-list piece of that ancestral remaining set, with
action `nestedAn \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_shrink_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host nestedAn piece : NodeSet S}
    {current : ProbabilityTerm S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece (NodeSet.diff host piece)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G nestedAn subpiece
            (NodeSet.diff nestedAn subpiece) current =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G nestedAn piece
    (NodeSet.diff host piece) current hexN hkeptN hfcN hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
nested ancestral shrink, then a product split, with remaining that
ancestral set and free side the failing subpiece, yields a hedge for
the original query once that remaining set meets `X` and is ancestral
of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece nestedAn subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hAn : NodeSet.Subset nestedAn host)
    (hhostK :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff host
            (NodeSet.inter (NodeSet.inter q.action kept) host)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) := by
    rw [hfcN]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hn : nestedAn i with
          | false =>
              simp [hp, hn] at hcut
          | true =>
              have hh : host i = true := hAn i hn
              simp [hp, hn, hh] at hcut
    have hfree :
        NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host) i = true :=
      cComponents_subset G _ hmem' i hp
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            simp [hh] at hfree
        | true =>
            have hk : kept i = true := hhostK i hh
            simp [hh, hk] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, nested product
split, and nested ancestral shrink, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the failing piece, with
action `(host \ piece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_shrink_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host nestedAn piece host2 : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) =
        [piece])
    (hsingleN : G.isSingleCComponent nestedAn = false)
    (hanyN :
      (G.cComponents nestedAn).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontN : G.containingCComponent nestedAn piece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece (NodeSet.diff host piece)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)
          host2)
        (chainProduct nestedAn host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G nestedAn piece
    (NodeSet.diff host piece) current hexN hkeptN hfcN hsingleN hanyN
    hcontN hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
nested ancestral shrink, then 4.3 onto the containing c-component of
the failing piece, with remaining that inner host and free side the
piece, yields a hedge for the original query once that host meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hhostK :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff host
            (NodeSet.inter (NodeSet.inter q.action kept) host)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            simp [hh] at hfree
        | true =>
            have hk : kept i = true := hhostK i hh
            simp [hh, hk] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, nested product
split, and nested ancestral shrink, a further ancestral shrink unpacks
as the ID run on `An(piece)` inside that nested ancestral remaining
set, with action `host \ piece`.  The second shrink is live when the
restricted action `(host \ piece) ∩ nestedAn` changes the ancestral
graph of the piece.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_shrink_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host nestedAn piece : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece (NodeSet.diff host piece)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        piece (NodeSet.diff host piece)
        (.marginalize
          (NodeSet.diff nestedAn
            (G.ancestralSet nestedAn
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) nestedAn))
              (NodeSet.inter piece nestedAn)))
          current) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G nestedAn piece
    (NodeSet.diff host piece) current hexN hkeptN hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
nested ancestral shrink, then a further ancestral shrink onto
`An(piece)` inside that remaining set, with remaining that ancestral
set and free side the piece, yields a hedge for the original query
once that remaining set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_shrink_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece nestedAn2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hhostK :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff host
            (NodeSet.inter (NodeSet.inter q.action kept) host)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host
          (NodeSet.inter (NodeSet.inter q.action kept) host) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            simp [hh] at hfree
        | true =>
            have hk : kept i = true := hhostK i hh
            simp [hh, hk] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested product, nested 4.3 restriction,
and nested product split, a further 4.3 restriction unpacks as the ID
run on the containing c-component of the failing subpiece, with action
`(larger \ subpiece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_restrict_product_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host larger subpiece host2 : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) larger) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        larger = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter (NodeSet.diff larger subpiece) larger)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent larger = false)
    (hany2 :
      (G.cComponents larger).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 : G.containingCComponent larger subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
          (chainProduct host larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff larger subpiece) larger) host2)
        (chainProduct larger host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G larger subpiece
    (chainProduct host larger) hexP2 hnestedKept2 hnestedFc2 hsingle2
    hany2 hcont2 hinner

/--
A first 4.3 restriction, nested product, nested 4.3 restriction, nested
product split, then 4.3 onto the containing c-component of the failing
subpiece, with remaining that inner host and free side the subpiece,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece larger subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hcontH : G.containingCComponent host piece = some larger)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hhostS : NodeSet.Subset larger host :=
    containingCComponent_subset_host G host piece hcontH
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff host (NodeSet.inter q.action host) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : larger i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : host i = true := hhostS i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested product, nested 4.3 restriction,
and nested product split, a further ancestral shrink unpacks as the ID
run on `An(subpiece)` inside that nested host, with action
`larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_restrict_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {host larger subpiece : NodeSet S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) larger) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        larger = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
          (chainProduct host larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger))
        subpiece (NodeSet.diff larger subpiece)
        (.marginalize
          (NodeSet.diff larger
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff larger subpiece) larger))
              (NodeSet.inter subpiece larger)))
          (chainProduct host larger)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G larger subpiece
    (chainProduct host larger) hexP2 hnestedKept2 hinner

/--
A first 4.3 restriction, nested product, nested 4.3 restriction, nested
product split, then ancestral shrink onto `An(subpiece)` inside that
host, with remaining that ancestral set and free side the subpiece,
yields a hedge for the original query once that remaining set meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hcontH : G.containingCComponent host piece = some larger)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) larger))
          (NodeSet.inter subpiece larger)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hhostS : NodeSet.Subset larger host :=
    containingCComponent_subset_host G host piece hcontH
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff host (NodeSet.inter q.action host) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : larger i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : host i = true := hhostS i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested product, nested ancestral shrink,
and nested product split, a further 4.3 restriction unpacks as the ID
run on the containing c-component of the failing subpiece, with action
`(nestedAn \ subpiece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_shrink_product_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {nestedAn subpiece host2 : NodeSet S}
    {current : ProbabilityTerm S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = true)
    (hnestedFc2 :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn)) =
        [subpiece])
    (hsingle2 : G.isSingleCComponent nestedAn = false)
    (hany2 :
      (G.cComponents nestedAn).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcont2 : G.containingCComponent nestedAn subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff nestedAn subpiece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) host2)
        (chainProduct nestedAn host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_restrict G nestedAn subpiece
    current hexP2 hnestedKept2 hnestedFc2 hsingle2 hany2 hcont2 hinner

/--
A first 4.3 restriction, nested product, nested ancestral shrink, nested
product split, then 4.3 onto the containing c-component of the failing
subpiece, with remaining that inner host and free side the subpiece,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece nestedAn subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcP :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hAn : NodeSet.Subset nestedAn host)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) := by
    rw [hfcP]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff host (NodeSet.inter q.action host) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : nestedAn i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : host i = true := hAn i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested product, nested ancestral shrink,
and nested product split, a further ancestral shrink unpacks as the ID
run on `An(subpiece)` inside that nested ancestral remaining set, with
action `nestedAn \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_shrink_product_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {nestedAn subpiece : NodeSet S}
    {current : ProbabilityTerm S}
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn) = false)
    (hnestedKept2 :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff nestedAn subpiece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        subpiece (NodeSet.diff nestedAn subpiece)
        (.marginalize
          (NodeSet.diff nestedAn
            (G.ancestralSet nestedAn
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
              (NodeSet.inter subpiece nestedAn)))
          current) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_piece_shrink G nestedAn subpiece
    current hexP2 hnestedKept2 hinner

/--
A first 4.3 restriction, nested product, nested ancestral shrink, nested
product split, then ancestral shrink onto `An(subpiece)` inside that
remaining set, with remaining that ancestral set and free side the
subpiece, yields a hedge for the original query once that remaining set
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece nestedAn subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcP :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hAn : NodeSet.Subset nestedAn host)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff nestedAn subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) := by
    rw [hfcP]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hpieceA : piece i = false := by
          cases hp : piece i with
          | false =>
              rfl
          | true =>
              have hfreeP :
                  NodeSet.diff host (NodeSet.inter q.action host) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : nestedAn i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : host i = true := hAn i hl
            simp [hl, hk] at hfreeS
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, nested product
split, and nested 4.3 restriction, a further product split unpacks as
the ID run of a free-list piece of that nested host, with action
`larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_restrict_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept larger piece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept piece) kept)
                larger)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)
            larger)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)
          (chainProduct kept larger) =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G larger subpiece
            (NodeSet.diff larger subpiece)
            (chainProduct kept larger) =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G larger piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff kept piece) kept)
      larger)
    (chainProduct kept larger) hexN hkeptN hfcN hinner

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
nested 4.3 restriction, then a product split, with remaining that nested
host and free side the failing subpiece, yields a hedge for the original
query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter (NodeSet.inter q.action host)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.diff
                  (G.ancestralSet host
                    (GraphMutilation.bar (NodeSet.inter q.action host))
                    (NodeSet.inter q.outcome host))
                  piece)
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host)))
              larger)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hhostL : NodeSet.Subset larger
      (G.ancestralSet host
        (GraphMutilation.bar (NodeSet.inter q.action host))
        (NodeSet.inter q.outcome host)))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.inter q.action host) kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)
            larger)) := by
    have hfcN' :
        G.cComponents
          (NodeSet.diff larger
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept piece) kept)
                larger)
              larger)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcN
    rw [hfcN']
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              have hk : kept i = true := hhostL i hl
              simp [hp, hl, hk] at hcut
    have hfree :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept) i = true :=
      cComponents_subset G _ hmem' i hp
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            have hk : kept i = true := by
              simpa [hh] using hfree
            have hh' : host i = true :=
              ancestralSet_subset G host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host) i (by simpa [kept] using hk)
            simp [hh] at hh'
        | true =>
            simp [hh] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, nested product
split, and nested 4.3 restriction, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the failing piece, with
action `((kept \ piece) ∩ larger) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_restrict_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept larger piece host2 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept piece) kept)
                larger)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)
            larger)) =
        [piece])
    (hsingleN : G.isSingleCComponent larger = false)
    (hanyN :
      (G.cComponents larger).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontN : G.containingCComponent larger piece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)
          (chainProduct kept larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)
            larger)
          host2)
        (chainProduct larger host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G larger piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff kept piece) kept)
      larger)
    (chainProduct kept larger) hexN hkeptN hfcN hsingleN hanyN hcontN
    hinner

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
nested 4.3 restriction, then 4.3 onto the containing c-component of the
failing piece, with remaining that inner host and free side the piece,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_restrict_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter (NodeSet.inter q.action host)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.inter q.action host) kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            have hk : kept i = true := by
              simpa [hh] using hfree
            have hh' : host i = true :=
              ancestralSet_subset G host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host) i (by simpa [kept] using hk)
            simp [hh] at hh'
        | true =>
            simp [hh] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, nested product
split, and nested 4.3 restriction, a further ancestral shrink unpacks as
the ID run on `An(piece)` inside that nested host, with action
`(kept \ piece) ∩ larger`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_restrict_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept larger piece : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept piece) kept)
                larger)
              larger))
          (NodeSet.inter piece larger))
        larger = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept piece) kept)
            larger)
          (chainProduct kept larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept piece) kept)
                larger)
              larger))
          (NodeSet.inter piece larger))
        piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff kept piece) kept)
          larger)
        (.marginalize
          (NodeSet.diff larger
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff kept piece) kept)
                    larger)
                  larger))
              (NodeSet.inter piece larger)))
          (chainProduct kept larger)) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G larger piece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff kept piece) kept)
      larger)
    (chainProduct kept larger) hexN hkeptN hinner

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
nested 4.3 restriction, then ancestral shrink onto `An(piece)` inside
that nested host, with remaining that ancestral set and free side the
piece, yields a hedge for the original query once that remaining set
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece nestedAn : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter (NodeSet.inter q.action host)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.inter q.action host) kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            have hk : kept i = true := by
              simpa [hh] using hfree
            have hh' : host i = true :=
              ancestralSet_subset G host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host) i (by simpa [kept] using hk)
            simp [hh] at hh'
        | true =>
            simp [hh] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, nested product
split, and nested ancestral shrink, a further product split unpacks as
the ID run of a free-list piece of that ancestral remaining set, with
action `nestedAn \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_shrink_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept nestedAn piece : NodeSet S}
    {current : ProbabilityTerm S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff kept piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece (NodeSet.diff kept piece)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G nestedAn subpiece
            (NodeSet.diff nestedAn subpiece) current =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G nestedAn piece
    (NodeSet.diff kept piece) current hexN hkeptN hfcN hinner

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
nested ancestral shrink, then a product split, with remaining that
ancestral set and free side the failing subpiece, yields a hedge for
the original query once that remaining set meets `X` and is ancestral
of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {host piece nestedAn subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter (NodeSet.inter q.action host)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))
              piece)
            nestedAn)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hAn : NodeSet.Subset nestedAn
      (G.ancestralSet host
        (GraphMutilation.bar (NodeSet.inter q.action host))
        (NodeSet.inter q.outcome host)))
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.inter q.action host) kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) := by
    have hfcN' :
        G.cComponents
          (NodeSet.diff nestedAn
            (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcN
    rw [hfcN']
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hn : nestedAn i with
          | false =>
              simp [hp, hn] at hcut
          | true =>
              have hk : kept i = true := hAn i hn
              simp [hp, hn, hk] at hcut
    have hfree :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept) i = true :=
      cComponents_subset G _ hmem' i hp
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            have hk : kept i = true := by
              simpa [hh] using hfree
            have hh' : host i = true :=
              ancestralSet_subset G host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host) i (by simpa [kept] using hk)
            simp [hh] at hh'
        | true =>
            simp [hh] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, nested product
split, and nested ancestral shrink, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the failing piece, with
action `(kept \ piece) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_shrink_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept nestedAn piece host2 : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff kept piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn)) =
        [piece])
    (hsingleN : G.isSingleCComponent nestedAn = false)
    (hanyN :
      (G.cComponents nestedAn).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontN : G.containingCComponent nestedAn piece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece (NodeSet.diff kept piece)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff kept piece) nestedAn)
          host2)
        (chainProduct nestedAn host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G nestedAn piece
    (NodeSet.diff kept piece) current hexN hkeptN hfcN hsingleN hanyN
    hcontN hinner

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
nested ancestral shrink, then 4.3 onto the containing c-component of
the failing piece, with remaining that inner host and free side the
piece, yields a hedge for the original query once that host meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter (NodeSet.inter q.action host)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.inter q.action host) kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            have hk : kept i = true := by
              simpa [hh] using hfree
            have hh' : host i = true :=
              ancestralSet_subset G host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host) i (by simpa [kept] using hk)
            simp [hh] at hh'
        | true =>
            simp [hh] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, nested product
split, and nested ancestral shrink, a further ancestral shrink unpacks
as the ID run on `An(piece)` inside that nested ancestral remaining
set, with action `kept \ piece`.  The second shrink is live when the
restricted action `(kept \ piece) ∩ nestedAn` changes the ancestral
graph of the piece.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_shrink_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept nestedAn piece : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff kept piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        nestedAn = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn piece (NodeSet.diff kept piece)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff kept piece) nestedAn))
          (NodeSet.inter piece nestedAn))
        piece (NodeSet.diff kept piece)
        (.marginalize
          (NodeSet.diff nestedAn
            (G.ancestralSet nestedAn
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff kept piece) nestedAn))
              (NodeSet.inter piece nestedAn)))
          current) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G nestedAn piece
    (NodeSet.diff kept piece) current hexN hkeptN hinner

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
nested ancestral shrink, then a further ancestral shrink onto
`An(piece)` inside that remaining set, with remaining that ancestral
set and free side the piece, yields a hedge for the original query
once that remaining set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_shrink_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {host piece nestedAn2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter (NodeSet.inter q.action host)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn2 = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.inter q.action host) kept)) =
          component :: component2 :: rest := by
      simpa [kept] using hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.inter q.action host) kept) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
        cases hh : host i with
        | false =>
            have hk : kept i = true := by
              simpa [hh] using hfree
            have hh' : host i = true :=
              ancestralSet_subset G host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host) i (by simpa [kept] using hk)
            simp [hh] at hh'
        | true =>
            simp [hh] at hfree
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested product
split, and nested 4.3 restriction, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the failing subpiece, with
action `((larger \ subpiece) ∩ larger2) ∩ host3`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_restrict_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger larger2 subpiece host3 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff larger subpiece) larger)
            larger2)
          larger2) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff larger subpiece) larger)
                larger2)
              larger2))
          (NodeSet.inter subpiece larger2))
        larger2 = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff larger subpiece) larger)
              larger2)
            larger2)) =
        [subpiece])
    (hsingleN : G.isSingleCComponent larger2 = false)
    (hanyN :
      (G.cComponents larger2).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcontN : G.containingCComponent larger2 subpiece = some host3)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger2 subpiece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff larger subpiece) larger)
            larger2)
          (chainProduct larger larger2) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host3 subpiece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff larger subpiece) larger)
              larger2)
            larger2)
          host3)
        (chainProduct larger2 host3) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G larger2 subpiece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff larger subpiece) larger)
      larger2)
    (chainProduct larger larger2) hexN hkeptN hfcN hsingleN hanyN hcontN
    hinner

/--
A first product split, nested 4.3 restriction, nested product split,
nested 4.3 restriction, then 4.3 onto the containing c-component of the
failing subpiece, with remaining that inner host and free side the
subpiece, yields a hedge for the original query once that host meets
`X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_restrict_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece host3 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host3 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested product
split, and nested 4.3 restriction, a further ancestral shrink unpacks
as the ID run on `An(subpiece)` inside that nested host, with action
`((larger \ subpiece) ∩ larger2)`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_restrict_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger larger2 subpiece : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff larger subpiece) larger)
            larger2)
          larger2) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff larger subpiece) larger)
                larger2)
              larger2))
          (NodeSet.inter subpiece larger2))
        larger2 = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger2 subpiece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff larger subpiece) larger)
            larger2)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff larger subpiece) larger)
                larger2)
              larger2))
          (NodeSet.inter subpiece larger2))
        subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff larger subpiece) larger)
          larger2)
        (.marginalize
          (NodeSet.diff larger2
            (G.ancestralSet larger2
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff larger subpiece) larger)
                    larger2)
                  larger2))
              (NodeSet.inter subpiece larger2)))
          current) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G larger2 subpiece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff larger subpiece) larger)
      larger2)
    current hexN hkeptN hinner

/--
After a first product split, nested 4.3 restriction, nested product
split, and nested 4.3 restriction, a further product split unpacks as
the ID run on a c-component of that inner host minus the restricted
action, with remaining that host and action `larger2 \ nested`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_restrict_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger larger2 subpiece : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff larger subpiece) larger)
            larger2)
          larger2) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff larger subpiece) larger)
                larger2)
              larger2))
          (NodeSet.inter subpiece larger2))
        larger2 = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff larger subpiece) larger)
              larger2)
            larger2)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger2 subpiece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff larger subpiece) larger)
            larger2)
          (chainProduct larger larger2) =
          IdentificationOutcome.failed fail) :
    Exists fun nested =>
      nested ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G larger2 nested
            (NodeSet.diff larger2 nested)
            (chainProduct larger larger2) =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G larger2 subpiece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff larger subpiece) larger)
      larger2)
    (chainProduct larger larger2) hexN hkeptN hfcN hinner

/--
A first product split, nested 4.3 restriction, nested product split,
nested 4.3 restriction, then a product split, with remaining that inner
host and free side the failing nested piece, yields a hedge for the
original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {outer outer2 : NodeSet S} {outerRest : List (NodeSet S)}
    {piece larger larger2 subpiece nested : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff larger subpiece) larger)
              larger2)
            larger2)) =
        outer :: outer2 :: outerRest)
    (hmemN : nested ∈ outer :: outer2 :: outerRest)
    (hhostL : NodeSet.Subset larger2 larger)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining larger2 = true)
    (hfreeEq : NodeSet.equal fail.free nested = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hmemN' :
      nested ∈ G.cComponents
        (NodeSet.diff larger2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff larger subpiece) larger)
              larger2)
            larger2)) := by
    rw [hfcN]
    exact hmemN
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcutN :
        NodeSet.diff larger2
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff larger subpiece) larger)
              larger2)
            larger2) i = true :=
      cComponents_subset G _ hmemN' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hs : subpiece i = true := by
      simp [NodeSet.diff, NodeSet.inter] at hcutN
      cases hs : subpiece i with
      | true =>
          rfl
      | false =>
          cases hl2 : larger2 i with
          | false =>
              simp [hs, hl2] at hcutN
          | true =>
              have hl : larger i = true := hhostL i hl2
              simp [hs, hl2, hl] at hcutN
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i hs
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
A first product split, nested 4.3 restriction, nested product split,
nested 4.3 restriction, then ancestral shrink onto `An(subpiece)`
inside that host, with remaining that ancestral set and free side the
subpiece, yields a hedge for the original query once that remaining
set meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger larger2 subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet larger2
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff larger subpiece) larger)
                larger2)
              larger2))
          (NodeSet.inter subpiece larger2)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested product
split, and nested ancestral shrink, a further 4.3 restriction unpacks
as the ID run on the containing c-component of the failing subpiece,
with action `((larger \ subpiece) ∩ nestedAn) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_shrink_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn subpiece host2 : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn)) =
        [subpiece])
    (hsingleN : G.isSingleCComponent nestedAn = false)
    (hanyN :
      (G.cComponents nestedAn).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcontN : G.containingCComponent nestedAn subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff larger subpiece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn)
          host2)
        (chainProduct nestedAn host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G nestedAn subpiece
    (NodeSet.diff larger subpiece) current hexN hkeptN hfcN hsingleN
    hanyN hcontN hinner

/--
A first product split, nested 4.3 restriction, nested product split,
nested ancestral shrink, then 4.3 onto the containing c-component of
the failing subpiece, with remaining that inner host and free side the
subpiece, yields a hedge for the original query once that host meets
`X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested product
split, and nested ancestral shrink, a further ancestral shrink unpacks
as the ID run on `An(subpiece)` inside that remaining set, with action
`larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_shrink_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn subpiece : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff larger subpiece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        subpiece (NodeSet.diff larger subpiece)
        (.marginalize
          (NodeSet.diff nestedAn
            (G.ancestralSet nestedAn
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn))
              (NodeSet.inter subpiece nestedAn)))
          current) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G nestedAn subpiece
    (NodeSet.diff larger subpiece) current hexN hkeptN hinner

/--
A first product split, nested 4.3 restriction, nested product split,
nested ancestral shrink, then a further ancestral shrink onto
`An(subpiece)` inside that remaining set, with remaining that ancestral
set and free side the subpiece, yields a hedge for the original query
once that remaining set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_shrink_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger nestedAn subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested 4.3 restriction, nested product
split, and nested ancestral shrink, a further product split unpacks as
the ID run on a c-component of that ancestral remaining minus the
restricted action, with remaining that ancestral set and action
`nestedAn \ nested`.
-/
theorem identifyJoint_eq_failed_of_first_product_restrict_product_shrink_product
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {larger nestedAn subpiece : NodeSet S}
    {current : ProbabilityTerm S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet nestedAn
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn))
          (NodeSet.inter subpiece nestedAn))
        nestedAn = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G nestedAn subpiece
          (NodeSet.diff larger subpiece) current =
          IdentificationOutcome.failed fail) :
    Exists fun nested =>
      nested ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G nestedAn nested
            (NodeSet.diff nestedAn nested) current =
            IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_product_of G nestedAn subpiece
    (NodeSet.diff larger subpiece) current hexN hkeptN hfcN hinner

/--
A first product split, nested 4.3 restriction, nested product split,
nested ancestral shrink, then a product split, with remaining that
ancestral set and free side the failing nested piece, yields a hedge
for the original query once that remaining set meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_restrict_product_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {outer outer2 : NodeSet S} {outerRest : List (NodeSet S)}
    {piece larger nestedAn subpiece nested : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfcN :
      G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn)) =
        outer :: outer2 :: outerRest)
    (hmemN : nested ∈ outer :: outer2 :: outerRest)
    (hAn : NodeSet.Subset nestedAn larger)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining nestedAn = true)
    (hfreeEq : NodeSet.equal fail.free nested = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger)) := by
    rw [hfcL]
    exact hmemS
  have hmemN' :
      nested ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn)) := by
    rw [hfcN]
    exact hmemN
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcutN :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff larger subpiece) nestedAn) i =
            true :=
      cComponents_subset G _ hmemN' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hs : subpiece i = true := by
      simp [NodeSet.diff, NodeSet.inter] at hcutN
      cases hs : subpiece i with
      | true =>
          rfl
      | false =>
          cases hn : nestedAn i with
          | false =>
              simp [hs, hn] at hcutN
          | true =>
              have hl : larger i = true := hAn i hn
              simp [hs, hn, hl] at hcutN
    have hcut :
        NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff NodeSet.full piece)
              NodeSet.full)
            larger) i = true :=
      cComponents_subset G _ hmemS' i hs
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hl : larger i with
          | false =>
              simp [hp, hl] at hcut
          | true =>
              simp [hp, hl] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested product
split, and nested 4.3 restriction, a further 4.3 restriction unpacks as
the ID run on the containing c-component of the failing subpiece, with
action `((kept \ subpiece) ∩ larger) ∩ host2`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_product_restrict_restrict
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept larger subpiece host2 : NodeSet S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept subpiece) kept)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept subpiece) kept)
                larger)
              larger))
          (NodeSet.inter subpiece larger))
        larger = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept subpiece) kept)
              larger)
            larger)) =
        [subpiece])
    (hsingleN : G.isSingleCComponent larger = false)
    (hanyN :
      (G.cComponents larger).any
        (fun c => NodeSet.equal c subpiece) = false)
    (hcontN : G.containingCComponent larger subpiece = some host2)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept subpiece) kept)
            larger)
          (chainProduct kept larger) =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host2 subpiece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept subpiece) kept)
              larger)
            larger)
          host2)
        (chainProduct larger host2) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_restrict_of G larger subpiece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff kept subpiece) kept)
      larger)
    (chainProduct kept larger) hexN hkeptN hfcN hsingleN hanyN hcontN
    hinner

/--
A first product split, nested ancestral shrink, nested product split,
nested 4.3 restriction, then 4.3 onto the containing c-component of the
failing subpiece, with remaining that inner host and free side the
subpiece, yields a hedge for the original query once that host meets
`X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_product_restrict_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece subpiece host2 : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq : NodeSet.equal fail.remaining host2 = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
      (NodeSet.inter piece NodeSet.full)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) := by
    have hfcK' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcK
    rw [hfcK']
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept) i =
          true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hk : kept i with
          | false =>
              simp [hp, hk] at hcut
          | true =>
              simp [hp, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, nested ancestral shrink, nested product
split, and nested 4.3 restriction, a further ancestral shrink unpacks
as the ID run on `An(subpiece)` inside that inner host, with action
`((kept \ subpiece) ∩ larger)`.
-/
theorem identifyJoint_eq_failed_of_first_product_shrink_product_restrict_shrink
    (G : ObservedGraph S) (_q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {kept larger subpiece : NodeSet S}
    {current : ProbabilityTerm S}
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept subpiece) kept)
            larger)
          larger) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept subpiece) kept)
                larger)
              larger))
          (NodeSet.inter subpiece larger))
        larger = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G larger subpiece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff kept subpiece) kept)
            larger)
          current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff kept subpiece) kept)
                larger)
              larger))
          (NodeSet.inter subpiece larger))
        subpiece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff kept subpiece) kept)
          larger)
        (.marginalize
          (NodeSet.diff larger
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff kept subpiece) kept)
                    larger)
                  larger))
              (NodeSet.inter subpiece larger)))
          current) =
        IdentificationOutcome.failed fail :=
  identifyFuel_eq_failed_of_shrink_of G larger subpiece
    (NodeSet.inter
      (NodeSet.inter (NodeSet.diff kept subpiece) kept)
      larger)
    current hexN hkeptN hinner

/--
A first product split, nested ancestral shrink, nested product split,
nested 4.3 restriction, then ancestral shrink onto `An(subpiece)`
inside that host, with remaining that ancestral set and free side the
subpiece, yields a hedge for the original query once that remaining
set meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_product_shrink_product_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfcK :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                NodeSet.full))
            (NodeSet.inter piece NodeSet.full))
          (NodeSet.inter (NodeSet.diff NodeSet.full piece)
            (G.ancestralSet NodeSet.full
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                  NodeSet.full))
              (NodeSet.inter piece NodeSet.full)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (_heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff
                  (G.ancestralSet NodeSet.full
                    (GraphMutilation.bar
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        NodeSet.full))
                    (NodeSet.inter piece NodeSet.full))
                  subpiece)
                  (G.ancestralSet NodeSet.full
                    (GraphMutilation.bar
                      (NodeSet.inter (NodeSet.diff NodeSet.full piece)
                        NodeSet.full))
                    (NodeSet.inter piece NodeSet.full)))
                larger)
              larger))
          (NodeSet.inter subpiece larger)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff NodeSet.full piece) NodeSet.full))
      (NodeSet.inter piece NodeSet.full)
  have hsub := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents (NodeSet.diff NodeSet.full q.action) := by
    simpa [hfc] using hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) := by
    have hfcK' :
        G.cComponents
          (NodeSet.diff kept
            (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept)) =
          inner :: inner2 :: innerRest := by
      simpa [kept] using hfcK
    rw [hfcK']
    exact hmemS
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hcut :
        NodeSet.diff kept
          (NodeSet.inter (NodeSet.diff NodeSet.full piece) kept) i =
          true :=
      cComponents_subset G _ hmemS' i (by
        simpa [failedHedgeSelection, hsub] using hi)
    have hp : piece i = true := by
      simp [NodeSet.diff, NodeSet.inter, NodeSet.full] at hcut
      cases hp : piece i with
      | true =>
          rfl
      | false =>
          cases hk : kept i with
          | false =>
              simp [hp, hk] at hcut
          | true =>
              simp [hp, hk] at hcut
    have hdisjP :=
      (NodeSet.disjointBool_eq_true_iff _ _).mp
        (product_piece_avoids_action G q hmem')
    exact hdisjP i hp
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
Top-level ID of an immediate 4.1 hedge: the full graph is ancestral of
`Y` in `G_{\overline{X}}`, `C(G) = {G}`, and `C(G \ X)` is a singleton.
Those Boolean facts are the local-action hypotheses, so the extractor
returns a `HedgeWitness`.
-/
theorem identifyJoint_eq_failed_immediate_query_site
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [fail.free])
    (hsingle : G.isSingleCComponent NodeSet.full = true)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true ∧
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hkept' :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
          (NodeSet.inter q.outcome NodeSet.full))
        NodeSet.full = true := by
    simpa [hinter, hy] using hkept
  have hfc' :
      G.cComponents
        (NodeSet.diff NodeSet.full (NodeSet.inter q.action NodeSet.full)) =
        [fail.free] := by
    simpa [hinter] using hfc
  have hfuel :
      Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome
        q.action (observationalJointTerm S) =
        IdentificationOutcome.failed fail := hfail
  rw [identificationFuel] at hfuel
  have parts :=
    identifyFuel_eq_failed_immediate_query_site
      (S.count * Nat.succ S.count * Nat.succ S.count) G NodeSet.full
      q.outcome q.action (observationalJointTerm S) hex' hkept' hfc'
      hsingle hfuel
  exact ⟨parts.2.2.1, parts.2.2.2⟩

theorem hedgeWitness?_eq_some_of_failed_immediate
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [fail.free])
    (hsingle : G.isSingleCComponent NodeSet.full = true)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed_local_action G q hfail
    (identifyJoint_eq_failed_immediate_query_site G q hex hkept hfc
      hsingle hfail).1
    (identifyJoint_eq_failed_immediate_query_site G q hex hkept hfc
      hsingle hfail).2

/--
Top-level ID failure, when the extractor succeeds, is a `HedgeWitness`.
Success of ID still needs a derivation-to-certificate map; this is the
failure half of the joint completeness diagram.
-/
def hedgeWitnessOfJoint (G : ObservedGraph S) (q : JointKernelQuery S) :
    Option (HedgeWitness G q) :=
  match Legacy.identifyJoint G q with
  | .failed fail => hedgeWitness? G q fail
  | _ => none


end Causality
end Thesis
