import Thesis.CausalTransport.CompletenessFailureExtraction

namespace Thesis
namespace Causality

open Probability

/-!
# Historical ancestral-shrink failure cases

Retains the existing ancestral-shrink and restriction special cases, together
with their exact trace and original-query hedge transport arguments.

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

/-!
## Legacy branch-specific failure lifting

The lemmas in this section are checked finite-depth special cases.  They are
kept because downstream developments may reuse their local graph facts, but
the general completeness proof should recurse over
`IdentificationFailureTrace` instead of extending this family with deeper
branch-name stacks.
-/

/--
After a first ancestral restriction, the nested ID run is the original
query on the ancestral remaining set.
-/
theorem identifyJoint_eq_failed_of_first_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Legacy.identifyFuel
        (S.count * Nat.succ S.count * Nat.succ S.count) G
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        q.outcome q.action
        (.marginalize
          (NodeSet.diff NodeSet.full
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          (observationalJointTerm S)) =
      IdentificationOutcome.failed fail := by
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
        NodeSet.full = false := by
    simpa [hinter, hy] using hkept
  have hfuel :
      Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome
        q.action (observationalJointTerm S) =
        IdentificationOutcome.failed fail := hfail
  rw [identificationFuel] at hfuel
  simp [Legacy.identifyFuel, hex', hkept'] at hfuel
  simpa [hinter, hy] using hfuel

theorem hedgeWitness?_eq_some_of_failed_after_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed_local_action G q hfail hfree
    (identifyFuel_eq_failed_query_of_remaining_eq
      (S.count * Nat.succ S.count * Nat.succ S.count) G
      (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
        q.outcome)
      q.outcome q.action
      (.marginalize
        (NodeSet.diff NodeSet.full
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome))
        (observationalJointTerm S))
      (identifyJoint_eq_failed_of_first_shrink G q hex hkept hfail)
      heq hfree)

/--
After a first ancestral restriction, a nested product split unpacks as
an ID run on one free c-component of the ancestral remaining set, with
action `kept \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            piece
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (.marginalize
              (NodeSet.diff NodeSet.full
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G kept
          q.outcome q.action
          (.marginalize
            (NodeSet.diff NodeSet.full kept) (observationalJointTerm S)) =
        IdentificationOutcome.failed fail :=
    identifyJoint_eq_failed_of_first_shrink G q hex hkept hfail
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G kept q.outcome q.action
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G kept q.outcome q.action
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have hexN' :
          NodeSet.isEmpty (NodeSet.inter q.action kept) = false := hexN
      have hkeptN' :
          NodeSet.equal
            (G.ancestralSet kept
              (GraphMutilation.bar (NodeSet.inter q.action kept))
              (NodeSet.inter q.outcome kept))
            kept = true := hkeptN
      have hfc' :
          G.cComponents
            (NodeSet.diff kept (NodeSet.inter q.action kept)) =
            component :: component2 :: rest := hfc
      have hprod :=
        identifyFuel_eq_failed_of_product n G kept q.outcome q.action
          (.marginalize
            (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
          hexN' hkeptN' hfc' hsucc
      rcases hprod with ⟨piece, hmem, hEq⟩
      exact ⟨piece, hmem, ⟨n, hEq⟩⟩

/--
A first ancestral restriction whose nested call then product-splits, with
free side the failing piece of the ancestral remaining set, yields a hedge
for the original query once that remaining set meets `X` and is ancestral
of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
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
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff kept (NodeSet.inter q.action kept) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexN with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
A product-piece ID run whose free side is already a single c-component
of itself, but not of the host remaining set, unpacks as the nested
4.3 restriction onto the containing c-component of that piece.  The
host remaining set is arbitrary: a first ancestral shrink followed by
a product is the typical smaller remaining set.
-/
theorem identifyFuel_eq_failed_of_product_piece_restrict
    (G : ObservedGraph S)
    (remaining piece : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S} {larger : NodeSet S}
    (hex :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff remaining piece) remaining) =
          false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff remaining piece) remaining))
          (NodeSet.inter piece remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining
          (NodeSet.inter (NodeSet.diff remaining piece) remaining)) =
        [piece])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent remaining piece = some larger)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G remaining piece
          (NodeSet.diff remaining piece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff remaining piece) remaining)
          larger)
        (chainProduct remaining larger) =
        IdentificationOutcome.failed fail := by
  rcases hinner with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G remaining piece
            (NodeSet.diff remaining piece) current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G remaining piece
            (NodeSet.diff remaining piece) current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      exact ⟨n,
        identifyFuel_eq_failed_of_restrict n G remaining piece
          (NodeSet.diff remaining piece) current
          hex hkept hfc hsingle hany hcont hsucc⟩

/--
A product-piece 4.3 restriction whose nested host then product-splits
unpacks as an ID run on one free c-component of that host, with action
`larger \ subpiece`.  The original remaining set is arbitrary.
-/
theorem identifyFuel_eq_failed_of_product_piece_restrict_product
    (G : ObservedGraph S)
    (remaining piece : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S} {larger : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff remaining piece) remaining) =
          false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff remaining piece) remaining))
          (NodeSet.inter piece remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining
          (NodeSet.inter (NodeSet.diff remaining piece) remaining)) =
        [piece])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent remaining piece = some larger)
    (hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff remaining piece) remaining)
          larger) = false)
    (hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff remaining piece) remaining)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff remaining piece) remaining)
            larger)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G remaining piece
          (NodeSet.diff remaining piece) current =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
            (chainProduct remaining larger) =
            IdentificationOutcome.failed fail := by
  rcases identifyFuel_eq_failed_of_product_piece_restrict G remaining piece
      current hex hkept hfc hsingle hany hcont hinner with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G larger piece
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff remaining piece) remaining)
              larger)
            (chainProduct remaining larger) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G larger piece
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff remaining piece) remaining)
              larger)
            (chainProduct remaining larger) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      have hinter :
          NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff remaining piece) remaining)
                larger)
              larger =
            NodeSet.inter
              (NodeSet.inter (NodeSet.diff remaining piece) remaining)
              larger := by
        funext i
        simp [NodeSet.inter]
      have hexL' :
          NodeSet.isEmpty
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter (NodeSet.diff remaining piece) remaining)
                larger)
              larger) = false := by
        simpa [hinter] using hexL
      have hkeptL' :
          NodeSet.equal
            (G.ancestralSet larger
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter (NodeSet.diff remaining piece)
                      remaining)
                    larger)
                  larger))
              (NodeSet.inter piece larger))
            larger = true := by
        simpa [hinter] using hkeptL
      have hfcL' :
          G.cComponents
            (NodeSet.diff larger
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter (NodeSet.diff remaining piece)
                    remaining)
                  larger)
                larger)) =
            component :: component2 :: rest := by
        simpa [hinter] using hfcL
      have hprod :=
        identifyFuel_eq_failed_of_product n G larger piece
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff remaining piece) remaining)
            larger)
          (chainProduct remaining larger) hexL' hkeptL' hfcL' hsucc
      rcases hprod with ⟨subpiece, hmemS, hEq⟩
      exact ⟨subpiece, hmemS, ⟨n, hEq⟩⟩

/--
A product-piece ID run whose remaining set is not ancestral of that
piece first restricts to `An(piece)` inside the host remaining set.
The host remaining set is arbitrary: a first ancestral shrink followed
by a product is the typical smaller remaining set.
-/
theorem identifyFuel_eq_failed_of_product_piece_shrink
    (G : ObservedGraph S)
    (remaining piece : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (hex :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff remaining piece) remaining) =
          false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff remaining piece) remaining))
          (NodeSet.inter piece remaining))
        remaining = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G remaining piece
          (NodeSet.diff remaining piece) current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet remaining
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff remaining piece) remaining))
          (NodeSet.inter piece remaining))
        piece (NodeSet.diff remaining piece)
        (.marginalize
          (NodeSet.diff remaining
            (G.ancestralSet remaining
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff remaining piece) remaining))
              (NodeSet.inter piece remaining)))
          current) =
        IdentificationOutcome.failed fail := by
  rcases hinner with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G remaining piece
            (NodeSet.diff remaining piece) current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G remaining piece
            (NodeSet.diff remaining piece) current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      exact ⟨n,
        identifyFuel_eq_failed_of_shrink n G remaining piece
          (NodeSet.diff remaining piece) current hex hkept hsucc⟩

/--
A product-piece ancestral shrink whose nested remaining set then
product-splits unpacks as an ID run on one free c-component of that
ancestral set, with action `An(piece) \ subpiece`.  The original
remaining set is arbitrary.
-/
theorem identifyFuel_eq_failed_of_product_piece_shrink_product
    (G : ObservedGraph S)
    (remaining piece : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff remaining piece) remaining) =
          false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff remaining piece) remaining))
          (NodeSet.inter piece remaining))
        remaining = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff remaining piece)
          (G.ancestralSet remaining
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff remaining piece) remaining))
            (NodeSet.inter piece remaining))) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet remaining
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff remaining piece) remaining))
            (NodeSet.inter piece remaining))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff remaining piece)
              (G.ancestralSet remaining
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff remaining piece)
                    remaining))
                (NodeSet.inter piece remaining))))
          (NodeSet.inter piece
            (G.ancestralSet remaining
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff remaining piece)
                  remaining))
              (NodeSet.inter piece remaining))))
        (G.ancestralSet remaining
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff remaining piece) remaining))
          (NodeSet.inter piece remaining)) = true)
    (hfcN :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet remaining
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff remaining piece) remaining))
            (NodeSet.inter piece remaining))
          (NodeSet.inter (NodeSet.diff remaining piece)
            (G.ancestralSet remaining
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff remaining piece)
                  remaining))
              (NodeSet.inter piece remaining)))) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G remaining piece
          (NodeSet.diff remaining piece) current =
          IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G
            (G.ancestralSet remaining
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff remaining piece)
                  remaining))
              (NodeSet.inter piece remaining))
            subpiece
            (NodeSet.diff
              (G.ancestralSet remaining
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff remaining piece)
                    remaining))
                (NodeSet.inter piece remaining))
              subpiece)
            (.marginalize
              (NodeSet.diff remaining
                (G.ancestralSet remaining
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff remaining piece)
                      remaining))
                  (NodeSet.inter piece remaining)))
              current) =
            IdentificationOutcome.failed fail := by
  rcases identifyFuel_eq_failed_of_product_piece_shrink G remaining piece
      current hex hkept hinner with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G
            (G.ancestralSet remaining
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff remaining piece)
                  remaining))
              (NodeSet.inter piece remaining))
            piece (NodeSet.diff remaining piece)
            (.marginalize
              (NodeSet.diff remaining
                (G.ancestralSet remaining
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff remaining piece)
                      remaining))
                  (NodeSet.inter piece remaining)))
              current) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G
            (G.ancestralSet remaining
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff remaining piece)
                  remaining))
              (NodeSet.inter piece remaining))
            piece (NodeSet.diff remaining piece)
            (.marginalize
              (NodeSet.diff remaining
                (G.ancestralSet remaining
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff remaining piece)
                      remaining))
                  (NodeSet.inter piece remaining)))
              current) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      have hprod :=
        identifyFuel_eq_failed_of_product n G
          (G.ancestralSet remaining
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff remaining piece) remaining))
            (NodeSet.inter piece remaining))
          piece (NodeSet.diff remaining piece)
          (.marginalize
            (NodeSet.diff remaining
              (G.ancestralSet remaining
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff remaining piece)
                    remaining))
                (NodeSet.inter piece remaining)))
            current) hexN hkeptN hfcN hsucc
      rcases hprod with ⟨subpiece, hmemS, hEq⟩
      exact ⟨subpiece, hmemS, ⟨n, hEq⟩⟩

/--
A failed ID run whose remaining set is ancestral of the local outcome
and whose free side has at least two c-components unpacks as an ID run
on one of those pieces, with action `remaining \ piece`.  The remaining
set, local outcome, action, and current formula are arbitrary, so this
is the last step of any recorded product-nested fail.
-/
theorem identifyFuel_eq_failed_of_product_of
    (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex :
      NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        component :: component2 :: rest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G remaining outcome action current =
          IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G remaining piece
            (NodeSet.diff remaining piece) current =
            IdentificationOutcome.failed fail := by
  rcases hinner with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G remaining outcome action current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G remaining outcome action current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      have hprod :=
        identifyFuel_eq_failed_of_product n G remaining outcome action
          current hex hkept hfc hsucc
      rcases hprod with ⟨piece, hmemP, hEq⟩
      exact ⟨piece, hmemP, ⟨n, hEq⟩⟩

/--
A failed ID run whose remaining set is ancestral of the local outcome
and whose free side is a singleton c-component that is not itself a
c-component of the remaining graph unpacks as the ID run on the
containing c-component of that piece, with action
`(action ∩ remaining) ∩ larger`.  The remaining set, local outcome,
action, and current formula are arbitrary, so this is the last step of
any recorded 4.3-nested fail.
-/
theorem identifyFuel_eq_failed_of_restrict_of
    (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S} {component larger : NodeSet S}
    (hex :
      NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent remaining component = some larger)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G remaining outcome action current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger outcome
        (NodeSet.inter (NodeSet.inter action remaining) larger)
        (chainProduct remaining larger) =
        IdentificationOutcome.failed fail := by
  rcases hinner with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G remaining outcome action current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G remaining outcome action current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      exact ⟨n,
        identifyFuel_eq_failed_of_restrict n G remaining outcome action
          current hex hkept hfc hsingle hany hcont hsucc⟩

/--
A failed ID run whose remaining set is not ancestral of the local
outcome unpacks as the ID run on `An(outcome)` inside that remaining
set, with the same action and the complementary marginal of the current
formula.  The remaining set, local outcome, action, and current formula
are arbitrary, so this is the last step of any recorded ancestral-shrink
fail.
-/
theorem identifyFuel_eq_failed_of_shrink_of
    (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (hex :
      NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G remaining outcome action current =
          IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        outcome action
        (.marginalize
          (NodeSet.diff remaining
            (G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining)))
          current) =
        IdentificationOutcome.failed fail := by
  rcases hinner with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G remaining outcome action current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G remaining outcome action current =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      exact ⟨n,
        identifyFuel_eq_failed_of_shrink n G remaining outcome action
          current hex hkept hsucc⟩

/--
After a first ancestral shrink and nested product split, a further 4.3
restriction unpacks as the ID run on the containing c-component of the
failing piece inside the ancestral remaining set.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [piece])
    (hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        piece = some larger)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          piece
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            piece)
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S)) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger piece
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          larger)
        (chainProduct
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          larger) =
        IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action kept) = false by
          simpa [kept] using hexN) with ⟨i, hi⟩
    have hpair : q.action i = true ∧ kept i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept (NodeSet.inter q.action kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_restrict G kept piece
    (.marginalize
      (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
    (by simpa [kept] using hexP)
    (by simpa [kept] using hnestedKept)
    (by simpa [kept] using hnestedFc)
    (by simpa [kept] using hsingle)
    (by simpa [kept] using hany)
    (by simpa [kept] using hcont)
    (by simpa [kept] using hinner)

/--
A first ancestral shrink, nested product split, then 4.3 restriction
onto the containing c-component of the failing piece, with remaining
that host and free side the piece, yields a hedge for the original
query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [piece])
    (hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        piece = some larger)
    (hexH :
      NodeSet.isEmpty (NodeSet.inter q.action larger) = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          piece
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            piece)
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S)) =
          IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            fail.remaining)) = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action kept) = false by
          simpa [kept] using hexN) with ⟨i, hi⟩
    have hpair : q.action i = true ∧ kept i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept (NodeSet.inter q.action kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  have hrestricted :=
    identifyFuel_eq_failed_of_product_piece_restrict G kept piece
      (.marginalize
        (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
      hexP
      (by simpa [kept] using hnestedKept)
      (by simpa [kept] using hnestedFc)
      (by simpa [kept] using hsingle)
      (by simpa [kept] using hany)
      (by simpa [kept] using hcont)
      (by simpa [kept] using hinner)
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hsub : NodeSet.Subset piece larger :=
    (containingCComponent_spec G kept piece
      (by simpa [kept] using hcont)).2
  have hhost : NodeSet.Subset larger kept :=
    containingCComponent_subset_host G kept piece
      (by simpa [kept] using hcont)
  have hfreeEq :
      NodeSet.equal fail.free piece = true := by
    have hcut :
        NodeSet.diff larger
            (NodeSet.inter (NodeSet.diff kept piece) larger) =
          piece := by
      funext i
      cases hp : piece i with
      | true =>
          have hl : larger i = true := hsub i hp
          have hk : kept i = true := hhost i hl
          simp [NodeSet.diff, NodeSet.inter, hp, hl, hk]
      | false =>
          cases hl : larger i with
          | false =>
              simp [NodeSet.diff, NodeSet.inter, hp, hl]
          | true =>
              have hk : kept i = true := hhost i hl
              simp [NodeSet.diff, NodeSet.inter, hp, hl, hk]
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
    exact (NodeSet.equal_eq_true_iff _ _).mpr
      (hfreeR.trans (by simpa [heqR, kept] using hcut))
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)
            fail.remaining)) = true := by
    have hsame :
        NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff kept piece) kept)
              larger)
            fail.remaining =
          NodeSet.inter (NodeSet.diff kept piece) fail.remaining := by
      rw [heqR]
      funext i
      simp [NodeSet.inter, NodeSet.diff, Bool.and_assoc, Bool.and_left_comm,
        Bool.and_self]
    simpa [hsame, kept] using hfree
  rcases hrestricted with ⟨n, hn⟩
  have hancFree :=
    identifyFuel_eq_failed_query_of_remaining_eq n G larger piece
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff kept piece) kept)
        larger)
      (chainProduct kept larger) hn heq hfree'
  have hancFree' :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true := by
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
    simpa [hfreeR] using hancFree
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeI :
        NodeSet.diff kept (NodeSet.inter q.action kept) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, (NodeSet.equal_eq_true_iff _ _).mp
          hfreeEq] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfreeI
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree' hancY

/--
After a first ancestral shrink, nested product split, and 4.3
restriction, a further product split unpacks as an ID run on one free
c-component of that nested host, with action `larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [piece])
    (hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        piece = some larger)
    (hexL :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          larger) = false)
    (hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.diff
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)
                  piece)
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              larger))
          (NodeSet.inter piece larger))
        larger = true)
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
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          piece
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            piece)
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S)) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ inner :: inner2 :: innerRest ∧
        Exists fun n =>
          Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
            (chainProduct
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              larger) =
            IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action kept) = false by
          simpa [kept] using hexN) with ⟨i, hi⟩
    have hpair : q.action i = true ∧ kept i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept (NodeSet.inter q.action kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_restrict_product G kept
    piece
    (.marginalize
      (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
    hexP
    (by simpa [kept] using hnestedKept)
    (by simpa [kept] using hnestedFc)
    (by simpa [kept] using hsingle)
    (by simpa [kept] using hany)
    (by simpa [kept] using hcont)
    (by simpa [kept] using hexL)
    (by simpa [kept] using hkeptL)
    (by simpa [kept] using hfcL)
    (by simpa [kept] using hinner)

/--
A first ancestral shrink, nested product, 4.3 restriction, then a
further product split, with remaining the nested host and free side the
failing subpiece, yields a hedge for the original query once that host
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_restrict_product
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
    (_hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (_hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (_hnestedFc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [piece])
    (_hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (_hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c piece) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        piece = some larger)
    (hexH :
      NodeSet.isEmpty (NodeSet.inter q.action larger) = false)
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
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
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
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink and nested product split, a further
ancestral shrink unpacks as the ID run on `An(piece)` inside that
ancestral remaining set, with action `kept \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          piece
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            piece)
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S)) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
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
        piece
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          piece)
        (.marginalize
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
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
                  q.outcome))))
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S))) =
        IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action kept) = false by
          simpa [kept] using hexN) with ⟨i, hi⟩
    have hpair : q.action i = true ∧ kept i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept (NodeSet.inter q.action kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_shrink G kept piece
    (.marginalize
      (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
    hexP
    (by simpa [kept] using hnestedKept)
    (by simpa [kept] using hinner)

/--
A first ancestral shrink, nested product split, then ancestral shrink
of that piece, with remaining `An(piece)` inside the first ancestral
set and free side the piece, yields a hedge for the original query once
that smaller remaining set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.diff
                  (G.ancestralSet NodeSet.full
                    (GraphMutilation.bar q.action) q.outcome)
                  piece)
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)))
            (NodeSet.inter piece
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))) = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          piece
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            piece)
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S)) =
          IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
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
              q.outcome))) = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              piece)
            fail.remaining)) = true)
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action kept) = false by
          simpa [kept] using hexN) with ⟨i, hi⟩
    have hpair : q.action i = true ∧ kept i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisjP : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept (NodeSet.inter q.action kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisjP i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  have hrestricted :=
    identifyFuel_eq_failed_of_product_piece_shrink G kept piece
      (.marginalize
        (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
      hexP
      (by simpa [kept] using hnestedKept)
      (by simpa [kept] using hinner)
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpieceSub : NodeSet.Subset piece kept :=
    NodeSet.Subset.trans
      (cComponents_subset G _ hmem')
      (NodeSet.diff_subset_left _ _)
  have hfreeEq :
      NodeSet.equal fail.free piece = true := by
    have hcut :
        NodeSet.diff fail.remaining
            (NodeSet.inter (NodeSet.diff kept piece) fail.remaining) =
          piece := by
      funext i
      have hAn : fail.remaining i = nestedAn i := by
        simpa [nestedAn, kept] using
          (congrArg (fun s => s i) heqR)
      cases hp : piece i with
      | true =>
          have hk : kept i = true := hpieceSub i hp
          have htargets : NodeSet.inter piece kept i = true := by
            simp [NodeSet.inter, hp, hk]
          have hrem : fail.remaining i = true := by
            rw [hAn]
            exact ancestralSet_contains_targets G kept
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff kept piece) kept))
              (NodeSet.inter piece kept) hk htargets
          simp [NodeSet.diff, NodeSet.inter, hp, hrem]
      | false =>
          cases hr : fail.remaining i with
          | false =>
              simp [NodeSet.diff, NodeSet.inter, hp, hr]
          | true =>
              have hk : kept i = true :=
                ancestralSet_subset G kept
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff kept piece) kept))
                  (NodeSet.inter piece kept) i (by
                    simpa [nestedAn, hAn] using hr)
              simp [NodeSet.diff, NodeSet.inter, hp, hr, hk]
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
    exact (NodeSet.equal_eq_true_iff _ _).mpr
      (hfreeR.trans (by simpa [kept] using hcut))
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff kept piece) fail.remaining)) =
        true := by
    simpa [kept] using hfree
  rcases hrestricted with ⟨n, hn⟩
  have hancFree :=
    identifyFuel_eq_failed_query_of_remaining_eq n G nestedAn piece
      (NodeSet.diff kept piece)
      (.marginalize
        (NodeSet.diff kept nestedAn)
        (.marginalize
          (NodeSet.diff NodeSet.full kept) (observationalJointTerm S)))
      (by simpa [nestedAn, kept] using hn) (by simpa [nestedAn, kept] using heq)
      hfree'
  have hancFree' :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true := by
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
    simpa [hfreeR] using hancFree
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeI :
        NodeSet.diff kept (NodeSet.inter q.action kept) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, (NodeSet.equal_eq_true_iff _ _).mp
          hfreeEq] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfreeI
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action nestedAn) = false by
          simpa [nestedAn, kept] using hexK) with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, nestedAn, kept, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree' hancY

/--
After a first ancestral shrink, nested product split, and ancestral
shrink of that piece, a further product split unpacks as an ID run on
one free c-component of `An(piece)`, with action `An(piece) \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_product_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hexP2 :
      NodeSet.isEmpty
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
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)
                  piece)
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)))
            (NodeSet.inter piece
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))) = false)
    (hkeptP :
      NodeSet.equal
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
                    q.outcome)))))
          (NodeSet.inter piece
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
              q.outcome))) = true)
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
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          piece
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            piece)
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S)) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ inner :: inner2 :: innerRest ∧
        Exists fun n =>
          Legacy.identifyFuel n G
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
                  q.outcome)))
            subpiece
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
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome)))
              subpiece)
            (.marginalize
              (NodeSet.diff
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome)
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
                      (GraphMutilation.bar q.action) q.outcome))))
              (.marginalize
                (NodeSet.diff NodeSet.full
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome))
                (observationalJointTerm S))) =
            IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action kept) = false by
          simpa [kept] using hexN) with ⟨i, hi⟩
    have hpair : q.action i = true ∧ kept i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept (NodeSet.inter q.action kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_shrink_product G kept piece
    (.marginalize
      (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
    hexP
    (by simpa [kept] using hnestedKept)
    (by simpa [kept] using hexP2)
    (by simpa [kept] using hkeptP)
    (by simpa [kept] using hfcP)
    (by simpa [kept] using hinner)

/--
A first ancestral shrink, nested product, ancestral shrink of that
piece, then a further product split, with remaining `An(piece)` and
free side the failing subpiece, yields a hedge for the original query
once that ancestral set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_product_shrink_product
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
    (_hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
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
    (_hnestedKept :
      NodeSet.equal
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
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter q.action
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
                q.outcome)))) = false)
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
    (heq :
      NodeSet.equal fail.remaining
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
              q.outcome))) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
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
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
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
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action nestedAn) = false by
          simpa [nestedAn, kept] using hexK) with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, nestedAn, kept, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, a nested 4.3 restriction unpacks as the
ID run on the containing c-component of the ancestral remaining set,
with action `X ∩ host`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun piece => NodeSet.equal piece seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G host q.outcome
        (NodeSet.inter
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          host)
        (chainProduct
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          host) =
        IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  have hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G kept
          q.outcome q.action
          (.marginalize
            (NodeSet.diff NodeSet.full kept) (observationalJointTerm S)) =
        IdentificationOutcome.failed fail :=
    identifyJoint_eq_failed_of_first_shrink G q hex hkept hfail
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G kept q.outcome q.action
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G kept q.outcome q.action
            (.marginalize
              (NodeSet.diff NodeSet.full kept)
              (observationalJointTerm S)) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      refine ⟨n, ?_⟩
      simpa [kept] using
        identifyFuel_eq_failed_of_restrict n G kept q.outcome q.action
          (.marginalize
            (NodeSet.diff NodeSet.full kept) (observationalJointTerm S))
          hexN hkeptN hfc hsingle hany hcont hsucc

/--
A first ancestral shrink whose nested call then 4.3-restricts, with
remaining the containing host and free side `host \ X`, yields a hedge
for the original query.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hfc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun piece => NodeSet.equal piece seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining host = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hhost :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) :=
    containingCComponent_subset_host G _ _ hcont
  have hlocal :
      NodeSet.inter
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)
          fail.remaining =
        NodeSet.inter q.action fail.remaining := by
    rw [heqR]
    funext i
    cases hh : host i with
    | false =>
        simp [NodeSet.inter, hh]
    | true =>
        have hkeptI :
            G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome i = true :=
          hhost i hh
        simp [NodeSet.inter, hh, hkeptI]
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host)
            fail.remaining)) = true := by
    simpa [hlocal] using hfree
  rcases identifyJoint_eq_failed_of_first_shrink_restrict G q hex hkept
      hexN hkeptN hfc hsingle hany hcont hfail with ⟨n, hn⟩
  exact hedgeWitness?_eq_some_of_failed_local_action G q hfail hfree
    (identifyFuel_eq_failed_query_of_remaining_eq n G host q.outcome
      (NodeSet.inter
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome))
        host)
      (chainProduct
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        host)
      hn heq hfree')

/--
After a first ancestral shrink and nested 4.3 restriction, a further
product split unpacks as an ID run on one free c-component of the
containing host, with action `host \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (hfc0 :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun piece => NodeSet.equal piece seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (hexH :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          host) = false)
    (hkeptH :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) =
        component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
            (chainProduct
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              host) =
            IdentificationOutcome.failed fail := by
  rcases identifyJoint_eq_failed_of_first_shrink_restrict G q hex hkept
      hexN hkeptN hfc0 hsingle hany hcont hfail with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G host q.outcome
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host)
            (chainProduct
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              host) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G host q.outcome
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host)
            (chainProduct
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)
              host) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        exact hm
      have hinter :
          NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter q.action
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome))
                host)
              host =
            NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host := by
        funext i
        simp [NodeSet.inter]
      have hexH' :
          NodeSet.isEmpty
            (NodeSet.inter
              (NodeSet.inter
                (NodeSet.inter q.action
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome))
                host)
              host) = false := by
        simpa [hinter] using hexH
      have hkeptH' :
          NodeSet.equal
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.inter
                    (NodeSet.inter q.action
                      (G.ancestralSet NodeSet.full
                        (GraphMutilation.bar q.action)
                        q.outcome))
                    host)
                  host))
              (NodeSet.inter q.outcome host))
            host = true := by
        simpa [hinter] using hkeptH
      have hfc' :
          G.cComponents
            (NodeSet.diff host
              (NodeSet.inter
                (NodeSet.inter
                  (NodeSet.inter q.action
                    (G.ancestralSet NodeSet.full
                      (GraphMutilation.bar q.action)
                      q.outcome))
                  host)
                host)) =
            component :: component2 :: rest := by
        simpa [hinter] using hfc
      have hprod :=
        identifyFuel_eq_failed_of_product n G host q.outcome
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)
          (chainProduct
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            host)
          hexH' hkeptH' hfc' hsucc
      rcases hprod with ⟨piece, hmem, hEq⟩
      exact ⟨piece, hmem, ⟨n, hEq⟩⟩

/--
A first ancestral shrink, nested 4.3 restriction, then product split,
with remaining the containing host and free side the failing piece,
yields a hedge for the original query once that host meets `X` and is
ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (_hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (_hfc0 :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (_hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (_hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (hexH :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          host) = false)
    (_hkeptH :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host))
          (NodeSet.inter q.outcome host))
        host = true)
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
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining host = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) := by
    rw [hfc]
    exact hmem
  have hhost :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) :=
    containingCComponent_subset_host G _ _ hcont
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host) i = true :=
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
            have hk :
                G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome i = true :=
              hhost i hh
            simp [hh, hk] at hfree
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    simp [NodeSet.inter] at hi
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR] using hi.2
    · exact hi.1.1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, and nested
product split, a further 4.3 restriction unpacks as the ID run on the
containing c-component of the failing piece inside that first host,
with action `(host \ piece) ∩ larger`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (_hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (_hfc0 :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (_hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (_hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (hexH :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          host) = false)
    (_hkeptH :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host))
          (NodeSet.inter q.outcome host))
        host = true)
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
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.diff host piece) host)) =
        [piece])
    (hsingleH : G.isSingleCComponent host = false)
    (hanyH :
      (G.cComponents host).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontH :
      G.containingCComponent host piece = some larger)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            host) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff host piece) host) larger)
        (chainProduct host larger) =
        IdentificationOutcome.failed fail := by
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) := by
    rw [hfc]
    exact hmem
  have hhost :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) :=
    containingCComponent_subset_host G _ _ hcont
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    simp [NodeSet.inter] at hi
    have hpair : q.action i = true ∧ host i = true :=
      ⟨hi.1.1, hi.2⟩
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host
              (NodeSet.inter
                (NodeSet.inter q.action
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome))
                host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ
            cases hh : host j with
            | false =>
                simp [hh] at hfreeJ
            | true =>
                have hk :
                    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                      q.outcome j = true :=
                  hhost j hh
                simp [hh, hk] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_restrict G host piece
    (chainProduct
      (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
        q.outcome)
      host)
    hexP hnestedKept hnestedFc hsingleH hanyH hcontH hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
then 4.3 onto the containing c-component of the failing piece, with
remaining that nested host and free side the piece, yields a hedge for
the original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (_hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (_hfc0 :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (_hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (_hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (_hexH :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          host) = false)
    (_hkeptH :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host))
          (NodeSet.inter q.outcome host))
        host = true)
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
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = true)
    (_hnestedFc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.diff host piece) host)) =
        [piece])
    (_hsingleH : G.isSingleCComponent host = false)
    (_hanyH :
      (G.cComponents host).any
        (fun c => NodeSet.equal c piece) = false)
    (_hcontH :
      G.containingCComponent host piece = some larger)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action larger) = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) := by
    rw [hfc]
    exact hmem
  have hhost :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) :=
    containingCComponent_subset_host G _ _ hcont
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host) i = true :=
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
            have hk :
                G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome i = true :=
              hhost i hh
            simp [hh, hk] at hfree
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first ancestral shrink, nested 4.3 restriction, and nested
product split, a further ancestral shrink unpacks as the ID run on
`An(piece)` inside that first host, with action `host \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_shrink_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (_hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (_hfc0 :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (_hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (_hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (hexH :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          host) = false)
    (_hkeptH :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host))
          (NodeSet.inter q.outcome host))
        host = true)
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
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            host) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        piece (NodeSet.diff host piece)
        (.marginalize
          (NodeSet.diff host
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) host))
              (NodeSet.inter piece host)))
          (chainProduct
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            host)) =
        IdentificationOutcome.failed fail := by
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) := by
    rw [hfc]
    exact hmem
  have hhost :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) :=
    containingCComponent_subset_host G _ _ hcont
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    simp [NodeSet.inter] at hi
    have hpair : q.action i = true ∧ host i = true :=
      ⟨hi.1.1, hi.2⟩
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host
              (NodeSet.inter
                (NodeSet.inter q.action
                  (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                    q.outcome))
                host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ
            cases hh : host j with
            | false =>
                simp [hh] at hfreeJ
            | true =>
                have hk :
                    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                      q.outcome j = true :=
                  hhost j hh
                simp [hh, hk] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_shrink G host piece
    (chainProduct
      (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
        q.outcome)
      host)
    hexP hnestedKept hinner

/--
A first ancestral shrink, nested 4.3 restriction, nested product split,
then ancestral shrink of that piece, with remaining `An(piece)` inside
the first host and free side the piece, yields a hedge for the original
query once that ancestral set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_shrink_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (_hexN :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (GraphMutilation.bar
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = true)
    (_hfc0 :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))) =
        [seed])
    (_hsingle :
      G.isSingleCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) = false)
    (_hany :
      (G.cComponents
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)).any
        (fun c => NodeSet.equal c seed) = false)
    (hcont :
      G.containingCComponent
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        seed = some host)
    (_hexH :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter q.action
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          host) = false)
    (_hkeptH :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter q.action
                (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome))
              host))
          (NodeSet.inter q.outcome host))
        host = true)
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
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet host
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff host piece) host))
            (NodeSet.inter piece host))) = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host)) = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let nestedAn :=
    G.ancestralSet host
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff host piece) host))
      (NodeSet.inter piece host)
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host)) := by
    rw [hfc]
    exact hmem
  have hhost :
      NodeSet.Subset host
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) :=
    containingCComponent_subset_host G _ _ hcont
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host
          (NodeSet.inter
            (NodeSet.inter q.action
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            host) i = true :=
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
            have hk :
                G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                  q.outcome i = true :=
              hhost i hh
            simp [hh, hk] at hfree
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action nestedAn) = false by
          simpa [nestedAn] using hexK) with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, nestedAn, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, the nested ID run is the original outcome
on the containing c-component, with action `X ∩ larger`.
-/
theorem identifyJoint_eq_failed_of_first_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {component larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [component])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent NodeSet.full component = some larger)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Legacy.identifyFuel
        (S.count * Nat.succ S.count * Nat.succ S.count) G larger
        q.outcome (NodeSet.inter q.action larger)
        (chainProduct NodeSet.full larger) =
      IdentificationOutcome.failed fail := by
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
        [component] := by
    simpa [hinter] using hfc
  have hfuel :
      Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome
        q.action (observationalJointTerm S) =
        IdentificationOutcome.failed fail := hfail
  rw [identificationFuel] at hfuel
  have hnested :=
    identifyFuel_eq_failed_of_restrict
      (S.count * Nat.succ S.count * Nat.succ S.count) G NodeSet.full
      q.outcome q.action (observationalJointTerm S) hex' hkept' hfc'
      hsingle hany hcont hfuel
  simpa [hinter] using hnested

/--
A 4.3 restriction whose fail remaining is the containing c-component, with
free side `larger \ X`, yields a hedge witness for the original query.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {component larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [component])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent NodeSet.full component = some larger)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.inter q.action larger) fail.remaining)) =
        true := by
    have hsame :
        NodeSet.inter (NodeSet.inter q.action larger) fail.remaining =
          NodeSet.inter q.action fail.remaining := by
      rw [heqR]
      funext i
      simp [NodeSet.inter]
    simpa [hsame] using hfree
  exact hedgeWitness?_eq_some_of_failed_local_action G q hfail hfree
    (identifyFuel_eq_failed_query_of_remaining_eq
      (S.count * Nat.succ S.count * Nat.succ S.count) G larger
      q.outcome (NodeSet.inter q.action larger)
      (chainProduct NodeSet.full larger)
      (identifyJoint_eq_failed_of_first_restrict G q hex hkept hfc
        hsingle hany hcont hfail)
      heq hfree')

/--
After a first 4.3 restriction, a nested product split unpacks as an ID
run on one free c-component of the containing host, with action
`larger \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {seed : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece seed) = false)
    (hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
            (chainProduct NodeSet.full host) =
            IdentificationOutcome.failed fail := by
  have hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G host
          q.outcome (NodeSet.inter q.action host)
          (chainProduct NodeSet.full host) =
        IdentificationOutcome.failed fail :=
    identifyJoint_eq_failed_of_first_restrict G q hex hkept hfc0
      hsingle hany hcont hfail
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G host q.outcome (NodeSet.inter q.action host)
            (chainProduct NodeSet.full host) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G host q.outcome
            (NodeSet.inter q.action host)
            (chainProduct NodeSet.full host) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have hinter :
          NodeSet.inter (NodeSet.inter q.action host) host =
            NodeSet.inter q.action host := by
        funext i
        simp [NodeSet.inter]
      have hexL' :
          NodeSet.isEmpty
            (NodeSet.inter (NodeSet.inter q.action host) host) =
            false := by
        simpa [hinter] using hexL
      have hkeptN' :
          NodeSet.equal
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.inter q.action host) host))
              (NodeSet.inter q.outcome host))
            host = true := by
        simpa [hinter] using hkeptN
      have hfc' :
          G.cComponents
            (NodeSet.diff host
              (NodeSet.inter (NodeSet.inter q.action host) host)) =
            component :: component2 :: rest := by
        simpa [hinter] using hfc
      have hprod :=
        identifyFuel_eq_failed_of_product n G host q.outcome
          (NodeSet.inter q.action host)
          (chainProduct NodeSet.full host) hexL' hkeptN' hfc' hsucc
      rcases hprod with ⟨piece, hmem, hEq⟩
      exact ⟨piece, hmem, ⟨n, hEq⟩⟩

/--
A first 4.3 restriction whose nested call then product-splits, with free
side the failing piece of the containing host, yields a hedge for the
original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {seed piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining host = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    have hfc' :
        G.cComponents
          (NodeSet.diff host (NodeSet.inter q.action host)) =
          component :: component2 :: rest := hfc
    rw [hfc']
    exact hmem
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfree :
        NodeSet.diff host (NodeSet.inter q.action host) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, hpiece] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction and nested product split, a further 4.3
restriction unpacks as the ID run on the containing c-component of the
failing piece inside that first host, with action
`(host \ piece) ∩ larger`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {seed piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.diff host piece) host)) =
        [piece])
    (hsingleH : G.isSingleCComponent host = false)
    (hanyH :
      (G.cComponents host).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontH :
      G.containingCComponent host piece = some larger)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct NodeSet.full host) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger piece
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff host piece) host) larger)
        (chainProduct host larger) =
        IdentificationOutcome.failed fail := by
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    have hpair : q.action i = true ∧ host i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host (NodeSet.inter q.action host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_restrict G host piece
    (chainProduct NodeSet.full host) hexP hnestedKept hnestedFc
    hsingleH hanyH hcontH hinner

/--
A first 4.3 restriction, nested product split, then 4.3 restriction
onto the containing c-component of the failing piece, with remaining
that nested host and free side the piece, yields a hedge for the
original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {seed piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.diff host piece) host)) =
        [piece])
    (hsingleH : G.isSingleCComponent host = false)
    (hanyH :
      (G.cComponents host).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontH :
      G.containingCComponent host piece = some larger)
    (hexH :
      NodeSet.isEmpty (NodeSet.inter q.action larger) = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct NodeSet.full host) =
          IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff host piece) fail.remaining)) =
        true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    have hpair : q.action i = true ∧ host i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisjP : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host (NodeSet.inter q.action host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisjP i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  have hrestricted :=
    identifyFuel_eq_failed_of_product_piece_restrict G host piece
      (chainProduct NodeSet.full host) hexP hnestedKept hnestedFc
      hsingleH hanyH hcontH hinner
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hsub : NodeSet.Subset piece larger :=
    (containingCComponent_spec G host piece hcontH).2
  have hhostS : NodeSet.Subset larger host :=
    containingCComponent_subset_host G host piece hcontH
  have hfreeEq :
      NodeSet.equal fail.free piece = true := by
    have hcut :
        NodeSet.diff larger
            (NodeSet.inter (NodeSet.diff host piece) larger) =
          piece := by
      funext i
      cases hp : piece i with
      | true =>
          have hl : larger i = true := hsub i hp
          have hk : host i = true := hhostS i hl
          simp [NodeSet.diff, NodeSet.inter, hp, hl, hk]
      | false =>
          cases hl : larger i with
          | false =>
              simp [NodeSet.diff, NodeSet.inter, hp, hl]
          | true =>
              have hk : host i = true := hhostS i hl
              simp [NodeSet.diff, NodeSet.inter, hp, hl, hk]
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
    exact (NodeSet.equal_eq_true_iff _ _).mpr (hfreeR.trans (by
      simpa [heqR] using hcut))
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            fail.remaining)) = true := by
    have hsame :
        NodeSet.inter
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger)
            fail.remaining =
          NodeSet.inter (NodeSet.diff host piece) fail.remaining := by
      rw [heqR]
      funext i
      simp [NodeSet.inter, NodeSet.diff, Bool.and_assoc, Bool.and_left_comm]
    simpa [hsame] using hfree
  rcases hrestricted with ⟨n, hn⟩
  have hancFree :=
    identifyFuel_eq_failed_query_of_remaining_eq n G larger piece
      (NodeSet.inter
        (NodeSet.inter (NodeSet.diff host piece) host)
        larger)
      (chainProduct host larger) hn heq hfree'
  have hancFree' :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true := by
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
    simpa [hfreeR] using hancFree
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeI :
        NodeSet.diff host (NodeSet.inter q.action host) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, (NodeSet.equal_eq_true_iff _ _).mp
          hfreeEq] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfreeI
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree' hancY

/--
After a first 4.3 restriction, nested product split, and nested 4.3
restriction, a further product split unpacks as an ID run on one free
c-component of that nested host, with action `larger \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {seed piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.diff host piece) host)) =
        [piece])
    (hsingleH : G.isSingleCComponent host = false)
    (hanyH :
      (G.cComponents host).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontH :
      G.containingCComponent host piece = some larger)
    (hexN :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.diff host piece) host) larger) =
          false)
    (hkeptL :
      NodeSet.equal
        (G.ancestralSet larger
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.inter (NodeSet.diff host piece) host)
              larger))
          (NodeSet.inter piece larger))
        larger = true)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)) =
        inner :: inner2 :: innerRest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct NodeSet.full host) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ inner :: inner2 :: innerRest ∧
        Exists fun n =>
          Legacy.identifyFuel n G larger subpiece (NodeSet.diff larger subpiece)
            (chainProduct host larger) =
            IdentificationOutcome.failed fail := by
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    have hpair : q.action i = true ∧ host i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host (NodeSet.inter q.action host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_restrict_product G host
    piece (chainProduct NodeSet.full host) hexP hnestedKept hnestedFc
    hsingleH hanyH hcontH hexN hkeptL hfcL hinner

/--
A first 4.3 restriction, nested product, nested 4.3 restriction, then a
further product split, with remaining the nested host and free side the
failing subpiece, yields a hedge for the original query once that host
meets `X` and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_restrict_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {seed piece larger subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (_hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = true)
    (_hnestedFc :
      G.cComponents
        (NodeSet.diff host
          (NodeSet.inter (NodeSet.diff host piece) host)) =
        [piece])
    (_hsingleH : G.isSingleCComponent host = false)
    (_hanyH :
      (G.cComponents host).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontH :
      G.containingCComponent host piece = some larger)
    (hexH :
      NodeSet.isEmpty (NodeSet.inter q.action larger) = false)
    (hfcL :
      G.cComponents
        (NodeSet.diff larger
          (NodeSet.inter
            (NodeSet.inter (NodeSet.diff host piece) host)
            larger)) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
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
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction and nested product split, a further
ancestral shrink unpacks as the ID run on `An(piece)` inside that
first host, with action `host \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {seed piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct NodeSet.full host) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        piece (NodeSet.diff host piece)
        (.marginalize
          (NodeSet.diff host
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) host))
              (NodeSet.inter piece host)))
          (chainProduct NodeSet.full host)) =
        IdentificationOutcome.failed fail := by
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    have hpair : q.action i = true ∧ host i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host (NodeSet.inter q.action host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_shrink G host piece
    (chainProduct NodeSet.full host) hexP hnestedKept hinner

/--
A first 4.3 restriction, nested product split, then ancestral shrink
of that piece, with remaining `An(piece)` inside the first host and
free side the piece, yields a hedge for the original query once that
smaller remaining set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {seed piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet host
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff host piece) host))
            (NodeSet.inter piece host))) = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct NodeSet.full host) =
          IdentificationOutcome.failed fail)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host)) = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff host piece) fail.remaining)) =
        true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let nestedAn :=
    G.ancestralSet host
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff host piece) host))
      (NodeSet.inter piece host)
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    have hpair : q.action i = true ∧ host i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisjP : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host (NodeSet.inter q.action host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisjP i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  have hrestricted :=
    identifyFuel_eq_failed_of_product_piece_shrink G host piece
      (chainProduct NodeSet.full host) hexP hnestedKept hinner
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpieceSub : NodeSet.Subset piece host :=
    NodeSet.Subset.trans
      (cComponents_subset G _ hmem')
      (NodeSet.diff_subset_left _ _)
  have hfreeEq :
      NodeSet.equal fail.free piece = true := by
    have hcut :
        NodeSet.diff fail.remaining
            (NodeSet.inter (NodeSet.diff host piece) fail.remaining) =
          piece := by
      funext i
      have hAn : fail.remaining i = nestedAn i :=
        congrArg (fun s => s i) heqR
      cases hp : piece i with
      | true =>
          have hk : host i = true := hpieceSub i hp
          have htargets : NodeSet.inter piece host i = true := by
            simp [NodeSet.inter, hp, hk]
          have hrem : fail.remaining i = true := by
            rw [hAn]
            exact ancestralSet_contains_targets G host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) host))
              (NodeSet.inter piece host) hk htargets
          simp [NodeSet.diff, NodeSet.inter, hp, hrem]
      | false =>
          cases hr : fail.remaining i with
          | false =>
              simp [NodeSet.diff, NodeSet.inter, hp, hr]
          | true =>
              have hk : host i = true :=
                ancestralSet_subset G host
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff host piece) host))
                  (NodeSet.inter piece host) i (by
                    simpa [nestedAn, hAn] using hr)
              simp [NodeSet.diff, NodeSet.inter, hp, hr, hk]
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfree
    exact (NodeSet.equal_eq_true_iff _ _).mpr (hfreeR.trans hcut)
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff host piece) fail.remaining)) =
        true :=
    hfree
  rcases hrestricted with ⟨n, hn⟩
  have hancFree :=
    identifyFuel_eq_failed_query_of_remaining_eq n G nestedAn piece
      (NodeSet.diff host piece)
      (.marginalize
        (NodeSet.diff host nestedAn)
        (chainProduct NodeSet.full host))
      (by simpa [nestedAn] using hn)
      (by simpa [nestedAn] using heq) hfree'
  have hancFree' :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true := by
    have hfreeR := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
    simpa [hfreeR] using hancFree
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeI :
        NodeSet.diff host (NodeSet.inter q.action host) i = true :=
      cComponents_subset G _ hmem' i (by
        simpa [failedHedgeSelection, (NodeSet.equal_eq_true_iff _ _).mp
          hfreeEq] using hi)
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfreeI
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action nestedAn) = false by
          simpa [nestedAn] using hexK) with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, nestedAn, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree' hancY

/--
After a first 4.3 restriction, nested product split, and ancestral
shrink of that piece, a further product split unpacks as an ID run on
one free c-component of `An(piece)`, with action `An(piece) \ subpiece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_product_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {seed piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = false)
    (hexP2 :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece)
          (G.ancestralSet host
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff host piece) host))
            (NodeSet.inter piece host))) = false)
    (hkeptP :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff host piece) host))
            (NodeSet.inter piece host))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece)
              (G.ancestralSet host
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff host piece) host))
                (NodeSet.inter piece host))))
          (NodeSet.inter piece
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) host))
              (NodeSet.inter piece host))))
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host)) = true)
    (hfcP :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff host piece) host))
            (NodeSet.inter piece host))
          (NodeSet.inter (NodeSet.diff host piece)
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) host))
              (NodeSet.inter piece host)))) =
        inner :: inner2 :: innerRest)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G host piece (NodeSet.diff host piece)
          (chainProduct NodeSet.full host) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun subpiece =>
      subpiece ∈ inner :: inner2 :: innerRest ∧
        Exists fun n =>
          Legacy.identifyFuel n G
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) host))
              (NodeSet.inter piece host))
            subpiece
            (NodeSet.diff
              (G.ancestralSet host
                (GraphMutilation.bar
                  (NodeSet.inter (NodeSet.diff host piece) host))
                (NodeSet.inter piece host))
              subpiece)
            (.marginalize
              (NodeSet.diff host
                (G.ancestralSet host
                  (GraphMutilation.bar
                    (NodeSet.inter (NodeSet.diff host piece) host))
                  (NodeSet.inter piece host)))
              (chainProduct NodeSet.full host)) =
            IdentificationOutcome.failed fail := by
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff host piece) host) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexL with ⟨i, hi⟩
    have hpair : q.action i = true ∧ host i = true :=
      Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff host (NodeSet.inter q.action host) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_shrink_product G host piece
    (chainProduct NodeSet.full host) hexP hnestedKept hexP2 hkeptP hfcP
    hinner

/--
A first 4.3 restriction, nested product, ancestral shrink of that
piece, then a further product split, with remaining `An(piece)` and
free side the failing subpiece, yields a hedge for the original query
once that ancestral set meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_product_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {inner inner2 : NodeSet S} {innerRest : List (NodeSet S)}
    {seed piece subpiece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (_hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hkeptN :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = true)
    (hfc :
      G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) =
        component :: component2 :: rest)
    (hmem : piece ∈ component :: component2 :: rest)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host))
        host = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet host
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff host piece) host))
            (NodeSet.inter piece host))) = false)
    (hfcP :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar
              (NodeSet.inter (NodeSet.diff host piece) host))
            (NodeSet.inter piece host))
          (NodeSet.inter (NodeSet.diff host piece)
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.diff host piece) host))
              (NodeSet.inter piece host)))) =
        inner :: inner2 :: innerRest)
    (hmemS : subpiece ∈ inner :: inner2 :: innerRest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet host
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.diff host piece) host))
          (NodeSet.inter piece host)) = true)
    (hfreeEq : NodeSet.equal fail.free subpiece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let nestedAn :=
    G.ancestralSet host
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff host piece) host))
      (NodeSet.inter piece host)
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hpiece := (NodeSet.equal_eq_true_iff _ _).mp hfreeEq
  have hmem' :
      piece ∈ G.cComponents
        (NodeSet.diff host (NodeSet.inter q.action host)) := by
    rw [hfc]
    exact hmem
  have hmemS' :
      subpiece ∈ G.cComponents
        (NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn)) := by
    have hfcP' :
        G.cComponents
          (NodeSet.diff nestedAn
            (NodeSet.inter (NodeSet.diff host piece) nestedAn)) =
          inner :: inner2 :: innerRest := by
      simpa [nestedAn] using hfcP
    rw [hfcP']
    exact hmemS
  have hhost : NodeSet.Subset nestedAn host :=
    ancestralSet_subset G host
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff host piece) host))
      (NodeSet.inter piece host)
  have hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hi
    have hfreeS :
        NodeSet.diff nestedAn
          (NodeSet.inter (NodeSet.diff host piece) nestedAn) i = true :=
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
                  NodeSet.diff host (NodeSet.inter q.action host) i =
                    true :=
                cComponents_subset G _ hmem' i hp
              simp [NodeSet.diff, NodeSet.inter, ha] at hfreeP
        simp [NodeSet.diff, NodeSet.inter, hpieceA] at hfreeS
        cases hl : nestedAn i with
        | false =>
            simp [hl] at hfreeS
        | true =>
            have hk : host i = true := hhost i hl
            simp [hl, hk] at hfreeS
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action nestedAn) = false by
          simpa [nestedAn] using hexK) with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, nestedAn, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, a nested ancestral shrink unpacks as the
ID run on `An(Y)` inside the containing host, with action `X ∩ host`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece seed) = false)
    (hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        q.outcome (NodeSet.inter q.action host)
        (.marginalize
          (NodeSet.diff host
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))
          (chainProduct NodeSet.full host)) =
        IdentificationOutcome.failed fail := by
  have hnested :
      Legacy.identifyFuel
          (S.count * Nat.succ S.count * Nat.succ S.count) G host
          q.outcome (NodeSet.inter q.action host)
          (chainProduct NodeSet.full host) =
        IdentificationOutcome.failed fail :=
    identifyJoint_eq_failed_of_first_restrict G q hex hkept hfc0
      hsingle hany hcont hfail
  cases hn : S.count * Nat.succ S.count * Nat.succ S.count with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G host q.outcome (NodeSet.inter q.action host)
            (chainProduct NodeSet.full host) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G host q.outcome
            (NodeSet.inter q.action host)
            (chainProduct NodeSet.full host) =
            IdentificationOutcome.failed fail := by
        rw [← hn]
        exact hnested
      have hinter :
          NodeSet.inter (NodeSet.inter q.action host) host =
            NodeSet.inter q.action host := by
        funext i
        simp [NodeSet.inter]
      have hexL' :
          NodeSet.isEmpty
            (NodeSet.inter (NodeSet.inter q.action host) host) =
            false := by
        simpa [hinter] using hexL
      have hkeptN' :
          NodeSet.equal
            (G.ancestralSet host
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.inter q.action host) host))
              (NodeSet.inter q.outcome host))
            host = false := by
        simpa [hinter] using hnestedKept
      refine ⟨n, ?_⟩
      have hshrunk :=
        identifyFuel_eq_failed_of_shrink n G host q.outcome
          (NodeSet.inter q.action host)
          (chainProduct NodeSet.full host) hexL' hkeptN' hsucc
      simpa [hinter] using hshrunk

/--
A first 4.3 restriction whose nested call then ancestrally shrinks, with
remaining that nested `An(Y)` and free side `remaining \ X`, yields a
hedge for the original query.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece seed) = false)
    (hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
  have hinter :
      NodeSet.inter (NodeSet.inter q.action host) fail.remaining =
        NodeSet.inter q.action fail.remaining := by
    rw [heqR]
    funext i
    cases hr :
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) i with
    | false =>
        simp [NodeSet.inter, hr]
    | true =>
        have hh : host i = true :=
          ancestralSet_subset G host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host) i hr
        simp [NodeSet.inter, hr, hh]
  have hfree' :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.inter q.action host) fail.remaining)) =
        true := by
    simpa [hinter] using hfree
  rcases identifyJoint_eq_failed_of_first_restrict_shrink G q hex hkept
      hfc0 hsingle hany hcont hexL hnestedKept hfail with ⟨n, hn⟩
  exact hedgeWitness?_eq_some_of_failed_local_action G q hfail hfree
    (identifyFuel_eq_failed_query_of_remaining_eq n G
      (G.ancestralSet host
        (GraphMutilation.bar (NodeSet.inter q.action host))
        (NodeSet.inter q.outcome host))
      q.outcome (NodeSet.inter q.action host)
      (.marginalize
        (NodeSet.diff host
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host)))
        (chainProduct NodeSet.full host))
      hn heq hfree')

/--
After a first 4.3 restriction and nested ancestral shrink, a further
product split unpacks as an ID run on one free c-component of that
nested `An(Y)`, with action `kept \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece seed) = false)
    (hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter q.action host)
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))) = false)
    (hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.inter q.action host)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter q.outcome
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
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
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        Exists fun n =>
          Legacy.identifyFuel n G
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))
            piece
            (NodeSet.diff
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))
              piece)
            (.marginalize
              (NodeSet.diff host
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host)))
              (chainProduct NodeSet.full host)) =
            IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
  rcases identifyJoint_eq_failed_of_first_restrict_shrink G q hex hkept
      hfc0 hsingle hany hcont hexL hnestedKept hfail with ⟨m, hm⟩
  cases hm' : m with
  | zero =>
      have hzero :
          Legacy.identifyFuel 0 G kept q.outcome (NodeSet.inter q.action host)
            (.marginalize
              (NodeSet.diff host kept) (chainProduct NodeSet.full host)) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        simpa [kept] using hm
      simp [Legacy.identifyFuel] at hzero
  | succ n =>
      have hsucc :
          Legacy.identifyFuel (n + 1) G kept q.outcome
            (NodeSet.inter q.action host)
            (.marginalize
              (NodeSet.diff host kept) (chainProduct NodeSet.full host)) =
            IdentificationOutcome.failed fail := by
        rw [← hm']
        simpa [kept] using hm
      have hexK' :
          NodeSet.isEmpty
            (NodeSet.inter (NodeSet.inter q.action host) kept) = false := by
        simpa [kept] using hexK
      have hkeptK' :
          NodeSet.equal
            (G.ancestralSet kept
              (GraphMutilation.bar
                (NodeSet.inter (NodeSet.inter q.action host) kept))
              (NodeSet.inter q.outcome kept))
            kept = true := by
        simpa [kept] using hkeptK
      have hfc' :
          G.cComponents
            (NodeSet.diff kept
              (NodeSet.inter (NodeSet.inter q.action host) kept)) =
            component :: component2 :: rest := by
        simpa [kept] using hfc
      have hprod :=
        identifyFuel_eq_failed_of_product n G kept q.outcome
          (NodeSet.inter q.action host)
          (.marginalize
            (NodeSet.diff host kept) (chainProduct NodeSet.full host))
          hexK' hkeptK' hfc' hsucc
      rcases hprod with ⟨piece, hmem, hEq⟩
      exact ⟨piece, hmem, ⟨n, by simpa [kept] using hEq⟩⟩

/--
A first 4.3 restriction, nested ancestral shrink, then product split,
with remaining that nested `An(Y)` and free side the failing piece,
yields a hedge for the original query once that remaining set meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (_hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter q.action host)
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))) = false)
    (_hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.inter q.action host)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter q.outcome
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
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
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
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
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
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
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexK with ⟨i, hi⟩
    simp [NodeSet.inter] at hi
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, kept] using hi.2
    · exact hi.1.1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, and nested
product split, a further 4.3 restriction unpacks as the ID run on the
containing c-component of the failing piece inside that ancestral
remaining set, with action `(kept \ piece) ∩ larger`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (_hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter q.action host)
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))) = false)
    (_hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.inter q.action host)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter q.outcome
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
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
    (hnestedAn :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host))
                piece)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter piece
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
    (hnestedFc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))
              piece)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        [piece])
    (hsingleH :
      G.isSingleCComponent
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = false)
    (hanyH :
      (G.cComponents
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))).any
        (fun c => NodeSet.equal c piece) = false)
    (hcontH :
      G.containingCComponent
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        piece = some larger)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          piece
          (NodeSet.diff
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))
            piece)
          (.marginalize
            (NodeSet.diff host
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host)))
            (chainProduct NodeSet.full host)) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G larger piece
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
        (chainProduct
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          larger) =
        IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty
            (NodeSet.inter (NodeSet.inter q.action host) kept) = false by
          simpa [kept] using hexK) with ⟨i, hi⟩
    simp [NodeSet.inter] at hi
    have hpair : q.action i = true ∧ kept i = true :=
      ⟨hi.1.1, hi.2⟩
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept
              (NodeSet.inter (NodeSet.inter q.action host) kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ
            cases hh : host j with
            | false =>
                have hk : kept j = true := by
                  simpa [hh] using hfreeJ
                have hh' : host j = true :=
                  ancestralSet_subset G host
                    (GraphMutilation.bar (NodeSet.inter q.action host))
                    (NodeSet.inter q.outcome host) j (by simpa [kept] using hk)
                simp [hh] at hh'
            | true =>
                simp [hh] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_restrict G kept piece
    (.marginalize
      (NodeSet.diff host kept) (chainProduct NodeSet.full host))
    hexP
    (by simpa [kept] using hnestedAn)
    (by simpa [kept] using hnestedFc)
    (by simpa [kept] using hsingleH)
    (by simpa [kept] using hanyH)
    (by simpa [kept] using hcontH)
    (by simpa [kept] using hinner)

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
then 4.3 onto the containing c-component of the failing piece, with
remaining that nested host and free side the piece, yields a hedge for
the original query once that host meets `X` and is ancestral of `Y` in
`G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece larger : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (_hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (_hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter q.action host)
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))) = false)
    (_hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.inter q.action host)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter q.outcome
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
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
    (_hnestedAn :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host))
                piece)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter piece
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
    (_hnestedFc :
      G.cComponents
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (NodeSet.inter
            (NodeSet.diff
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))
              piece)
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) =
        [piece])
    (_hsingleH :
      G.isSingleCComponent
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = false)
    (_hanyH :
      (G.cComponents
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))).any
        (fun c => NodeSet.equal c piece) = false)
    (_hcontH :
      G.containingCComponent
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        piece = some larger)
    (hexH :
      NodeSet.isEmpty (NodeSet.inter q.action larger) = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining larger = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
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
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
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
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp hexH with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first 4.3 restriction, nested ancestral shrink, and nested
product split, a further ancestral shrink unpacks as the ID run on
`An(piece)` inside that ancestral remaining set, with action
`kept \ piece`.
-/
theorem identifyJoint_eq_failed_of_first_restrict_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (_hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter q.action host)
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))) = false)
    (_hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.inter q.action host)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter q.outcome
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
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
    (hnestedAn :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host))
                piece)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter piece
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = false)
    (hinner :
      Exists fun n =>
        Legacy.identifyFuel n G
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          piece
          (NodeSet.diff
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))
            piece)
          (.marginalize
            (NodeSet.diff host
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host)))
            (chainProduct NodeSet.full host)) =
          IdentificationOutcome.failed fail)
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun n =>
      Legacy.identifyFuel n G
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host))
                piece)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter piece
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        piece
        (NodeSet.diff
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          piece)
        (.marginalize
          (NodeSet.diff
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))
            (G.ancestralSet
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))
              (GraphMutilation.bar
                (NodeSet.inter
                  (NodeSet.diff
                    (G.ancestralSet host
                      (GraphMutilation.bar (NodeSet.inter q.action host))
                      (NodeSet.inter q.outcome host))
                    piece)
                  (G.ancestralSet host
                    (GraphMutilation.bar (NodeSet.inter q.action host))
                    (NodeSet.inter q.outcome host))))
              (NodeSet.inter piece
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host)))))
          (.marginalize
            (NodeSet.diff host
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host)))
            (chainProduct NodeSet.full host))) =
        IdentificationOutcome.failed fail := by
  let kept :=
    G.ancestralSet host
      (GraphMutilation.bar (NodeSet.inter q.action host))
      (NodeSet.inter q.outcome host)
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
  have hexP :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff kept piece) kept) = false := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty
            (NodeSet.inter (NodeSet.inter q.action host) kept) = false by
          simpa [kept] using hexK) with ⟨i, hi⟩
    simp [NodeSet.inter] at hi
    have hpair : q.action i = true ∧ kept i = true :=
      ⟨hi.1.1, hi.2⟩
    have hdisj : NodeSet.disjointBool piece q.action = true :=
      (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun j hj => by
        have hfreeJ :
            NodeSet.diff kept
              (NodeSet.inter (NodeSet.inter q.action host) kept) j = true :=
          cComponents_subset G _ hmem' j hj
        cases ha : q.action j with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, NodeSet.inter, ha] at hfreeJ
            cases hh : host j with
            | false =>
                have hk : kept j = true := by
                  simpa [hh] using hfreeJ
                have hh' : host j = true :=
                  ancestralSet_subset G host
                    (GraphMutilation.bar (NodeSet.inter q.action host))
                    (NodeSet.inter q.outcome host) j (by simpa [kept] using hk)
                simp [hh] at hh'
            | true =>
                simp [hh] at hfreeJ)
    have hnot : piece i = false := by
      cases hp : piece i with
      | false =>
          rfl
      | true =>
          exact (Bool.false_ne_true
            (((NodeSet.disjointBool_eq_true_iff _ _).mp hdisj i hp).symm.trans
              hpair.1)).elim
    exact (NodeSet.isEmpty_eq_false_iff _).mpr
      ⟨i, by simp [NodeSet.diff, NodeSet.inter, hnot, hpair.2]⟩
  exact identifyFuel_eq_failed_of_product_piece_shrink G kept piece
    (.marginalize
      (NodeSet.diff host kept) (chainProduct NodeSet.full host))
    hexP
    (by simpa [kept] using hnestedAn)
    (by simpa [kept] using hinner)

/--
A first 4.3 restriction, nested ancestral shrink, nested product split,
then ancestral shrink of that piece, with remaining `An(piece)` inside
the first ancestral remaining set and free side the piece, yields a
hedge for the original query once that smaller remaining set meets `X`
and is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem hedgeWitness?_eq_some_of_failed_after_restrict_shrink_product_shrink
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S} {host seed : NodeSet S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    {piece : NodeSet S}
    (_hex : NodeSet.isEmpty q.action = false)
    (_hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (_hfc0 :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [seed])
    (_hsingle : G.isSingleCComponent NodeSet.full = false)
    (_hany :
      (G.cComponents NodeSet.full).any
        (fun c => NodeSet.equal c seed) = false)
    (_hcont :
      G.containingCComponent NodeSet.full seed = some host)
    (_hexL :
      NodeSet.isEmpty (NodeSet.inter q.action host) = false)
    (_hnestedKept :
      NodeSet.equal
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host))
        host = false)
    (_hexK :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter q.action host)
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))) = false)
    (_hkeptK :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter (NodeSet.inter q.action host)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter q.outcome
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = true)
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
    (_hnestedAn :
      NodeSet.equal
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host))
                piece)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter piece
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))))
        (G.ancestralSet host
          (GraphMutilation.bar (NodeSet.inter q.action host))
          (NodeSet.inter q.outcome host)) = false)
    (hexK2 :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host))
            (GraphMutilation.bar
              (NodeSet.inter
                (NodeSet.diff
                  (G.ancestralSet host
                    (GraphMutilation.bar (NodeSet.inter q.action host))
                    (NodeSet.inter q.outcome host))
                  piece)
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host))))
            (NodeSet.inter piece
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))) = false)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq :
      NodeSet.equal fail.remaining
        (G.ancestralSet
          (G.ancestralSet host
            (GraphMutilation.bar (NodeSet.inter q.action host))
            (NodeSet.inter q.outcome host))
          (GraphMutilation.bar
            (NodeSet.inter
              (NodeSet.diff
                (G.ancestralSet host
                  (GraphMutilation.bar (NodeSet.inter q.action host))
                  (NodeSet.inter q.outcome host))
                piece)
              (G.ancestralSet host
                (GraphMutilation.bar (NodeSet.inter q.action host))
                (NodeSet.inter q.outcome host))))
          (NodeSet.inter piece
            (G.ancestralSet host
              (GraphMutilation.bar (NodeSet.inter q.action host))
              (NodeSet.inter q.outcome host)))) = true)
    (hfreeEq : NodeSet.equal fail.free piece = true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
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
  let nestedAn :=
    G.ancestralSet kept
      (GraphMutilation.bar
        (NodeSet.inter (NodeSet.diff kept piece) kept))
      (NodeSet.inter piece kept)
  have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
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
  have hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true := by
    rcases (NodeSet.isEmpty_eq_false_iff _).mp
        (show NodeSet.isEmpty (NodeSet.inter q.action nestedAn) = false by
          simpa [nestedAn, kept] using hexK2) with ⟨i, hi⟩
    refine (NodeSet.meetsBool_eq_true_iff _ _).mpr ?_
    refine ⟨i, ?_, ?_⟩
    · simpa [failedHedgeSelection, heqR, nestedAn, kept, NodeSet.inter] using
        (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).2
    · exact (Bool.and_eq_true_iff.mp (by simpa [NodeSet.inter] using hi)).1
  exact hedgeWitness?_eq_some_of_failed_free_ancestral G q hfail hmeets
    hdisj hancFree hancY

/--
After a first product split, the nested ID run that actually failed is
the original remaining set with that free c-component as outcome and
`V \ piece` as action.
-/
theorem identifyJoint_eq_failed_of_first_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        Legacy.identifyFuel
            (S.count * Nat.succ S.count * Nat.succ S.count) G
            NodeSet.full piece (NodeSet.diff NodeSet.full piece)
            (observationalJointTerm S) =
          IdentificationOutcome.failed fail := by
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
        component :: component2 :: rest := by
    simpa [hinter] using hfc
  have hfuel :
      Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome
        q.action (observationalJointTerm S) =
        IdentificationOutcome.failed fail := hfail
  rw [identificationFuel] at hfuel
  exact identifyFuel_eq_failed_of_product
    (S.count * Nat.succ S.count * Nat.succ S.count) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) hex' hkept' hfc' hfuel

/--
A free c-component of `remaining \ (action ∩ remaining)` avoids `action`.
-/
theorem product_piece_avoids_action_of
    (G : ObservedGraph S) (remaining action : NodeSet S)
    {piece : NodeSet S}
    (hmem : piece ∈ G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining))) :
    NodeSet.disjointBool piece action = true :=
  (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun i hi => by
    have hfree :
        NodeSet.diff remaining (NodeSet.inter action remaining) i = true :=
      cComponents_subset G _ hmem i hi
    cases ha : action i with
    | false =>
        rfl
    | true =>
        simp [NodeSet.diff, NodeSet.inter, ha] at hfree)

/--
If a nested product failure's free side avoids the factor action
`remaining \ piece`, then it lies in `piece` and therefore avoids the outer
action.  The explicit remaining-set inclusion keeps this lemma independent of
any particular failure-trace depth.
-/
theorem product_nested_free_avoids_action_of
    (G : ObservedGraph S) (remaining action piece free : NodeSet S)
    (pieceMem : piece ∈ G.cComponents
      (NodeSet.diff remaining (NodeSet.inter action remaining)))
    (freeSubsetRemaining : NodeSet.Subset free remaining)
    (nestedAvoids :
      NodeSet.disjointBool free (NodeSet.diff remaining piece) = true) :
    NodeSet.disjointBool free action = true := by
  have nestedDisjoint :
      NodeSet.Disjoint free (NodeSet.diff remaining piece) :=
    (NodeSet.disjointBool_eq_true_iff _ _).mp nestedAvoids
  have freeSubsetPiece : NodeSet.Subset free piece := by
    intro i hiFree
    have hiRemaining : remaining i = true := freeSubsetRemaining i hiFree
    cases hiPiece : piece i with
    | true =>
        rfl
    | false =>
        have hiNestedAction : NodeSet.diff remaining piece i = true := by
          simp [NodeSet.diff, hiRemaining, hiPiece]
        exact False.elim
          (Bool.false_ne_true
            ((nestedDisjoint i hiFree).symm.trans hiNestedAction))
  have pieceDisjoint : NodeSet.Disjoint piece action :=
    (NodeSet.disjointBool_eq_true_iff _ _).mp
      (product_piece_avoids_action_of G remaining action pieceMem)
  exact (NodeSet.disjointBool_eq_true_iff _ _).mpr
    (NodeSet.Disjoint.of_subset_left pieceDisjoint freeSubsetPiece)

/--
A connected nested product failure that meets the factor action must meet the
outer action.  Otherwise its whole remaining host would lie in
`remaining \ action`; connectivity to a nonempty free vertex inside `piece`
would then force the factor-action witness back into the same outer
c-component `piece`, contradicting that it lies outside `piece`.
-/
theorem product_nested_remaining_meets_action_of
    (G : ObservedGraph S)
    (remaining action piece failedRemaining free : NodeSet S)
    (pieceMem : piece ∈ G.cComponents
      (NodeSet.diff remaining (NodeSet.inter action remaining)))
    (failedRemainingSubset : NodeSet.Subset failedRemaining remaining)
    (freeSubset : NodeSet.Subset free failedRemaining)
    (freeNonempty : NodeSet.isEmpty free = false)
    (failedRemainingSingle :
      G.isSingleCComponent failedRemaining = true)
    (nestedMeets :
      NodeSet.meetsBool failedRemaining (NodeSet.diff remaining piece) = true)
    (nestedAvoids :
      NodeSet.disjointBool free (NodeSet.diff remaining piece) = true) :
    NodeSet.meetsBool failedRemaining action = true := by
  cases outerMeets : NodeSet.meetsBool failedRemaining action with
  | true =>
      rfl
  | false =>
      have emptyIntersection :
          NodeSet.isEmpty (NodeSet.inter failedRemaining action) = true := by
        cases emptyResult :
            NodeSet.isEmpty (NodeSet.inter failedRemaining action) with
        | true =>
            rfl
        | false =>
            simp [NodeSet.meetsBool, emptyResult] at outerMeets
      have failedRemainingAvoids : NodeSet.Disjoint failedRemaining action := by
        intro i hiRemaining
        cases hiAction : action i with
        | false =>
            rfl
        | true =>
            have hiIntersection :
                NodeSet.inter failedRemaining action i = true := by
              simp [NodeSet.inter, hiRemaining, hiAction]
            have hiEmpty :
                NodeSet.inter failedRemaining action i = false :=
              (NodeSet.isEmpty_eq_true_iff
                (NodeSet.inter failedRemaining action)).mp emptyIntersection i
            exact False.elim
              (Bool.false_ne_true (hiEmpty.symm.trans hiIntersection))
      rcases (NodeSet.isEmpty_eq_false_iff free).mp freeNonempty with
        ⟨inside, insideFree⟩
      have insideFailed : failedRemaining inside = true :=
        freeSubset inside insideFree
      have insideRemaining : remaining inside = true :=
        failedRemainingSubset inside insideFailed
      have nestedDisjoint :
          NodeSet.Disjoint free (NodeSet.diff remaining piece) :=
        (NodeSet.disjointBool_eq_true_iff _ _).mp nestedAvoids
      have insidePiece : piece inside = true := by
        cases insidePieceEq : piece inside with
        | true =>
            rfl
        | false =>
            have insideNestedAction :
                NodeSet.diff remaining piece inside = true := by
              simp [NodeSet.diff, insideRemaining, insidePieceEq]
            exact False.elim
              (Bool.false_ne_true
                ((nestedDisjoint inside insideFree).symm.trans
                  insideNestedAction))
      rcases (NodeSet.meetsBool_eq_true_iff _ _).mp nestedMeets with
        ⟨outside, outsideFailed, outsideNestedAction⟩
      have outsideRemaining : remaining outside = true :=
        failedRemainingSubset outside outsideFailed
      have outsidePiece : piece outside = false := by
        cases outsidePieceEq : piece outside with
        | false =>
            rfl
        | true =>
            simp [NodeSet.diff, outsidePieceEq] at outsideNestedAction
      have hostInsideOuterFree :
          NodeSet.Subset failedRemaining
            (NodeSet.diff remaining (NodeSet.inter action remaining)) := by
        intro i hiFailed
        have hiRemaining : remaining i = true :=
          failedRemainingSubset i hiFailed
        have hiAction : action i = false :=
          failedRemainingAvoids i hiFailed
        simp [NodeSet.diff, NodeSet.inter, hiRemaining, hiAction]
      have insideToOutsideInFailed :
          BidirectedConnectedWithin G failedRemaining inside outside :=
        (bidirectedReachableWithin_eq_true_iff G failedRemaining
          insideFailed outsideFailed).mp
          (bidirectedReachableWithin_of_single G failedRemaining
            failedRemainingSingle insideFailed outsideFailed)
      have insideToOutsideInOuterFree :
          BidirectedConnectedWithin G
            (NodeSet.diff remaining (NodeSet.inter action remaining))
            inside outside :=
        insideToOutsideInFailed.mono hostInsideOuterFree
      rcases cComponents_mem G _ pieceMem with
        ⟨pieceRoot, pieceRootSelected, pieceEq⟩
      have rootToInside :
          BidirectedConnectedWithin G
            (NodeSet.diff remaining (NodeSet.inter action remaining))
            pieceRoot inside :=
        (cComponentOf_eq_true_iff G _ pieceRootSelected).mp (by
          rw [← pieceEq]
          exact insidePiece)
      have rootToOutside :
          BidirectedConnectedWithin G
            (NodeSet.diff remaining (NodeSet.inter action remaining))
            pieceRoot outside :=
        BidirectedConnectedWithin.trans rootToInside
          insideToOutsideInOuterFree
      have outsideInPiece : piece outside = true := by
        rw [pieceEq]
        exact (cComponentOf_eq_true_iff G _ pieceRootSelected).mpr
          rootToOutside
      exact False.elim
        (Bool.false_ne_true (outsidePiece.symm.trans outsideInPiece))

/--
Query transport from a recursive failure to its terminal immediate site.
Before the first product frame, the site's local outcome and action agree
with the invocation on `fail.remaining`.  After a product frame, the useful
normal form is instead the three hedge-core facts relative to the invocation:
the remaining side meets the action, the free side avoids it, and the
remaining side is ancestral of the free side after cutting their difference.
-/
inductive IdentificationFailureQueryTransport
    (G : ObservedGraph S) (outcome action : NodeSet S)
    (fail : IdentificationFail S)
    (site : IdentificationImmediateFailureSite G fail) : Type
  | local
      (outcomeAgreement :
        NodeSet.equal (NodeSet.inter site.outcome fail.remaining)
          (NodeSet.inter outcome fail.remaining) = true)
      (actionAgreement :
        NodeSet.equal (NodeSet.inter site.action fail.remaining)
          (NodeSet.inter action fail.remaining) = true)
  | product
      (remainingMeetsAction :
        NodeSet.meetsBool fail.remaining action = true)
      (freeAvoidsAction :
        NodeSet.disjointBool fail.free action = true)
      (freeAncestral :
        NodeSet.equal
          (G.ancestralSet fail.remaining
            (GraphMutilation.bar
              (NodeSet.diff fail.remaining fail.free))
            (NodeSet.inter fail.free fail.remaining))
          fail.remaining = true)

/--
Local-site agreement for a product-factor query already supplies the nested
hedge core.  The factor query is `piece | do(remaining \ piece)`: its local
free equation therefore identifies `fail.free` with `piece ∩ fail.remaining`.
The generic nonempty failure cut gives contact with the factor action, and
the same equality gives disjointness and free-component ancestry.
-/
theorem product_child_core_of_site_agrees
    (G : ObservedGraph S) (remaining piece : NodeSet S)
    {fuel : Nat} {current : ProbabilityTerm S}
    {fail : IdentificationFail S}
    (trace : IdentificationFailureTrace G fuel remaining piece
      (NodeSet.diff remaining piece) current fail)
    (outcomeAgreement :
      NodeSet.equal
        (NodeSet.inter trace.immediateSite.outcome fail.remaining)
        (NodeSet.inter piece fail.remaining) = true)
    (actionAgreement :
      NodeSet.equal
        (NodeSet.inter trace.immediateSite.action fail.remaining)
        (NodeSet.inter (NodeSet.diff remaining piece) fail.remaining) = true) :
    NodeSet.meetsBool fail.remaining (NodeSet.diff remaining piece) = true ∧
      NodeSet.disjointBool fail.free (NodeSet.diff remaining piece) = true ∧
        NodeSet.equal
          (G.ancestralSet fail.remaining
            (GraphMutilation.bar
              (NodeSet.diff fail.remaining fail.free))
            (NodeSet.inter fail.free fail.remaining))
          fail.remaining = true := by
  let site := trace.immediateSite
  have localFacts := site.local_query_site
  have actionEq :
      NodeSet.inter site.action fail.remaining =
        NodeSet.inter (NodeSet.diff remaining piece) fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp actionAgreement
  have outcomeEq :
      NodeSet.inter site.outcome fail.remaining =
        NodeSet.inter piece fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp outcomeAgreement
  have freeEq :
      fail.free =
        NodeSet.diff fail.remaining
          (NodeSet.inter (NodeSet.diff remaining piece) fail.remaining) := by
    have localFree := (NodeSet.equal_eq_true_iff _ _).mp localFacts.1
    simpa [actionEq] using localFree
  have failedRemainingSubset : NodeSet.Subset fail.remaining remaining :=
    trace.fail_remaining_subset
  have freeSubset : NodeSet.Subset fail.free fail.remaining :=
    (identifyFuel_eq_failed_free fuel G remaining piece
      (NodeSet.diff remaining piece) current trace.eq_failed).1
  have freeAsPiece :
      fail.free = NodeSet.inter piece fail.remaining := by
    rw [freeEq]
    funext i
    cases hiFailed : fail.remaining i with
    | false =>
        simp [NodeSet.diff, NodeSet.inter, hiFailed]
    | true =>
        have hiRemaining : remaining i = true :=
          failedRemainingSubset i hiFailed
        cases hiPiece : piece i <;>
          simp [NodeSet.diff, NodeSet.inter, hiFailed, hiRemaining, hiPiece]
  have cutEq :
      NodeSet.diff fail.remaining fail.free =
        NodeSet.inter (NodeSet.diff remaining piece) fail.remaining :=
    failedHedgeSelection_cut_eq_of_free fail
      (NodeSet.diff remaining piece)
      ((NodeSet.equal_eq_true_iff _ _).mpr freeEq)
  have cutNonempty :
      NodeSet.isEmpty (NodeSet.diff fail.remaining fail.free) = false :=
    identifyFuel_eq_failed_cut_nonempty fuel G remaining piece
      (NodeSet.diff remaining piece) current trace.eq_failed
  have nestedIntersectionNonempty :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.diff remaining piece) fail.remaining) = false := by
    simpa [cutEq] using cutNonempty
  have nestedMeets :
      NodeSet.meetsBool fail.remaining (NodeSet.diff remaining piece) = true := by
    unfold NodeSet.meetsBool
    rw [NodeSet.inter_comm]
    simp [nestedIntersectionNonempty]
  have nestedAvoids :
      NodeSet.disjointBool fail.free (NodeSet.diff remaining piece) = true := by
    refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
    intro i hiFree
    have hiFailed : fail.remaining i = true := freeSubset i hiFree
    have hiPiece : piece i = true := by
      have hiInter : NodeSet.inter piece fail.remaining i = true := by
        simpa [freeAsPiece] using hiFree
      exact NodeSet.inter_subset_left piece fail.remaining i hiInter
    simp [NodeSet.diff, hiPiece]
  have freeInter : NodeSet.inter fail.free fail.remaining = fail.free := by
    rw [NodeSet.inter_comm]
    exact NodeSet.inter_eq_of_subset freeSubset
  have targetEq :
      NodeSet.inter site.outcome fail.remaining =
        NodeSet.inter fail.free fail.remaining := by
    rw [outcomeEq, freeInter, freeAsPiece]
  have freeAncestral :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true := by
    have localAncestral := localFacts.2
    simpa [targetEq] using localAncestral
  exact ⟨nestedMeets, nestedAvoids, freeAncestral⟩

/--
Collapse an arbitrary structural failure trace to either local query
agreement or the product-derived hedge core.  Shrink frames preserve the
summary verbatim.  A 4.3 frame transports action facts through its containing
host.  The first product frame converts local agreement to the hedge core;
later product frames preserve that core via the two generic c-component
lemmas above.
-/
noncomputable def IdentificationFailureTrace.queryTransport
    {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S} {fail : IdentificationFail S}
    (trace :
      IdentificationFailureTrace G fuel remaining outcome action current fail) :
    IdentificationFailureQueryTransport G outcome action fail
      trace.immediateSite := by
  induction trace with
  | immediate =>
      exact .local
        ((NodeSet.equal_eq_true_iff _ _).mpr rfl)
        ((NodeSet.equal_eq_true_iff _ _).mpr rfl)
  | shrink _fuel _remaining _outcome _action _current _fail _actionNonempty
      _notAncestral _nested inductionHypothesis =>
      exact inductionHypothesis
  | restrict fuel remaining outcome action _current fail component larger
      _actionNonempty _ancestral _oneFreeComponent
      _severalRemainingComponents _componentNotMaximal containingComponent
      nested inductionHypothesis =>
      cases inductionHypothesis with
      | «local» outcomeAgreement actionAgreement =>
          have failedInLarger : NodeSet.Subset fail.remaining larger :=
            nested.fail_remaining_subset
          have largerInRemaining : NodeSet.Subset larger remaining :=
            containingCComponent_subset_host G remaining component
              containingComponent
          have restrictedAction :
              NodeSet.inter
                  (NodeSet.inter (NodeSet.inter action remaining) larger)
                  fail.remaining =
                NodeSet.inter action fail.remaining := by
            funext i
            cases hiFail : fail.remaining i with
            | false =>
                simp [NodeSet.inter, hiFail]
            | true =>
                have hiLarger : larger i = true := failedInLarger i hiFail
                have hiRemaining : remaining i = true :=
                  largerInRemaining i hiLarger
                simp [NodeSet.inter, hiFail, hiLarger, hiRemaining]
          have localActionEq :
              NodeSet.inter nested.immediateSite.action fail.remaining =
                NodeSet.inter
                  (NodeSet.inter (NodeSet.inter action remaining) larger)
                  fail.remaining :=
            (NodeSet.equal_eq_true_iff _ _).mp actionAgreement
          exact .local outcomeAgreement
            ((NodeSet.equal_eq_true_iff _ _).mpr
              (localActionEq.trans restrictedAction))
      | product remainingMeetsAction freeAvoidsAction freeAncestral =>
          have failedInLarger : NodeSet.Subset fail.remaining larger :=
            nested.fail_remaining_subset
          have largerInRemaining : NodeSet.Subset larger remaining :=
            containingCComponent_subset_host G remaining component
              containingComponent
          have freeSubsetFailed : NodeSet.Subset fail.free fail.remaining :=
            (identifyFuel_eq_failed_free fuel G larger outcome
              (NodeSet.inter (NodeSet.inter action remaining) larger)
              (chainProduct remaining larger) nested.eq_failed).1
          have liftedMeets :
              NodeSet.meetsBool fail.remaining action = true := by
            rcases (NodeSet.meetsBool_eq_true_iff _ _).mp
                remainingMeetsAction with ⟨i, hiFail, hiRestricted⟩
            have hiAction : action i = true :=
              NodeSet.inter_subset_left action remaining i
                (NodeSet.inter_subset_left
                  (NodeSet.inter action remaining) larger i hiRestricted)
            exact (NodeSet.meetsBool_eq_true_iff _ _).mpr
              ⟨i, hiFail, hiAction⟩
          have liftedAvoids :
              NodeSet.disjointBool fail.free action = true := by
            have restrictedDisjoint :
                NodeSet.Disjoint fail.free
                  (NodeSet.inter (NodeSet.inter action remaining) larger) :=
              (NodeSet.disjointBool_eq_true_iff _ _).mp freeAvoidsAction
            refine (NodeSet.disjointBool_eq_true_iff _ _).mpr ?_
            intro i hiFree
            have hiFail : fail.remaining i = true :=
              freeSubsetFailed i hiFree
            have hiLarger : larger i = true := failedInLarger i hiFail
            have hiRemaining : remaining i = true :=
              largerInRemaining i hiLarger
            cases hiAction : action i with
            | false =>
                rfl
            | true =>
                have hiRestricted :
                    NodeSet.inter (NodeSet.inter action remaining) larger i =
                      true := by
                  simp [NodeSet.inter, hiAction, hiRemaining, hiLarger]
                exact False.elim
                  (Bool.false_ne_true
                    ((restrictedDisjoint i hiFree).symm.trans hiRestricted))
          exact .product liftedMeets liftedAvoids freeAncestral
  | product fuel remaining _outcome action current fail component component2
      rest piece _actionNonempty _ancestral freeComponents firstFailingFactor
      nested inductionHypothesis =>
      have nestedCore :
          NodeSet.meetsBool fail.remaining (NodeSet.diff remaining piece) =
              true ∧
            NodeSet.disjointBool fail.free (NodeSet.diff remaining piece) =
              true ∧
            NodeSet.equal
              (G.ancestralSet fail.remaining
                (GraphMutilation.bar
                  (NodeSet.diff fail.remaining fail.free))
                (NodeSet.inter fail.free fail.remaining))
              fail.remaining = true := by
        cases inductionHypothesis with
        | «local» outcomeAgreement actionAgreement =>
            exact product_child_core_of_site_agrees G remaining piece nested
              outcomeAgreement actionAgreement
        | product remainingMeetsAction freeAvoidsAction freeAncestral =>
            exact ⟨remainingMeetsAction, freeAvoidsAction, freeAncestral⟩
      have pieceMem :
          piece ∈
            G.cComponents
              (NodeSet.diff remaining (NodeSet.inter action remaining)) := by
        rw [freeComponents]
        exact firstFailingFactor.mem
      have failedRemainingSubset : NodeSet.Subset fail.remaining remaining :=
        nested.fail_remaining_subset
      have freeSubsetFailed : NodeSet.Subset fail.free fail.remaining :=
        (identifyFuel_eq_failed_free fuel G remaining piece
          (NodeSet.diff remaining piece) current nested.eq_failed).1
      have freeSubsetRemaining : NodeSet.Subset fail.free remaining :=
        NodeSet.Subset.trans freeSubsetFailed failedRemainingSubset
      have failedRemainingSingle :
          G.isSingleCComponent fail.remaining = true :=
        (identifyFuel_eq_failed fuel G remaining piece
          (NodeSet.diff remaining piece) current nested.eq_failed).1
      have freeNonempty : NodeSet.isEmpty fail.free = false := by
        rcases identifyFuel_eq_failed_free_self fuel G remaining piece
            (NodeSet.diff remaining piece) current nested.eq_failed with
          ⟨root, rootInFree, _freeSelf⟩
        exact (NodeSet.isEmpty_eq_false_iff fail.free).mpr
          ⟨root, rootInFree⟩
      have outerMeets : NodeSet.meetsBool fail.remaining action = true :=
        product_nested_remaining_meets_action_of G remaining action piece
          fail.remaining fail.free pieceMem failedRemainingSubset
          freeSubsetFailed freeNonempty failedRemainingSingle nestedCore.1
          nestedCore.2.1
      have outerAvoids : NodeSet.disjointBool fail.free action = true :=
        product_nested_free_avoids_action_of G remaining action piece fail.free
          pieceMem freeSubsetRemaining nestedCore.2.1
      exact .product outerMeets outerAvoids nestedCore.2.2

/--
Every vertex in the terminal failure host is an ancestor of the invocation's
outcome inside the invocation's remaining graph after deleting incoming edges
to its action.

This invariant deliberately follows only the outermost frame.  An immediate,
restriction, or product frame records that its whole remaining set is
ancestral.  A shrink frame records the ancestral set itself as the recursive
host, and the generic failure-host containment theorem places the terminal
vertex in that host.  Replacing `action ∩ remaining` by `action` is sound on
the induced remaining graph by `ancestralSet_bar_inter`.
-/
theorem IdentificationFailureTrace.failed_remaining_ancestorOfWithin
    {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S} {fail : IdentificationFail S}
    (trace :
      IdentificationFailureTrace G fuel remaining outcome action current fail)
    {i : Fin S.count} (hi : fail.remaining i = true) :
    G.ancestorOfWithin remaining (GraphMutilation.bar action)
      (NodeSet.inter outcome remaining) i = true := by
  cases trace with
  | immediate _fuel remaining outcome action _current _component
      _actionNonempty ancestral _oneFreeComponent _oneRemainingComponent =>
      rw [ancestralSet_bar_inter G remaining action
        (NodeSet.inter outcome remaining)] at ancestral
      exact ancestorOfWithin_of_ancestralSet G remaining _ _ ancestral hi
  | shrink _fuel remaining outcome action _current _fail _actionNonempty
      _notAncestral nested =>
      have hiKept :
          G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining) i = true :=
        nested.fail_remaining_subset i hi
      rw [ancestralSet_bar_inter G remaining action
        (NodeSet.inter outcome remaining)] at hiKept
      simpa [ObservedGraph.ancestralSet] using hiKept
  | restrict _fuel remaining outcome action _current _fail _component larger
      _actionNonempty ancestral _oneFreeComponent
      _severalRemainingComponents _componentNotMaximal containingComponent
      nested =>
      have hiLarger : larger i = true :=
        nested.fail_remaining_subset i hi
      have hiRemaining : remaining i = true :=
        containingCComponent_subset_host G remaining _ containingComponent i
          hiLarger
      rw [ancestralSet_bar_inter G remaining action
        (NodeSet.inter outcome remaining)] at ancestral
      exact ancestorOfWithin_of_ancestralSet G remaining _ _ ancestral
        hiRemaining
  | product _fuel remaining outcome action _current _fail _component
      _component2 _rest _piece _actionNonempty ancestral _freeComponents
      _firstFailingFactor nested =>
      have hiRemaining : remaining i = true :=
        nested.fail_remaining_subset i hi
      rw [ancestralSet_bar_inter G remaining action
        (NodeSet.inter outcome remaining)] at ancestral
      exact ancestorOfWithin_of_ancestralSet G remaining _ _ ancestral
        hiRemaining

/--
The canonical roots selected from any failed public ID run reach the original
query outcome.  This is the last hedge Boolean that cannot be read directly
from the terminal 4.1 failure: the structural trace carries the reachability
back through every shrink, restriction, and product frame.
-/
theorem JointIdentificationFailureTrace.failedHedgeSelection_rootsReach
    {G : ObservedGraph S} {q : JointKernelQuery S}
    {fail : IdentificationFail S}
    (trace : JointIdentificationFailureTrace G q fail) :
    rootsReachOutcomeBool q
      (keptSinks (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child) = true := by
  apply rootsReachOutcomeBool_of_each_ancestor G q NodeSet.full
    (keptSinks fail.remaining (closedForestChild fail.remaining fail.free))
  intro root hroot
  have hrootFailed : fail.remaining root = true :=
    keptSinks_subset fail.remaining
      (closedForestChild fail.remaining fail.free) root hroot
  simpa [JointIdentificationFailureTrace, NodeSet.inter_full_right] using
    trace.failed_remaining_ancestorOfWithin hrootFailed

/--
Every structurally certified public ID failure yields an extracted hedge.

The query-transport summary separates the only two mathematically distinct
cases.  Product-free traces preserve the terminal 4.1 query on the failure
host and use its local free/ancestral equations directly.  Once a product
frame occurs, the summary instead supplies the failure host's contact with
the original action, avoidance by the free component, and free-component
ancestry.  The trace-wide reachability invariant above supplies the remaining
large-forest test in both cases.
-/
theorem hedgeWitness?_eq_some_of_failureTrace
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (trace : JointIdentificationFailureTrace G q fail) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hfail :
      Legacy.identifyJoint G q = IdentificationOutcome.failed fail := by
    simpa [Legacy.identifyJoint, JointIdentificationFailureTrace] using
      trace.eq_failed
  cases trace.queryTransport with
  | «local» outcomeAgreement actionAgreement =>
      let site := trace.immediateSite
      have localFacts := site.local_query_site
      exact hedgeWitness?_eq_some_of_failed_site_agrees G q hfail
        site.outcome site.action localFacts.1 localFacts.2
        outcomeAgreement actionAgreement
  | product remainingMeetsAction freeAvoidsAction freeAncestral =>
      have rootsReach := trace.failedHedgeSelection_rootsReach
      have keptSinksInFree :=
        failedHedgeSelection_keptSinks_of_free_ancestral G q hfail
          freeAncestral
      have smallReady :=
        failedHedgeSelection_smallForestReady_of G q hfail
          freeAvoidsAction keptSinksInFree
      have tests :=
        failedHedgeSelection_tests_of G q hfail remainingMeetsAction
          rootsReach smallReady
      exact hedgeWitness?_eq_some_of_failed G q fail tests

/--
Executable form of general failure-to-hedge extraction.  The failed equation
is first reified as a finite structural trace, then discharged by the generic
trace theorem; no propositional choice is used to recover the recursive path.
-/
theorem hedgeWitness?_eq_some_of_identifyJoint_failed
    {S : ObservedSignature.{0}}
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  let trace : JointIdentificationFailureTrace G q fail :=
    IdentificationFailureTrace.of_eq_failed (identificationFuel S) G
      NodeSet.full q.outcome q.action (observationalJointTerm S) hfail
  exact hedgeWitness?_eq_some_of_failureTrace G q trace

/--
Inspectable result of the failure-to-hedge search.  Retaining the extractor
equation makes the data useful to later executable constructions without
reopening an existential proposition.
-/
structure ExtractedHedgeWitness (G : ObservedGraph S)
    (q : JointKernelQuery S) (fail : IdentificationFail S) where
  witness : HedgeWitness G q
  result : hedgeWitness? G q fail = some witness

/--
Evaluate the finite hedge search certified by a structural failure trace.

The proof first establishes propositionally that `none` is impossible, then
case-splits on the computed option.  Thus the witness returned in `Type` is
the search result itself; it is not selected from an existential and requires
neither choice nor excluded middle.
-/
noncomputable def JointIdentificationFailureTrace.extractedHedge
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (trace : JointIdentificationFailureTrace G q fail) :
    ExtractedHedgeWitness G q fail := by
  have notNone : hedgeWitness? G q fail ≠ none := by
    intro result
    rcases hedgeWitness?_eq_some_of_failureTrace G q trace with
      ⟨witness, found⟩
    rw [result] at found
    cases found
  cases result : hedgeWitness? G q fail with
  | none =>
      exact False.elim (notNone result)
  | some witness =>
      exact ⟨witness, result⟩

/--
Identifiability rules out the failure branch of the now-total public ID
engine once every extracted hedge has its semantic counterexample.

This isolates the two genuine remaining completeness tasks: compile the
successful structural trace to a published certificate, and construct the
general hedge countermodel.  Fuel exhaustion and arbitrary recursive failure
nesting no longer appear in the statement.
-/
theorem identifyJoint_eq_identified_of_identifiable
    {S : ObservedSignature.{0}} {G : ObservedGraph S}
    {C : GraphModelClass G} (q : JointKernelQuery S)
    (hedgeCounterexample : HedgeWitness G q -> CounterexampleIn C q)
    (identifiable : C.identifiable q) :
    Exists fun term =>
      Legacy.identifyJoint G q = IdentificationOutcome.identified term := by
  cases identifyJoint_terminalTrace G q with
  | identified term trace =>
      exact ⟨term, by
        simpa [Legacy.identifyJoint, JointIdentificationSuccessTrace] using
          trace.eq_identified⟩
  | failed fail trace =>
      let extracted := trace.extractedHedge G q
      exact False.elim
        ((hedgeCounterexample extracted.witness).not_identifiable
          identifiable)


end Causality
end Thesis
