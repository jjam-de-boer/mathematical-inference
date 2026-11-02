import Thesis.CausalTransport.NativeTargetStates
import Thesis.CausalTransport.NativeDemandFrames

namespace Thesis.Causality.NativeTargetRecognition

open Probability NativeDemandTyping NativeDemandEncoding

/-!
# Exact finite recognition of acceptable target formulas

For a fixed profile family, observational support pattern, outer demand and
evaluation reference, acceptance asks four independent questions: are all
annotations coherent at that demand, is the term natively supported at its
demanded cells, is all syntax action-free, and is observational evaluation
available at the requested reference? The finite-state fold answers exactly
the existing four checks, including null conditionals and unused branches.

Availability is still required when the native demand is empty. Conversely,
an available formula supplies neither support of a separate causal source
nor a derivation from that source. The caller must retain those obligations;
this recognizer does not manufacture a guard, a proof or a causal value.

Strict multiplication's associativity and commutativity preserve the whole
state, also inside literal frames. Weighted multiplication is asymmetric and
is not declared AC. No search, normalization, reachability decision or
universal stopping theorem is introduced here.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
variable {profiles : List (NativeTemplateInstance P)}

private theorem demandEqual_self (requested : Demand profiles) :
    demandEqual profiles requested requested = true := (demandEqual_exact ..).mpr rfl

/-- A root request can be separated from internal annotation coherence.
This is literal finite demand equality, not equality of support grades. -/
private theorem annotations_at_root (term : Term profiles) (requested : Demand profiles) :
    term.checkAnnotations requested = (demandEqual profiles requested term.demand && term.wellFormed) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true_iff, demandEqual_exact]
  constructor
  · intro accepted
    have same : requested = term.demand := by
      have root := congrArg Term.demand ((Term.checkAnnotations_exact ..).mp accepted)
      simpa only [Term.demand_encode] using root
    exact ⟨same, by simpa only [same, Term.wellFormed] using accepted⟩
  · rintro ⟨same, coherent⟩
    simpa only [same, Term.wellFormed] using coherent

private theorem annotations_of_coherent (pattern : S.Assignment → Bool) (term : Term profiles)
    (coherent : (summarize pattern term).coherent = term.wellFormed) (requested : Demand profiles) :
    (summarize pattern term).annotations requested = term.checkAnnotations requested := by
  rw [State.annotations, demand_summarize, coherent, annotations_at_root]

theorem coherent_summarize (pattern : S.Assignment → Bool) (term : Term profiles) :
    (summarize pattern term).coherent = term.wellFormed := by
  induction term with
  | zero requested => exact (demandEqual_self requested).symm
  | kernel requested current => exact (demandEqual_self requested).symm
  | marginalize requested nodes inner ih =>
      change (summarize pattern inner).annotations (marginalDemand profiles requested nodes) =
        (demandEqual profiles requested requested && inner.checkAnnotations (marginalDemand profiles requested nodes))
      rw [annotations_of_coherent pattern inner ih, demandEqual_self, Bool.true_and]
  | evaluateAt requested fixed inner ih =>
      change (summarize pattern inner).annotations (fixedDemand profiles requested fixed) =
        (demandEqual profiles requested requested && inner.checkAnnotations (fixedDemand profiles requested fixed))
      rw [annotations_of_coherent pattern inner ih, demandEqual_self, Bool.true_and]
  | add requested left right leftIH rightIH
  | multiply requested left right leftIH rightIH
  | divide requested left right leftIH rightIH =>
      change ((summarize pattern left).annotations requested && (summarize pattern right).annotations requested) =
        (demandEqual profiles requested requested && (left.checkAnnotations requested && right.checkAnnotations requested))
      rw [annotations_of_coherent pattern left leftIH, annotations_of_coherent pattern right rightIH,
        demandEqual_self, Bool.true_and]
  | weightedMultiply requested weight factor weightIH factorIH =>
      change ((summarize pattern weight).annotations requested &&
        (summarize pattern factor).annotations (positiveDemand profiles requested (summarize pattern weight).native)) =
          (demandEqual profiles requested requested && (weight.checkAnnotations requested &&
            factor.checkAnnotations (positiveDemand profiles requested (termStatus profiles weight.erase))))
      rw [native_summarize, annotations_of_coherent pattern weight weightIH,
        annotations_of_coherent pattern factor factorIH, demandEqual_self, Bool.true_and]

theorem annotations_summarize (pattern : S.Assignment → Bool) (term : Term profiles) (requested : Demand profiles) :
    (summarize pattern term).annotations requested = term.checkAnnotations requested :=
  annotations_of_coherent pattern term (coherent_summarize pattern term) requested

namespace State

/-- Finite acceptance on a state. Observational availability is tested
independently of the native demand, including when that demand is empty. -/
def accepts (state : State profiles) (requested : Demand profiles) (reference : S.Assignment) : Bool :=
  ((state.annotations requested && allNeeded profiles requested (fun index value => (state.native index value).isDefined)) &&
    state.actionFree) && (state.observational reference).isDefined

end State

def recognize (pattern : S.Assignment → Bool) (requested : Demand profiles) (reference : S.Assignment)
    (term : Term profiles) : Bool := (summarize pattern term).accepts requested reference

/-- Boolean agreement for every tree, including malformed annotations,
actionful unused children and hypothetical observational support patterns. -/
theorem recognize_exact (pattern : S.Assignment → Bool) (requested : Demand profiles) (reference : S.Assignment)
    (term : Term profiles) :
    recognize pattern requested reference term =
      (((term.checkAnnotations requested && NativeDemandTyping.check profiles term.erase requested) &&
        term.actionFreeCheck) && (term.erase.supportStatus pattern reference).isDefined) := by
  rw [recognize, State.accepts, annotations_summarize, native_summarize, actionFree_summarize,
    observational_summarize, check_status]

/-- At an actual observed law the fourth test is exactly the established
partial evaluator's availability; no positivity assumption is added. -/
theorem recognize_record (record : FiniteProbRecord S.Assignment) (requested : Demand profiles)
    (reference : S.Assignment) (term : Term profiles) :
    recognize record.support requested reference term =
      (((term.checkAnnotations requested && NativeDemandTyping.check profiles term.erase requested) &&
        term.actionFreeCheck) && (term.erase.observationalDenote record reference).isSome) := by
  rw [recognize_exact, ProbabilityTerm.supportStatus_exact, ProbabilityResult.status_isDefined]

theorem recognize_record_iff (record : FiniteProbRecord S.Assignment) (requested : Demand profiles)
    (reference : S.Assignment) (term : Term profiles) :
    recognize record.support requested reference term = true ↔
      term.checkAnnotations requested = true ∧
      NativeDemandTyping.check profiles term.erase requested = true ∧
      term.actionFreeCheck = true ∧ (term.erase.observationalDenote record reference).isSome = true := by
  rw [recognize_record]
  simp only [Bool.and_eq_true_iff, and_assoc]

/-- A canonically encoded candidate has no extra annotation premise. The
native, syntactic and observational obligations nevertheless remain separate. -/
theorem recognize_encode (pattern : S.Assignment → Bool) (requested : Demand profiles)
    (reference : S.Assignment) (term : ProbabilityTerm S) :
    recognize pattern requested reference (Term.encode profiles term requested) =
      ((NativeDemandTyping.check profiles term requested && term.actionFreeCheck) &&
        (term.supportStatus pattern reference).isDefined) := by
  rw [recognize_exact, Term.checkAnnotations_encode, Term.erase_encode, Term.actionFreeCheck_encode, Bool.true_and]

/-- Every computed state belongs to the explicit finite carrier. Neither
this theorem nor recognition evaluates that exhaustive state catalogue. -/
theorem summarize_mem (pattern : S.Assignment → Bool) (term : Term profiles) :
    summarize pattern term ∈ State.enumeration profiles := State.mem_enumeration _

private theorem state_ext {left right : State profiles}
    (demand : left.demand = right.demand) (native : left.native = right.native)
    (observational : left.observational = right.observational)
    (coherent : left.coherent = right.coherent) (actionFree : left.actionFree = right.actionFree) : left = right := by
  cases left
  cases right
  cases demand
  cases native
  cases observational
  cases coherent
  cases actionFree
  rfl

private theorem status_multiply_comm (left right : ProbabilityResult.Status) :
    ProbabilityResult.Status.multiply left right = ProbabilityResult.Status.multiply right left := by
  cases left <;> cases right <;> rfl

private theorem status_multiply_assoc (first second third : ProbabilityResult.Status) :
    ProbabilityResult.Status.multiply (ProbabilityResult.Status.multiply first second) third =
      ProbabilityResult.Status.multiply first (ProbabilityResult.Status.multiply second third) := by
  cases first <;> cases second <;> cases third <;> rfl

namespace State

/-- Equality of complete recognition states, not a new causal equation.
The laws hold even for incoherent child states, so no validity premise is
lost when passing to an AC-invariant target language. -/
theorem multiply_comm (requested : Demand profiles) (left right : State profiles) :
    multiply requested left right = multiply requested right left := by
  apply state_ext
  · rfl
  · funext index reference
    exact status_multiply_comm _ _
  · funext reference
    exact status_multiply_comm _ _
  · exact Bool.and_comm _ _
  · exact Bool.and_comm _ _

theorem multiply_assoc (requested : Demand profiles) (first second third : State profiles) :
    multiply requested (multiply requested first second) third =
      multiply requested first (multiply requested second third) := by
  apply state_ext
  · rfl
  · funext index reference
    exact status_multiply_assoc _ _ _
  · funext reference
    exact status_multiply_assoc _ _ _
  · simp only [multiply, strictBinary, annotations, demandEqual_self, Bool.true_and, Bool.and_assoc]
  · exact Bool.and_assoc _ _ _

end State

theorem summarize_multiply_comm (pattern : S.Assignment → Bool) (requested : Demand profiles)
    (left right : Term profiles) :
    summarize pattern (.multiply requested left right) = summarize pattern (.multiply requested right left) :=
  State.multiply_comm requested _ _

theorem summarize_multiply_assoc (pattern : S.Assignment → Bool) (requested : Demand profiles)
    (first second third : Term profiles) :
    summarize pattern (.multiply requested (.multiply requested first second) third) =
      summarize pattern (.multiply requested first (.multiply requested second third)) :=
  State.multiply_assoc requested _ _ _

/-- Literal siblings are unchanged. Equal child states preserve parent
recognition metadata in all ten frames, including either weighted position.
This congruence of the recognizer does not certify equality of the terms. -/
theorem summarize_fill_congr (pattern : S.Assignment → Bool) (frame : Frame profiles)
    {left right : Term profiles} (same : summarize pattern left = summarize pattern right) :
    summarize pattern (frame.fill left) = summarize pattern (frame.fill right) := by
  cases frame <;> simp only [Frame.fill, summarize, same]

/-- Iteration gives AC invariance at arbitrary depth without flattening or
sorting products, changing a sibling, or treating weighted multiplication as AC. -/
theorem summarize_context_congr (pattern : S.Assignment → Bool) (frames : List (Frame profiles))
    {left right : Term profiles} (same : summarize pattern left = summarize pattern right) :
    summarize pattern (frames.foldr Frame.fill left) = summarize pattern (frames.foldr Frame.fill right) := by
  induction frames with
  | nil => exact same
  | cons frame rest ih => exact summarize_fill_congr pattern frame ih

theorem recognize_context_congr (pattern : S.Assignment → Bool) (requested : Demand profiles)
    (reference : S.Assignment) (frames : List (Frame profiles)) {left right : Term profiles}
    (same : summarize pattern left = summarize pattern right) :
    recognize pattern requested reference (frames.foldr Frame.fill left) =
      recognize pattern requested reference (frames.foldr Frame.fill right) :=
  congrArg (fun state => state.accepts requested reference) (summarize_context_congr pattern frames same)

theorem recognize_multiply_comm (pattern : S.Assignment → Bool) (requested : Demand profiles)
    (reference : S.Assignment) (operationDemand : Demand profiles) (left right : Term profiles) :
    recognize pattern requested reference (.multiply operationDemand left right) =
      recognize pattern requested reference (.multiply operationDemand right left) :=
  congrArg (fun state => state.accepts requested reference) (summarize_multiply_comm pattern operationDemand left right)

theorem recognize_multiply_assoc (pattern : S.Assignment → Bool) (requested : Demand profiles)
    (reference : S.Assignment) (operationDemand : Demand profiles) (first second third : Term profiles) :
    recognize pattern requested reference (.multiply operationDemand (.multiply operationDemand first second) third) =
      recognize pattern requested reference (.multiply operationDemand first (.multiply operationDemand second third)) :=
  congrArg (fun state => state.accepts requested reference) (summarize_multiply_assoc pattern operationDemand first second third)

end Thesis.Causality.NativeTargetRecognition
