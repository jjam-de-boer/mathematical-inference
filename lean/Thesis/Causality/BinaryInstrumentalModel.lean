import Thesis.Causality.BinaryInstrumentalResponse

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Realize arbitrary independent IV profile records as actual finite SCMs

One private root samples the instrument; a second root samples the complete
treatment/outcome response profile and feeds only `X,Y`.  Both root value
types use the same explicit sixteen-profile alphabet.  The private root's
factor is the supplied Boolean instrument law encoded in its first bit;
the remaining private bits are fixed and unused.  This homogeneous finite
presentation avoids selecting any dependent latent value or changing the
observed signature.

The prior is the actual supplied independent instrument/response product,
pushed through its displayed two-root encoding.  Its coordinate product law
is proved, and the mechanisms access only their declared parent/root inputs.
Whole observational and treatment-interventional probability preservation
establish the reverse half of the response representation: a feasible set of
profile weights produces a genuine causal model, not merely a relaxation.

Instrument or response probabilities may vanish, and every response map,
including decreasing treatment responses, is permitted.  No monotonicity,
faithfulness, or additional positivity condition is present.
-/

def profileLatent : LatentExtension signature where
  count := 2
  Value := fun _ => Profile
  valueEnumeration := fun _ => profiles
  value_complete := fun _ => profiles_complete
  valueDecidableEq := fun _ => profileDecidableEq
  incident := fun root child => if root.val = 0 then decide (child.val = 0)
    else decide (child.val = 1 ∨ child.val = 2)

def instrumentRoot : Fin profileLatent.count := ⟨0, by decide⟩
def responseRoot : Fin profileLatent.count := ⟨1, by decide⟩

def instrumentSeed (instrument : Bool) : Profile :=
  fun bit => if bit.val = 0 then instrument else false

def encodeRoots (pair : Bool × Profile) : profileLatent.Assignment :=
  fun root => if root.val = 0 then instrumentSeed pair.1 else pair.2

def profileFactors (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile)
    (root : Fin profileLatent.count) : FiniteProbRecord Profile :=
  if root.val = 0 then instrument.map instrumentSeed else responses

def profilePrior (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile) :
    FiniteProbRecord profileLatent.Assignment :=
  (instrument.product responses).map encodeRoots

private theorem encoded_rectangle (events : (root : Fin profileLatent.count) → Profile → Bool)
    (pair : Bool × Profile) : profileLatent.rectangularEvent events (encodeRoots pair) =
      (events instrumentRoot (instrumentSeed pair.1) && events responseRoot pair.2) := by
  change (events responseRoot pair.2 && (events instrumentRoot (instrumentSeed pair.1) && true)) = _
  rw [Bool.and_true, Bool.and_comm]

private theorem profile_product_law (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile)
    (events : (root : Fin profileLatent.count) → Profile → Bool) :
    QProb.Equiv ((profilePrior instrument responses).probVal (profileLatent.rectangularEvent events))
      (FiniteProduct.qProduct profileLatent.count
        (fun root => (profileFactors instrument responses root).probVal (events root))) := by
  have paired : QProb.Equiv
      ((profilePrior instrument responses).probVal (profileLatent.rectangularEvent events))
      (QProb.mul (instrument.probVal (fun value => events instrumentRoot (instrumentSeed value)))
        (responses.probVal (events responseRoot))) :=
    QProb.equiv_trans ((instrument.product responses).map_probVal encodeRoots _)
      (QProb.equiv_trans
        ((instrument.product responses).probVal_congr _ _ (encoded_rectangle events))
        (instrument.product_probVal responses
          (fun value => events instrumentRoot (instrumentSeed value)) (events responseRoot)))
  have encoded := instrument.map_probVal instrumentSeed (events instrumentRoot)
  have simplified : QProb.Equiv
      (FiniteProduct.qProduct profileLatent.count
        (fun root => (profileFactors instrument responses root).probVal (events root)))
      (QProb.mul (responses.probVal (events responseRoot))
        ((instrument.map instrumentSeed).probVal (events instrumentRoot))) := by
    change QProb.Equiv
      (QProb.mul (responses.probVal (events responseRoot))
        (QProb.mul ((instrument.map instrumentSeed).probVal (events instrumentRoot)) QProb.one)) _
    exact QProb.mul_congr (QProb.equiv_refl _) (QProb.mul_one _)
  exact QProb.equiv_trans paired
    (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_symm encoded) (QProb.equiv_refl _))
      (QProb.equiv_trans (QProb.mul_comm _ _) (QProb.equiv_symm simplified)))

/-- Every supplied independent pair of finite records gives an actual SCM,
with no readiness predicate or external semantic certificate as a field. -/
def profileModel (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile) :
    ExactModel signature where
  latent := profileLatent
  factor := profileFactors instrument responses
  prior := profilePrior instrument responses
  product_law := profile_product_law instrument responses
  mechanism := fun child parents inputs =>
    if atZ : child.val = 0 then
      (inputs instrumentRoot (by simp [profileLatent, instrumentRoot, atZ])) ⟨0, by decide⟩
    else if atX : child.val = 1 then
      treatmentAt (inputs responseRoot (by simp [profileLatent, responseRoot, atX]))
        (parents z (by simp [signature, z, atX]))
    else
      let atY : child.val = 2 := by
        have bounded : child.val < 3 := child.isLt
        omega
      outcomeAt (inputs responseRoot (by simp [profileLatent, responseRoot, atY]))
        (parents x (by simp [signature, x, atY]))

/-- Finite incidence contains only a private root and one pair root.  The
explicit node cases avoid treating canonical membership as an assumed axiom. -/
theorem profileModel_isCanonical (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile) :
    (profileModel instrument responses).IsCanonicalSemiMarkovian := by
  change profileLatent.CanonicalSemiMarkovian
  intro root first second third firstIncident secondIncident thirdIncident
  rcases node_cases first with same | same | same <;> subst first <;>
    rcases node_cases second with same | same | same <;> subst second <;>
    rcases node_cases third with same | same | same <;> subst third <;>
    by_cases privateRoot : root.val = 0 <;>
    simp [profileLatent, z, x, y, privateRoot] at *

theorem profileModel_hasProjectedGraph (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile) :
    HasProjectedGraph (profileModel instrument responses) graph := by
  change forall first second : Fin signature.count,
    profileLatent.projectedBidirected first second = graph.bidirected first second
  decide +kernel

theorem profileModel_compatible (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile) :
    Compatible (profileModel instrument responses) graph :=
  ⟨profileModel_isCanonical instrument responses, profileModel_hasProjectedGraph instrument responses⟩

/-! ## Unit and probability preservation -/

theorem profileModel_instrumentRead (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile)
    (pair : Bool × Profile) : instrumentRead (profileModel instrument responses) (encodeRoots pair) = pair.1 := rfl

private theorem profile_index_cases : forall bit : Fin 4,
    bit = ⟨0, by decide⟩ ∨ bit = ⟨1, by decide⟩ ∨
      bit = ⟨2, by decide⟩ ∨ bit = ⟨3, by decide⟩ := by decide +kernel

theorem profileModel_profileRead (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile)
    (pair : Bool × Profile) : profileRead (profileModel instrument responses) (encodeRoots pair) = pair.2 := by
  funext bit
  rcases profile_index_cases bit with same | same | same | same <;> subst bit <;> rfl

theorem profileModel_eval (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile)
    (pair : Bool × Profile) : (profileModel instrument responses).eval (encodeRoots pair) = observedAssignment pair.1 pair.2 := by
  rw [eval_observedAssignment, profileModel_instrumentRead, profileModel_profileRead]

/-- The whole forward observed record is exactly the actual SCM's law, up
to rational presentation equivalence for every Boolean observed event. -/
theorem profileModel_observationalValue (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile)
    (event : Event signature.Assignment) :
    QProb.Equiv ((profileModel instrument responses).observationalValue event)
      ((observedRecord instrument responses).probVal event) :=
  QProb.equiv_trans ((profileModel instrument responses).observationalValue_eq event)
    (QProb.equiv_trans
      ((instrument.product responses).map_probVal encodeRoots
        (fun unit => event ((profileModel instrument responses).eval unit)))
      (QProb.equiv_trans
        ((instrument.product responses).probVal_congr _ _
          (fun pair => congrArg event (profileModel_eval instrument responses pair)))
        (QProb.equiv_symm
          ((instrument.product responses).map_probVal (fun pair => observedAssignment pair.1 pair.2) event))))

theorem profileModel_interventionalValue (instrument : FiniteProbRecord Bool) (responses : FiniteProbRecord Profile)
    (action : Bool) :
    QProb.Equiv ((profileModel instrument responses).interventionalValue (intervention action).value (fun sample => sample y))
      ((effectRecord responses action).probVal id) := by
  have unit : QProb.Equiv
      ((profileModel instrument responses).interventionalValue (intervention action).value (fun sample => sample y))
      ((instrument.product responses).probVal (fun pair => outcomeAt pair.2 action)) :=
    QProb.equiv_trans ((profileModel instrument responses).interventionalValue_eq (intervention action).value _)
      (QProb.equiv_trans
        ((instrument.product responses).map_probVal encodeRoots
          (fun unit => (profileModel instrument responses).evalUnder (intervention action).value unit y))
        ((instrument.product responses).probVal_congr _ _ (fun pair => by
          rw [eval_doX_outcome, profileModel_profileRead])))
  exact QProb.equiv_trans unit
    (QProb.equiv_trans (instrument.product_probVal_right responses (fun profile => outcomeAt profile action))
      (QProb.equiv_symm (effectRecord_probVal responses action)))

end BinaryInstrumental
end Causality
end Thesis
