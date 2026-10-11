import Thesis.CausalTransport.SupportAwareChain
import Thesis.CausalTransport.SupportAwareChainCompilation
import Thesis.Causality.ProbabilityTermEquality

namespace Thesis
namespace Causality
namespace Examples
namespace ZeroCellChain

open Probability

/-!
# Kernel-level regressions for a distribution containing zeros

The finite SCM has `X = false` and an unbiased independent `Y`.  Thus all
observational cells with `X = true` have zero mass.  At such a cell the
conditional `P(Y | X)` is undefined, the old strict chain product is
undefined, and the guarded joint contribution is zero.  A zero *base*
conditioner is different: it leaves the complete expression undefined.

The equations below use actual observational pushforwards and kernel
evaluation, not mock partial results.  Every numerical regression is checked
by ordinary kernel reduction.  The general chain proof is also instantiated
at every assignment, without a positivity assumption.
-/

/-- Two Boolean coordinates with no allowed directed arrows. -/
def signature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

/-- One private noise bit is visible only to the `Y` mechanism. -/
def latent : LatentExtension signature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun _ child => decide (child.val = 1)

def unbiased : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- Independent finite product noise and constant `X` produce a genuine
zero-containing observational law.  No external distribution identity or
default conditional value is supplied. -/
def model : FiniteLatentSCM signature where
  latent := latent
  factor := fun _ => unbiased
  prior := FiniteProduct.record 1 (fun _ => Bool) (fun _ => unbiased)
  product_law := fun events =>
    FiniteProduct.record_rectangular_probVal 1 (fun _ => Bool)
      (fun _ => unbiased) events
  mechanism := fun child _parents inputs =>
    if atY : child.val = 1 then
      inputs ⟨0, by decide⟩ (by
        simpa only [latent] using (decide_eq_true atY))
    else false

/-- The reference selects an impossible observational `X` cell. -/
def reference : signature.Assignment := fun _ => true

def weight : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.singleton x, NodeSet.empty, NodeSet.empty⟩

def conditional : ProbabilityTerm signature :=
  .kernel ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.singleton x⟩

/-- The factor is genuinely unsupported at the impossible `X = true` cell. -/
theorem conditional_is_undefined : conditional.denote model reference = none := rfl

/-- Strict multiplication keeps its previous support propagation. -/
theorem strict_chain_is_undefined :
    (.multiply conditional weight : ProbabilityTerm signature).denote model reference =
      none := rfl

/-- Only the complete guarded contribution becomes zero.  The conditional
regression above remains undefined. -/
theorem guarded_chain_is_zero :
    (.weightedMultiply weight conditional : ProbabilityTerm signature).denote
      model reference = some QProb.zero := rfl

/-- A zero base conditioner cannot be rescued by the guard.  Here the weight
`P(Y | X = true)` is itself undefined, rather than a defined zero. -/
theorem unsupported_base_remains_undefined :
    (.weightedMultiply conditional
      (.kernel ⟨NodeSet.empty, NodeSet.empty,
        NodeSet.union (NodeSet.singleton y) (NodeSet.singleton x)⟩) :
        ProbabilityTerm signature).denote model reference = none := rfl

/-- The general zero-aware chain identity holds at every valuation of this
SCM, including both its supported and zero-probability cells. -/
noncomputable def chain_at_every_assignment (assignment : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨NodeSet.union (NodeSet.singleton y) (NodeSet.singleton x),
        NodeSet.empty, NodeSet.empty⟩)
      (.weightedMultiply weight conditional) assignment := by
  simpa only [weight, conditional, NodeSet.union_empty_right] using
    ProbabilityTerm.weightedChain_soundAt model NodeSet.empty
      (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty assignment

/-- The exact syntax comparator distinguishes guarded products from strict
ones.  Algebraic agreement on positive cells is not literal term equality. -/
theorem guarded_syntax_is_distinct :
    ProbabilityTerm.equal (.weightedMultiply weight conditional)
      (.multiply weight conditional) = false := rfl

/-- The new constructor is action-free only because both displayed kernels
are action-free; a guard does not erase causal actions from syntax. -/
theorem guarded_chain_actionFree :
    (.weightedMultiply weight conditional : ProbabilityTerm signature).ActionFree :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## A whole compiled chain, not only its two-kernel step -/

/-- At an impossible joint cell the *generated whole-host formula* has a
defined zero value, even though its final displayed conditional is undefined.
This checks the compiler's prefix weights and their direction numerically. -/
theorem compiled_joint_is_zero :
    (guardedChainTerm (NodeSet.full : NodeSet signature)).denote model reference =
      some QProb.zero := rfl

/-- The generated formula has a constructive support witness at every
assignment of this nonpositive SCM.  No positivity record is supplied. -/
noncomputable def compiled_joint_supported (assignment : signature.Assignment) :
    (guardedChainTerm (NodeSet.full : NodeSet signature)).SupportedAt model assignment :=
  guardedChainTerm_supportedAt model NodeSet.full assignment

/-- A host containing only the later variable leaves a gap in the prefix
enumeration.  The general compiled formula still denotes that host joint. -/
noncomputable def gapped_host_chain (assignment : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.empty⟩)
      (guardedChainTerm (NodeSet.singleton y)) assignment :=
  guardedChainTerm_soundAt model (NodeSet.singleton y) assignment

/-- An empty host needs no selected vertex or nonempty-list premise.  Its
generated unit formula is supported by the same general compiler. -/
noncomputable def empty_host_supported (assignment : signature.Assignment) :
    (guardedChainTerm (NodeSet.empty : NodeSet signature)).SupportedAt model assignment :=
  guardedChainTerm_supportedAt model NodeSet.empty assignment

end ZeroCellChain
end Examples
end Causality
end Thesis
