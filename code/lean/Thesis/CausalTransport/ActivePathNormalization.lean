import Thesis.CausalTransport.DSeparationWitness

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

/-!
# Constructive collider normalization of an active path

A directed activation branch may return to its active path.  Rerouting along
that branch can remove a collider, but it can also replace it by a later
collider.  Merely minimizing path length, or merely minimizing the number of
colliders, does not justify ruling out the second possibility.

This module establishes the finite selection needed for that argument.  The
primary objective is the number of internal colliders; among equal counts,
the secondary objective maximizes their observed topological ranks.  A bounded
natural-number score encodes both objectives.  The least-score witness search
returns actual path data, and its proved optimality derives both objectives.
No classical minimizer or caller-supplied normalization flag is used.

This is the selection stage, not the rerouting theorem.  It does not yet prove
that activation branches avoid the chosen path, and it makes no claim about
intersections with the small hedge forest or about conditional countermodels.
The underlying exhaustive search is only intended for normal-form witnesses,
not for ordinary separation decisions or large executable graph regressions.
-/

namespace PathSpecification

/-! ## Executable collider statistics -/

/-- Count internal collider windows.  Endpoints are never counted, and the
Boolean test uses the exact mutilated expanded graph, including latent pairs. -/
def colliderCount (G : ObservedGraph S) (m : GraphMutilation S) : List (SeparationNode S) -> Nat
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | previous :: middle :: next :: rest =>
      (if isColliderBool G m previous middle next then 1 else 0) +
        colliderCount G m (middle :: next :: rest)

/-- Observed ranks are the signature's constructive topological order.
A latent vertex receives rank zero; in a well-formed expanded graph it cannot
be a collider because no expanded arrow enters a latent vertex. -/
def observedColliderRank : SeparationNode S -> Nat
  | .observed node => node.val
  | .latentPair _ _ => 0

/-- Sum the ranks of internal colliders, using the same windows as the
primary count.  This is a tie-breaker, not a substitute for that count. -/
def colliderRankSum (G : ObservedGraph S) (m : GraphMutilation S) : List (SeparationNode S) -> Nat
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | previous :: middle :: next :: rest =>
      (if isColliderBool G m previous middle next then observedColliderRank middle else 0) +
        colliderRankSum G m (middle :: next :: rest)

private theorem observedColliderRank_le_count (node : SeparationNode S) :
    observedColliderRank node ≤ S.count := by
  cases node with
  | observed node => exact Nat.le_of_lt node.isLt
  | latentPair _ _ => exact Nat.zero_le _

/-- Even before simplicity is used, the rank sum is bounded by list length
times the observed alphabet size.  The proof inspects the list; it does not
decide an arbitrary proposition about the path. -/
theorem colliderRankSum_le_length_mul_count (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : colliderRankSum G m nodes ≤ nodes.length * S.count := by
  induction nodes with
  | nil => exact Nat.zero_le _
  | cons previous tail inductionHypothesis =>
      cases tail with
      | nil => exact Nat.zero_le _
      | cons middle rest =>
          cases rest with
          | nil => exact Nat.zero_le _
          | cons next tail =>
              have middleBound := observedColliderRank_le_count middle
              cases collider : isColliderBool G m previous middle next <;>
                simp only [colliderRankSum, collider, Bool.false_eq_true, if_false, if_true,
                  List.length_cons, Nat.succ_mul] at * <;> omega

/-- A uniform bound for rank sums of simple expanded paths.  Keeping this
bound independent of a particular path makes equal-count scores comparable. -/
def colliderRankBound (G : ObservedGraph S) : Nat := G.separationNodes.length * S.count

theorem colliderRankSum_le_bound_of_nodup (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (simple : nodes.Nodup) :
    colliderRankSum G m nodes ≤ colliderRankBound G := by
  have lengthBound := nodup_length_le_of_subset SeparationNode.beq SeparationNode.beq_eq_true_iff
    nodes G.separationNodes simple (fun node _member => SeparationNode.mem_all node)
  exact Nat.le_trans (colliderRankSum_le_length_mul_count G m nodes)
    (Nat.mul_le_mul_right S.count lengthBound)

/-- One fewer collider outweighs every possible change in the secondary
rank term.  With equal counts, larger rank sums have smaller scores. -/
def colliderNormalizationScore (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : Nat :=
  (colliderRankBound G + 1) * colliderCount G m nodes +
    (colliderRankBound G - colliderRankSum G m nodes)

/-! ## The score really has the advertised lexicographic priority -/

/-- The primary objective dominates the entire bounded secondary term.
In particular, a later-rank competitor cannot compensate for one extra collider. -/
theorem colliderNormalizationScore_lt_of_count_lt (G : ObservedGraph S) (m : GraphMutilation S)
    (left right : List (SeparationNode S))
    (fewer : colliderCount G m left < colliderCount G m right) :
    colliderNormalizationScore G m left < colliderNormalizationScore G m right := by
  have primary := Nat.mul_le_mul_left (colliderRankBound G + 1) (Nat.succ_le_of_lt fewer)
  rw [Nat.mul_succ] at primary
  unfold colliderNormalizationScore
  omega

/-- At equal collider count, replacing an earlier collider by a later one
strictly improves the score.  Simplicity supplies the common rank-sum bound,
so natural subtraction does not truncate either competing secondary term. -/
theorem colliderNormalizationScore_lt_of_rank_lt (G : ObservedGraph S) (m : GraphMutilation S)
    (left right : List (SeparationNode S)) (leftSimple : left.Nodup) (rightSimple : right.Nodup)
    (sameCount : colliderCount G m left = colliderCount G m right)
    (later : colliderRankSum G m right < colliderRankSum G m left) :
    colliderNormalizationScore G m left < colliderNormalizationScore G m right := by
  have leftBound := colliderRankSum_le_bound_of_nodup G m left leftSimple
  have rightBound := colliderRankSum_le_bound_of_nodup G m right rightSimple
  unfold colliderNormalizationScore
  rw [sameCount]
  omega

/-! ## Actual least-collider, latest-rank path data -/

/-- Select a collider-normal active path by the finite least-score search.
The existence argument only certifies that search failure is impossible. -/
def colliderNormalActivePathOfNonempty (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (existsPath : Nonempty (ActivePath G m conditioned source target)) :
    ActivePath G m conditioned source target :=
  leastScoreActivePathOfNonempty G m conditioned source target (colliderNormalizationScore G m) existsPath

/-- No competing simple active path with these endpoints has fewer colliders.
This is derived from the executable search, not stored as an assumption. -/
theorem colliderNormalActivePathOfNonempty_count_minimal (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (existsPath : Nonempty (ActivePath G m conditioned source target))
    (competitor : ActivePath G m conditioned source target) :
    colliderCount G m (colliderNormalActivePathOfNonempty G m conditioned source target existsPath).nodes ≤
      colliderCount G m competitor.nodes := by
  have optimal := leastScoreActivePathOfNonempty_minimal G m conditioned source target
    (colliderNormalizationScore G m) existsPath competitor
  apply Nat.le_of_not_gt
  intro fewer
  exact Nat.not_lt_of_ge optimal (colliderNormalizationScore_lt_of_count_lt G m _ _ fewer)

/-- Among equal-count competitors, the selected path has greatest collider
rank sum.  Thus a rerouting which preserves count but increases ranks will
contradict a theorem of the selected data. -/
theorem colliderNormalActivePathOfNonempty_rank_maximal (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (existsPath : Nonempty (ActivePath G m conditioned source target))
    (competitor : ActivePath G m conditioned source target)
    (sameCount : colliderCount G m competitor.nodes =
      colliderCount G m (colliderNormalActivePathOfNonempty G m conditioned source target existsPath).nodes) :
    colliderRankSum G m competitor.nodes ≤
      colliderRankSum G m (colliderNormalActivePathOfNonempty G m conditioned source target existsPath).nodes := by
  have optimal := leastScoreActivePathOfNonempty_minimal G m conditioned source target
    (colliderNormalizationScore G m) existsPath competitor
  apply Nat.le_of_not_gt
  intro later
  exact Nat.not_lt_of_ge optimal (colliderNormalizationScore_lt_of_rank_lt G m _ _ competitor.simple
    (colliderNormalActivePathOfNonempty G m conditioned source target existsPath).simple sameCount later)

end PathSpecification

end Causality
end Thesis
