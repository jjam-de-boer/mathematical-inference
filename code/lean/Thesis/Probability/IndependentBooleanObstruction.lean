import Thesis.Probability.RationalSquareObstruction
import Thesis.Probability.FiniteRecordOverlap

namespace Thesis.Probability.IndependentBooleanObstruction

open FiniteProbRecord

/-!
# An exact rational infeasibility obstruction for fixed finite mechanisms

Let `A`, `B`, `F` be independent Boolean sources and observe
`V = A && B`, `O = if F then A else !B`. No finite rational source records
give the uniform observed law on `(O, V)`. More strongly, the three requested
probabilities `P(V)=1/2`, `P(O && V)=1/4`, `P(O)=1/2` are inconsistent.

The result quantifies over arbitrary original source records, including
repeated Boolean labels, zero cells and unreduced denominators. Independence
is implemented by actual finite products, not an external moment interface.
Event-mass identities bind the polynomial equations to these concrete laws.
They imply a fraction whose square is one half, contradicting the finite
descent theorem. No real-valued or irrational probabilities are introduced.

The mechanisms are fixed. This is not graph-wide incompatibility: replacing
them by `V = A`, `O = F` allows a rational uniform law. Nor does this example
establish impossibility of a general rational feasibility algorithm. It does
show why an unrestricted rational feasibility theorem needs its own proof,
rather than an automatic transfer from an enlarged scalar domain.
-/

abbrev Input := Bool × (Bool × Bool)

def inputLaw (a b f : FiniteProbRecord Bool) : FiniteProbRecord Input := f.product (a.product b)

/-- The first input is the switch, followed by the two shared readout inputs. -/
def readout (state : Input) : Bool × Bool :=
  ((if state.1 then state.2.1 else !state.2.2), state.2.1 && state.2.2)

def law (a b f : FiniteProbRecord Bool) : FiniteProbRecord (Bool × Bool) :=
  (inputLaw a b f).map readout

def uniform : FiniteProbRecord (Bool × Bool) :=
  ⟨[((false, false), 1), ((false, true), 1), ((true, false), 1), ((true, true), 1)], 4, by decide, rfl⟩

def vEvent : Event Input := fun state => state.2.1 && state.2.2
def oEvent : Event Input := fun state => if state.1 then state.2.1 else !state.2.2
def jointEvent : Event Input := fun state => oEvent state && vEvent state
private def onBranch : Event Input := fun state => state.1 && state.2.1
private def offBranch : Event Input := fun state => !state.1 && !state.2.2

theorem v_mass (a b f : FiniteProbRecord Bool) :
    eventMass (inputLaw a b f).atoms vEvent = f.den * (eventMass a.atoms id * eventMass b.atoms id) := by
  have pair : eventMass (a.product b).atoms (fun state => state.1 && state.2) =
      eventMass a.atoms id * eventMass b.atoms id := eventMass_weightedCartesian a.atoms b.atoms id id
  have outer : eventMass (inputLaw a b f).atoms vEvent =
      eventMass f.atoms topEvent * eventMass (a.product b).atoms (fun state => state.1 && state.2) :=
    eventMass_weightedCartesian f.atoms (a.product b).atoms topEvent
      (fun state : Bool × Bool => state.1 && state.2)
  rw [pair, eventMass_top, f.total_mass] at outer
  exact outer

theorem joint_mass (a b f : FiniteProbRecord Bool) :
    eventMass (inputLaw a b f).atoms jointEvent =
      eventMass f.atoms id * (eventMass a.atoms id * eventMass b.atoms id) := by
  have pointwise : jointEvent = (fun state : Input => state.1 && (state.2.1 && state.2.2)) := by
    funext state
    rcases state with ⟨switch, first, second⟩
    cases switch <;> cases first <;> cases second <;> rfl
  rw [pointwise]
  have pair : eventMass (a.product b).atoms (fun state => state.1 && state.2) =
      eventMass a.atoms id * eventMass b.atoms id := eventMass_weightedCartesian a.atoms b.atoms id id
  exact (eventMass_weightedCartesian f.atoms (a.product b).atoms id
    (fun state : Bool × Bool => state.1 && state.2)).trans
      (congrArg (fun mass => eventMass f.atoms id * mass) pair)

theorem o_mass (a b f : FiniteProbRecord Bool) :
    eventMass (inputLaw a b f).atoms oEvent =
      eventMass f.atoms id * (eventMass a.atoms id * b.den) +
        eventMass f.atoms (fun bit => !bit) * (a.den * eventMass b.atoms (fun bit => !bit)) := by
  have firstPair : eventMass (a.product b).atoms (fun state => state.1) = eventMass a.atoms id * b.den := by
    simpa only [product, topEvent, Bool.and_true, eventMass_top, b.total_mass] using
      (eventMass_weightedCartesian a.atoms b.atoms id topEvent)
  have secondPair : eventMass (a.product b).atoms (fun state => !state.2) = a.den * eventMass b.atoms (fun bit => !bit) := by
    simpa only [product, topEvent, Bool.true_and, eventMass_top, a.total_mass] using
      (eventMass_weightedCartesian a.atoms b.atoms topEvent (fun bit => !bit))
  have firstMass : eventMass (inputLaw a b f).atoms onBranch = eventMass f.atoms id * (eventMass a.atoms id * b.den) := by
    exact (eventMass_weightedCartesian f.atoms (a.product b).atoms id (fun state => state.1)).trans
      (congrArg (fun mass => eventMass f.atoms id * mass) firstPair)
  have secondMass : eventMass (inputLaw a b f).atoms offBranch =
      eventMass f.atoms (fun bit => !bit) * (a.den * eventMass b.atoms (fun bit => !bit)) := by
    exact (eventMass_weightedCartesian f.atoms (a.product b).atoms (fun bit => !bit) (fun state => !state.2)).trans
      (congrArg (fun mass => eventMass f.atoms (fun bit => !bit) * mass) secondPair)
  have cover : union onBranch offBranch = oEvent := by
    funext state
    rcases state with ⟨switch, first, second⟩
    cases switch <;> cases first <;> cases second <;> rfl
  have apart : inter onBranch offBranch = (fun _ => false) := by
    funext state
    rcases state with ⟨switch, first, second⟩
    cases switch <;> cases first <;> cases second <;> rfl
  have partition := eventMass_union_add_inter (inputLaw a b f).atoms onBranch offBranch
  rw [cover, apart, eventMass_false, Nat.add_zero, firstMass, secondMass] at partition
  exact partition

/-- All assumptions below are exact natural mass equations. No source
probability is divided out: only positive total masses and the positive
product forced by the requested conjunction probability are cancelled. -/
private theorem mass_equations_inconsistent
    (a b bZero f fZero aDen bDen fDen : Nat)
    (aPositive : 0 < aDen) (bPositive : 0 < bDen) (fPositive : 0 < fDen)
    (bPartition : b + bZero = bDen) (fPartition : f + fZero = fDen)
    (halfV : 2 * (a * b) = aDen * bDen)
    (quarterJoint : 4 * (f * (a * b)) = fDen * (aDen * bDen))
    (halfO : 2 * (f * (a * bDen) + fZero * (aDen * bZero)) = fDen * (aDen * bDen)) : False := by
  have productPositive : 0 < a * b := by
    have totalPositive := Nat.mul_pos aPositive bPositive
    omega
  have switchCleared : 4 * f = 2 * fDen := by
    apply Nat.eq_of_mul_eq_mul_right productPositive
    calc
      (4 * f) * (a * b) = 4 * (f * (a * b)) := by ac_rfl
      _ = fDen * (aDen * bDen) := quarterJoint
      _ = fDen * (2 * (a * b)) := by rw [halfV]
      _ = (2 * fDen) * (a * b) := by ac_rfl
  have switchHalf : 2 * f = fDen := by omega
  have switchPositive : 0 < f := by omega
  have switchEqual : fZero = f := by omega
  have outcomeCleared : a * bDen + aDen * bZero = aDen * bDen := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by decide : 0 < 2) switchPositive)
    calc
      (2 * f) * (a * bDen + aDen * bZero) =
          2 * (f * (a * bDen) + fZero * (aDen * bZero)) := by
            rw [switchEqual, Nat.mul_add, Nat.mul_add]
            ac_rfl
      _ = fDen * (aDen * bDen) := halfO
      _ = (2 * f) * (aDen * bDen) := by rw [switchHalf]
  have equalRatio : a * bDen = aDen * b := by
    apply Nat.add_right_cancel (m := aDen * bZero)
    calc
      a * bDen + aDen * bZero = aDen * bDen := outcomeCleared
      _ = aDen * b + aDen * bZero := by rw [← bPartition, Nat.mul_add]
  have square : 2 * (a * a) = aDen * aDen := by
    apply Nat.eq_of_mul_eq_mul_right bPositive
    calc
      (2 * (a * a)) * bDen = (2 * a) * (a * bDen) := by ac_rfl
      _ = (2 * a) * (aDen * b) := by rw [equalRatio]
      _ = aDen * (2 * (a * b)) := by ac_rfl
      _ = aDen * (aDen * bDen) := by rw [halfV]
      _ = (aDen * aDen) * bDen := by ac_rfl
  exact RationalSquareObstruction.twice_square_ne_square a aDen aPositive square

/-- A finite, rational, original-record incompatibility theorem for the
fixed readout, stronger than merely excluding its uniform joint table. -/
theorem no_target_marginals (a b f : FiniteProbRecord Bool) :
    ¬ (QProb.Equiv ((law a b f).probVal Prod.snd) ⟨1, 2, by decide⟩ ∧
      QProb.Equiv ((law a b f).probVal (fun pair => pair.1 && pair.2)) ⟨1, 4, by decide⟩ ∧
      QProb.Equiv ((law a b f).probVal Prod.fst) ⟨1, 2, by decide⟩) := by
  rintro ⟨halfV, quarterJoint, halfO⟩
  have vInput := QProb.equiv_trans (QProb.equiv_symm ((inputLaw a b f).map_probVal readout Prod.snd)) halfV
  have jointInput := QProb.equiv_trans
    (QProb.equiv_symm ((inputLaw a b f).map_probVal readout (fun pair => pair.1 && pair.2))) quarterJoint
  have oInput := QProb.equiv_trans (QProb.equiv_symm ((inputLaw a b f).map_probVal readout Prod.fst)) halfO
  change eventMass (inputLaw a b f).atoms vEvent * 2 = 1 * (f.den * (a.den * b.den)) at vInput
  change eventMass (inputLaw a b f).atoms jointEvent * 4 = 1 * (f.den * (a.den * b.den)) at jointInput
  change eventMass (inputLaw a b f).atoms oEvent * 2 = 1 * (f.den * (a.den * b.den)) at oInput
  rw [v_mass, Nat.one_mul] at vInput
  rw [joint_mass, Nat.one_mul] at jointInput
  rw [o_mass, Nat.one_mul] at oInput
  have clearedV : 2 * (eventMass a.atoms id * eventMass b.atoms id) = a.den * b.den := by
    apply Nat.eq_of_mul_eq_mul_left f.den_pos
    calc
      f.den * (2 * (eventMass a.atoms id * eventMass b.atoms id)) =
          (f.den * (eventMass a.atoms id * eventMass b.atoms id)) * 2 := by ac_rfl
      _ = f.den * (a.den * b.den) := vInput
  have bPartition := eventMass_add_complement b.atoms id
  have fPartition := eventMass_add_complement f.atoms id
  rw [b.total_mass] at bPartition
  rw [f.total_mass] at fPartition
  exact mass_equations_inconsistent _ _ _ _ _ _ _ _ a.den_pos b.den_pos f.den_pos
    bPartition fPartition clearedV (by simpa only [Nat.mul_comm] using jointInput)
    (by simpa only [Nat.mul_comm] using oInput)

theorem uniform_v : QProb.Equiv (uniform.probVal Prod.snd) ⟨1, 2, by decide⟩ := by decide +kernel
theorem uniform_joint : QProb.Equiv (uniform.probVal (fun pair => pair.1 && pair.2)) ⟨1, 4, by decide⟩ := by decide +kernel
theorem uniform_o : QProb.Equiv (uniform.probVal Prod.fst) ⟨1, 2, by decide⟩ := by decide +kernel

theorem not_uniform (a b f : FiniteProbRecord Bool) :
    ¬ (∀ event, QProb.Equiv ((law a b f).probVal event) (uniform.probVal event)) := by
  intro fitted
  exact no_target_marginals a b f
    ⟨QProb.equiv_trans (fitted Prod.snd) uniform_v,
      QProb.equiv_trans (fitted (fun pair => pair.1 && pair.2)) uniform_joint,
      QProb.equiv_trans (fitted Prod.fst) uniform_o⟩

section ArbitrarySourcePresentations

variable {A : Type u} {B : Type v} {F : Type w}

/-- Private sources may have any finite record presentation, even an infinite
ambient label type. Only their displayed Boolean readouts enter the fixed
mechanisms; no two-state assumption is imposed on the private sources. -/
def sourceLaw (a : FiniteProbRecord A) (b : FiniteProbRecord B) (f : FiniteProbRecord F)
    (aBit : A → Bool) (bBit : B → Bool) (fBit : F → Bool) : FiniteProbRecord (Bool × Bool) :=
  (f.product (a.product b)).map (fun state => readout (fBit state.1, aBit state.2.1, bBit state.2.2))

/-- Push the explicit readouts through the actual products, retaining every
observed event. There is no supplied preservation or independence interface. -/
theorem sourceLaw_probVal (a : FiniteProbRecord A) (b : FiniteProbRecord B) (f : FiniteProbRecord F)
    (aBit : A → Bool) (bBit : B → Bool) (fBit : F → Bool) (event : Event (Bool × Bool)) :
    QProb.Equiv ((law (a.map aBit) (b.map bBit) (f.map fBit)).probVal event)
      ((sourceLaw a b f aBit bBit fBit).probVal event) := by
  have coded := (inputLaw (a.map aBit) (b.map bBit) (f.map fBit)).map_probVal readout event
  have switch := f.product_map_left_probVal ((a.map aBit).product (b.map bBit)) fBit
    (fun state => event (readout state))
  have slices (sample : F) :
      QProb.Equiv (((a.map aBit).product (b.map bBit)).probVal (fun pair => event (readout (fBit sample, pair))))
        ((a.product b).probVal (fun pair => event (readout (fBit sample, aBit pair.1, bBit pair.2)))) :=
    QProb.equiv_trans
      (a.product_map_left_probVal (b.map bBit) aBit (fun pair => event (readout (fBit sample, pair))))
      (a.product_map_right_probVal b bBit (fun pair => event (readout (fBit sample, aBit pair.1, pair.2))))
  have original := f.product_probVal_equiv_of_slices ((a.map aBit).product (b.map bBit)) (a.product b)
    (fun state => event (readout (fBit state.1, state.2)))
    (fun state => event (readout (fBit state.1, aBit state.2.1, bBit state.2.2))) slices
  exact QProb.equiv_trans coded (QProb.equiv_trans switch (QProb.equiv_trans original
    (QProb.equiv_symm ((f.product (a.product b)).map_probVal
      (fun state => readout (fBit state.1, aBit state.2.1, bBit state.2.2)) event))))

/-- Enlarging or relabelling the finite private source alphabets cannot
repair this fixed Boolean-readout obstruction. Denominators are unbounded. -/
theorem sourceLaw_not_uniform (a : FiniteProbRecord A) (b : FiniteProbRecord B) (f : FiniteProbRecord F)
    (aBit : A → Bool) (bBit : B → Bool) (fBit : F → Bool) :
    ¬ (∀ event, QProb.Equiv ((sourceLaw a b f aBit bBit fBit).probVal event) (uniform.probVal event)) := by
  intro fitted
  exact not_uniform (a.map aBit) (b.map bBit) (f.map fBit)
    (fun event => QProb.equiv_trans (sourceLaw_probVal a b f aBit bBit fBit event) (fitted event))

end ArbitrarySourcePresentations

end Thesis.Probability.IndependentBooleanObstruction
