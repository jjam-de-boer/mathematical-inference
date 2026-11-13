import Thesis.CausalTransport.BinaryInstrumental.Transportation

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability
open FourLabelTransportation

/-!
# Compute exact IV arm margins from the supplied observed record

Instrument and joint-cell masses are read from the actual natural weights.
When both instrument values have positive mass, use the product of those
two masses as a common total: multiply the false-arm cells by the true-arm
mass and the flipped true-arm cells by the false-arm mass.  No conditional
record, rational rounding, denominator search, or chosen representative is
needed.  Zero treatment/outcome cells remain permitted.

Finite fibre additivity proves the two normalization equations.  Direct
natural fraction algebra proves the eight joint-cell equations against the
record's real instrument marginal.  These are computed certificates, not
external semantic interfaces supplied by an optimizer caller.

The four transportation capacity inequalities are deliberately *not*
assumed true for an arbitrary observed law: incompatible IV data can fail
them.  Their necessity and sufficiency for native compatibility are separate
obligations.  A null instrument value is also a separate branch; this module
never divides by it or assigns it an observational conditional.
-/

def instrumentEvent (instrument : Bool) : Event signature.Assignment :=
  fun sample => decide (sample z = instrument)

def instrumentMass (law : FiniteProbRecord signature.Assignment) (instrument : Bool) : Nat :=
  FiniteProbRecord.eventMass law.atoms (instrumentEvent instrument)

def categoryProject (sample : signature.Assignment) : Fin 4 := encodeCategory (sample x) (sample y)

def categoryMasses (law : FiniteProbRecord signature.Assignment) (instrument : Bool) : Masses :=
  fun label => FiniteProbRecord.eventMass law.atoms
    (observedCell instrument (decodeCategory label).1 (decodeCategory label).2)

def flippedCategoryMasses (law : FiniteProbRecord signature.Assignment) : Masses :=
  fun label => FiniteProbRecord.eventMass law.atoms
    (observedCell true (decodeCategory label).1 (!(decodeCategory label).2))

private theorem encode_category_match : forall treatment outcome : Bool, forall label : Fin 4,
    decide (encodeCategory treatment outcome = label) =
      (decide (treatment = (decodeCategory label).1) && decide (outcome = (decodeCategory label).2)) := by
  decide +kernel

private theorem category_fibre (instrument : Bool) (label : Fin 4) :
    FiniteProbRecord.fibreEvent categoryProject (instrumentEvent instrument) label =
      observedCell instrument (decodeCategory label).1 (decodeCategory label).2 := by
  funext sample
  change (decide (encodeCategory (sample x) (sample y) = label) && decide (sample z = instrument)) = _
  rw [encode_category_match]
  exact Bool.and_comm _ _

/-- All four arm cells recover the actual instrument mass, even when that
mass is zero.  Only the complete record denominator is cancelled in the
underlying fibre theorem. -/
theorem categoryMasses_total (law : FiniteProbRecord signature.Assignment) (instrument : Bool) :
    sum4 (categoryMasses law instrument) = instrumentMass law instrument := by
  have split := law.eventMass_eq_listSum_fibres categoryProject (instrumentEvent instrument)
    labels labels_nodup labels_complete
  simp only [category_fibre] at split
  simpa only [categoryMasses, instrumentMass, sum4, labels, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using split.symm

theorem flippedCategoryMasses_total (law : FiniteProbRecord signature.Assignment) :
    sum4 (flippedCategoryMasses law) = instrumentMass law true := by
  calc
    _ = sum4 (categoryMasses law true) := by
      change
        FiniteProbRecord.eventMass law.atoms (observedCell true false true) +
          FiniteProbRecord.eventMass law.atoms (observedCell true false false) +
          FiniteProbRecord.eventMass law.atoms (observedCell true true true) +
          FiniteProbRecord.eventMass law.atoms (observedCell true true false) =
        FiniteProbRecord.eventMass law.atoms (observedCell true false false) +
          FiniteProbRecord.eventMass law.atoms (observedCell true false true) +
          FiniteProbRecord.eventMass law.atoms (observedCell true true false) +
          FiniteProbRecord.eventMass law.atoms (observedCell true true true)
      ac_rfl
    _ = _ := categoryMasses_total law true

/-- The two Boolean instrument masses partition the entire observed law.
Thus at least one instrument value is nonnull, without a global decision
principle on arbitrary semantic propositions. -/
theorem instrumentMass_partition (law : FiniteProbRecord signature.Assignment) :
    instrumentMass law false + instrumentMass law true = law.den := by
  have complement : (fun sample => !(instrumentEvent false sample)) = instrumentEvent true := by
    funext sample
    cases value : sample z <;> simp [instrumentEvent, value]
  have partition := FiniteProbRecord.eventMass_add_complement law.atoms (instrumentEvent false)
  rw [complement] at partition
  exact partition.trans law.total_mass

def observedTotal (law : FiniteProbRecord signature.Assignment) : Nat := instrumentMass law false * instrumentMass law true
def observedRows (law : FiniteProbRecord signature.Assignment) : Masses :=
  fun label => categoryMasses law false label * instrumentMass law true
def observedColumns (law : FiniteProbRecord signature.Assignment) : Masses :=
  fun label => flippedCategoryMasses law label * instrumentMass law false

theorem observedTotal_positive (law : FiniteProbRecord signature.Assignment)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    0 < observedTotal law := Nat.mul_pos falsePositive truePositive

theorem observedRows_total (law : FiniteProbRecord signature.Assignment) : sum4 (observedRows law) = observedTotal law :=
  (sum4_scale (categoryMasses law false) (instrumentMass law true)).trans
    (congrArg (fun mass => mass * instrumentMass law true) (categoryMasses_total law false))

theorem observedColumns_total (law : FiniteProbRecord signature.Assignment) : sum4 (observedColumns law) = observedTotal law :=
  (sum4_scale (flippedCategoryMasses law) (instrumentMass law false)).trans
    ((congrArg (fun mass => mass * instrumentMass law false) (flippedCategoryMasses_total law)).trans (Nat.mul_comm _ _))

theorem instrumentMarginal_probVal (law : FiniteProbRecord signature.Assignment) (instrument : Bool) :
    QProb.Equiv ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent instrument))
      ⟨instrumentMass law instrument, law.den, law.den_pos⟩ :=
  law.map_probVal (fun sample => sample z) (FiniteProbRecord.singletonEvent instrument)

/-- All eight normalized arm equations follow from the supplied
observed data.  Positivity justifies the computed common denominator, not
positivity of every cell or the existence of a compatible causal model. -/
def observedArmMarginals (law : FiniteProbRecord signature.Assignment)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    ArmMarginals law (observedTotal law) (observedTotal_positive law falsePositive truePositive)
      (observedRows law) (observedColumns law) where
  false_cells := by
    intro treatment outcome
    have coefficient := QProb.mul_congr (instrumentMarginal_probVal law false)
      (QProb.equiv_refl (⟨observedRows law (encodeCategory treatment outcome), observedTotal law,
        observedTotal_positive law falsePositive truePositive⟩ : QProb))
    have algebra : QProb.Equiv (law.probVal (observedCell false treatment outcome))
        (QProb.mul ⟨instrumentMass law false, law.den, law.den_pos⟩
          ⟨observedRows law (encodeCategory treatment outcome), observedTotal law,
            observedTotal_positive law falsePositive truePositive⟩) := by
      simp only [QProb.Equiv, QProb.mul, FiniteProbRecord.probVal, observedRows, observedTotal,
        categoryMasses, decode_encodeCategory]
      ac_rfl
    exact QProb.equiv_trans algebra (QProb.equiv_symm coefficient)
  true_cells := by
    intro treatment outcome
    have coefficient := QProb.mul_congr (instrumentMarginal_probVal law true)
      (QProb.equiv_refl (⟨observedColumns law (encodeCategory treatment (!outcome)), observedTotal law,
        observedTotal_positive law falsePositive truePositive⟩ : QProb))
    have algebra : QProb.Equiv (law.probVal (observedCell true treatment outcome))
        (QProb.mul ⟨instrumentMass law true, law.den, law.den_pos⟩
          ⟨observedColumns law (encodeCategory treatment (!outcome)), observedTotal law,
            observedTotal_positive law falsePositive truePositive⟩) := by
      simp only [QProb.Equiv, QProb.mul, FiniteProbRecord.probVal, observedColumns, observedTotal,
        flippedCategoryMasses, decode_encodeCategory, Bool.not_not]
      ac_rfl
    exact QProb.equiv_trans algebra (QProb.equiv_symm coefficient)

end BinaryInstrumental
end Causality
end Thesis
