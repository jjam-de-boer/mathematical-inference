import Thesis.Probability.ConstructiveRealFaceMultipliers
import Thesis.Probability.ConstructiveRealEntropyKKTNecessity

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

/-- Construct the ideal maximum and fit natural-unit signed KKT coefficients
from a positive feasible witness. The optimizer's floors are derived by the
entropy interior theorem, rather than supplied as an assumption on an
unknown optimum. Finite elimination is effective, with no efficiency claim. -/
def RealLaw.fittedNaturalKKT {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) :
    {certificate : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (feasible.maximize.mass i).value
      (interiorLower variables (lower i)) (feasible.maximize_positive lower positive i)) // certificate.KKTAt feasible.maximize} :=
  feasible.maximize.naturalKKTMultipliers feasible.maximize_maximal
    (fun i => interiorLower variables (lower i)) (feasible.maximize_positive lower positive)

/-- The same fitted signed coefficients describe the actual normalized
Gibbs law. Units, signs and complementary products belong to one computed
coefficient system. -/
theorem RealLaw.fittedKKT_gibbsForm {problem : RationalEntropyProblem variables} (feasible : problem.RealLaw)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (feasible.mass i).value) (i : Fin variables) :
    let certificate := (feasible.fittedNaturalKKT lower positive).val
    Equiv (feasible.maximize.mass i).value (mul (neg (certificate.score i)).exp certificate.partitionInverse) :=
  gibbsForm_of_coefficients feasible.maximize (fun i => interiorLower variables (lower i))
    (feasible.maximize_positive lower positive) (feasible.fittedNaturalKKT lower positive).val i

end Thesis.Probability.Distros.RationalEntropyProblem

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- Starting from any rational feasible seed, compute the feasible support
face, its ideal maximum, and signed natural KKT multipliers for the original
expectation intervals restricted to that face. The seed may contain zeros.
Forced-zero coordinates require no finite multiplier on the original grid. -/
def CompatibleLaw.faceKKTMultipliers [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw) :
    {certificate : seed.supportFace.analyticProblem.LagrangeCoefficients (fun i =>
      entropyNaturalGradient (seed.faceSeed.maximize.mass i).value
        (RationalEntropyProblem.interiorLower seed.supportFace.cells.length (seed.faceFloors i))
        (seed.faceSeed.maximize_positive seed.faceFloors seed.faceFloors_le i)) // certificate.KKTAt seed.faceSeed.maximize} :=
  seed.faceSeed.fittedNaturalKKT seed.faceFloors seed.faceFloors_le

/-- The computed face Gibbs representation uses coefficients satisfying
interval signs and complementary slackness, including redundant rows. -/
theorem CompatibleLaw.faceKKT_gibbsForm [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw)
    (i : Fin seed.supportFace.cells.length) :
    let certificate := seed.faceKKTMultipliers.val
    Equiv (seed.faceSeed.maximize.mass i).value (mul (neg (certificate.score i)).exp certificate.partitionInverse) :=
  seed.faceSeed.fittedKKT_gibbsForm seed.faceFloors seed.faceFloors_le i

end Thesis.Probability.Distros.PartialMomentProblem
