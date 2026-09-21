import MorganTianLib.Ch02.NeckVolume.CylinderModelFacts
import MorganTianLib.Ch01.RiemannianMeasureRegularity

open Set MeasureTheory Riemannian Bundle
open scoped ContDiff Manifold Topology ENNReal Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib

/-- **Math.** The coordinate Gram matrix of the round sphere--axis product,
written using the fixed three-dimensional model basis. No cylinder length enters. -/
def roundCylinderCoordinateGram (alpha : EpsilonNeckSphere)
    (u : EuclideanSpace ℝ (Fin 2)) :
    Matrix (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
      (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ℝ :=
  let p := (extChartAt (𝓡 2) alpha).symm u
  let split := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    (Module.finBasis ℝ (EuclideanSpace ℝ (Fin 3)) i)
  let lift := (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) alpha).symm p
  fun i j => roundSphereMetric.metricInner p (lift (split i).1) (lift (split j).1) +
    inner ℝ (split i).2 (split j).2

/-- **Math.** The positive coordinate density of the sphere--axis product,
restricted in later theorems to the sphere chart target. -/
def roundCylinderCoordinateDensity (alpha : EpsilonNeckSphere)
    (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.sqrt (roundCylinderCoordinateGram alpha u).det

end MorganTianLib
