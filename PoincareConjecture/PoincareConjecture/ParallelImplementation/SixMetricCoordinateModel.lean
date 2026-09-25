import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
def metricOp (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (u : E3 → E6) (x : E3) : E3 →L[ℝ] E3 := 1 + E (u x)
def metricCoefficients (u : E3 → E6) (x : E3) : Mat :=
  fun i j => (if i=j then 1 else 0) + symmetricSixMatrix (u x) i j
def firstCoefficients (u : E3 → E6) (x : E3) : First :=
  fun a i j => symmetricSixMatrix (fderiv ℝ u x (EuclideanSpace.single a 1)) i j
def secondCoefficients (u : E3 → E6) (x : E3) : Second :=
  fun a b i j => symmetricSixMatrix (fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j
def inverseCoefficients (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (u : E3 → E6) (x : E3) : Mat :=
  fun i j => (Ring.inverse (metricOp E u x) (EuclideanSpace.single j 1)) i
def christoffelField (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (u : E3 → E6) (x : E3) : First :=
  christoffel (inverseCoefficients E u x) (firstCoefficients u x)
def deturckField (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (u : E3 → E6) (x : E3) : Idx → ℝ :=
  deturckVector (inverseCoefficients E u x) (firstCoefficients u x)
/-- Ricci's coordinate expression, using actual scalar derivatives of Christoffel fields. -/
def actualRicci (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (u : E3 → E6) (x : E3) : Mat :=
  fun i j => (∑ k : Idx,
    (deriv (fun t : ℝ => christoffelField E u (x+t • EuclideanSpace.single k 1) k i j) 0 -
     deriv (fun t : ℝ => christoffelField E u (x+t • EuclideanSpace.single j 1) k i k) 0)) +
    ∑ k : Idx, ∑ l : Idx, (christoffelField E u x k k l * christoffelField E u x l i j -
      christoffelField E u x k j l * christoffelField E u x l i k)
/-- Lie derivative coordinate expression, using actual derivatives of the DeTurck vector. -/
def actualLie (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (u : E3 → E6) (x : E3) : Mat :=
  fun i j => ∑ k : Idx,
    (deturckField E u x k * firstCoefficients u x k i j +
      metricCoefficients u x k j * deriv
        (fun t : ℝ => deturckField E u (x+t • EuclideanSpace.single i 1) k) 0 +
      metricCoefficients u x i k * deriv
        (fun t : ℝ => deturckField E u (x+t • EuclideanSpace.single j 1) k) 0)
end PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
