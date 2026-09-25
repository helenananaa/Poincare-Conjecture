import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import PoincareConjecture.ParallelImplementation.CoordinateActualVectorDerivative
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateLieDerivativeIdentification
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
theorem lie_eq_actual_coordinate_derivatives
    (g h : E3 → Mat) (d : E3 → First) (dd : Second) (dh : Idx → Mat) (x : E3)
    (hg : ∀ a i j, HasDerivAt (fun t : ℝ => g (x + t • EuclideanSpace.single a 1) i j) (d x a i j) 0)
    (hh : ∀ a i j, HasDerivAt (fun t : ℝ => h (x + t • EuclideanSpace.single a 1) i j) (dh a i j) 0)
    (hd : ∀ a b i j, HasDerivAt (fun t : ℝ => d (x + t • EuclideanSpace.single a 1) b i j) (dd a b i j) 0)
    (hInv : ∀ a : Idx, ∀ᶠ t : ℝ in 𝓝 0, ∀ i j : Idx,
      (∑ k : Idx, g (x + t • EuclideanSpace.single a 1) i k * h (x + t • EuclideanSpace.single a 1) k j) = if i = j then 1 else 0)
    (hLeft : ∀ i j : Idx, (∑ k : Idx, h x i k * g x k j) = if i = j then 1 else 0) :

    ∀ i j : Idx,
      (∑ k : Idx, (deturckVector (h x) (d x) k * d x k i j +
        g x k j * deriv (fun t : ℝ => deturckVector (h (x + t • EuclideanSpace.single i 1)) (d (x + t • EuclideanSpace.single i 1)) k) 0 +
        g x i k * deriv (fun t : ℝ => deturckVector (h (x + t • EuclideanSpace.single j 1)) (d (x + t • EuclideanSpace.single j 1)) k) 0)) =
        lieMetric (g x) (h x) (d x) dd i j :=
/- SWARM_PROOF_BEGIN -/
by
  have hcoord (a k : Idx) :
      deriv (fun t : ℝ =>
        deturckVector (h (x + t • EuclideanSpace.single a 1))
          (d (x + t • EuclideanSpace.single a 1)) k) 0 =
        vectorDerivative (h x) (d x) dd a k := by
    let gc : ℝ → Mat := fun t => g (x + t • EuclideanSpace.single a 1)
    let hc : ℝ → Mat := fun t => h (x + t • EuclideanSpace.single a 1)
    let dc : ℝ → First := fun t => d (x + t • EuclideanSpace.single a 1)
    have hactual := CoordinateActualVectorDerivative.actual_vector_derivative
      gc hc dc (dh a) dd 0 a
      (by
        intro i j
        simpa [gc, dc] using hg a i j)
      (by
        intro i j
        simpa [hc] using hh a i j)
      (by
        intro b i j
        simpa [dc] using hd a b i j)
      (by
        simpa [gc, hc] using hInv a)
      (by
        simpa [gc, hc] using hLeft)
    have hk := hactual k
    simpa [gc, hc, dc] using hk.deriv
  intro i j
  change (∑ k : Idx,
      (deturckVector (h x) (d x) k * d x k i j +
        g x k j * deriv (fun t : ℝ =>
          deturckVector (h (x + t • EuclideanSpace.single i 1))
            (d (x + t • EuclideanSpace.single i 1)) k) 0 +
        g x i k * deriv (fun t : ℝ =>
          deturckVector (h (x + t • EuclideanSpace.single j 1))
            (d (x + t • EuclideanSpace.single j 1)) k) 0)) =
      ∑ k : Idx,
        (deturckVector (h x) (d x) k * d x k i j +
          g x k j * vectorDerivative (h x) (d x) dd i k +
          g x i k * vectorDerivative (h x) (d x) dd j k)
  apply Finset.sum_congr rfl
  intro k _
  rw [hcoord i k, hcoord j k]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateLieDerivativeIdentification
