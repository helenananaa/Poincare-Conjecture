import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import PoincareConjecture.ParallelImplementation.CoordinateActualGammaDerivative
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateRicciDerivativeIdentification
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
theorem ricci_eq_actual_coordinate_derivatives
    (g h : E3 → Mat) (d : E3 → First) (dd : Second) (dh : Idx → Mat) (x : E3)
    (hg : ∀ a i j, HasDerivAt (fun t : ℝ => g (x + t • EuclideanSpace.single a 1) i j) (d x a i j) 0)
    (hh : ∀ a i j, HasDerivAt (fun t : ℝ => h (x + t • EuclideanSpace.single a 1) i j) (dh a i j) 0)
    (hd : ∀ a b i j, HasDerivAt (fun t : ℝ => d (x + t • EuclideanSpace.single a 1) b i j) (dd a b i j) 0)
    (hInv : ∀ a : Idx, ∀ᶠ t : ℝ in 𝓝 0, ∀ i j : Idx,
      (∑ k : Idx, g (x + t • EuclideanSpace.single a 1) i k * h (x + t • EuclideanSpace.single a 1) k j) = if i = j then 1 else 0)
    (hLeft : ∀ i j : Idx, (∑ k : Idx, h x i k * g x k j) = if i = j then 1 else 0) :

    ∀ i j : Idx,
      (∑ k : Idx, (deriv (fun t : ℝ => christoffel (h (x + t • EuclideanSpace.single k 1)) (d (x + t • EuclideanSpace.single k 1)) k i j) 0 -
        deriv (fun t : ℝ => christoffel (h (x + t • EuclideanSpace.single j 1)) (d (x + t • EuclideanSpace.single j 1)) k i k) 0)) +
      (∑ k : Idx, ∑ l : Idx, (christoffel (h x) (d x) k k l * christoffel (h x) (d x) l i j -
        christoffel (h x) (d x) k j l * christoffel (h x) (d x) l i k)) = ricci (h x) (d x) dd i j :=
/- SWARM_PROOF_BEGIN -/
by
  have hGamma : ∀ a k i j : Idx,
      deriv (fun t : ℝ =>
        christoffel (h (x + t • EuclideanSpace.single a 1))
          (d (x + t • EuclideanSpace.single a 1)) k i j) 0 =
        gammaDerivative (h x) (d x) dd a k i j := by
    intro a k i j
    let p : ℝ → E3 := fun t => x + t • EuclideanSpace.single a 1
    have hg' : ∀ u v : Idx,
        HasDerivAt (fun t : ℝ => g (p t) u v) (d (p 0) a u v) 0 := by
      intro u v
      simpa [p] using hg a u v
    have hh' : ∀ u v : Idx,
        HasDerivAt (fun t : ℝ => h (p t) u v) (dh a u v) 0 := by
      intro u v
      simpa [p] using hh a u v
    have hd' : ∀ b u v : Idx,
        HasDerivAt (fun t : ℝ => d (p t) b u v) (dd a b u v) 0 := by
      intro b u v
      simpa [p] using hd a b u v
    have hInv' : ∀ᶠ t : ℝ in 𝓝 0, ∀ u v : Idx,
        (∑ m : Idx, g (p t) u m * h (p t) m v) = if u = v then 1 else 0 := by
      simpa [p] using hInv a
    have hLeft' : ∀ u v : Idx,
        (∑ m : Idx, h (p 0) u m * g (p 0) m v) = if u = v then 1 else 0 := by
      simpa [p] using hLeft
    have hActual :=
      CoordinateActualGammaDerivative.actual_gamma_derivative
        (fun t : ℝ => g (p t)) (fun t : ℝ => h (p t))
        (fun t : ℝ => d (p t)) (dh a) dd 0 a hg' hh' hd' hInv' hLeft'
    simpa [p] using (hActual k i j).deriv
  intro i j
  simp_rw [hGamma]
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateRicciDerivativeIdentification
