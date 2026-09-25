import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothOperatorInverse
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem smooth_operator_inverse
    (A : E3 → (E3 →L[ℝ] E3)) (hA : ContDiff ℝ ∞ A)
    (hunit : ∀ x : E3, IsUnit (A x)) :

    ContDiff ℝ ∞ (fun x => Ring.inverse (A x)) :=
/- SWARM_PROOF_BEGIN -/
by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨u, hu⟩ := hunit x
  have hInv := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
  rw [hu] at hInv
  exact hInv.comp x hA.contDiffAt
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothOperatorInverse
