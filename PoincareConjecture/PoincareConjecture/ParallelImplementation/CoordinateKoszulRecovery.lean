import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateKoszulRecovery
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem recover_christoffel_from_lower
    (g h : Mat) (d : First) (w : Idx → ℝ) (i j : Idx)
    (hInv : ∀ a b : Idx, (∑ l : Idx, h a l*g l b) = if a=b then 1 else 0)
    (hw : ∀ l : Idx, (∑ k : Idx, g l k*w k) = lowerChristoffel d l i j) :

    ∀ a : Idx, w a = christoffel h d a i j :=
/- SWARM_PROOF_BEGIN -/
by
  intro a
  change w a = ∑ l : Idx, h a l * lowerChristoffel d l i j
  calc
    w a = ∑ k : Idx, (if a = k then (1 : ℝ) else 0) * w k := by
      simp
    _ = ∑ k : Idx, (∑ l : Idx, h a l * g l k) * w k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hInv a k]
    _ = ∑ l : Idx, h a l * (∑ k : Idx, g l k * w k) := by
      calc
        _ = ∑ k : Idx, ∑ l : Idx, (h a l * g l k) * w k := by
          simp only [Finset.sum_mul]
        _ = ∑ l : Idx, ∑ k : Idx, (h a l * g l k) * w k := by
          rw [Finset.sum_comm]
        _ = ∑ l : Idx, h a l * (∑ k : Idx, g l k * w k) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ l : Idx, h a l * lowerChristoffel d l i j := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hw l]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateKoszulRecovery
