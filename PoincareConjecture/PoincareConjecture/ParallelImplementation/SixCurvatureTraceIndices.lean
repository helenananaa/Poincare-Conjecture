import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixCurvatureTraceIndices
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem six_curvature_trace_indices
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (u : E3 → E6) (x : E3) :

    ∀ i j : Idx, (∑ k : Idx, (deriv (fun t : ℝ => (christoffelField E u) (x + t • EuclideanSpace.single k 1) k j i) 0 - deriv (fun t : ℝ => (christoffelField E u) (x + t • EuclideanSpace.single j 1) k k i) 0 + (∑ m : Idx, ((christoffelField E u) x m j i * (christoffelField E u) x k k m - (christoffelField E u) x m k i * (christoffelField E u) x k j m)))) = actualRicci E u x i j :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  have hFirstSymm : ∀ (y : E3) (a b c : Idx),
      firstCoefficients u y a b c = firstCoefficients u y a c b := by
    intro y a b c
    fin_cases b <;> fin_cases c <;>
      simp [firstCoefficients, symmetricSixMatrix]
  have hGamma : ∀ (y : E3) (k a b : Idx),
      christoffelField E u y k a b = christoffelField E u y k b a := by
    intro y k a b
    unfold christoffelField christoffel
    apply Finset.sum_congr rfl
    intro l hl
    unfold lowerChristoffel
    rw [hFirstSymm y l a b]
    ring
  have hDeriv₁ : ∀ k : Idx,
      deriv (fun t : ℝ => christoffelField E u
        (x + t • EuclideanSpace.single k 1) k j i) 0 =
      deriv (fun t : ℝ => christoffelField E u
        (x + t • EuclideanSpace.single k 1) k i j) 0 := by
    intro k
    congr 1
    funext t
    exact hGamma (x + t • EuclideanSpace.single k 1) k j i
  have hDeriv₂ : ∀ k : Idx,
      deriv (fun t : ℝ => christoffelField E u
        (x + t • EuclideanSpace.single j 1) k k i) 0 =
      deriv (fun t : ℝ => christoffelField E u
        (x + t • EuclideanSpace.single j 1) k i k) 0 := by
    intro k
    congr 1
    funext t
    exact hGamma (x + t • EuclideanSpace.single j 1) k k i
  unfold actualRicci
  rw [Finset.sum_add_distrib]
  have hderivs :
      (∑ k : Idx,
        (deriv (fun t : ℝ => christoffelField E u
          (x + t • EuclideanSpace.single k 1) k j i) 0 -
         deriv (fun t : ℝ => christoffelField E u
          (x + t • EuclideanSpace.single j 1) k k i) 0)) =
      ∑ k : Idx,
        (deriv (fun t : ℝ => christoffelField E u
          (x + t • EuclideanSpace.single k 1) k i j) 0 -
         deriv (fun t : ℝ => christoffelField E u
          (x + t • EuclideanSpace.single j 1) k i k) 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hDeriv₁ k, hDeriv₂ k]
  have hquadratic :
      (∑ k : Idx, ∑ m : Idx,
        (christoffelField E u x m j i * christoffelField E u x k k m -
         christoffelField E u x m k i * christoffelField E u x k j m)) =
      ∑ k : Idx, ∑ l : Idx,
        (christoffelField E u x k k l * christoffelField E u x l i j -
         christoffelField E u x k j l * christoffelField E u x l i k) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro m hm
    rw [hGamma x m j i, hGamma x m k i]
    ring
  rw [hderivs, hquadratic]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixCurvatureTraceIndices
