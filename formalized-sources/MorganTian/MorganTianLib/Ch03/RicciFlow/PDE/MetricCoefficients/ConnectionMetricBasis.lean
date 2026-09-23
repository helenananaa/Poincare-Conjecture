import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionBasisExpansion
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Metric compatibility for three coordinate basis vectors. -/
theorem connection_metric_basis (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0 < c)
    (hA : ∀ v : E3, c * ‖v‖ ^ 2 ≤ inner ℝ (A v) v)
    (hsym : ∀ v w : E3, inner ℝ (A v) w = inner ℝ v (A w))
    (hP : ∀ r : Fin 3, ∀ v w : E3, inner ℝ (P r v) w = inner ℝ v (P r w))
    (r i j : Fin 3) :
    inner ℝ (P r (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) =
      inner ℝ (A (connectionVector A P (EuclideanSpace.single r 1)
        (EuclideanSpace.single i 1))) (EuclideanSpace.single j 1) +
      inner ℝ (A (EuclideanSpace.single i 1))
        (connectionVector A P (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hCompat :=
    (coordinate_metric_compatibility A c hc hA hsym P hP).2 r i j
  have hLeft :
      inner ℝ (P r (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) =
        (P r (EuclideanSpace.single j 1)) i := by
    simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      hP r (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hFirst :
      inner ℝ (A (∑ k : Fin 3,
        coordinateChristoffel A P k r i • EuclideanSpace.single k 1))
          (EuclideanSpace.single j 1) =
        ∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
          coordinateChristoffel A P k r i := by
    calc
      _ = (A (∑ k : Fin 3,
          coordinateChristoffel A P k r i • EuclideanSpace.single k 1)) j := by
        rw [EuclideanSpace.inner_single_right]
        simp
      _ = (∑ k : Fin 3, coordinateChristoffel A P k r i •
          A (EuclideanSpace.single k 1)) j := by
        simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
        simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hSecond :
      inner ℝ (A (EuclideanSpace.single i 1))
          (∑ k : Fin 3,
            coordinateChristoffel A P k r j • EuclideanSpace.single k 1) =
        ∑ k : Fin 3, A (EuclideanSpace.single k 1) i *
          coordinateChristoffel A P k r j := by
    calc
      _ = inner ℝ (EuclideanSpace.single i 1)
          (A (∑ k : Fin 3,
            coordinateChristoffel A P k r j • EuclideanSpace.single k 1)) := by
        exact hsym _ _
      _ = (A (∑ k : Fin 3,
          coordinateChristoffel A P k r j • EuclideanSpace.single k 1)) i := by
        rw [EuclideanSpace.inner_single_left]
        simp
      _ = (∑ k : Fin 3, coordinateChristoffel A P k r j •
          A (EuclideanSpace.single k 1)) i := by
        simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
        simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [connection_vector_basis_expansion A P r i,
    connection_vector_basis_expansion A P r j]
  rw [hLeft, hCompat, hFirst, hSecond]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
