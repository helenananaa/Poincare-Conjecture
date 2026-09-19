import Mathlib
import PoincareConjecture.ParallelMath.Core
import ReferenceBridges.Quantitative.EpsilonC0
import ReferenceBridges.Quantitative.EpsilonMatrix
import ReferenceBridges.Quantitative.FrameParseval
import ReferenceBridges.Quantitative.FrameExpansion
import PoincareConjecture.ParallelMath.Tensor.MetricComparison
import MorganTianLib.Ch02.EpsilonClose
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter Riemannian
open scoped BigOperators Topology Manifold ContDiff
open MorganTianLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The original epsilon-closeness condition yields actual pointwise quadratic metric comparison. -/
theorem epsilonClose_metric_comparison {epsilon : ℝ} (g0 g : Riemannian.RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose epsilon g0 g) :
    ∀ p : M, ∀ v : TangentSpace I p,
      (1-epsilon)*g0.metricInner p v v ≤ g.metricInner p v v ∧
      g.metricInner p v v ≤ (1+epsilon)*g0.metricInner p v v :=
/- SWARM_PROOF_BEGIN -/
by
  intro p v
  have heps : 0 ≤ epsilon := by
    rw [MorganTianLib.EpsilonClose] at h
    obtain ⟨he0, _⟩ := h
    exact le_of_lt he0
  let A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => g.metricInner p (orthoFrameField g0 p i p) (orthoFrameField g0 p j p)
  let coeff : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => g0.metricInner p v (orthoFrameField g0 p i p)
  have herror :
      (∑ i, ∑ j, (A i j - if i = j then 1 else 0) ^ 2) ≤ epsilon ^ 2 := by
    have heq :
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (A i j - if i = j then 1 else 0) ^ 2) =
          MorganTianLib.metricCovariantDerivativeNormSq g0 g 0 p := by
      change
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              (g.metricInner p (orthoFrameField g0 p i p)
                  (orthoFrameField g0 p j p) -
                if i = j then 1 else 0) ^ 2) =
            MorganTianLib.metricCovariantDerivativeNormSq g0 g 0 p
      exact (zero_metric_norm_eq_matrix_error g0 g p).symm
    rw [heq]
    exact le_of_lt (epsilonClose_zero_norm_bound g0 g h p).2
  have hcmp := metric_comparison_of_frobenius_error A epsilon heps herror coeff
  have hparseval : (∑ i, (coeff i) ^ 2) = g0.metricInner p v v := by
    change
        (∑ i : Fin (Module.finrank ℝ E),
            (g0.metricInner p v (orthoFrameField g0 p i p)) ^ 2) =
          g0.metricInner p v v
    exact metric_frame_parseval g0 p v
  have hexp : quadraticForm A coeff = g.metricInner p v v := by
    unfold quadraticForm
    change
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            g.metricInner p (orthoFrameField g0 p i p)
                (orthoFrameField g0 p j p) *
              g0.metricInner p v (orthoFrameField g0 p i p) *
              g0.metricInner p v (orthoFrameField g0 p j p)) =
          g.metricInner p v v
    exact (metric_bilinear_frame_expansion g0 g p v v).symm
  rw [← hparseval, ← hexp]
  exact hcmp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
