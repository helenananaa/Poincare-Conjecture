import Mathlib
import PoincareConjecture.ParallelMath.Core
import ReferenceBridges.Quantitative.EpsilonC0
import ReferenceBridges.Quantitative.EpsilonMatrix
import ReferenceBridges.Quantitative.FrameParseval
import ReferenceBridges.Quantitative.FrameExpansion
import PoincareConjecture.ParallelMath.Quantitative.BilinearFrobenius
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

/-- **Math.** Original epsilon-closeness controls mixed metric errors on actual tangent vectors. -/
theorem epsilonClose_mixed_error_sq {epsilon : ℝ} (g0 g : Riemannian.RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose epsilon g0 g) :
    ∀ p : M, ∀ v w : TangentSpace I p,
      (g.metricInner p v w - g0.metricInner p v w)^2 ≤
        epsilon^2 * g0.metricInner p v v * g0.metricInner p w w :=
/- SWARM_PROOF_BEGIN -/
by
  intro p v w
  have hp : p ∈ orthoFrameSet (I := I) (M := M) p :=
    mem_orthoFrameSet_self (I := I) (M := M) p
  have hexp_g := metric_bilinear_frame_expansion g0 g p v w
  have hexp_g0 :
      g0.metricInner p v w =
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (if i = j then (1 : ℝ) else 0) *
            g0.metricInner p v (orthoFrameField g0 p i p) *
            g0.metricInner p w (orthoFrameField g0 p j p) := by
    rw [metric_bilinear_frame_expansion g0 g0 p v w]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [orthoFrameField_orthonormal g0 p hp i j]
  have hdiff :
      g.metricInner p v w - g0.metricInner p v w =
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (g.metricInner p (orthoFrameField g0 p i p) (orthoFrameField g0 p j p) -
            if i = j then 1 else 0) *
            g0.metricInner p v (orthoFrameField g0 p i p) *
            g0.metricInner p w (orthoFrameField g0 p j p) := by
    rw [hexp_g, hexp_g0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_mul, sub_mul]
  have hC0 := epsilonClose_zero_norm_bound (epsilon := epsilon) g0 g h p
  have hFrobenius := zero_metric_norm_eq_matrix_error g0 g p
  have hPv := metric_frame_parseval g0 p v
  have hPw := metric_frame_parseval g0 p w
  have hv_nonneg : 0 ≤ g0.metricInner p v v := by
    rw [← hPv]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw_nonneg : 0 ≤ g0.metricInner p w w := by
    rw [← hPw]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound :=
    bilinear_frobenius_sq_bound
      (fun i j =>
        g.metricInner p (orthoFrameField g0 p i p) (orthoFrameField g0 p j p) -
          if i = j then 1 else 0)
      (fun i => g0.metricInner p v (orthoFrameField g0 p i p))
      (fun j => g0.metricInner p w (orthoFrameField g0 p j p))
  calc
    (g.metricInner p v w - g0.metricInner p v w) ^ 2
        = (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (g.metricInner p (orthoFrameField g0 p i p) (orthoFrameField g0 p j p) -
              if i = j then 1 else 0) *
              g0.metricInner p v (orthoFrameField g0 p i p) *
              g0.metricInner p w (orthoFrameField g0 p j p)) ^ 2 := by
          rw [hdiff]
      _ ≤ (∑ i, ∑ j,
            (g.metricInner p (orthoFrameField g0 p i p) (orthoFrameField g0 p j p) -
              if i = j then 1 else 0) ^ 2) *
            (∑ i, (g0.metricInner p v (orthoFrameField g0 p i p)) ^ 2) *
            (∑ j, (g0.metricInner p w (orthoFrameField g0 p j p)) ^ 2) :=
          hbound
      _ = MorganTianLib.metricCovariantDerivativeNormSq g0 g 0 p *
            g0.metricInner p v v * g0.metricInner p w w := by
          rw [← hFrobenius, hPv, hPw]
      _ ≤ epsilon ^ 2 * g0.metricInner p v v * g0.metricInner p w w := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_of_lt hC0.2) hv_nonneg) hw_nonneg
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
