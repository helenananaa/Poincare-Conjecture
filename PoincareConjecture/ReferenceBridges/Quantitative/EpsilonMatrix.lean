import Mathlib
import PoincareConjecture.ParallelMath.Core
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

/-- **Math.** The actual zeroth tensor norm is exactly the frame-matrix Frobenius error. -/
theorem zero_metric_norm_eq_matrix_error (g0 g : Riemannian.RiemannianMetric I M) (p : M) :
    MorganTianLib.metricCovariantDerivativeNormSq g0 g 0 p =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (g.metricInner p (orthoFrameField g0 p i p) (orthoFrameField g0 p j p) - if i=j then 1 else 0)^2 :=
/- SWARM_PROOF_BEGIN -/
by
  unfold metricCovariantDerivativeNormSq
  have hzero :
      ∀ X : Fin (0 + 2) → SmoothVectorField I M,
        iteratedCovariantMetricDifference g0 g 0 X p =
          g.metricInner p (X 0 p) (X 1 p) - g0.metricInner p (X 0 p) (X 1 p) :=
    fun X => rfl
  simp_rw [hzero]
  refine
    (Fintype.sum_equiv (finTwoArrowEquiv (Fin (Module.finrank ℝ E)))
        (fun idx =>
          (g.metricInner p (orthoFrameField g0 p (idx 0) p)
              (orthoFrameField g0 p (idx 1) p) -
            g0.metricInner p (orthoFrameField g0 p (idx 0) p)
              (orthoFrameField g0 p (idx 1) p)) ^ 2)
        (fun q =>
          (g.metricInner p (orthoFrameField g0 p q.1 p) (orthoFrameField g0 p q.2 p) -
            g0.metricInner p (orthoFrameField g0 p q.1 p) (orthoFrameField g0 p q.2 p)) ^
              2)
        (fun _ => rfl)).trans
      ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hp : p ∈ orthoFrameSet (I := I) (M := M) p :=
    mem_orthoFrameSet_self (I := I) (M := M) p
  rw [orthoFrameField_orthonormal g0 p hp i j]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
