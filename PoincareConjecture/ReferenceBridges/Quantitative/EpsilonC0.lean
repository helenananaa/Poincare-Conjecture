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

/-- **Math.** The original C^[1/epsilon] closeness bounds its zeroth derivative term. -/
theorem epsilonClose_zero_norm_bound {epsilon : ℝ} (g0 g : Riemannian.RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose epsilon g0 g) :
    ∀ p : M, 0 ≤ MorganTianLib.metricCovariantDerivativeNormSq g0 g 0 p ∧
      MorganTianLib.metricCovariantDerivativeNormSq g0 g 0 p < epsilon^2 :=
/- SWARM_PROOF_BEGIN -/
by
  rw [MorganTianLib.EpsilonClose] at h
  obtain ⟨_, _, C, hC, hbound⟩ := h
  intro p
  have hsq : ∀ n : ℕ, 0 ≤ MorganTianLib.metricCovariantDerivativeNormSq g0 g n p := by
    intro n
    rw [MorganTianLib.metricCovariantDerivativeNormSq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨hsq 0, ?_⟩
  have hdens := hbound p
  rw [MorganTianLib.epsilonClosenessDensity] at hdens
  have hsum :
      0 ≤ ∑ l ∈ Finset.Icc 1 (MorganTianLib.epsilonDerivativeOrder epsilon),
        MorganTianLib.metricCovariantDerivativeNormSq g0 g l p :=
    Finset.sum_nonneg fun l _ => hsq l
  have hle : MorganTianLib.metricCovariantDerivativeNormSq g0 g 0 p ≤ C :=
    (le_add_of_nonneg_right hsum).trans hdens
  exact lt_of_le_of_lt hle hC
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
