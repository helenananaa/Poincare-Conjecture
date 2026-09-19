import ReferenceBridges.GlobalTransfer.EpsilonAreaIntegrable
import ReferenceBridges.GlobalTransfer.EpsilonSurfaceArea
import PoincareConjecture.ParallelMath.Variational.LeastAreaReduce
import ReferenceBridges.GlobalTransfer.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory Riemannian Manifold
open scoped Topology BigOperators Manifold ContDiff ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The actual derivative-area comparison passes to the least area of a fixed nonempty family of parametrized surfaces. -/
theorem epsilonClose_least_parametrized_area {ε : ℝ} (g0 g : RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose ε g0 g)
    {A : Type*} [Nonempty A] (F : A → EuclideanSpace ℝ (Fin 2) → M)
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (h0 : ∀ a, Integrable (paramAreaDensity g0 (F a)) μ)
    (hgm : ∀ a, AEStronglyMeasurable (paramAreaDensity g (F a)) μ) :
    (1-ε)*Variational.leastCost (fun a => ∫ x, paramAreaDensity g0 (F a) x ∂μ) ≤
      Variational.leastCost (fun a => ∫ x, paramAreaDensity g (F a) x ∂μ) ∧
    Variational.leastCost (fun a => ∫ x, paramAreaDensity g (F a) x ∂μ) ≤
      (1+ε)*Variational.leastCost (fun a => ∫ x, paramAreaDensity g0 (F a) x ∂μ) :=
/- SWARM_PROOF_BEGIN -/
by
  have h1 : ∀ a, Integrable (paramAreaDensity g (F a)) μ := fun a =>
    epsilonClose_area_integrable g0 g h (F a) μ (h0 a) (hgm a)
  have he0 : 0 < ε := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have hehalf : ε < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hl : 0 < 1 - ε :=
    sub_pos.mpr (hehalf.trans (by norm_num : (1 : ℝ) / 2 < 1))
  have hlu : 1 - ε ≤ 1 + ε := by linarith [he0.le]
  have hpos : ∀ a, ∀ᵐ x ∂μ, 0 ≤ paramAreaDensity g0 (F a) x :=
    fun a => Eventually.of_forall fun x => by
      unfold paramAreaDensity gramArea
      exact Real.sqrt_nonneg _
  have hdist : ∀ a, ∀ᵐ x ∂μ,
      (1 - ε) * paramAreaDensity g0 (F a) x ≤ paramAreaDensity g (F a) x ∧
        paramAreaDensity g (F a) x ≤ (1 + ε) * paramAreaDensity g0 (F a) x :=
    fun a => Eventually.of_forall fun x =>
      (epsilonClose_parametrized_area g0 g h (F a) μ).1 x
  exact Variational.least_integral_distortion μ
    (fun a => paramAreaDensity g0 (F a))
    (fun a => paramAreaDensity g (F a))
    h0 h1 hpos (1 - ε) (1 + ε) hl hlu hdist
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
