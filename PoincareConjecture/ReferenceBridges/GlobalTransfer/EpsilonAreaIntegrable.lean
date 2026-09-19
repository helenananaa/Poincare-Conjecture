import ReferenceBridges.GlobalTransfer.EpsilonSurfaceArea
import PoincareConjecture.ParallelMath.Transfer.IntegralDomination
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

/-- **Math.** Finite reference area and measurable new differential density imply finite new area under actual epsilon-closeness. -/
theorem epsilonClose_area_integrable {ε : ℝ} (g0 g : RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose ε g0 g)
    (F : EuclideanSpace ℝ (Fin 2) → M) (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (h0 : Integrable (paramAreaDensity g0 F) μ)
    (hm : AEStronglyMeasurable (paramAreaDensity g F) μ) :
    Integrable (paramAreaDensity g F) μ :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < ε := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have hC : 0 ≤ (1 : ℝ) + ε := add_nonneg (by norm_num) he0.le
  have hnn (g' : RiemannianMetric I M) (x : EuclideanSpace ℝ (Fin 2)) :
      0 ≤ paramAreaDensity g' F x := by
    unfold paramAreaDensity gramArea
    exact Real.sqrt_nonneg _
  have hpt := (epsilonClose_parametrized_area g0 g h F μ).1
  exact integrable_sqrt_gram_of_domination μ
    (paramAreaDensity g F) (paramAreaDensity g0 F) hm h0 (1 + ε) hC
    (Eventually.of_forall fun x => hnn g0 x)
    (Eventually.of_forall fun x => ⟨hnn g x, (hpt x).2⟩)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
