import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import ReferenceBridges.Quantitative.EpsilonMetricComparison
import MorganTianLib.Ch02.EpsilonClose
import ReferenceBridges.Transport.EpsilonIntegratedArea
import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport.Reference
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Actual metric closeness controls infima of parametrized areas, including singular tangent pairs and nonattained infima. -/
theorem epsilonClose_least_parametrized_area {epsilon : ℝ}
    (g0 g : Riemannian.RiemannianMetric I M) (h : MorganTianLib.EpsilonClose epsilon g0 g)
    {A Omega : Type*} [Nonempty A] [MeasurableSpace Omega] (mu : Measure Omega)
    (p : A → Omega → M) (v w : ∀ x z, TangentSpace I (p x z))
    (hf : ∀ x, Integrable (fun z => Real.sqrt (g0.metricInner (p x z) (v x z) (v x z)*g0.metricInner (p x z) (w x z) (w x z)-(g0.metricInner (p x z) (v x z) (w x z))^2)) mu)
    (hg : ∀ x, AEStronglyMeasurable (fun z => Real.sqrt (g.metricInner (p x z) (v x z) (v x z)*g.metricInner (p x z) (w x z) (w x z)-(g.metricInner (p x z) (v x z) (w x z))^2)) mu) :
    (∀ x, Integrable (fun z => Real.sqrt (g.metricInner (p x z) (v x z) (v x z)*g.metricInner (p x z) (w x z) (w x z)-(g.metricInner (p x z) (v x z) (w x z))^2)) mu) ∧
      (1-epsilon)*PoincareConjecture.ParallelMath.Variational.leastCost
        (fun x => ∫ z, Real.sqrt (g0.metricInner (p x z) (v x z) (v x z)*g0.metricInner (p x z) (w x z) (w x z)-(g0.metricInner (p x z) (v x z) (w x z))^2) ∂mu) ≤
      PoincareConjecture.ParallelMath.Variational.leastCost (fun x => ∫ z, Real.sqrt (g.metricInner (p x z) (v x z) (v x z)*g.metricInner (p x z) (w x z) (w x z)-(g.metricInner (p x z) (v x z) (w x z))^2) ∂mu) ∧
      PoincareConjecture.ParallelMath.Variational.leastCost (fun x => ∫ z, Real.sqrt (g.metricInner (p x z) (v x z) (v x z)*g.metricInner (p x z) (w x z) (w x z)-(g.metricInner (p x z) (v x z) (w x z))^2) ∂mu) ≤
      (1+epsilon)*PoincareConjecture.ParallelMath.Variational.leastCost
        (fun x => ∫ z, Real.sqrt (g0.metricInner (p x z) (v x z) (v x z)*g0.metricInner (p x z) (w x z) (w x z)-(g0.metricInner (p x z) (v x z) (w x z))^2) ∂mu) :=
/- SWARM_PROOF_BEGIN -/
by
  have hx := fun x =>
    epsilonClose_integrated_pair_area g0 g h mu (p x) (v x) (w x) (hf x) (hg x)
  have he0 : 0 < epsilon := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have hehalf : epsilon < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hl : 0 < 1 - epsilon :=
    sub_pos.mpr (hehalf.trans (by norm_num : (1 : ℝ) / 2 < 1))
  have hl0 : 0 ≤ 1 - epsilon := hl.le
  have hu0 : 0 ≤ 1 + epsilon := add_nonneg (by norm_num) he0.le
  have hf0 : ∀ x, 0 ≤ ∫ z, Real.sqrt (g0.metricInner (p x z) (v x z) (v x z) *
      g0.metricInner (p x z) (w x z) (w x z) - (g0.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu :=
    fun x => integral_nonneg fun _ => Real.sqrt_nonneg _
  have hg0 : ∀ x, 0 ≤ ∫ z, Real.sqrt (g.metricInner (p x z) (v x z) (v x z) *
      g.metricInner (p x z) (w x z) (w x z) - (g.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu :=
    fun x => integral_nonneg fun _ => Real.sqrt_nonneg _
  refine ⟨fun x => (hx x).1, ?_, ?_⟩
  · have hrev :
        PoincareConjecture.ParallelMath.Variational.leastCost
            (fun x => ∫ z, Real.sqrt (g0.metricInner (p x z) (v x z) (v x z) *
              g0.metricInner (p x z) (w x z) (w x z) -
                (g0.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu) ≤
          (1 - epsilon)⁻¹ *
            PoincareConjecture.ParallelMath.Variational.leastCost
              (fun x => ∫ z, Real.sqrt (g.metricInner (p x z) (v x z) (v x z) *
                g.metricInner (p x z) (w x z) (w x z) -
                  (g.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu) + 0 :=
      PoincareConjecture.ParallelMath.Variational.leastCost_transfer
        (fun x => ∫ z, Real.sqrt (g.metricInner (p x z) (v x z) (v x z) *
          g.metricInner (p x z) (w x z) (w x z) - (g.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu)
        (fun x => ∫ z, Real.sqrt (g0.metricInner (p x z) (v x z) (v x z) *
          g0.metricInner (p x z) (w x z) (w x z) - (g0.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu)
        hg0 hf0 id (1 - epsilon)⁻¹ 0 (inv_nonneg.mpr hl0) fun x => by
          simpa using (le_inv_mul_iff₀ hl).mpr (hx x).2.1
    exact (le_inv_mul_iff₀ hl).mp (by simpa using hrev)
  · simpa using
      PoincareConjecture.ParallelMath.Variational.leastCost_transfer
        (fun x => ∫ z, Real.sqrt (g0.metricInner (p x z) (v x z) (v x z) *
          g0.metricInner (p x z) (w x z) (w x z) - (g0.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu)
        (fun x => ∫ z, Real.sqrt (g.metricInner (p x z) (v x z) (v x z) *
          g.metricInner (p x z) (w x z) (w x z) - (g.metricInner (p x z) (v x z) (w x z)) ^ 2) ∂mu)
        hf0 hg0 id (1 + epsilon) 0 hu0 fun x => by
          simpa using (hx x).2.2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
