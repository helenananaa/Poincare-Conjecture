import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideTranslationL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A genuine small-time contraction estimate for nonlinear forcing differences. -/
theorem bounded_duhamel_nonlinear_difference (N : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|)
    (F G : (ℝ × E3) →ᵇ ℝ) (T : ℝ) (hT : 0 ≤ T) (x : E3) :
    IntervalIntegrable (fun s => ∫ y : E3, euclideanHeatKernel 3 (T-s) y *
      (N (F (s,x-y))-N (G (s,x-y)))) volume 0 T ∧
    |∫ s in (0:ℝ)..T, ∫ y : E3, euclideanHeatKernel 3 (T-s) y *
      (N (F (s,x-y))-N (G (s,x-y)))| ≤ T*L*‖F-G‖ :=
/- SWARM_PROOF_BEGIN -/
by
  have hNlip : LipschitzWith L.toNNReal N :=
    LipschitzWith.of_dist_le_mul (fun a b => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
      exact hN a b)
  have hNcont : Continuous N := hNlip.continuous
  have hHcont : Continuous (fun p : ℝ × E3 => N (F p) - N (G p)) :=
    (hNcont.comp F.continuous).sub (hNcont.comp G.continuous)
  have hpoint : ∀ p : ℝ × E3, |F p - G p| ≤ ‖F - G‖ := by
    intro p
    rw [← Real.norm_eq_abs]
    exact (F - G).norm_coe_le_norm p
  have hC : 0 ≤ L * ‖F - G‖ := mul_nonneg hL (norm_nonneg _)
  have hHbound : ∀ p : ℝ × E3,
      ‖N (F p) - N (G p)‖ ≤ L * ‖F - G‖ := by
    intro p
    rw [Real.norm_eq_abs]
    exact (hN (F p) (G p)).trans
      (mul_le_mul_of_nonneg_left (hpoint p) hL)
  let H : (ℝ × E3) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (F p) - N (G p)) hHcont (L * ‖F - G‖) hHbound
  have hHnorm : ‖H‖ ≤ L * ‖F - G‖ := by
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      hHcont hC hHbound
  have hduh := euclideanHeatKernel_three_bounded_duhamel H T hT x
  refine ⟨?_, ?_⟩
  · simpa [H] using hduh.1
  · calc
      |∫ s in (0 : ℝ)..T, ∫ y : E3,
          euclideanHeatKernel 3 (T-s) y * (N (F (s,x-y))-N (G (s,x-y)))|
          = |∫ s in (0 : ℝ)..T, ∫ y : E3,
          euclideanHeatKernel 3 (T-s) y * H (s, x-y)| := by
            simp [H]
      _ ≤ T * ‖H‖ := hduh.2
      _ ≤ T * (L * ‖F-G‖) := mul_le_mul_of_nonneg_left hHnorm hT
      _ = T * L * ‖F-G‖ := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
