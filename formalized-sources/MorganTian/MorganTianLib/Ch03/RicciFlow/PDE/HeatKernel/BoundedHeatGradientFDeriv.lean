import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ShiftedDerivativeDominator
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The first differentiated-kernel integral has the actual Hessian integral as its derivative. -/
theorem bounded_heat_gradient_fderiv (f : E3 →ᵇ ℝ) {t : ℝ} (ht : 0 < t)
    (x : E3) (i : Fin 3) :
    HasFDerivAt (fun z : E3 => ∫ y : E3, fderiv ℝ (euclideanHeatKernel 3 t)
      (z-y) (EuclideanSpace.single i 1)*f y)
      (∑ j : Fin 3, (∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*f y) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)) x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : E3 → ℝ := euclideanHeatKernel 3 t
  let G : E3 → ℝ := fun z => fderiv ℝ K z (EuclideanSpace.single i 1)
  let F : E3 → E3 → ℝ := fun z y => G (z - y) * f y
  let F' : E3 → E3 → E3 →L[ℝ] ℝ := fun z y =>
    (f y) • fderiv ℝ G (z - y)
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    euclideanHeatKernel_three_shifted_derivative_dominator t (‖x‖ + 1) ht (by positivity)
  have hK : ContDiff ℝ ∞ K := by
    simpa [K] using (euclideanHeatKernel_three_heat_equation ht).1
  have hG : ContDiff ℝ 1 G := by
    dsimp [G]
    exact (hK.fderiv_right (m := 1) (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ (∞ : ℕ∞ω)
      exact WithTop.coe_le_coe.2
        (OrderTop.le_top (α := ℕ∞) (2 : ℕ∞)))).clm_apply contDiff_const
  have hGcont : Continuous G := hG.continuous
  have hGdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hFcont (z : E3) : Continuous (F z) := by
    dsimp [F]
    exact (hGcont.comp (continuous_const.sub continuous_id)).mul f.continuous
  have hFmeas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) volume := by
    exact Eventually.of_forall (fun z => (hFcont z).aestronglyMeasurable)
  have hHcont (z : E3) : Continuous (F' z) := by
    dsimp [F']
    have hfd : Continuous (fun y : E3 => fderiv ℝ G (z - y)) := by
      exact (hG.continuous_fderiv (by norm_num)).comp (continuous_const.sub continuous_id)
    exact f.continuous.smul hfd
  have hF'meas : AEStronglyMeasurable (F' x) volume :=
    (hHcont x).aestronglyMeasurable
  have hR : 0 ≤ ‖x‖ + 1 := by positivity
  have hR_x : ‖x‖ ≤ ‖x‖ + 1 := by linarith
  have hFint : Integrable (F x) volume := by
    have hmajor : Integrable (fun y : E3 => ‖f‖ * g y) volume :=
      hg.const_mul ‖f‖
    apply hmajor.mono' (hFcont x).aestronglyMeasurable
    filter_upwards [] with y
    dsimp [F]
    change |G (x - y) * f y| ≤ ‖f‖ * g y
    rw [abs_mul]
    have hgrad : |G (x - y)| ≤ g y := by
      simpa [G, K] using (hdom x y hR_x).2.1 i
    calc
      |G (x - y)| * ‖f y‖ ≤
          g y * ‖f‖ := mul_le_mul hgrad (f.norm_coe_le_norm y)
            (abs_nonneg _) (hg_nonneg y)
      _ = ‖f‖ * g y := by ring
  have hLdecomp (L : E3 →L[ℝ] ℝ) :
      L = ∑ j : Fin 3, (L (EuclideanSpace.single j 1)) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) := by
    ext v
    have hv : v = ∑ j : Fin 3, v j • EuclideanSpace.single j 1 := by
      apply PiLp.ext
      intro k
      simp [Pi.single_apply]
    calc
      L v = L (∑ j : Fin 3, v j • EuclideanSpace.single j 1) := by rw [← hv]
      _ = ∑ j : Fin 3, v j • L (EuclideanSpace.single j 1) := by
        simp only [map_sum, map_smul]
      _ = ∑ j : Fin 3, (L (EuclideanSpace.single j 1)) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) v := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [PiLp.proj_apply]
        simp [smul_eq_mul, mul_comm]
  have hLnorm (z y : E3) (hz : z ∈ Metric.ball x 1) :
      ‖fderiv ℝ G (z - y)‖ ≤ 3 * g y := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by norm_num) (hg_nonneg y))
    intro v
    rw [hLdecomp (fderiv ℝ G (z - y))]
    calc
      ‖∑ j : Fin 3,
          (fderiv ℝ G (z - y) (EuclideanSpace.single j 1)) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) v‖ ≤
          ∑ j : Fin 3, ‖(fderiv ℝ G (z - y) (EuclideanSpace.single j 1)) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) v‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, g y * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, PiLp.proj_apply]
        have hzy := hdom z y (by
          rw [Metric.mem_ball, dist_eq_norm] at hz
          have hzx : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
            calc
              ‖z‖ = ‖(z - x) + x‖ := by congr 1 <;> abel
              _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
          exact hzx.trans (by linarith))
        have hj' : |fderiv ℝ G (z-y) (EuclideanSpace.single j 1)| ≤ g y := by
          simpa [G, K] using hzy.2.2 i j
        have hvj : |v j| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v j)
        exact mul_le_mul hj' hvj (abs_nonneg _) (hg_nonneg y)
      _ = 3 * g y * ‖v‖ := by
        simp
        ring
  have hF'bound : ∀ᵐ y : E3, ∀ z ∈ Metric.ball x 1, ‖F' z y‖ ≤
      (3 * ‖f‖) * g y := by
    filter_upwards [] with y z hz
    dsimp [F']
    rw [norm_smul]
    calc
      ‖f y‖ * ‖fderiv ℝ G (z - y)‖ ≤
          ‖f‖ * (3 * g y) := mul_le_mul (f.norm_coe_le_norm y)
            (hLnorm z y hz) (norm_nonneg _) (by positivity)
      _ = (3 * ‖f‖) * g y := by ring
  have hF'bound_int : Integrable (fun y : E3 => (3 * ‖f‖) * g y) volume :=
    hg.const_mul (3 * ‖f‖)
  have hdiff : ∀ᵐ y : E3, ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y z hz
    have hcomp := (hGdiff (z - y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const y)
    have hmul := hcomp.mul_const (f y)
    simpa [F, F'] using hmul
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := (volume : Measure E3)) (F := F) (F' := F') (x₀ := x) (s := Metric.ball x 1)
      (bound := fun y : E3 => (3 * ‖f‖) * g y)
      (Metric.ball_mem_nhds x one_pos) hFmeas hFint hF'meas hF'bound hF'bound_int hdiff
  have hcoeff_int (j : Fin 3) : Integrable
      (fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ K z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * f y) volume := by
    have hmajor : Integrable (fun y : E3 => ‖f‖ * g y) volume := hg.const_mul ‖f‖
    have hmeas : AEStronglyMeasurable
        (fun y : E3 => fderiv ℝ G (x-y) (EuclideanSpace.single j 1) * f y) volume := by
      have hfd : Continuous (fun y : E3 => fderiv ℝ G (x-y)) :=
        (hG.continuous_fderiv (by norm_num)).comp (continuous_const.sub continuous_id)
      exact (hfd.clm_apply continuous_const |>.mul f.continuous).aestronglyMeasurable
    apply hmajor.mono' (by simpa [G, K] using hmeas)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul]
    have hj : |fderiv ℝ (fun z : E3 => fderiv ℝ K z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)| ≤ g y := by
      simpa [K] using (hdom x y hR_x).2.2 i j
    calc
      |fderiv ℝ (fun z : E3 => fderiv ℝ K z (EuclideanSpace.single i 1)) (x-y)
          (EuclideanSpace.single j 1)| * ‖f y‖ ≤ g y * ‖f‖ :=
        mul_le_mul hj (f.norm_coe_le_norm y) (abs_nonneg _) (hg_nonneg y)
      _ = ‖f‖ * g y := by ring
  have hF'expand (z y : E3) : F' z y = ∑ j : Fin 3,
      (fderiv ℝ (fun q : E3 => fderiv ℝ K q (EuclideanSpace.single i 1)) (z-y)
        (EuclideanSpace.single j 1) * f y) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) := by
    dsimp [F']
    rw [hLdecomp (fderiv ℝ G (z-y))]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul]
    congr 1
    simp [G, K, mul_comm]
  have hIntegral_expand : (∫ y : E3, F' x y) =
      ∑ j : Fin 3, (∫ y : E3, fderiv ℝ
        (fun q : E3 => fderiv ℝ K q (EuclideanSpace.single i 1)) (x-y)
        (EuclideanSpace.single j 1) * f y) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) := by
    rw [show (fun y : E3 => F' x y) = (fun y : E3 => ∑ j : Fin 3,
        (fderiv ℝ (fun q : E3 => fderiv ℝ K q (EuclideanSpace.single i 1)) (x-y)
          (EuclideanSpace.single j 1) * f y) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)) by
      funext y
      exact hF'expand x y]
    rw [integral_finsetSum]
    · simp_rw [integral_smul_const]
    · intro j hj
      exact (hcoeff_int j).smul_const
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)
  rw [hIntegral_expand] at hmain
  simpa [F, G, K] using hmain
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
