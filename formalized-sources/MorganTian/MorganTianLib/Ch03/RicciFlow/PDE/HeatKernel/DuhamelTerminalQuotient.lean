import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FixedDomainDuhamel
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedDuhamelOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearLocalMildIVP
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The true short terminal Duhamel average recovers the continuous source at the endpoint. -/
theorem duhamel_terminal_quotient (F : (ℝ × E3) →ᵇ ℝ) (T : ℝ) (x : E3) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ s in T..(T+h), ∫ y : E3,
      euclideanHeatKernel 3 (T+h-s) y * F (s,x-y)) (𝓝[>] (0:ℝ)) (𝓝 (F (T,x))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let F₀ : (ℝ × E3) →ᵇ ℝ := F.compContinuous
    ⟨fun p : ℝ × E3 => (T + p.1, p.2), by fun_prop⟩
  let K : E3 → ℝ := euclideanHeatKernel 3 1
  let G : ℝ → (ℝ × E3) → ℝ := fun h p =>
    K p.2 * F (T + h * p.1,
      x - (Real.sqrt (h * (1 - p.1))) • p.2)
  let J : ℝ → ℝ := fun h =>
    ∫ r in (0 : ℝ)..1, ∫ z : E3, G h (r, z)
  have hKint : Integrable K (volume : Measure E3) := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 1 (by norm_num) |>.1
  have hKmass : (∫ z : E3, K z) = 1 := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 1 (by norm_num) |>.2
  have hKcont : Continuous K := by
    simpa [K] using
      (euclideanHeatKernel_three_heat_equation (t := (1 : ℝ)) (by norm_num)).1.continuous
  have hFshift (h : ℝ) (hh : 0 < h) :
      (∫ s in T..(T + h), ∫ y : E3,
          euclideanHeatKernel 3 (T + h - s) y * F (s, x - y)) =
        h * J h := by
    have hshift :
        (∫ s in T..(T + h), ∫ y : E3,
            euclideanHeatKernel 3 (T + h - s) y * F (s, x - y)) =
          ∫ u in (0 : ℝ)..h, ∫ y : E3,
            euclideanHeatKernel 3 (h - u) y * F₀ (u, x - y) := by
      have hc := intervalIntegral.integral_comp_sub_right
        (f := fun u : ℝ => ∫ y : E3,
          euclideanHeatKernel 3 (h - u) y * F₀ (u, x - y))
        (a := T) (b := T + h) T
      calc
        (∫ s in T..(T + h), ∫ y : E3,
            euclideanHeatKernel 3 (T + h - s) y * F (s, x - y)) =
            ∫ s in T..(T + h), ∫ y : E3,
              euclideanHeatKernel 3 (h - (s - T)) y * F₀ (s - T, x - y) := by
          apply intervalIntegral.integral_congr
          intro s hs
          apply integral_congr_ae
          filter_upwards [] with y
          change euclideanHeatKernel 3 (T + h - s) y * F (s, x - y) =
            euclideanHeatKernel 3 (h - (s - T)) y *
              F (T + (s - T), x - y)
          rw [show T + h - s = h - (s - T) by ring,
            show T + (s - T) = s by ring]
        _ = ∫ u in (0 : ℝ)..h, ∫ y : E3,
              euclideanHeatKernel 3 (h - u) y * F₀ (u, x - y) := by
          simpa using hc
    rw [hshift, duhamel_fixed_domain_formula F₀ h hh.le x]
    rfl
  let μ : Measure (ℝ × E3) :=
    (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure E3)
  let B : (ℝ × E3) → ℝ := fun p => ‖F‖ * K p.2
  have hconst : Integrable (fun _ : ℝ => ‖F‖)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    exact (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1)
      (C := ‖F‖) (by simp)).integrable
  have hBint : Integrable B μ := by
    simpa [B, μ] using hconst.mul_prod hKint
  have hGcont (p : ℝ × E3) :
      ContinuousAt (fun h : ℝ => G h p) (0 : ℝ) := by
    dsimp [G]
    fun_prop
  have hGcont' (h : ℝ) : Continuous (G h) := by
    dsimp [G]
    fun_prop (disch := aesop)
  have hGmeas : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (G h) μ := by
    filter_upwards [] with h
    exact (hGcont' h).aestronglyMeasurable
  have hGbound : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ),
      ∀ᵐ p ∂μ, ‖G h p‖ ≤ B p := by
    filter_upwards [] with h
    filter_upwards [] with p
    rcases p with ⟨r, z⟩
    dsimp [G, B, K]
    rw [abs_mul, abs_of_nonneg (euclideanHeatKernel_pos 3 (by norm_num) z).le]
    calc
      euclideanHeatKernel 3 1 z *
          |F (T + h * r, x - (Real.sqrt (h * (1 - r))) • z)| ≤
          euclideanHeatKernel 3 1 z * ‖F‖ :=
        mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using
            F.norm_coe_le_norm (T + h * r,
              x - (Real.sqrt (h * (1 - r))) • z))
          (euclideanHeatKernel_pos 3 (by norm_num) z).le
      _ = ‖F‖ * euclideanHeatKernel 3 1 z := by ring
  have hGint (h : ℝ) : Integrable (G h) μ := by
    apply hBint.mono
    · exact (hGcont' h).aestronglyMeasurable
    · filter_upwards [] with p
      rcases p with ⟨r, z⟩
      dsimp [G, B, K]
      rw [abs_mul, abs_of_nonneg (euclideanHeatKernel_pos 3 (by norm_num) z).le,
        abs_mul, abs_of_nonneg (norm_nonneg F),
        abs_of_nonneg (euclideanHeatKernel_pos 3 (by norm_num) z).le]
      calc
        euclideanHeatKernel 3 1 z *
            |F (T + h * r, x - (Real.sqrt (h * (1 - r))) • z)| ≤
            euclideanHeatKernel 3 1 z * ‖F‖ :=
          mul_le_mul_of_nonneg_left
            (by simpa [Real.norm_eq_abs] using
              F.norm_coe_le_norm (T + h * r,
                x - (Real.sqrt (h * (1 - r))) • z))
            (euclideanHeatKernel_pos 3 (by norm_num) z).le
        _ = ‖F‖ * euclideanHeatKernel 3 1 z := by ring
  have hprod_cont :
      ContinuousAt (fun h => ∫ p, G h p ∂μ) (0 : ℝ) := by
    exact MeasureTheory.continuousAt_of_dominated
      hGmeas hGbound hBint (Eventually.of_forall hGcont)
  have hJprod (h : ℝ) : J h = ∫ p, G h p ∂μ := by
    change (∫ r in (0 : ℝ)..1, ∫ z : E3, G h (r, z)) = _
    rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa [μ] using (integral_prod (G h) (hGint h)).symm
  have hJzero : J 0 = F (T, x) := by
    dsimp [J, G]
    simp only [zero_mul, zero_add, zero_sub, mul_zero, Real.sqrt_zero, zero_smul,
      sub_zero]
    rw [integral_mul_const, hKmass]
    simp
  have hprod_zero : (∫ p, G 0 p ∂μ) = F (T, x) := by
    rw [← hJprod 0, hJzero]
  have hJlim : Tendsto J (𝓝[>] (0 : ℝ)) (𝓝 (F (T, x))) := by
    have hp : Tendsto (fun h => ∫ p, G h p ∂μ)
        (𝓝[>] (0 : ℝ)) (𝓝 (F (T, x))) := by
      simpa [hprod_zero] using
        (hprod_cont.tendsto.mono_left nhdsWithin_le_nhds)
    apply hp.congr'
    filter_upwards [] with h
    exact (hJprod h).symm
  apply hJlim.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  change 0 < h at hh
  rw [hFshift h hh]
  simp [ne_of_gt hh]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
