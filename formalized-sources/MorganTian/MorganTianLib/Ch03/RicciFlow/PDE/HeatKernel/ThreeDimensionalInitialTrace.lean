import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Gaussian convolution recovers any bounded uniformly continuous initial datum uniformly in space. -/
theorem euclideanHeatKernel_three_uniform_initial_trace (f : E3 →ᵇ ℝ)
    (hf : UniformContinuous f) :
    TendstoUniformly (fun t : ℝ => fun x : E3 =>
      ∫ y : E3, euclideanHeatKernel 3 t y * f (x - y)) f (𝓝[>] (0 : ℝ)) := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨C, hC, hmoment⟩ :=
    euclideanHeatKernel_three_fractional_moment (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hpow : Tendsto (fun t : ℝ => t ^ (1 / 4 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).tendsto
      (0 : ℝ)
    simpa only [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using
      h.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ :=
    (Metric.uniformContinuous_iff.mp hf) (ε / 2) (by linarith)
  let B : Set E3 := Metric.ball (0 : E3) δ
  have hB : MeasurableSet B := measurableSet_ball
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧
      2 * ‖f‖ * δ ^ (-(1 / 2 : ℝ)) * C * t ^ (1 / 4 : ℝ) < ε / 2 := by
    have hlim : Tendsto
        (fun t : ℝ => 2 * ‖f‖ * δ ^ (-(1 / 2 : ℝ)) * C * t ^ (1 / 4 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds.mul hpow) :
          Tendsto (fun t : ℝ =>
            (2 * ‖f‖ * δ ^ (-(1 / 2 : ℝ)) * C) * t ^ (1 / 4 : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 ((2 * ‖f‖ * δ ^ (-(1 / 2 : ℝ)) * C) * 0)))
    have htail_event : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        2 * ‖f‖ * δ ^ (-(1 / 2 : ℝ)) * C * t ^ (1 / 4 : ℝ) < ε / 2 :=
      hlim.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 2))
    filter_upwards [self_mem_nhdsWithin, htail_event] with t (ht : 0 < t) htail
    exact ⟨ht, htail⟩
  filter_upwards [hevent] with t ht
  let K : E3 → ℝ := fun y => euclideanHeatKernel 3 t y
  obtain ⟨hkernel, hmass⟩ := (euclideanHeatKernel_mass_semigroup 3).1 t ht.1
  obtain ⟨hmoment_int, hmoment_bound⟩ := hmoment t ht.1
  have hkernel_cont : Continuous K := by
    dsimp [K]
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun i _ =>
      (gaussianHeatKernel_derivatives ht.1).1.comp (by fun_prop))).continuous
  have hbase_dom (x : E3) : Integrable
      (fun y : E3 => K y * ‖f‖) volume := by
    dsimp [K]
    exact hkernel.mul_const _
  have hbase_bound (x y : E3) :
      ‖K y * f (x - y)‖ ≤ K y * ‖f‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (euclideanHeatKernel_pos 3 ht.1 y)]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x - y))
      (euclideanHeatKernel_pos 3 ht.1 y).le
  have hbase_int (x : E3) : Integrable
      (fun y : E3 => K y * f (x - y)) volume := by
    have hc : Continuous (fun y : E3 => K y * f (x - y)) := by fun_prop
    apply (hbase_dom x).mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    exact hbase_bound x y
  let tailKernel : E3 → ℝ := Bᶜ.indicator K
  have htailKernel_int : Integrable tailKernel volume := by
    dsimp [tailKernel]
    exact (hkernel.integrableOn.mono_set (subset_univ Bᶜ)).integrable_indicator
      hB.compl
  have htail_mass :
      (∫ y : E3, tailKernel y) ≤ δ ^ (-(1 / 2 : ℝ)) *
        (∫ y : E3, K y * ‖y‖ ^ (1 / 2 : ℝ)) := by
    have htail_on : IntegrableOn K Bᶜ volume :=
      hkernel.integrableOn.mono_set (subset_univ Bᶜ)
    have htail_moment_on : IntegrableOn
        (fun y : E3 => K y * ‖y‖ ^ (1 / 2 : ℝ)) Bᶜ volume :=
      hmoment_int.integrableOn.mono_set (subset_univ Bᶜ)
    have hpoint : ∀ y ∈ Bᶜ, K y ≤ δ ^ (-(1 / 2 : ℝ)) *
        (K y * ‖y‖ ^ (1 / 2 : ℝ)) := by
      intro y hy
      have hyδ : δ ≤ ‖y‖ := by
        have hnot : ¬ dist y 0 < δ := by
          intro h
          exact hy (by simpa [B] using h)
        simpa [dist_eq_norm] using le_of_not_gt hnot
      have hδpow : δ ^ (1 / 2 : ℝ) ≤ ‖y‖ ^ (1 / 2 : ℝ) := by
        exact Real.rpow_le_rpow (le_of_lt hδ) hyδ (by norm_num)
      have hδpowpos : 0 < δ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
      have hscale : 1 ≤ δ ^ (-(1 / 2 : ℝ)) * ‖y‖ ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hδ)]
        calc
          1 ≤ ‖y‖ ^ (1 / 2 : ℝ) / δ ^ (1 / 2 : ℝ) :=
            (le_div_iff₀ hδpowpos).2 (by simpa using hδpow)
          _ = (δ ^ (1 / 2 : ℝ))⁻¹ * ‖y‖ ^ (1 / 2 : ℝ) := by
            rw [div_eq_mul_inv]
            ring
      calc
        K y = 1 * K y := by ring
        _ ≤ (δ ^ (-(1 / 2 : ℝ)) * ‖y‖ ^ (1 / 2 : ℝ)) * K y :=
          mul_le_mul_of_nonneg_right hscale (euclideanHeatKernel_pos 3 ht.1 y).le
        _ = δ ^ (-(1 / 2 : ℝ)) * (K y * ‖y‖ ^ (1 / 2 : ℝ)) := by ring
    let tailMoment : E3 → ℝ :=
      Bᶜ.indicator (fun y : E3 => K y * ‖y‖ ^ (1 / 2 : ℝ))
    have htailMoment_int : Integrable tailMoment volume := by
      dsimp [tailMoment]
      exact htail_moment_on.integrable_indicator hB.compl
    have hset : (∫ y : E3, tailKernel y) ≤
        ∫ y : E3, δ ^ (-(1 / 2 : ℝ)) * tailMoment y := by
      exact integral_mono htailKernel_int
        (htailMoment_int.const_mul (δ ^ (-(1 / 2 : ℝ)))) (by
          intro y
          by_cases hy : y ∈ Bᶜ
          · simpa [tailKernel, tailMoment, hy] using hpoint y hy
          · simp [tailKernel, tailMoment, hy])
    have hfull :
        (∫ y : E3 in Bᶜ, K y * ‖y‖ ^ (1 / 2 : ℝ)) ≤
          ∫ y : E3, K y * ‖y‖ ^ (1 / 2 : ℝ) := by
      dsimp [K]
      have hfull0 := setIntegral_mono_set (s := Bᶜ) (t := (Set.univ : Set E3))
        hmoment_int.integrableOn
        (by
          filter_upwards [] with y
          exact mul_nonneg (euclideanHeatKernel_pos 3 ht.1 y).le
            (Real.rpow_nonneg (norm_nonneg y) _))
        (ae_of_all _ (fun y hy => trivial))
      simpa only [setIntegral_univ] using hfull0
    calc
      (∫ y : E3, tailKernel y) ≤
          ∫ y : E3, δ ^ (-(1 / 2 : ℝ)) * tailMoment y := hset
      _ = δ ^ (-(1 / 2 : ℝ)) *
          (∫ y : E3 in Bᶜ, K y * ‖y‖ ^ (1 / 2 : ℝ)) := by
        rw [integral_const_mul]
        congr 1
        simpa [tailMoment] using
          (integral_indicator (f := fun y : E3 => K y * ‖y‖ ^ (1 / 2 : ℝ)) hB.compl)
      _ ≤ δ ^ (-(1 / 2 : ℝ)) *
          (∫ y : E3, K y * ‖y‖ ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfull (Real.rpow_nonneg (le_of_lt hδ) _)
  have htail_mass' :
      (∫ y : E3, tailKernel y) ≤ δ ^ (-(1 / 2 : ℝ)) * C * t ^ (1 / 4 : ℝ) := by
    norm_num at hmoment_bound
    calc
      (∫ y : E3, tailKernel y) ≤ δ ^ (-(1 / 2 : ℝ)) *
          (∫ y : E3, K y * ‖y‖ ^ (1 / 2 : ℝ)) := htail_mass
      _ ≤ δ ^ (-(1 / 2 : ℝ)) * (C * t ^ (1 / 4 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hmoment_bound
          (Real.rpow_nonneg (le_of_lt hδ) _)
      _ = δ ^ (-(1 / 2 : ℝ)) * C * t ^ (1 / 4 : ℝ) := by ring
  intro x
  have hvalue : (∫ y : E3, K y * f x) = f x := by
    rw [integral_mul_const, hmass]
    ring
  let d : E3 → ℝ := fun y => K y * (f (x - y) - f x)
  let D : E3 → ℝ := fun y => (ε / 2) * K y + (2 * ‖f‖) * tailKernel y
  have hd_cont : Continuous d := by
    dsimp [d]
    fun_prop
  have hD_int : Integrable D volume := by
    dsimp [D]
    exact (hkernel.const_mul (ε / 2)).add (htailKernel_int.const_mul (2 * ‖f‖))
  have hd_bound : ∀ y : E3, ‖d y‖ ≤ D y := by
    intro y
    by_cases hy : y ∈ B
    · have hosc : ‖f (x - y) - f x‖ < ε / 2 := by
        apply hδf
        have hy' : ‖y‖ < δ := by simpa [B] using hy
        simpa [dist_eq_norm] using hy'
      have htailzero : tailKernel y = 0 := by simp [tailKernel, hy]
      have hk : 0 ≤ K y := (euclideanHeatKernel_pos 3 ht.1 y).le
      have hmul := mul_le_mul_of_nonneg_right (le_of_lt hosc) hk
      have hmul' : K y * ‖f (x - y) - f x‖ ≤ (ε / 2) * K y := by
        simpa [mul_comm] using hmul
      change ‖K y * (f (x - y) - f x)‖ ≤
        (ε / 2) * K y + (2 * ‖f‖) * tailKernel y
      calc
        ‖K y * (f (x - y) - f x)‖ = K y * ‖f (x - y) - f x‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (euclideanHeatKernel_pos 3 ht.1 y)]
        _ ≤ (ε / 2) * K y := hmul'
        _ ≤ (ε / 2) * K y + (2 * ‖f‖) * tailKernel y := by
          rw [htailzero]
          simp [htailzero]
    · have htail_eq : tailKernel y = K y := by simp [tailKernel, hy]
      have hk : 0 ≤ K y := (euclideanHeatKernel_pos 3 ht.1 y).le
      have hfd : ‖f (x - y) - f x‖ ≤ 2 * ‖f‖ := by
        calc
          ‖f (x - y) - f x‖ ≤ ‖f (x - y)‖ + ‖f x‖ := norm_sub_le _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add
            (f.norm_coe_le_norm (x - y)) (f.norm_coe_le_norm x)
          _ = 2 * ‖f‖ := by ring
      dsimp [K]
      have hmul := mul_le_mul_of_nonneg_right hfd hk
      have hmul' : K y * ‖f (x - y) - f x‖ ≤ (2 * ‖f‖) * K y := by
        simpa [mul_comm] using hmul
      change ‖K y * (f (x - y) - f x)‖ ≤
        (ε / 2) * K y + (2 * ‖f‖) * tailKernel y
      calc
        ‖K y * (f (x - y) - f x)‖ = K y * ‖f (x - y) - f x‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (euclideanHeatKernel_pos 3 ht.1 y)]
        _ ≤ (2 * ‖f‖) * K y := hmul'
        _ ≤ (ε / 2) * K y + (2 * ‖f‖) * tailKernel y := by
          rw [htail_eq]
          have he : 0 ≤ ε / 2 := by linarith
          nlinarith [mul_nonneg he hk]
  have hd_int : Integrable d volume := by
    apply hD_int.mono' hd_cont.aestronglyMeasurable
    filter_upwards [] with y
    exact hd_bound y
  have hrewrite :
      (∫ y : E3, K y * f (x - y)) - f x = ∫ y : E3, d y := by
    calc
      (∫ y : E3, K y * f (x - y)) - f x =
          (∫ y : E3, K y * f (x - y)) - (∫ y : E3, K y * f x) := by rw [hvalue]
      _ = ∫ y : E3, (K y * f (x - y) - K y * f x) :=
        (integral_sub (hbase_int x) (hkernel.mul_const _)).symm
      _ = ∫ y : E3, d y := by
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [d]
        ring
  rw [show dist (f x) (∫ y : E3, K y * f (x - y)) =
      ‖(∫ y : E3, K y * f (x - y)) - f x‖ by
        simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using
          (show |f x - (∫ y : E3, K y * f (x - y))| =
            |(∫ y : E3, K y * f (x - y)) - f x| by rw [abs_sub_comm]), hrewrite]
  have hcalc :
      (∫ y : E3, D y) = ε / 2 + 2 * ‖f‖ * (∫ y : E3, tailKernel y) := by
    dsimp [D]
    rw [integral_add (hkernel.const_mul (ε / 2))
      (htailKernel_int.const_mul (2 * ‖f‖)), integral_const_mul, hmass,
      integral_const_mul]
    ring
  calc
    ‖∫ y : E3, d y‖ ≤ ∫ y : E3, D y :=
      norm_integral_le_of_norm_le hD_int (Eventually.of_forall (fun y => hd_bound y))
    _ = ε / 2 + 2 * ‖f‖ * (∫ y : E3, tailKernel y) := hcalc
    _ ≤ ε / 2 + 2 * ‖f‖ *
        (δ ^ (-(1 / 2 : ℝ)) * C * t ^ (1 / 4 : ℝ)) := by
      gcongr
    _ < ε := by nlinarith [ht.2]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
