import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.CompactSpatialDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatFirstFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction RealInnerProductSpace
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Differentiate the time-truncated heat integral once, with its exact linear derivative. -/
theorem truncated_duhamel_first_derivative (F : (ℝ × E3) →ᵇ ℝ) (T eps : ℝ)
    (heps : 0<eps) (hT : eps≤T) (x : E3) :
    HasFDerivAt (fun z : E3 => ∫ s in (0:ℝ)..(T-eps),
      ∫ y : E3, euclideanHeatKernel 3 (T-s) (z-y)*F (s,y))
      (∑ i : Fin 3, (∫ s in (0:ℝ)..(T-eps), ∫ y : E3,
        fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y) (EuclideanSpace.single i 1)*F (s,y)) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)) x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let b : ℝ := T - eps
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith
  have hTpos : 0 < T := lt_of_lt_of_le heps hT
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    compact_time_spatial_derivative_dominator eps T (‖x‖ + 1) heps hT
      (by positivity)
  have hball_norm (z : E3) (hz : z ∈ Metric.ball x 1) :
      ‖z‖ ≤ ‖x‖ + 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc
      ‖z‖ = ‖(z - x) + x‖ := by congr 1 <;> abel
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ 1 + ‖x‖ := by linarith
      _ = ‖x‖ + 1 := by ring
  let fs : ℝ → E3 →ᵇ ℝ := fun s =>
    ⟨⟨fun y : E3 => F (s, y),
      F.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      ⟨2 * ‖F‖, by
        intro u v
        exact F.dist_le_two_norm (s, u) (s, v)⟩⟩
  have hfs_norm (s : ℝ) : ‖fs s‖ ≤ ‖F‖ := by
    apply (BoundedContinuousFunction.norm_le (f := fs s) (norm_nonneg _)).2
    intro y
    change |F (s, y)| ≤ ‖F‖
    simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, y)
  let H : ℝ → E3 → Fin 3 → ℝ := fun t v i =>
    -(v i / (2 * t)) * euclideanHeatKernel 3 t v
  have hH_eq (t : ℝ) (ht : 0 < t) (v : E3) (i : Fin 3) :
      H t v i = fderiv ℝ (euclideanHeatKernel 3 t) v
        (EuclideanSpace.single i 1) := by
    dsimp [H]
    exact (euclideanHeatKernel_three_gradient_formula ht v i).symm
  have hH_cont (t : ℝ) (ht : 0 < t) (z : E3) (s : ℝ) (i : Fin 3) :
      Continuous (fun y : E3 => H t (z - y) i * F (s, y)) := by
    have hk : Continuous (fun v : E3 => euclideanHeatKernel 3 t v) :=
      (euclideanHeatKernel_three_heat_equation ht).1.continuous
    have hc : Continuous (fun y : E3 => -((z - y) i / (2 * t))) := by
      fun_prop
    have hk' : Continuous (fun y : E3 => euclideanHeatKernel 3 t (z - y)) :=
      hk.comp (continuous_const.sub continuous_id)
    have hF : Continuous (fun y : E3 => F (s, y)) :=
      F.continuous.comp (continuous_const.prodMk continuous_id)
    convert (hc.mul hk').mul hF using 1 <;> ext y <;> dsimp [H] <;> ring
  let c : Fin 3 → E3 → ℝ → ℝ := fun i z s =>
    ∫ y : E3, H (T - s) (z - y) i * F (s, y)
  have htime (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) :
      T - s ∈ Icc eps T := by
    rcases hs with ⟨hs0, hsb⟩
    dsimp [b] at hsb
    constructor <;> linarith
  have hc_sm (i : Fin 3) (z : E3) : StronglyMeasurable (c i z) := by
    have hm : Measurable (fun p : ℝ × E3 =>
        H (T - p.1) (z - p.2) i * F (p.1, p.2)) := by
      dsimp [H]
      unfold euclideanHeatKernel gaussianHeatKernel
      measurability
    simpa [c] using hm.stronglyMeasurable.integral_prod_right'
  let G : E3 → ℝ → ℝ := fun z s =>
    ∫ y : E3, euclideanHeatKernel 3 (T - s) (z - y) * F (s, y)
  let G' : E3 → ℝ → E3 →L[ℝ] ℝ := fun z s =>
    ∑ i : Fin 3, (c i z s) •
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)
  have hG_sm (z : E3) : StronglyMeasurable (G z) := by
    have hm : Measurable (fun p : ℝ × E3 =>
        euclideanHeatKernel 3 (T - p.1) (z - p.2) * F (p.1, p.2)) := by
      unfold euclideanHeatKernel gaussianHeatKernel
      measurability
    simpa [G] using hm.stronglyMeasurable.integral_prod_right'
  have hG'_sm : StronglyMeasurable (G' x) := by
    dsimp [G']
    exact Finset.univ.stronglyMeasurable_sum (fun i _ =>
      (hc_sm i x).smul_const _)
  have hG_meas : ∀ᶠ z : E3 in 𝓝 x,
      AEStronglyMeasurable (G z) (volume.restrict (uIoc (0 : ℝ) b)) := by
    exact Eventually.of_forall (fun z => (hG_sm z).aestronglyMeasurable.restrict)
  have hG'_meas : AEStronglyMeasurable (G' x)
      (volume.restrict (uIoc (0 : ℝ) b)) :=
    hG'_sm.aestronglyMeasurable.restrict
  have hG_bound (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) :
      ‖G x s‖ ≤ ‖F‖ := by
    have hts : 0 < T - s := lt_of_lt_of_le heps (htime s hs).1
    have hmass := (euclideanHeatKernel_mass_semigroup 3).1 (T - s) hts
    have hKshift : Integrable
        (fun y : E3 => euclideanHeatKernel 3 (T - s) (x-y)) volume := by
      have hshift :=
        (Measure.measurePreserving_sub_left (volume : Measure E3) x).integrable_comp_of_integrable
          hmass.1
      simpa [Function.comp_def] using hshift
    have hmeas : AEStronglyMeasurable (fun y : E3 => F (s, y)) volume := by
      exact (F.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hint : Integrable
        (fun y : E3 => euclideanHeatKernel 3 (T - s) (x-y) * F (s, y)) volume := by
      apply hKshift.mul_bdd hmeas
      exact Eventually.of_forall (fun y => F.norm_coe_le_norm (s, y))
    have hnorm := norm_integral_le_of_norm_le
      (f := fun y : E3 => euclideanHeatKernel 3 (T - s) (x-y) * F (s, y))
      (hKshift.mul_const ‖F‖) (by
        filter_upwards [] with y
        rw [norm_mul, Real.norm_eq_abs]
        have hky : 0 ≤ euclideanHeatKernel 3 (T - s) (x-y) :=
          (euclideanHeatKernel_pos 3 hts (x-y)).le
        rw [abs_of_nonneg hky]
        gcongr
        exact F.norm_coe_le_norm (s, y))
    have hshift_norm :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding
        (fun y : E3 => euclideanHeatKernel 3 (T - s) y * ‖F‖)
    have hmass_shift : (∫ y : E3,
        euclideanHeatKernel 3 (T - s) (x-y) * ‖F‖) = ‖F‖ := by
      calc
        (∫ y : E3, euclideanHeatKernel 3 (T - s) (x-y) * ‖F‖) =
            ∫ y : E3, euclideanHeatKernel 3 (T - s) y * ‖F‖ := by
              simpa [Function.comp_def] using hshift_norm
        _ = ‖F‖ * (∫ y : E3, euclideanHeatKernel 3 (T-s) y) := by
              rw [integral_mul_const]
              ring
        _ = ‖F‖ := by rw [hmass.2, mul_one]
    calc
      ‖G x s‖ ≤ ∫ y : E3,
          euclideanHeatKernel 3 (T - s) (x-y) * ‖F‖ := by
            simpa [G] using hnorm
      _ = ‖F‖ := hmass_shift
  have hG_int : IntervalIntegrable (G x) volume 0 b := by
    have hbound : (fun s => ‖G x s‖) ≤ᵐ[volume.restrict (uIoc 0 b)]
        (fun _ => ‖F‖) := by
      rw [uIoc_of_le hb]
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall (fun s hs => hG_bound s hs))
    exact intervalIntegrable_const.mono_fun' (hG_sm x).aestronglyMeasurable hbound
  have hIg : 0 ≤ ∫ y : E3, g y :=
    integral_nonneg_of_ae (Eventually.of_forall hg_nonneg)
  have hA : 0 ≤ 3 * ‖F‖ * (∫ y : E3, g y) := by positivity
  have hcoef_int (i : Fin 3) (z : E3) (s : ℝ)
      (hs : s ∈ Ioc (0 : ℝ) b) (hz : z ∈ Metric.ball x 1) :
      Integrable (fun y : E3 => H (T - s) (z - y) i * F (s, y)) volume := by
    have hts := htime s hs
    have hz' : ‖z‖ ≤ ‖x‖ + 1 := hball_norm z hz
    have hmajor : Integrable (fun y : E3 => ‖F‖ * g y) volume :=
      hg.const_mul ‖F‖
    apply hmajor.mono' (hH_cont (T - s) (lt_of_lt_of_le heps hts.1) z s i).aestronglyMeasurable
    filter_upwards [] with y
    rw [norm_mul, Real.norm_eq_abs, hH_eq (T - s) (lt_of_lt_of_le heps hts.1)
      (z - y) i]
    calc
      |fderiv ℝ (euclideanHeatKernel 3 (T - s)) (z - y)
          (EuclideanSpace.single i 1)| * |F (s, y)| ≤ g y * ‖F‖ := by
        exact mul_le_mul (hdom (T - s) hts z y hz' |>.2.1 i)
          (F.norm_coe_le_norm (s, y)) (abs_nonneg _) (hg_nonneg y)
      _ = ‖F‖ * g y := by ring
  have hcoef_bound (i : Fin 3) (z : E3) (s : ℝ)
      (hs : s ∈ Ioc (0 : ℝ) b) (hz : z ∈ Metric.ball x 1) :
      |c i z s| ≤ ‖F‖ * (∫ y : E3, g y) := by
    have hts : 0 < T - s := lt_of_lt_of_le heps (htime s hs).1
    have hmajor : Integrable (fun y : E3 => ‖F‖ * g y) volume :=
      hg.const_mul ‖F‖
    have hnorm := norm_integral_le_of_norm_le
      (f := fun y : E3 => H (T - s) (z - y) i * F (s, y)) hmajor (by
      filter_upwards [] with y
      rw [norm_mul, Real.norm_eq_abs, hH_eq (T - s) hts (z - y) i]
      calc
        |fderiv ℝ (euclideanHeatKernel 3 (T - s)) (z-y)
            (EuclideanSpace.single i 1)| * |F (s,y)| ≤
            g y * |F (s,y)| :=
          mul_le_mul_of_nonneg_right
            (hdom (T - s) (htime s hs) z y (hball_norm z hz) |>.2.1 i)
            (abs_nonneg _)
        _ ≤ g y * ‖F‖ :=
          mul_le_mul_of_nonneg_left (F.norm_coe_le_norm (s,y)) (hg_nonneg y)
        _ = ‖F‖ * g y := by ring)
    calc
      |c i z s| = |∫ y : E3, H (T - s) (z - y) i * F (s, y)| := by rfl
      _ ≤
          ∫ y : E3, ‖F‖ * g y := by
        simpa [Real.norm_eq_abs] using hnorm
      _ = ‖F‖ * (∫ y : E3, g y) := by rw [integral_const_mul]
  have hG'_bound (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) (z : E3)
      (hz : z ∈ Metric.ball x 1) : ‖G' z s‖ ≤ 3 * ‖F‖ * (∫ y : E3, g y) := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro v
    dsimp [G']
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      PiLp.proj_apply, smul_eq_mul]
    calc
      ‖∑ i : Fin 3, c i z s * v i‖ ≤
          ∑ i : Fin 3, ‖c i z s * v i‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, |c i z s| * |v i| := by
        simp [Real.norm_eq_abs]
      _ ≤ ∑ i : Fin 3, (‖F‖ * (∫ y : E3, g y)) * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |c i z s| * |v i| ≤
              (‖F‖ * (∫ y : E3, g y)) * |v i| :=
            mul_le_mul_of_nonneg_right (hcoef_bound i z s hs hz) (abs_nonneg _)
          _ ≤ (‖F‖ * (∫ y : E3, g y)) * ‖v‖ :=
            mul_le_mul_of_nonneg_left
              (by simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v i))
              (by positivity)
      _ = (3 * ‖F‖ * (∫ y : E3, g y)) * ‖v‖ := by
        simp
        ring
  have hinner (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) (z : E3)
      (hz : z ∈ Metric.ball x 1) :
      HasFDerivAt (G · s) (G' z s) z := by
    have hts : 0 < T - s := lt_of_lt_of_le heps (htime s hs).1
    have h := bounded_heat_first_fderiv (fs s) hts z
    have heq : (∑ i : Fin 3,
        (∫ y : E3, fderiv ℝ (euclideanHeatKernel 3 (T - s)) (z-y)
          (EuclideanSpace.single i 1) * fs s y) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i)) = G' z s := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        change fderiv ℝ (euclideanHeatKernel 3 (T - s)) (z-y)
            (EuclideanSpace.single i 1) * F (s, y) =
          H (T-s) (z-y) i * F (s,y)
        rw [← hH_eq (T - s) hts (z-y) i])
    rw [heq] at h
    simpa [G, fs] using h
  have h_bound : ∀ᵐ s ∂volume.restrict (uIoc (0 : ℝ) b),
      ∀ z ∈ Metric.ball x 1, ‖G' z s‖ ≤ 3 * ‖F‖ * (∫ y : E3, g y) := by
    rw [uIoc_of_le hb]
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall (fun s hs z hz => hG'_bound s hs z hz))
  have h_diff : ∀ᵐ s ∂volume.restrict (uIoc (0 : ℝ) b),
      ∀ z ∈ Metric.ball x 1, HasFDerivAt (G · s) (G' z s) z := by
    rw [uIoc_of_le hb]
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall (fun s hs z hz => hinner s hs z hz))
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (μ := (volume : Measure ℝ)) (F := G) (F' := G')
      (a := (0 : ℝ)) (b := b) (bound := fun _ : ℝ =>
        3 * ‖F‖ * (∫ y : E3, g y)) (s := Metric.ball x 1) (x₀ := x)
      (Metric.ball_mem_nhds x one_pos) hG_meas hG_int hG'_meas h_bound
      intervalIntegrable_const h_diff
  have hc_int (i : Fin 3) : IntervalIntegrable (c i x) volume 0 b := by
    have hle : (fun s => ‖c i x s‖) ≤ᵐ[volume.restrict (uIoc 0 b)]
        (fun _ => ‖F‖ * (∫ y : E3, g y)) := by
      rw [uIoc_of_le hb]
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall (fun s hs => by
          simpa [Real.norm_eq_abs] using hcoef_bound i x s hs
            (Metric.mem_ball_self one_pos)))
    exact intervalIntegrable_const.mono_fun' (hc_sm i x).aestronglyMeasurable hle
  have hsum_int : (∫ s in (0 : ℝ)..b, G' x s) =
      ∑ i : Fin 3, (∫ s in (0 : ℝ)..b, c i x s) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
    calc
      (∫ s in (0 : ℝ)..b, G' x s) =
          ∫ s in (0 : ℝ)..b, ∑ i : Fin 3, (c i x s) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
              rfl
      _ = ∑ i : Fin 3, ∫ s in (0 : ℝ)..b, (c i x s) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
              exact intervalIntegral.integral_finsetSum (s := Finset.univ)
                (fun i hi => (hc_int i).smul_continuousOn continuousOn_const)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_smul_const]
  have hc_eq (i : Fin 3) :
      (∫ s in (0 : ℝ)..b, c i x s) =
        ∫ s in (0 : ℝ)..b, ∫ y : E3,
          fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
            (EuclideanSpace.single i 1) * F (s,y) := by
    change (∫ s in (0 : ℝ)..b, (∫ y : E3,
      H (T-s) (x-y) i * F (s,y))) = _
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le hb]
    exact Eventually.of_forall (fun s hs => by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        change H (T-s) (x-y) i * F (s,y) =
          fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
            (EuclideanSpace.single i 1) * F (s,y)
        rw [hH_eq (T-s) (by
          exact lt_of_lt_of_le heps (htime s hs).1) (x-y) i]) )
  have hsum_final : (∫ s in (0 : ℝ)..b, G' x s) =
      ∑ i : Fin 3, (∫ s in (0 : ℝ)..b, ∫ y : E3,
        fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
          (EuclideanSpace.single i 1) * F (s,y)) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) := by
    rw [hsum_int]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc_eq i]
  rw [← hsum_final]
  simpa [G, b] using hmain
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
