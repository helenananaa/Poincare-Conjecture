import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HolderInitialTrace

open Set MeasureTheory Filter
open scoped Topology
noncomputable section
namespace MorganTianLib.ParabolicPDE

/-- **Math.** The actual heat convolution converges uniformly to globally Holder
initial data as positive time tends to zero, even for unbounded data. -/
theorem gaussianHeatKernel_holder_uniform_initial_trace
    {alpha H : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1) (hH : 0 ≤ H)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hholder : ∀ x y, |f x - f y| ≤ H * |x - y| ^ alpha) :
    TendstoUniformly
      (fun t x : ℝ => ∫ y : ℝ, gaussianHeatKernel t y * f (x - y))
      f (𝓝[>] (0 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := gaussianHeatKernel_holder_initial_trace alpha ha ha1
  have hb : 0 < alpha / 2 := by linarith
  have hp : Tendsto (fun t : ℝ => t ^ (alpha / 2)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuous_rpow_const hb.le).tendsto (0 : ℝ)
    simpa only [Real.zero_rpow hb.ne'] using h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => C * H * t ^ (alpha / 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hp :
      Tendsto (fun t : ℝ => (C * H) * t ^ (alpha / 2)) (𝓝[>] 0) (𝓝 ((C * H) * 0)))
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hsmall := hlim.eventually (eventually_lt_nhds hepsilon)
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht htime
  intro x
  simpa only [Real.dist_eq, abs_sub_comm] using
    ((hbound f H hf hH hholder t htime x).2.trans_lt ht)

end MorganTianLib.ParabolicPDE
