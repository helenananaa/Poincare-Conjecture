import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHolderControl

open Set MeasureTheory Filter
open scoped Topology
noncomputable section
namespace MorganTianLib.ParabolicPDE

/-- **Math.** The actual time-integrated heat-Hessian convolution has zero initial trace uniformly in space. -/
theorem gaussianHeatKernel_duhamel_uniform_zero_trace
    {alpha H : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1) (hH : 0 ≤ H)
    {F : ℝ × ℝ → ℝ} (hF : Continuous F)
    (hholder : ∀ s : ℝ, 0 ≤ s → ∀ x y : ℝ,
      |F (s, x) - F (s, y)| ≤ H * |x - y| ^ alpha) :
    TendstoUniformly
      (fun t x : ℝ => ∫ s in (0 : ℝ)..t, ∫ y : ℝ,
        iteratedDeriv 2 (gaussianHeatKernel (t - s)) y * F (s, x - y))
      (fun _ : ℝ => 0) (𝓝[>] (0 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := gaussianHeatKernel_duhamel_holder_control alpha ha ha1
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
  have htimepos : 0 < t := htime
  have h := (hbound F hF H t hH htimepos.le
    (fun s hs => hholder s hs.1) x).2
  simpa only [Real.dist_eq, zero_sub, abs_neg] using h.trans_lt ht

end MorganTianLib.ParabolicPDE
