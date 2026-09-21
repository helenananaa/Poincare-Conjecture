import DoCarmoLib.Riemannian.Metric.RiemannianMetric

open Set Function Riemannian Bundle
open scoped ContDiff Manifold Topology Bundle
noncomputable section
namespace MorganTianLib.SurgeryInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A scalar cutoff constant near the tip removes nonsmoothness of a radial coordinate. -/
theorem contMDiff_comp_of_flattened_tip (s : M → ℝ) (F : ℝ → ℝ)
    {a b c : ℝ} (hab : a < b) (hs : Continuous s)
    (hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ s {x | s x < b})
    (hF : ContDiff ℝ ∞ F) (hflat : ∀ r, a ≤ r → F r = c) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (F ∘ s) := by
/- SWARM_PROOF_BEGIN -/
  intro x
  by_cases hx : s x < b
  · have hnb : {y | s y < b} ∈ 𝓝 x := by
      change s ⁻¹' Iio b ∈ 𝓝 x
      apply hs.continuousAt.preimage_mem_nhds
      exact isOpen_Iio.mem_nhds hx
    exact hF.contMDiff.contMDiffAt.comp x
      (hsmooth.contMDiffAt hnb)
  · have hxa : a < s x := lt_of_lt_of_le hab (le_of_not_gt hx)
    have hnb : {y | a < s y} ∈ 𝓝 x := by
      change s ⁻¹' Ioi a ∈ 𝓝 x
      apply hs.continuousAt.preimage_mem_nhds
      exact isOpen_Ioi.mem_nhds hxa
    apply contMDiffAt_const (c := c) |>.congr_of_eventuallyEq
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, hflat (s y) (le_of_lt hy)]
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryInterpolation
