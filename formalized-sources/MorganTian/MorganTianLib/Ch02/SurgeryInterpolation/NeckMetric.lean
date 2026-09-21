import MorganTianLib.Ch02.SurgeryInterpolation.WeightedMetric
import MorganTianLib.Ch02.SurgeryInterpolation.ScalarProfile

open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryInterpolation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A genuine smooth neck-side interpolation with exact seams and pointwise contraction. -/
theorem exists_neck_interpolationMetric (g g0 : RiemannianMetric I M)
    (s : M → ℝ) (hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ s)
    (amplitude q eta : ℝ) (ha : 0 ≤ amplitude) (hq : 0 < q) (heta : 0 < eta)
    (hdom : ∀ x v, eta * g0.metricInner x v v ≤ g.metricInner x v v) :
    ∃ gh : RiemannianMetric I M,
      (∀ x v w, gh.metricInner x v w = Real.exp (-2 * neckProfile amplitude q (s x)) *
        (neckCutoff (s x) * g.metricInner x v w +
          (1 - neckCutoff (s x)) * eta * g0.metricInner x v w)) ∧
      (∀ x, s x ≤ 0 → ∀ v w, gh.metricInner x v w = g.metricInner x v w) ∧
      (∀ x, 7 / 4 ≤ s x → ∀ v w, gh.metricInner x v w =
        Real.exp (-2 * neckProfile amplitude q (s x)) * eta * g0.metricInner x v w) ∧
      (∀ x v, gh.metricInner x v v ≤ g.metricInner x v v) := by
/- SWARM_PROOF_BEGIN -/
  let f : M → ℝ := fun x => neckProfile amplitude q (s x)
  let c : M → ℝ := fun x => neckCutoff (s x)
  let e : M → ℝ := fun x => Real.exp (-2 * f x)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    exact (neckProfile_contDiff amplitude q).contMDiff.comp hs
  have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ c := by
    exact neckCutoff_contDiff.contMDiff.comp hs
  have he : ContMDiff I 𝓘(ℝ, ℝ) ∞ e := by
    exact (Real.contDiff_exp.comp (contDiff_const.mul (neckProfile_contDiff amplitude q))).contMDiff.comp hs
  have hscale_pos : ∀ x, 0 < e x := by
    intro x
    exact Real.exp_pos _
  have hscale_le_one : ∀ x, e x ≤ 1 := by
    intro x
    apply Real.exp_le_one_iff.mpr
    dsimp [e, f]
    nlinarith [neckProfile_nonneg ha q (s x)]
  have hc_mem : ∀ x, c x ∈ Icc (0 : ℝ) 1 := by
    intro x
    exact neckCutoff_mem_Icc (s x)
  have hpos : ∀ x, 0 < e x * c x + e x * (1 - c x) * eta := by
    intro x
    have hcx := hc_mem x
    by_cases hcp : 0 < c x
    · have hleft : 0 < e x * c x := mul_pos (hscale_pos x) hcp
      have hright : 0 ≤ e x * (1 - c x) * eta := by
        exact mul_nonneg (mul_nonneg (hscale_pos x).le (sub_nonneg.mpr hcx.2)) heta.le
      linarith
    · have hc0 : c x = 0 := le_antisymm (le_of_not_gt hcp) hcx.1
      rw [hc0]
      simpa using mul_pos (hscale_pos x) heta
  obtain ⟨gh, hgh⟩ := exists_weighted_riemannianMetric g g0
    (fun x => e x * c x) (fun x => e x * (1 - c x) * eta)
    (he.mul hc) ((he.mul (contMDiff_const.sub hc)).mul contMDiff_const)
    (fun x => mul_nonneg (hscale_pos x).le (hc_mem x).1)
    (fun x => mul_nonneg (mul_nonneg (hscale_pos x).le (sub_nonneg.mpr (hc_mem x).2)) heta.le)
    hpos
  refine ⟨gh, ?_, ?_, ?_, ?_⟩
  · intro x v w
    rw [hgh]
    dsimp [e, f, c]
    ring
  · intro x hx v w
    have hfx : f x = 0 := by
      dsimp [f]
      exact neckProfile_eq_zero hq hx amplitude
    have hcx : c x = 1 := by
      dsimp [c]
      exact neckCutoff_eq_one (le_trans hx (by norm_num))
    rw [hgh]
    simp [e, hfx, hcx]
  · intro x hx v w
    have hcx : c x = 0 := by
      dsimp [c]
      exact neckCutoff_eq_zero hx
    rw [hgh, hcx]
    dsimp [e]
    ring
  · intro x v
    have hcx := hc_mem x
    have hfx : 0 ≤ f x := neckProfile_nonneg ha q (s x)
    have h0 : 0 ≤ g.metricInner x v v := g.metricInner_self_nonneg x v
    have h00 : 0 ≤ g0.metricInner x v v := g0.metricInner_self_nonneg x v
    have hterm : (1 - c x) * eta * g0.metricInner x v v ≤
        (1 - c x) * g.metricInner x v v := by
      have hmul := mul_le_mul_of_nonneg_left (hdom x v) (sub_nonneg.mpr hcx.2)
      nlinarith
    have hcomb : c x * g.metricInner x v v +
        (1 - c x) * eta * g0.metricInner x v v ≤ g.metricInner x v v := by
      have hadd := add_le_add_left hterm (c x * g.metricInner x v v)
      nlinarith
    have hcomb0 : 0 ≤ c x * g.metricInner x v v +
        (1 - c x) * eta * g0.metricInner x v v := by
      exact add_nonneg (mul_nonneg hcx.1 h0)
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr hcx.2) heta.le) h00)
    have hscale := mul_le_mul_of_nonneg_right (hscale_le_one x) hcomb0
    rw [hgh]
    calc
      e x * c x * g.metricInner x v v + e x * (1 - c x) * eta *
          g0.metricInner x v v =
        e x * (c x * g.metricInner x v v +
          (1 - c x) * eta * g0.metricInner x v v) := by ring
      _ ≤ 1 * (c x * g.metricInner x v v +
          (1 - c x) * eta * g0.metricInner x v v) := hscale
      _ = c x * g.metricInner x v v +
          (1 - c x) * eta * g0.metricInner x v v := by ring
      _ ≤ g.metricInner x v v := hcomb
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryInterpolation
