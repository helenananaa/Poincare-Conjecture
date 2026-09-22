import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedClassicalIVP
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedDuhamelNonlinearDifference
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- An actual bounded mild solution recovers its prescribed initial data uniformly. -/
theorem semilinear_mild_initial_trace (f : E3 →ᵇ ℝ) (hf : UniformContinuous f)
    (N : ℝ → ℝ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 < T)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|)
    (u : (ℝ × E3) →ᵇ ℝ)
    (hu : ∀ p : ℝ × E3, u p =
      (if max 0 (min T p.1) = 0 then f p.2 else
        ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)) y * f (p.2-y)) +
      ∫ s in (0:ℝ)..max 0 (min T p.1), ∫ y : E3,
        euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * N (u (s,p.2-y))) :
    (∀ x, u (0,x)=f x) ∧ TendstoUniformly (fun t x => u (t,x)) f (𝓝[>] (0:ℝ)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hNlip : LipschitzWith L.toNNReal N :=
    LipschitzWith.of_dist_le_mul (fun a b : ℝ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
      exact hN a b)
  have hNcont : Continuous N := hNlip.continuous
  have hcont : Continuous (fun p : ℝ × E3 => N (u p)) :=
    hNcont.comp u.continuous
  have hC : 0 ≤ |N 0| + L * ‖u‖ := by positivity
  have hbound : ∀ p : ℝ × E3,
      ‖N (u p)‖ ≤ |N 0| + L * ‖u‖ := by
    intro p
    rw [Real.norm_eq_abs]
    calc
      |N (u p)| ≤ |N (u p) - N 0| + |N 0| := by
        calc
          |N (u p)| = |(N (u p) - N 0) + N 0| := by congr 1 <;> ring
          _ ≤ |N (u p) - N 0| + |N 0| := abs_add_le _ _
      _ ≤ L * |u p| + |N 0| := by
        gcongr
        simpa using hN (u p) 0
      _ ≤ |N 0| + L * ‖u‖ := by
        have hu' : |u p| ≤ ‖u‖ := by
          rw [← Real.norm_eq_abs]
          exact u.norm_coe_le_norm p
        calc
          L * |u p| + |N 0| = |N 0| + L * |u p| := add_comm _ _
          _ ≤ |N 0| + L * ‖u‖ := by
            simpa [add_comm] using
              (add_le_add_left (mul_le_mul_of_nonneg_left hu' hL) |N 0|)
  let H : (ℝ × E3) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (u p)) hcont (|N 0| + L * ‖u‖) hbound
  have hHnorm : ‖H‖ ≤ |N 0| + L * ‖u‖ :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      hcont hC hbound
  have htrace := euclideanHeatKernel_three_uniform_initial_trace f hf
  refine ⟨?_, ?_⟩
  · intro x
    rw [hu (0, x)]
    simp [hT.le]
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have htraceε : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ∀ x : E3, dist
          (∫ y : E3, euclideanHeatKernel 3 t y * f (x - y)) (f x) < ε / 2 := by
      have := (Metric.tendstoUniformly_iff.mp htrace) (ε / 2) (by linarith)
      filter_upwards [this] with t ht x
      simpa [dist_comm] using ht x
    have hforce_lim : Tendsto (fun t : ℝ => t * (|N 0| + L * ‖u‖))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hid.mul tendsto_const_nhds
    have hforce : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        t * (|N 0| + L * ‖u‖) < ε / 2 :=
      hforce_lim.eventually (eventually_lt_nhds (by linarith))
    have hTevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < T :=
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, htraceε, hforce, hTevent]
      with t ht hlin hforcing htT
    intro x
    have ht0 : 0 < t := ht
    have hclip : max 0 (min T t) = t := by
      rw [max_eq_right (lt_min hT ht0).le, min_eq_right (le_of_lt htT)]
    have huform : u (t, x) =
        (∫ y : E3, euclideanHeatKernel 3 t y * f (x - y)) +
          ∫ s in (0 : ℝ)..t, ∫ y : E3,
            euclideanHeatKernel 3 (t - s) y * H (s, x - y) := by
      rw [hu (t, x), hclip]
      simp [ht0.ne', H]
    have hduh := euclideanHeatKernel_three_bounded_duhamel H t (le_of_lt ht) x
    let a : ℝ := ∫ y : E3, euclideanHeatKernel 3 t y * f (x - y)
    let b : ℝ := ∫ s in (0 : ℝ)..t, ∫ y : E3,
      euclideanHeatKernel 3 (t - s) y * H (s, x - y)
    have huform' : u (t, x) = a + b := by
      simpa [a, b] using huform
    have ha : |a - f x| < ε / 2 := by
      simpa [a, Real.dist_eq] using hlin x
    have hb : |b| ≤ t * ‖H‖ := by
      simpa [b] using hduh.2
    have hb' : |b| ≤ t * (|N 0| + L * ‖u‖) :=
      hb.trans (mul_le_mul_of_nonneg_left hHnorm (le_of_lt ht0))
    rw [huform', Real.dist_eq, abs_sub_comm]
    calc
      |(a + b) - f x| = |(a - f x) + b| := by
        congr 1
        ring_nf
      _ ≤ |a - f x| + |b| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · exact ha
        · exact hb'.trans_lt hforcing
      _ = ε := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
