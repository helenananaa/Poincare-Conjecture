import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- **Math.** local selfadjoint extension. -/
theorem local_selfadjoint_extension (G : E3 → (E3 →L[ℝ] E3)) (x : E3) (hG : ContDiffAt ℝ 2 G x)
    (hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w)) :
    ∃ H : E3 → (E3 →L[ℝ] E3), ContDiff ℝ 2 H ∧
      (∀ y v w : E3, inner ℝ (H y v) w = inner ℝ v (H y w)) ∧
      H =ᶠ[𝓝 x] G :=
/- SWARM_PROOF_BEGIN -/
by
  have hGon : ContDiffWithinAt ℝ 2 G univ x := hG
  obtain ⟨U₀, hU₀, hGU₀⟩ :=
    (contDiffWithinAt_iff_contDiffOn_nhds (n := (2 : ℕ∞))
      (f := G) (s := univ) (x := x) (by norm_num)).mp hGon
  have hU₀' : U₀ ∈ 𝓝 x := by simpa using hU₀
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hU₀'
  have hGU : ContDiffOn ℝ 2 G U := hGU₀.mono hUsub
  have hSym : {y : E3 | ∀ v w : E3,
      inner ℝ (G y v) w = inner ℝ v (G y w)} ∈ 𝓝 x := hsym
  have hUS : U ∩ {y : E3 | ∀ v w : E3,
      inner ℝ (G y v) w = inner ℝ v (G y w)} ∈ 𝓝 x :=
    Filter.inter_mem (hUopen.mem_nhds hxU) hSym
  obtain ⟨d, hdpos, hdsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hUS
  let b : ContDiffBump x := ⟨d / 2, d, half_pos hdpos, half_lt_self hdpos⟩
  let χ : E3 → ℝ := b
  have hχcont : ContDiff ℝ 2 χ := by
    exact b.contDiff (n := 2)
  let H : E3 → (E3 →L[ℝ] E3) := fun y => χ y • G y
  have hHcont : ContDiff ℝ 2 H := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hyU : y ∈ U
    · have hGy : ContDiffAt ℝ 2 G y :=
        (hGU y hyU).contDiffAt (hUopen.mem_nhds hyU)
      have hχy : ContDiffAt ℝ 2 χ y := hχcont.contDiffAt
      exact hχy.smul hGy
    · have hyts : y ∉ tsupport χ := by
        intro hyts
        have hyclosed : y ∈ Metric.closedBall x d := by
          simpa [χ, b.tsupport_eq] using hyts
        exact hyU (hdsub hyclosed).1
      have hχzero : χ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
        (notMem_tsupport_iff_eventuallyEq).mp hyts
      have hHzero : H =ᶠ[𝓝 y] (fun _ => (0 : E3 →L[ℝ] E3)) :=
        hχzero.mono fun z hz => by
          change χ z • G z = 0
          rw [hz]
          exact zero_smul ℝ (G z)
      exact contDiff_const.contDiffAt.congr_of_eventuallyEq hHzero
  refine ⟨H, hHcont, ?_, ?_⟩
  · intro y v w
    by_cases hyχ : χ y = 0
    · simp [H, hyχ]
    · have hyS : ∀ v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w) := by
        have hyball : y ∈ Metric.ball x d := by
          rw [← b.support_eq]
          change χ y ≠ 0
          exact hyχ
        have hyclosed : y ∈ Metric.closedBall x d := Metric.ball_subset_closedBall hyball
        exact (hdsub hyclosed).2
      simp [H, inner_smul_left, inner_smul_right, hyS]
  · have hb1 : χ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      exact b.eventuallyEq_one
    filter_upwards [hb1] with y hy
    simp [H, hy]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
