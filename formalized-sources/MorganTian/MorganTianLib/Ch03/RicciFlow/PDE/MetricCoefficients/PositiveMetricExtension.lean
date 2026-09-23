import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PositivePerturbation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** positive metric extension. -/
theorem positive_metric_extension (G : E3 → (E3 →L[ℝ] E3)) (x : E3) (hG : ContDiffAt ℝ 2 G x)
    (hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w))
    (c : ℝ) (hc : 0 < c) (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) :
    ∃ H : E3 → (E3 →L[ℝ] E3), ContDiff ℝ 2 H ∧
      (∀ y v w : E3, inner ℝ (H y v) w = inner ℝ v (H y w)) ∧
      (∀ y v : E3, (c/2)*‖v‖^2 ≤ inner ℝ (H y v) v) ∧
      H =ᶠ[𝓝 x] G ∧ HasCompactSupport (fun y => H y-G x) :=
/- SWARM_PROOF_BEGIN -/
by
  have hGon : ContDiffWithinAt ℝ 2 G univ x := hG
  obtain ⟨U₀, hU₀, hGU₀⟩ :=
    (contDiffWithinAt_iff_contDiffOn_nhds (n := (2 : ℕ∞))
      (f := G) (s := univ) (x := x) (by norm_num)).mp hGon
  have hU₀' : U₀ ∈ 𝓝 x := by simpa using hU₀
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hU₀'
  have hGU : ContDiffOn ℝ 2 G U := hGU₀.mono hUsub
  have hSymX : ∀ v w : E3, inner ℝ (G x v) w = inner ℝ v (G x w) :=
    hsym.self_of_nhds
  have hclose : {y : E3 | ‖G y - G x‖ < c / 2} ∈ 𝓝 x := by
    have hball : Metric.ball (G x) (c / 2) ∈ 𝓝 (G x) :=
      Metric.ball_mem_nhds _ (by linarith [hc])
    filter_upwards [hG.continuousAt.eventually_mem hball] with y hy
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  let good : Set E3 := U ∩
    ({y : E3 | ∀ v w : E3,
      inner ℝ (G y v) w = inner ℝ v (G y w)} ∩
      {y : E3 | ‖G y - G x‖ < c / 2})
  have hgood : good ∈ 𝓝 x := by
    have hSym : {y : E3 | ∀ v w : E3,
        inner ℝ (G y v) w = inner ℝ v (G y w)} ∈ 𝓝 x := hsym
    have hUmem : U ∈ 𝓝 x := hUopen.mem_nhds hxU
    simpa [good] using Filter.inter_mem hUmem (Filter.inter_mem hSym hclose)
  obtain ⟨d, hdpos, hdsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgood
  let b : ContDiffBump x := ⟨d / 2, d, half_pos hdpos, half_lt_self hdpos⟩
  let χ : E3 → ℝ := b
  have hχcont : ContDiff ℝ 2 χ := b.contDiff (n := 2)
  let H : E3 → (E3 →L[ℝ] E3) := fun y => G x + χ y • (G y - G x)
  have hHcont : ContDiff ℝ 2 H := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hyU : y ∈ U
    · have hGy : ContDiffAt ℝ 2 G y :=
        (hGU y hyU).contDiffAt (hUopen.mem_nhds hyU)
      have hχy : ContDiffAt ℝ 2 χ y := hχcont.contDiffAt
      exact contDiffAt_const.add (hχy.smul (hGy.sub contDiffAt_const))
    · have hyts : y ∉ tsupport χ := by
        intro hyts
        have hyclosed : y ∈ Metric.closedBall x d := by
          simpa [χ, b.tsupport_eq] using hyts
        have hygood : y ∈ good := hdsub hyclosed
        exact hyU hygood.1
      have hχzero : χ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
        (notMem_tsupport_iff_eventuallyEq).mp hyts
      have hHconst : H =ᶠ[𝓝 y] (fun _ => G x) :=
        hχzero.mono fun z hz => by simp [H, hz]
      exact contDiff_const.contDiffAt.congr_of_eventuallyEq hHconst
  refine ⟨H, hHcont, ?_, ?_, ?_, ?_⟩
  · intro y v w
    by_cases hχzero : χ y = 0
    · simpa [H, hχzero] using hSymX v w
    · have hyball : y ∈ Metric.ball x d := by
        rw [← b.support_eq]
        change χ y ≠ 0
        exact hχzero
      have hygood : y ∈ good := hdsub (Metric.ball_subset_closedBall hyball)
      have hSymY : ∀ v w : E3,
          inner ℝ (G y v) w = inner ℝ v (G y w) := hygood.2.1
      calc
        inner ℝ (H y v) w =
            inner ℝ (G x v) w + χ y *
              (inner ℝ (G y v) w - inner ℝ (G x v) w) := by
          simp [H, inner_add_left, inner_sub_left, inner_smul_left]
        _ = inner ℝ v (G x w) + χ y *
              (inner ℝ v (G y w) - inner ℝ v (G x w)) := by
          rw [hSymX v w, hSymY v w]
        _ = inner ℝ v (H y w) := by
          simp [H, inner_add_right, inner_sub_right, inner_smul_right]
  · intro y v
    by_cases hχzero : χ y = 0
    · have hhalf : (c / 2) * ‖v‖ ^ 2 ≤ c * ‖v‖ ^ 2 := by
        nlinarith [mul_nonneg (le_of_lt hc) (sq_nonneg ‖v‖)]
      simpa [H, hχzero] using le_trans hhalf (hpos v)
    · have hyball : y ∈ Metric.ball x d := by
        rw [← b.support_eq]
        change χ y ≠ 0
        exact hχzero
      have hygood : y ∈ good := hdsub (Metric.ball_subset_closedBall hyball)
      have hGypos : ∀ v : E3, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ (G y v) v :=
        coercivity_survives_operator_perturbation (G x) (G y) c hc hpos
          (le_of_lt hygood.2.2)
      have hχnonneg : 0 ≤ χ y := b.nonneg
      have hχle : χ y ≤ 1 := b.le_one
      have hcoef : 0 ≤ 1 - χ y := by linarith
      have hformula : H y v = (1 - χ y) • G x v + χ y • G y v := by
        simp [H]
        module
      have hweighted := add_le_add
        (mul_le_mul_of_nonneg_left (hpos v) hcoef)
        (mul_le_mul_of_nonneg_left (hGypos v) hχnonneg)
      have hbase : (c / 2) * ‖v‖ ^ 2 ≤
          (1 - χ y) * (c * ‖v‖ ^ 2) + χ y * ((c / 2) * ‖v‖ ^ 2) := by
        nlinarith [mul_nonneg hcoef
          (mul_nonneg (le_of_lt hc) (sq_nonneg ‖v‖))]
      have hinner : inner ℝ (H y v) v =
          (1 - χ y) * inner ℝ (G x v) v + χ y * inner ℝ (G y v) v := by
        rw [hformula, inner_add_left, inner_smul_left, inner_smul_left]
        simp
      calc
        (c / 2) * ‖v‖ ^ 2 ≤
            (1 - χ y) * (c * ‖v‖ ^ 2) + χ y * ((c / 2) * ‖v‖ ^ 2) := hbase
        _ ≤ (1 - χ y) * inner ℝ (G x v) v + χ y * inner ℝ (G y v) v := hweighted
        _ = inner ℝ (H y v) v := hinner.symm
  · have hb1 : χ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := b.eventuallyEq_one
    filter_upwards [hb1] with y hy
    simp [H, hy]
  · have hHcp : HasCompactSupport (fun y => H y - G x) := by
      let K : Set E3 := {y | ∀ i : Fin 3, dist (y i) (x i) ≤ d}
      let Kpi : Set (Fin 3 → ℝ) :=
        Set.pi univ (fun i : Fin 3 => Metric.closedBall (x i) d)
      let e : E3 ≃ₜ (Fin 3 → ℝ) := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
      have hKpi : IsCompact Kpi := by
        simpa [Kpi] using
          (isCompact_univ_pi (fun i : Fin 3 => isCompact_closedBall (x i) d))
      have hKeq : K = e.symm '' Kpi := by
        ext y
        simp only [K, Kpi, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi,
          Set.mem_univ, e, PiLp.homeomorph]
        constructor
        · intro hy
          refine ⟨y.ofLp, ?_, ?_⟩
          · simpa using hy
          · simp
        · rintro ⟨z, hz, hzy⟩
          have hz' : z = y.ofLp := by
            have h := congrArg (fun q : E3 => q.ofLp) hzy
            simpa using h
          simpa [hz'] using hz
      have hK : IsCompact K := by
        rw [hKeq]
        exact hKpi.image e.symm.continuous
      have hsupport : Function.support (fun y => H y - G x) ⊆ K := by
        intro y hy
        have hχne : χ y ≠ 0 := by
          intro hχzero
          apply hy
          simp [H, hχzero]
        have hyball : y ∈ Metric.ball x d := by
          rw [← b.support_eq]
          change χ y ≠ 0
          exact hχne
        have hnorm : ‖y - x‖ ≤ d :=
          (le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hyball))
        intro i
        calc
          dist (y i) (x i) = ‖(y - x) i‖ := by simp [dist_eq_norm]
          _ ≤ ‖y - x‖ := PiLp.norm_apply_le (y - x) i
          _ ≤ d := hnorm
      exact HasCompactSupport.of_support_subset_isCompact hK hsupport
    exact hHcp
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
