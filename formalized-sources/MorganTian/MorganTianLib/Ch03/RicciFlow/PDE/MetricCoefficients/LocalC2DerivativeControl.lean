import Mathlib
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)

/-- **Math.** local C2 derivative control. -/
theorem local_C2_derivative_control {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x0 : E) (hf : ContDiffAt ℝ 2 f x0) :
    ∃ r M L : ℝ, 0 < r ∧ 0 < M ∧ 0 < L ∧
      (∀ x ∈ Metric.ball x0 r, DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ M) ∧
      ∀ x ∈ Metric.ball x0 r, ∀ y ∈ Metric.ball x0 r,
        ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ L*‖x-y‖ :=
/- SWARM_PROOF_BEGIN -/
by
  rcases (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (f := f) (x := x0)).mp hf with
    ⟨g, ⟨u, hu, hfg⟩, hg⟩
  rcases hg.exists_lipschitzOnWith with ⟨K, t, ht, hLip⟩
  rcases Metric.mem_nhds_iff.mp (Filter.inter_mem hu ht) with ⟨ε, hε, hball⟩
  have hder (x : E) (hx : x ∈ u) : fderiv ℝ f x = g x := (hfg x hx).fderiv
  have hx0t : x0 ∈ t := (hball (Metric.mem_ball_self hε)).2
  refine ⟨ε, ‖g x0‖ + (K : ℝ) * ε + 1, (K : ℝ) + 1, hε, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro x hx
    have hxu : x ∈ u := (hball hx).1
    have hxt : x ∈ t := (hball hx).2
    have hLipx := hLip.dist_le_mul x hxt x0 hx0t
    have hnormdiff : ‖g x - g x0‖ ≤ (K : ℝ) * ‖x - x0‖ := by
      simpa only [dist_eq_norm] using hLipx
    have hxnorm : ‖x - x0‖ ≤ ε := by
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx).le
    refine ⟨(hfg x hxu).differentiableAt, ?_⟩
    rw [hder x hxu]
    calc
      ‖g x‖ ≤ ‖g x - g x0‖ + ‖g x0‖ := by
        calc
          ‖g x‖ = ‖(g x - g x0) + g x0‖ := by congr 1; abel
          _ ≤ ‖g x - g x0‖ + ‖g x0‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖x - x0‖ + ‖g x0‖ := by
        simpa [add_comm] using add_le_add_left hnormdiff ‖g x0‖
      _ ≤ (K : ℝ) * ε + ‖g x0‖ := by
        gcongr
      _ ≤ ‖g x0‖ + (K : ℝ) * ε + 1 := by linarith
  · intro x hx y hy
    have hxt : x ∈ t := (hball hx).2
    have hyt : y ∈ t := (hball hy).2
    have hLipxy := hLip.dist_le_mul x hxt y hyt
    have hnormdiff : ‖g x - g y‖ ≤ (K : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hLipxy
    have hxu : x ∈ u := (hball hx).1
    have hyu : y ∈ u := (hball hy).1
    calc
      ‖fderiv ℝ f x - fderiv ℝ f y‖ = ‖g x - g y‖ := by rw [hder x hxu, hder y hyu]
      _ ≤ (K : ℝ) * ‖x - y‖ := hnormdiff
      _ ≤ ((K : ℝ) + 1) * ‖x - y‖ := by
        have hn := norm_nonneg (x - y)
        nlinarith
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
