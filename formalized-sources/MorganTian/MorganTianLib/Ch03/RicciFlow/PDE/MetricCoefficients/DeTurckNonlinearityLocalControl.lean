import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckLieLowerSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.RicciLowerLocalControl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** deturck nonlinearity local control. -/
theorem deturck_nonlinearity_local_control (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (i j : Fin 3) :
    let F := fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
      -2*ricciLowerOrder q.1 q.2 i j + deturckLieLowerOrder q.1 q.2 i j;
    ContDiffAt ℝ ∞ F (A,P) ∧ ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
      ∀ q z, ‖q-(A,P)‖ < r → ‖z-(A,P)‖ < r → |F q-F z| ≤ K*‖q-z‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  have hRicci : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        ricciLowerOrder q.1 q.2 i j) (A, P) :=
    (ricci_lower_order_local_control A P c hc hA i j).1
  have hGauge : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        deturckLieLowerOrder q.1 q.2 i j) (A, P) :=
    deturck_lie_lower_order_smooth A P c hc hA i j
  have hF : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        -2 * ricciLowerOrder q.1 q.2 i j + deturckLieLowerOrder q.1 q.2 i j)
      (A, P) := by
    simpa [smul_eq_mul, mul_neg] using ((hRicci.neg).const_smul (2 : ℝ)).add hGauge
  constructor
  · exact hF
  · have hF1 : ContDiffAt ℝ 1
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          -2 * ricciLowerOrder q.1 q.2 i j + deturckLieLowerOrder q.1 q.2 i j)
        (A, P) := hF.of_le (by simp)
    obtain ⟨K, U, hU, hLip⟩ := hF1.exists_lipschitzOnWith
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨r, (K : ℝ) + 1, hr, by positivity, ?_⟩
    intro q z hq hz
    have hqU : q ∈ U := hrU (by simpa [Metric.mem_ball, dist_eq_norm] using hq)
    have hzU : z ∈ U := hrU (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have h := hLip.dist_le_mul q hqU z hzU
    have h' :
        |(-2 * ricciLowerOrder q.1 q.2 i j + deturckLieLowerOrder q.1 q.2 i j) -
            (-2 * ricciLowerOrder z.1 z.2 i j + deturckLieLowerOrder z.1 z.2 i j)| ≤
          (K : ℝ) * ‖q - z‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using h
    exact h'.trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
