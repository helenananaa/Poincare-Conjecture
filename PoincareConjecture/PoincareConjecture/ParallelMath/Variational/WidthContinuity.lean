import PoincareConjecture.ParallelMath.Variational.InfimumApproximation
import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Uniform exponential distortion gives continuity of a variational width,
even when no minimizer exists at any time. -/
theorem leastCost_continuous_of_exp_distortion {A : Type*} [Nonempty A]
    (F : ℝ → A → ℝ) (hF : ∀ t a, 0 ≤ F t a) (K : ℝ) (hK : 0 ≤ K)
    (hcontrol : ∀ s t a, F t a ≤ Real.exp (K*|t-s|) * F s a) :
    Continuous (fun t => leastCost (F t)) :=
/- SWARM_PROOF_BEGIN -/
by
  have htrans : ∀ s t,
      leastCost (F t) ≤ Real.exp (K * |t - s|) * leastCost (F s) := by
    intro s t
    have hKd : 0 ≤ K * |t - s| := mul_nonneg hK (abs_nonneg _)
    have h :=
      leastCost_transfer (F s) (F t) (hF s) (hF t) (id : A → A)
        (Real.exp (K * |t - s|)) 0 (le_trans zero_le_one (Real.one_le_exp hKd))
        fun a => by simpa using hcontrol s t a
    simpa using h
  refine continuous_iff_continuousAt.mpr fun s => ?_
  have hlo :
      (fun t => leastCost (F s) * Real.exp (-(K * |t - s|))) ≤
        fun t => leastCost (F t) := by
    intro t
    dsimp
    have he : 0 < Real.exp (K * |t - s|) := Real.exp_pos _
    have hst : leastCost (F s) ≤ Real.exp (K * |t - s|) * leastCost (F t) := by
      simpa [abs_sub_comm] using htrans t s
    rw [Real.exp_neg]
    exact (mul_inv_le_iff₀ he).mpr (by rwa [mul_comm] at hst)
  have hhi :
      (fun t => leastCost (F t)) ≤
        fun t => leastCost (F s) * Real.exp (K * |t - s|) := by
    intro t
    dsimp
    simpa [mul_comm] using htrans s t
  have hlo_lim :
      Tendsto (fun t => leastCost (F s) * Real.exp (-(K * |t - s|))) (𝓝 s)
        (𝓝 (leastCost (F s))) := by
    have hc : Continuous fun t => leastCost (F s) * Real.exp (-(K * |t - s|)) := by
      fun_prop
    simpa [sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero] using hc.tendsto s
  have hhi_lim :
      Tendsto (fun t => leastCost (F s) * Real.exp (K * |t - s|)) (𝓝 s)
        (𝓝 (leastCost (F s))) := by
    have hc : Continuous fun t => leastCost (F s) * Real.exp (K * |t - s|) := by
      fun_prop
    simpa [sub_self, abs_zero, mul_zero, Real.exp_zero] using hc.tendsto s
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo_lim hhi_lim hlo hhi
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
