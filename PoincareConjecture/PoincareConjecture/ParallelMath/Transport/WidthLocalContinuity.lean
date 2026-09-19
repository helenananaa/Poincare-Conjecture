import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Variational.WidthContinuity

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Uniform exponential distortion on an arbitrary time set gives relative continuity of the infimum. -/
theorem leastCost_continuousOn_of_exp_distortion {A : Type*} [Nonempty A]
    (F : ℝ → A → ℝ) (S : Set ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hn : ∀ t ∈ S, ∀ a, 0 ≤ F t a)
    (hc : ∀ s ∈ S, ∀ t ∈ S, ∀ a, F t a ≤ Real.exp (K*|t-s|)*F s a) :
    ContinuousOn (fun t => PoincareConjecture.ParallelMath.Variational.leastCost (F t)) S :=
/- SWARM_PROOF_BEGIN -/
by
  intro s hs
  have htrans : ∀ u ∈ S, ∀ v ∈ S,
      PoincareConjecture.ParallelMath.Variational.leastCost (F v) ≤
        Real.exp (K * |v - u|) *
          PoincareConjecture.ParallelMath.Variational.leastCost (F u) := by
    intro u hu v hv
    have hKd : 0 ≤ K * |v - u| := mul_nonneg hK (abs_nonneg _)
    have h :=
      PoincareConjecture.ParallelMath.Variational.leastCost_transfer
        (F u) (F v) (hn u hu) (hn v hv) (id : A → A)
        (Real.exp (K * |v - u|)) 0 (le_trans zero_le_one (Real.one_le_exp hKd))
        fun a => by simpa using hc u hu v hv a
    simpa using h
  have hlo :
      ∀ t ∈ S,
        PoincareConjecture.ParallelMath.Variational.leastCost (F s) *
            Real.exp (-(K * |t - s|)) ≤
          PoincareConjecture.ParallelMath.Variational.leastCost (F t) := by
    intro t ht
    have he : 0 < Real.exp (K * |t - s|) := Real.exp_pos _
    have hst :
        PoincareConjecture.ParallelMath.Variational.leastCost (F s) ≤
          Real.exp (K * |t - s|) *
            PoincareConjecture.ParallelMath.Variational.leastCost (F t) := by
      simpa [abs_sub_comm] using htrans t ht s hs
    rw [Real.exp_neg]
    exact (mul_inv_le_iff₀ he).mpr (by rwa [mul_comm] at hst)
  have hhi :
      ∀ t ∈ S,
        PoincareConjecture.ParallelMath.Variational.leastCost (F t) ≤
          PoincareConjecture.ParallelMath.Variational.leastCost (F s) *
            Real.exp (K * |t - s|) := by
    intro t ht
    simpa [mul_comm] using htrans s hs t ht
  have hlo_lim :
      Tendsto
        (fun t =>
          PoincareConjecture.ParallelMath.Variational.leastCost (F s) *
            Real.exp (-(K * |t - s|)))
        (nhdsWithin s S)
        (𝓝 (PoincareConjecture.ParallelMath.Variational.leastCost (F s))) := by
    have hcont :
        Continuous fun t =>
          PoincareConjecture.ParallelMath.Variational.leastCost (F s) *
            Real.exp (-(K * |t - s|)) := by
      fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      simpa [sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero] using hcont.tendsto s
  have hhi_lim :
      Tendsto
        (fun t =>
          PoincareConjecture.ParallelMath.Variational.leastCost (F s) *
            Real.exp (K * |t - s|))
        (nhdsWithin s S)
        (𝓝 (PoincareConjecture.ParallelMath.Variational.leastCost (F s))) := by
    have hcont :
        Continuous fun t =>
          PoincareConjecture.ParallelMath.Variational.leastCost (F s) *
            Real.exp (K * |t - s|) := by
      fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      simpa [sub_self, abs_zero, mul_zero, Real.exp_zero] using hcont.tendsto s
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hhi_lim ?_ ?_
  · exact eventually_of_mem self_mem_nhdsWithin hlo
  · exact eventually_of_mem self_mem_nhdsWithin hhi
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
