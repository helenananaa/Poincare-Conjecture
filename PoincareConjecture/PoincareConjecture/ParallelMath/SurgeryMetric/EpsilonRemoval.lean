import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Remove the approximate-length error without requiring an actual minimizing path. -/
theorem le_mul_of_forall_length_error (d r L : ℝ) (hL : 0 ≤ L)
    (h : ∀ epsilon : ℝ, 0 < epsilon → d ≤ L*(r+epsilon)) : d ≤ L*r :=
/- SWARM_PROOF_BEGIN -/
by
  rcases eq_or_lt_of_le hL with rfl | _
  · simpa using h 1 one_pos
  · have hlim : Tendsto (fun ε : ℝ => L * (r + ε)) (𝓝[>] 0) (𝓝 (L * r)) := by
      have hc : Continuous fun ε : ℝ => L * (r + ε) := by fun_prop
      have : Tendsto (fun ε : ℝ => L * (r + ε)) (𝓝 0) (𝓝 (L * r)) := by
        simpa using hc.tendsto (0 : ℝ)
      exact this.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim <|
      eventually_of_mem self_mem_nhdsWithin fun ε hε => h ε hε
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
