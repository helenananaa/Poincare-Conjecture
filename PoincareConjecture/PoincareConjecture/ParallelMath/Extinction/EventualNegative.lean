import PoincareConjecture.ParallelMath.Core
import PoincareConjecture.ParallelMath.Extinction.ExplicitDerivative

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped Topology

/-- If the coefficient stays nonnegative, the linear comparison solution with
positive forcing eventually becomes negative. Distinct from
`powerBarrier_eventually_negative`. -/
theorem comparisonSolution_eventually_negative
    (q : ℝ → ℝ) (hq : Continuous q) (k a s : ℝ)
    (hqnn : ∀ t, s ≤ t → 0 ≤ q t) (hk : 0 < k) :
    ∃ T : ℝ, s ≤ T ∧ ∀ t : ℝ, T ≤ t → comparisonSolution q k a s t < 0 :=
/- SWARM_PROOF_BEGIN -/
by
  -- Indefinite integral of a continuous coefficient is C¹, hence continuous.
  have hA_cont : Continuous (fun u => rateIntegral q s u) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hq.integral_hasStrictDerivAt s u).hasDerivAt.continuousAt
  have hExp_cont : Continuous (fun x => Real.exp (rateIntegral q s x)) :=
    Real.continuous_exp.comp hA_cont
  -- Nonnegativity of `q` on `[s, ∞)` makes the integrating factor at least `1`.
  have hrate : ∀ x, s ≤ x → 0 ≤ rateIntegral q s x := fun x hx =>
    intervalIntegral.integral_nonneg hx fun u hu => hqnn u hu.1
  -- After time `s + max(a/k, 0) + 1` the length `t - s` already exceeds `a/k`.
  set T : ℝ := s + max (a / k) 0 + 1
  have hsT : s ≤ T :=
    (le_add_of_nonneg_right (le_max_right (a / k) 0)).trans
      (le_add_of_nonneg_right zero_le_one)
  refine ⟨T, hsT, fun t ht => ?_⟩
  have hst : s ≤ t := hsT.trans ht
  have hge : t - s ≤ ∫ x in s..t, Real.exp (rateIntegral q s x) := by
    have h1 : (∫ _ in s..t, (1 : ℝ)) = t - s := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [← h1]
    exact intervalIntegral.integral_mono_on hst
      (continuous_const.intervalIntegrable s t)
      (hExp_cont.intervalIntegrable s t)
      (fun x hx => Real.one_le_exp (hrate x hx.1))
  have hgt : a / k < t - s := by
    have hT : T - s = max (a / k) 0 + 1 := by
      simp only [T]
      ring
    have : a / k < T - s := by
      rw [hT]
      exact (le_max_left (a / k) 0).trans_lt (lt_add_of_pos_right _ one_pos)
    exact this.trans_le (sub_le_sub_right ht s)
  have hinter :
      a - k * (∫ x in s..t, Real.exp (rateIntegral q s x)) < 0 := by
    rw [sub_lt_zero]
    have : a / k < ∫ x in s..t, Real.exp (rateIntegral q s x) := hgt.trans_le hge
    have hmul := (div_lt_iff₀ hk).mp this
    rwa [mul_comm] at hmul
  -- Prefactor `exp(-∫ q)` is strictly positive, so the product has the inner sign.
  simpa [comparisonSolution] using
    mul_neg_of_pos_of_neg (Real.exp_pos _) hinter
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
