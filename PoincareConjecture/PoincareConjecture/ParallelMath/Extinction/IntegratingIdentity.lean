import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Every continuous scalar ODE solution has the exact integrating-factor identity. -/
theorem integratingFactor_identity (q w : ℝ → ℝ) (hq : Continuous q)
    (k s t : ℝ) (hst : s ≤ t) (hw : ContinuousOn w (Icc s t))
    (hd : ∀ x ∈ Ioo s t, HasDerivAt w (-k-q x*w x) x) :
    Real.exp (rateIntegral q s t) * w t =
      w s - k * ∫ x in s..t, Real.exp (rateIntegral q s x) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases eq_or_lt_of_le hst with rfl | hst
  · simp [rateIntegral, intervalIntegral.integral_same]
  set μ : ℝ → ℝ := fun x => Real.exp (rateIntegral q s x)
  set F : ℝ → ℝ := fun x => μ x * w x
  have hμ : ∀ x, HasDerivAt μ (μ x * q x) x := fun x =>
    (hq.integral_hasStrictDerivAt s x).hasDerivAt.exp
  have hFderiv : ∀ x ∈ Ioo s t, HasDerivAt F (-k * μ x) x := by
    intro x hx
    refine ((hμ x).mul (hd x hx)).congr_deriv ?_
    ring
  have hμcont : Continuous μ :=
    continuous_iff_continuousAt.2 fun x => (hμ x).continuousAt
  have hFcont : ContinuousOn F (Icc s t) := hμcont.continuousOn.mul hw
  have hint : IntervalIntegrable (fun x => -k * μ x) MeasureTheory.volume s t :=
    (hμcont.const_mul (-k)).intervalIntegrable s t
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst.le hFcont hFderiv hint
  have hμs : μ s = 1 := by simp [μ, rateIntegral, intervalIntegral.integral_same]
  calc
    Real.exp (rateIntegral q s t) * w t = F t := rfl
    _ = F s + (F t - F s) := by ring
    _ = μ s * w s + ∫ x in s..t, -k * μ x := by
      rw [hFTC]
    _ = w s + (-k) * ∫ x in s..t, μ x := by
      rw [hμs, one_mul, intervalIntegral.integral_const_mul]
    _ = w s - k * ∫ x in s..t, Real.exp (rateIntegral q s x) := by
      ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
