import PoincareConjecture.ParallelMath.Core
import PoincareConjecture.ParallelMath.Extinction.ExplicitDerivative

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped Topology Interval

/-- Variable-coefficient inequality form of the width ODE: if `w' ≤ -k - q w`
on the open interval, then `w t ≤ comparisonSolution q k (w s) s t`.
Distinct from `integratingFactor_identity` (equality) and from
`inhomogeneous_integrating_factor` (constant `D`). -/
theorem comparisonSolution_dominates_deriv_le
    (q w : ℝ → ℝ) (hq : Continuous q) (k s t : ℝ) (hst : s ≤ t)
    (hw : ContinuousOn w (Icc s t))
    (hd : ∀ x ∈ Ioo s t, ∃ w' : ℝ, HasDerivAt w w' x ∧ w' ≤ -k - q x * w x) :
    w t ≤ comparisonSolution q k (w s) s t :=
/- SWARM_PROOF_BEGIN -/
by
  rcases eq_or_lt_of_le hst with rfl | _
  · simp [comparisonSolution, rateIntegral, intervalIntegral.integral_same]
  set μ : ℝ → ℝ := fun x => Real.exp (rateIntegral q s x)
  set F : ℝ → ℝ := fun x => μ x * w x
  have hμ : ∀ x, HasDerivAt μ (μ x * q x) x := fun x =>
    (hq.integral_hasStrictDerivAt s x).hasDerivAt.exp
  have hwderiv : ∀ x ∈ Ioo s t, HasDerivAt w (deriv w x) x := by
    intro x hx
    obtain ⟨w', hw'd, _⟩ := hd x hx
    exact hw'd.differentiableAt.hasDerivAt
  have hw'le : ∀ x ∈ Ioo s t, deriv w x ≤ -k - q x * w x := by
    intro x hx
    obtain ⟨w', hw'd, hle⟩ := hd x hx
    rwa [hw'd.deriv]
  set F' : ℝ → ℝ := fun x => μ x * (deriv w x + q x * w x)
  have hFderiv : ∀ x ∈ Ioo s t, HasDerivAt F (F' x) x := by
    intro x hx
    refine ((hμ x).mul (hwderiv x hx)).congr_deriv ?_
    simp only [F']
    ring
  have hF'le : ∀ x ∈ Ioo s t, F' x ≤ -k * μ x := by
    intro x hx
    have hinner : deriv w x + q x * w x ≤ -k := le_sub_iff_add_le.mp (hw'le x hx)
    calc
      F' x = μ x * (deriv w x + q x * w x) := rfl
      _ ≤ μ x * (-k) :=
        mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
      _ = -k * μ x := by ring
  have hμcont : Continuous μ :=
    continuous_iff_continuousAt.2 fun x => (hμ x).continuousAt
  have hFcont : ContinuousOn F (Icc s t) := hμcont.continuousOn.mul hw
  have hφint : MeasureTheory.IntegrableOn (fun x => -k * μ x) (Icc s t) :=
    (hμcont.const_mul (-k)).continuousOn.integrableOn_Icc
  have hFTC :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst hFcont
      (fun x hx => (hFderiv x hx).hasDerivWithinAt) hφint hF'le
  have hμs : μ s = 1 := by simp [μ, rateIntegral, intervalIntegral.integral_same]
  have hineq : μ t * w t ≤ w s - k * ∫ x in s..t, μ x := by
    have h := hFTC
    simp [F, hμs, intervalIntegral.integral_const_mul] at h
    linarith
  have hμinv : Real.exp (-rateIntegral q s t) * μ t = 1 := by
    simp [μ, ← Real.exp_add]
  calc
    w t = Real.exp (-rateIntegral q s t) * (μ t * w t) := by
      rw [← mul_assoc, hμinv, one_mul]
    _ ≤ Real.exp (-rateIntegral q s t) *
          (w s - k * ∫ x in s..t, Real.exp (rateIntegral q s x)) :=
      mul_le_mul_of_nonneg_left hineq (Real.exp_pos _).le
    _ = comparisonSolution q k (w s) s t := rfl
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
