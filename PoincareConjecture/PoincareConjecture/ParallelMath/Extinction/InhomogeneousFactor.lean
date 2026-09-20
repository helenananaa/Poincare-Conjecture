import PoincareConjecture.ParallelMath.Core

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped Topology Interval

/-- Inhomogeneous integrating-factor comparison: if `y' ≤ D y + f` on the
open interval, then

  `y t₂ ≤ exp(D(t₂-t')) (y t' + ∫_{t'}^{t₂} exp(-D(s-t')) f s ds)`.

Distinct from the homogeneous identity `integratingFactor_identity`. No
geometric cutoff or curve-shrinking content. -/
theorem inhomogeneous_integrating_factor
    (y f : ℝ → ℝ) (D t' t2 : ℝ) (ht : t' ≤ t2)
    (hy : ContinuousOn y (Icc t' t2))
    (hf : ContinuousOn f (Icc t' t2))
    (hd : ∀ x ∈ Ioo t' t2, ∃ y' : ℝ, HasDerivAt y y' x ∧ y' ≤ D * y x + f x) :
    y t2 ≤
      Real.exp (D * (t2 - t')) *
        (y t' + ∫ s in t'..t2, Real.exp (-D * (s - t')) * f s) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases eq_or_lt_of_le ht with rfl | _
  · simp [intervalIntegral.integral_same]
  set μ : ℝ → ℝ := fun x => Real.exp (-D * (x - t'))
  set F : ℝ → ℝ := fun x => μ x * y x
  have hμ : ∀ x, HasDerivAt μ (-D * μ x) x := fun x => by
    have hlin : HasDerivAt (fun z : ℝ => -D * (z - t')) (-D) x :=
      (((hasDerivAt_id' x).sub_const t').const_mul (-D)).congr_deriv (by ring)
    exact hlin.exp.congr_deriv (by simp [μ]; ring)
  have hyderiv : ∀ x ∈ Ioo t' t2, HasDerivAt y (deriv y x) x := by
    intro x hx
    obtain ⟨y', hy'd, _⟩ := hd x hx
    exact hy'd.differentiableAt.hasDerivAt
  have hy'le : ∀ x ∈ Ioo t' t2, deriv y x ≤ D * y x + f x := by
    intro x hx
    obtain ⟨y', hy'd, hle⟩ := hd x hx
    rwa [hy'd.deriv]
  set F' : ℝ → ℝ := fun x => μ x * (deriv y x - D * y x)
  have hFderiv : ∀ x ∈ Ioo t' t2, HasDerivAt F (F' x) x := by
    intro x hx
    refine ((hμ x).mul (hyderiv x hx)).congr_deriv ?_
    simp only [F']
    ring
  have hF'le : ∀ x ∈ Ioo t' t2, F' x ≤ μ x * f x := by
    intro x hx
    exact mul_le_mul_of_nonneg_left ((sub_le_iff_le_add').mpr (hy'le x hx))
      (Real.exp_pos _).le
  have hμcont : Continuous μ :=
    continuous_iff_continuousAt.2 fun x => (hμ x).continuousAt
  have hFcont : ContinuousOn F (Icc t' t2) := hμcont.continuousOn.mul hy
  have hφint : MeasureTheory.IntegrableOn (fun s => μ s * f s) (Icc t' t2) :=
    (hμcont.continuousOn.mul hf).integrableOn_Icc
  have hFTC :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht hFcont
      (fun x hx => (hFderiv x hx).hasDerivWithinAt) hφint hF'le
  have hμt' : μ t' = 1 := by simp [μ]
  have hineq : μ t2 * y t2 ≤ y t' + ∫ s in t'..t2, μ s * f s := by
    have h := hFTC
    simp [F, hμt'] at h
    rwa [add_comm] at h
  have hμinv : Real.exp (D * (t2 - t')) * μ t2 = 1 := by
    simp [μ, ← Real.exp_add]
  calc
    y t2 = Real.exp (D * (t2 - t')) * (μ t2 * y t2) := by
      rw [← mul_assoc, hμinv, one_mul]
    _ ≤ Real.exp (D * (t2 - t')) *
          (y t' + ∫ s in t'..t2, Real.exp (-D * (s - t')) * f s) :=
      mul_le_mul_of_nonneg_left hineq (Real.exp_pos _).le
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
