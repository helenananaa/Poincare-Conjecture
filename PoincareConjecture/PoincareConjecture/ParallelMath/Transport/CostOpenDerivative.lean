import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Variational.CostGrowth

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Two-sided growth needs derivatives only inside the time interval, not at its endpoints. -/
theorem cost_growth_from_interior_derivatives (f f' : ℝ → ℝ) (a b K : ℝ)
    (hab : a ≤ b) (hK : 0 ≤ K) (hf : ContinuousOn f (Icc a b))
    (hn : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbnd : ∀ t ∈ Ioo a b, |f' t| ≤ K*f t) :
    Real.exp (-K*(b-a))*f a ≤ f b ∧ f b ≤ Real.exp (K*(b-a))*f a :=
/- SWARM_PROOF_BEGIN -/
by
  -- Integrating factor μ_c(t) = exp(c (t-a)): never divide by f (which may vanish).
  -- Derivatives of f are used only on Ioo a b = interior (Icc a b), so the
  -- a = b case is vacuous and the K = 0 case is the constant-factor bound.
  have hKf : ∀ t ∈ Icc a b, 0 ≤ K * f t := fun t ht => mul_nonneg hK (hn t ht)
  have hexp : ∀ (c x : ℝ),
      HasDerivAt (fun y => Real.exp (c * (y - a))) (c * Real.exp (c * (x - a))) x :=
    fun c x =>
      ((((hasDerivAt_id' x).sub_const a).const_mul c).exp).congr_deriv (by ring)
  have hF : ∀ (c x : ℝ), x ∈ Ioo a b →
      HasDerivAt (fun y => Real.exp (c * (y - a)) * f y)
        (Real.exp (c * (x - a)) * (f' x + c * f x)) x :=
    fun c x hx => ((hexp c x).mul (hd x hx)).congr_deriv (by ring)
  have hFcont : ∀ c : ℝ,
      ContinuousOn (fun y => Real.exp (c * (y - a)) * f y) (Icc a b) := fun c =>
    (continuous_iff_continuousAt.2 fun x => (hexp c x).continuousAt).continuousOn.mul hf
  have haI : a ∈ Icc a b := left_mem_Icc.2 hab
  have hbI : b ∈ Icc a b := right_mem_Icc.2 hab
  constructor
  · -- Lower bound: F(t) = exp(K(t-a)) f(t) has F' ≥ 0 on the interior, so F is monotone.
    set F : ℝ → ℝ := fun y => Real.exp (K * (y - a)) * f y
    have hmono : MonotoneOn F (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hFcont K)
      · rw [interior_Icc]
        exact fun x hx => (hF K x hx).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        rw [(hF K x hx).deriv]
        refine mul_nonneg (Real.exp_pos _).le ?_
        have hbound := abs_le.mp (hbnd x hx)
        linarith [hKf x (Ioo_subset_Icc_self hx)]
    have hFa : F a = f a := by simp [F, sub_self, Real.exp_zero]
    have hle : f a ≤ Real.exp (K * (b - a)) * f b := by
      simpa [F, hFa] using hmono haI hbI hab
    rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    exact hle
  · -- Upper bound: G(t) = exp(-K(t-a)) f(t) has G' ≤ 0 on the interior, so G is antitone.
    set G : ℝ → ℝ := fun y => Real.exp ((-K) * (y - a)) * f y
    have hanti : AntitoneOn G (Icc a b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (hFcont (-K))
      · rw [interior_Icc]
        exact fun x hx => (hF (-K) x hx).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        rw [(hF (-K) x hx).deriv]
        refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
        have hbound := abs_le.mp (hbnd x hx)
        linarith [hKf x (Ioo_subset_Icc_self hx)]
    have hGa : G a = f a := by simp [G, sub_self, Real.exp_zero]
    have hle : Real.exp ((-K) * (b - a)) * f b ≤ f a := by
      simpa [G, hGa] using hanti haI hbI hab
    rw [← inv_mul_le_iff₀ (Real.exp_pos (K * (b - a))), ← Real.exp_neg, ← neg_mul]
    exact hle
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
