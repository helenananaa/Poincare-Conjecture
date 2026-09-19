import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A nonnegative continuously differentiable cost has two-sided exponential
control from an absolute derivative bound, including the zero-cost case. -/
theorem cost_twoSided_growth (f f' : ℝ → ℝ) (a b K : ℝ) (hab : a ≤ b) (hK : 0 ≤ K)
    (hf : ContinuousOn f (Icc a b)) (hn : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hbnd : ∀ t ∈ Icc a b, |f' t| ≤ K * f t) :
    Real.exp (-K*(b-a)) * f a ≤ f b ∧ f b ≤ Real.exp (K*(b-a)) * f a :=
/- SWARM_PROOF_BEGIN -/
by
  -- Integrating factor μ_c(t) = exp(c (t-a)): never divide by f (which may vanish).
  have hKf : ∀ t ∈ Icc a b, 0 ≤ K * f t := fun t ht => mul_nonneg hK (hn t ht)
  have hexp : ∀ (c x : ℝ),
      HasDerivAt (fun y => Real.exp (c * (y - a))) (c * Real.exp (c * (x - a))) x :=
    fun c x =>
      ((((hasDerivAt_id' x).sub_const a).const_mul c).exp).congr_deriv (by ring)
  have hF : ∀ (c x : ℝ), x ∈ Icc a b →
      HasDerivAt (fun y => Real.exp (c * (y - a)) * f y)
        (Real.exp (c * (x - a)) * (f' x + c * f x)) x :=
    fun c x hx => ((hexp c x).mul (hd x hx)).congr_deriv (by ring)
  have hFcont : ∀ c : ℝ,
      ContinuousOn (fun y => Real.exp (c * (y - a)) * f y) (Icc a b) := fun c =>
    (continuous_iff_continuousAt.2 fun x => (hexp c x).continuousAt).continuousOn.mul hf
  have haI : a ∈ Icc a b := left_mem_Icc.2 hab
  have hbI : b ∈ Icc a b := right_mem_Icc.2 hab
  constructor
  · -- Lower bound: F(t) = exp(K(t-a)) f(t) has F' ≥ 0, so F is monotone.
    set F : ℝ → ℝ := fun y => Real.exp (K * (y - a)) * f y
    have hmono : MonotoneOn F (Icc a b) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a b) (hFcont K)
        (fun x hx => (hF K x (interior_subset hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => by
          have hxI := interior_subset hx
          rw [(hF K x hxI).deriv]
          refine mul_nonneg (Real.exp_pos _).le ?_
          have hbound := abs_le.mp (hbnd x hxI)
          linarith [hKf x hxI])
    have hFa : F a = f a := by simp [F, sub_self, Real.exp_zero]
    have hle : f a ≤ Real.exp (K * (b - a)) * f b := by
      simpa [F, hFa] using hmono haI hbI hab
    rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    exact hle
  · -- Upper bound: G(t) = exp(-K(t-a)) f(t) has G' ≤ 0, so G is antitone.
    set G : ℝ → ℝ := fun y => Real.exp ((-K) * (y - a)) * f y
    have hanti : AntitoneOn G (Icc a b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc a b) (hFcont (-K))
        (fun x hx => (hF (-K) x (interior_subset hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => by
          have hxI := interior_subset hx
          rw [(hF (-K) x hxI).deriv]
          refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
          have hbound := abs_le.mp (hbnd x hxI)
          linarith [hKf x hxI])
    have hGa : G a = f a := by simp [G, sub_self, Real.exp_zero]
    have hle : Real.exp ((-K) * (b - a)) * f b ≤ f a := by
      simpa [G, hGa] using hanti haI hbI hab
    rw [← inv_mul_le_iff₀ (Real.exp_pos (K * (b - a))), ← Real.exp_neg, ← neg_mul]
    exact hle
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
