import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- The explicit integrating-factor candidate solves the scalar comparison ODE. -/
theorem comparisonSolution_hasDerivAt (q : ℝ → ℝ) (hq : Continuous q)
    (k a s t : ℝ) :
    HasDerivAt (comparisonSolution q k a s)
      (-k - q t * comparisonSolution q k a s t) t :=
/- SWARM_PROOF_BEGIN -/
by
  -- Integrating factor A(u) = ∫_s^u q, via FTC.
  have hA : ∀ u, HasDerivAt (fun v => rateIntegral q s v) (q u) u := fun u =>
    (hq.integral_hasStrictDerivAt s u).hasDerivAt
  have hA_cont : Continuous (fun u => rateIntegral q s u) :=
    continuous_iff_continuousAt.mpr fun u => (hA u).continuousAt
  have hExp_cont : Continuous (fun x => Real.exp (rateIntegral q s x)) :=
    Real.continuous_exp.comp hA_cont
  -- Variation-of-constants integral I(u) = ∫_s^u exp(A(x)) dx, via FTC.
  have hI : HasDerivAt (fun u => ∫ x in s..u, Real.exp (rateIntegral q s x))
      (Real.exp (rateIntegral q s t)) t :=
    (hExp_cont.integral_hasStrictDerivAt s t).hasDerivAt
  have hexp : HasDerivAt (fun u => Real.exp (-rateIntegral q s u))
      (Real.exp (-rateIntegral q s t) * (-q t)) t :=
    (hA t).neg.exp
  have hinner : HasDerivAt (fun u => a - k * ∫ x in s..u, Real.exp (rateIntegral q s x))
      (-(k * Real.exp (rateIntegral q s t))) t :=
    (hI.const_mul k).const_sub a
  have hcancel : Real.exp (-rateIntegral q s t) * Real.exp (rateIntegral q s t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hderiv :
      Real.exp (-rateIntegral q s t) * (-q t) *
          (a - k * ∫ x in s..t, Real.exp (rateIntegral q s x)) +
        Real.exp (-rateIntegral q s t) * (-(k * Real.exp (rateIntegral q s t))) =
      -k - q t * comparisonSolution q k a s t := by
    simp only [comparisonSolution, mul_neg, neg_mul, mul_assoc, sub_eq_add_neg]
    rw [mul_left_comm (Real.exp (-rateIntegral q s t)) k, hcancel, mul_one]
    ring
  -- Rephrase via the little-o characterization so ℝ-module instance diamonds drop out.
  -- `comparisonSolution` is definitionally the product of the two factors above.
  refine HasDerivAt.of_isLittleO ?_
  simpa only [comparisonSolution] using
    ((hexp.fun_mul hinner).congr_deriv hderiv).isLittleO
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
