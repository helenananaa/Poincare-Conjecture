import PoincareConjecture.ParallelMath.Extinction.ExplicitDerivative
import PoincareConjecture.ParallelMath.Extinction.InitialSensitivity
import PoincareConjecture.ParallelMath.Extinction.IntegratingIdentity
import PoincareConjecture.ParallelMath.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped BigOperators Topology

/-- Existence, uniqueness on forward times, and monotone dependence on initial width. -/
theorem scalarComparison_solution_interface (q : ℝ → ℝ) (hq : Continuous q)
    (k a s : ℝ) :
    comparisonSolution q k a s s = a ∧
    (∀ t : ℝ, HasDerivAt (comparisonSolution q k a s)
      (-k-q t*comparisonSolution q k a s t) t) ∧
    (∀ w : ℝ → ℝ, ContinuousOn w (Ici s) → w s = a →
      (∀ t ∈ Ioi s, HasDerivAt w (-k-q t*w t) t) →
      EqOn w (comparisonSolution q k a s) (Ici s)) ∧
    (∀ a' : ℝ, a ≤ a' → ∀ t : ℝ,
      comparisonSolution q k a s t ≤ comparisonSolution q k a' s t) :=
/- SWARM_PROOF_BEGIN -/
by
  refine ⟨(comparisonSolution_initial_and_sensitivity q k a s).1,
    comparisonSolution_hasDerivAt q hq k a s, ?uniq, ?mono⟩
  · intro w hw_cont hw_init hw_deriv t ht
    have hst : s ≤ t := mem_Ici.mp ht
    have hid := integratingFactor_identity q w hq k s t hst
      (hw_cont.mono Icc_subset_Ici_self)
      (fun x hx => hw_deriv x (Ioo_subset_Ioi_self hx))
    have hμ_ne : Real.exp (rateIntegral q s t) ≠ 0 := (Real.exp_pos _).ne'
    apply mul_left_cancel₀ hμ_ne
    rw [hw_init] at hid
    convert hid using 1
    simp only [comparisonSolution, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, one_mul]
  · intro a' ha t
    have hdiff := (comparisonSolution_initial_and_sensitivity q k a s).2 a' t
    have : 0 ≤ comparisonSolution q k a' s t - comparisonSolution q k a s t := by
      rw [hdiff]
      exact mul_nonneg (sub_nonneg.mpr ha) (Real.exp_pos _).le
    exact sub_nonneg.mp this
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath
