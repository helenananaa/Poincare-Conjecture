import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Pointwise domination by an integrable nonnegative density supplies integrability of a measurable new area density. -/
theorem integrable_sqrt_gram_of_domination {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (J J0 : Ω → ℝ) (hJ : AEStronglyMeasurable J μ)
    (h0 : Integrable J0 μ) (C : ℝ) (hC : 0 ≤ C)
    (h0n : ∀ᵐ x ∂μ, 0 ≤ J0 x)
    (hb : ∀ᵐ x ∂μ, 0 ≤ J x ∧ J x ≤ C*J0 x) : Integrable J μ :=
/- SWARM_PROOF_BEGIN -/
by
  have hdom : ∀ᵐ x ∂μ, ‖J x‖ ≤ ‖C * J0 x‖ := by
    filter_upwards [h0n, hb] with x hx0 hJx
    have hC0 : 0 ≤ C * J0 x := mul_nonneg hC hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hJx.1, abs_of_nonneg hC0]
    exact hJx.2
  exact (h0.const_mul C).mono hJ hdom
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
