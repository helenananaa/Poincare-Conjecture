import PoincareConjecture.ParallelMath.Variational.PlaneAreaDistortion
import PoincareConjecture.ParallelMath.Variational.LeastAreaReduce
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Pointwise two-plane metric distortion passes through the Jacobian integral
to the least area of an arbitrary nonempty admissible family. -/
theorem quadratic_area_leastCost_comparison {A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (μ : Measure Ω) (J a b c : A → Ω → ℝ)
    (hJ : ∀ p, Integrable (J p) μ)
    (hJnew : ∀ p, Integrable (fun x => J p x * Real.sqrt (a p x*c p x-(b p x)^2)) μ)
    (hn : ∀ p, ∀ᵐ x ∂μ, 0 ≤ J p x) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hform : ∀ p, ∀ᵐ x ∂μ, ∀ s t : ℝ,
      (1-ε)*(s^2+t^2) ≤ a p x*s^2+2*b p x*s*t+c p x*t^2 ∧
      a p x*s^2+2*b p x*s*t+c p x*t^2 ≤ (1+ε)*(s^2+t^2)) :
    (1-ε) * leastCost (fun p => ∫ x, J p x ∂μ) ≤
      leastCost (fun p => ∫ x, J p x * Real.sqrt (a p x*c p x-(b p x)^2) ∂μ) ∧
    leastCost (fun p => ∫ x, J p x * Real.sqrt (a p x*c p x-(b p x)^2) ∂μ) ≤
      (1+ε) * leastCost (fun p => ∫ x, J p x ∂μ) :=
/- SWARM_PROOF_BEGIN -/
by
  have hl : 0 < 1 - ε := sub_pos.mpr hε1
  have hlu : 1 - ε ≤ 1 + ε := by linarith [hε0]
  have hdist : ∀ p, ∀ᵐ x ∂μ,
      (1 - ε) * J p x ≤ J p x * Real.sqrt (a p x * c p x - (b p x) ^ 2) ∧
      J p x * Real.sqrt (a p x * c p x - (b p x) ^ 2) ≤ (1 + ε) * J p x := by
    intro p
    filter_upwards [hn p, hform p] with x hJx hquad
    have hsqrt := plane_area_distortion (a p x) (b p x) (c p x) ε hε0 hε1 hquad
    constructor
    · calc
        (1 - ε) * J p x
            = J p x * (1 - ε) := mul_comm _ _
        _ ≤ J p x * Real.sqrt (a p x * c p x - (b p x) ^ 2) :=
          mul_le_mul_of_nonneg_left hsqrt.1 hJx
    · calc
        J p x * Real.sqrt (a p x * c p x - (b p x) ^ 2)
            ≤ J p x * (1 + ε) := mul_le_mul_of_nonneg_left hsqrt.2 hJx
        _ = (1 + ε) * J p x := mul_comm _ _
  exact least_integral_distortion μ J
    (fun p x => J p x * Real.sqrt (a p x * c p x - (b p x) ^ 2))
    hJ hJnew hn (1 - ε) (1 + ε) hl hlu hdist
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
