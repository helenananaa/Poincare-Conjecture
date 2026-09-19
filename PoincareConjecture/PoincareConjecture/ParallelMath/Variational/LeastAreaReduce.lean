import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer
import PoincareConjecture.ParallelMath.Variational.IntegralJacobian
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- An actual integral estimate for every admissible surface yields a
least-area estimate without assuming Plateau/minimal-surface existence. -/
theorem least_integral_distortion {A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (μ : Measure Ω) (J J' : A → Ω → ℝ)
    (hJ : ∀ a, Integrable (J a) μ) (hJ' : ∀ a, Integrable (J' a) μ)
    (hpos : ∀ a, ∀ᵐ x ∂μ, 0 ≤ J a x) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (hdist : ∀ a, ∀ᵐ x ∂μ, l * J a x ≤ J' a x ∧ J' a x ≤ u * J a x) :
    l * leastCost (fun a => ∫ x, J a x ∂μ) ≤ leastCost (fun a => ∫ x, J' a x ∂μ) ∧
      leastCost (fun a => ∫ x, J' a x ∂μ) ≤ u * leastCost (fun a => ∫ x, J a x ∂μ) :=
/- SWARM_PROOF_BEGIN -/
by
  have hl0 : 0 ≤ l := hl.le
  have hu0 : 0 ≤ u := hl0.trans hlu
  have harea : ∀ a,
      0 ≤ ∫ x, J' a x ∂μ ∧
        l * ∫ x, J a x ∂μ ≤ ∫ x, J' a x ∂μ ∧
        ∫ x, J' a x ∂μ ≤ u * ∫ x, J a x ∂μ := fun a =>
    integral_twoSided_distortion μ (J a) (J' a) (hJ a) (hJ' a) l u
      hl0 hlu (hpos a) (hdist a)
  have hf : ∀ a, 0 ≤ ∫ x, J a x ∂μ := fun a => integral_nonneg_of_ae (hpos a)
  have hg : ∀ a, 0 ≤ ∫ x, J' a x ∂μ := fun a => (harea a).1
  constructor
  · have hrev : leastCost (fun a => ∫ x, J a x ∂μ) ≤
        l⁻¹ * leastCost (fun a => ∫ x, J' a x ∂μ) + 0 :=
      leastCost_transfer (fun a => ∫ x, J' a x ∂μ) (fun a => ∫ x, J a x ∂μ)
        hg hf id l⁻¹ 0 (inv_nonneg.mpr hl0) fun a => by
          simpa using (le_inv_mul_iff₀ hl).mpr (harea a).2.1
    exact (le_inv_mul_iff₀ hl).mp (by simpa using hrev)
  · simpa using
      leastCost_transfer (fun a => ∫ x, J a x ∂μ) (fun a => ∫ x, J' a x ∂μ)
        hf hg id u 0 hu0 fun a => by simpa using (harea a).2.2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
