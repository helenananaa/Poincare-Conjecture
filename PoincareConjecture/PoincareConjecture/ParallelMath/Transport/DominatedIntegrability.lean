import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Variational.IntegralJacobian

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Finite reference area and measurability suffice; target integrability is derived, not assumed. -/
theorem integrable_twoSided_from_reference {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (f g : Omega → ℝ) (hf : Integrable f mu)
    (hg : AEStronglyMeasurable g mu) (l u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u)
    (hn : ∀ᵐ x ∂mu, 0 ≤ f x)
    (h : ∀ᵐ x ∂mu, l*f x ≤ g x ∧ g x ≤ u*f x) :
    Integrable g mu ∧ l*(∫ x, f x ∂mu) ≤ ∫ x, g x ∂mu ∧
      (∫ x, g x ∂mu) ≤ u*(∫ x, f x ∂mu) :=
/- SWARM_PROOF_BEGIN -/
by
  have hg0 : ∀ᵐ x ∂mu, 0 ≤ g x := by
    filter_upwards [hn, h] with x hfx hgx
    exact (mul_nonneg hl hfx).trans hgx.1
  have habs : ∀ᵐ x ∂mu, |g x| ≤ u * f x := by
    filter_upwards [hg0, h] with x hx0 hgx
    rw [abs_of_nonneg hx0]
    exact hgx.2
  have hg_int : Integrable g mu := by
    refine (hf.const_mul u).mono' hg ?_
    filter_upwards [habs] with x hx
    simpa [Real.norm_eq_abs] using hx
  have hdist :=
    PoincareConjecture.ParallelMath.Variational.integral_twoSided_distortion
      mu f g hf hg_int l u hl hlu hn h
  exact ⟨hg_int, hdist.2⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
