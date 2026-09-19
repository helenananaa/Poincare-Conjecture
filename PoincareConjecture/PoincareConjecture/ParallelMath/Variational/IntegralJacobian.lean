import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Pointwise nonnegative Jacobian distortion passes to the actual integral. -/
theorem integral_twoSided_distortion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hbound : ∀ᵐ x ∂μ, a * f x ≤ g x ∧ g x ≤ b * f x) :
    0 ≤ ∫ x, g x ∂μ ∧ a * (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ ∧
      (∫ x, g x ∂μ) ≤ b * (∫ x, f x ∂μ) :=
/- SWARM_PROOF_BEGIN -/
by
  have hf_a : Integrable (fun x => a * f x) μ := hf.const_mul a
  have hf_b : Integrable (fun x => b * f x) μ := hf.const_mul b
  have h_ag : (fun x => a * f x) ≤ᵐ[μ] g := hbound.mono fun _ hx => hx.1
  have h_gb : g ≤ᵐ[μ] fun x => b * f x := hbound.mono fun _ hx => hx.2
  have h_left : a * ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
    rw [← integral_const_mul a f]
    exact integral_mono_ae hf_a hg h_ag
  have h_right : ∫ x, g x ∂μ ≤ b * ∫ x, f x ∂μ := by
    rw [← integral_const_mul b f]
    exact integral_mono_ae hg hf_b h_gb
  have h0f : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae hn
  have _h_ab : a * ∫ x, f x ∂μ ≤ b * ∫ x, f x ∂μ :=
    mul_le_mul_of_nonneg_right hab h0f
  exact ⟨(mul_nonneg ha h0f).trans h_left, h_left, h_right⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Variational
