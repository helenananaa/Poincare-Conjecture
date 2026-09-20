import PoincareConjecture.ParallelMath.Core

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped Topology

/-- Coupled exponential comparison for nonnegative length and total-curvature
scalars. If `L' ≤ C₂ L` and `Θ' ≤ (C₁+C₂)Θ + C₁ L` at interior points, then

  `L t ≤ L 0 · exp(C₂ t)`
  `Θ t + L t ≤ (Θ 0 + L 0) · exp((C₁+C₂) t)`

on `[0,T]`. This is the ODE core of `lem:coupled-length-curvature-comparison`.
It does not mention curves, ramps, or Ricci flow. -/
theorem coupled_length_curvature_comparison
    (L Θ : ℝ → ℝ) (C1 C2 T : ℝ) (hT : 0 ≤ T)
    (hLcont : ContinuousOn L (Icc 0 T))
    (hΘcont : ContinuousOn Θ (Icc 0 T))
    (hLnn : ∀ t ∈ Icc 0 T, 0 ≤ L t)
    (hΘnn : ∀ t ∈ Icc 0 T, 0 ≤ Θ t)
    (hLbound : ∀ t ∈ Ioo 0 T, ∃ L' : ℝ, HasDerivAt L L' t ∧ L' ≤ C2 * L t)
    (hΘbound : ∀ t ∈ Ioo 0 T, ∃ Θ' : ℝ, HasDerivAt Θ Θ' t ∧
      Θ' ≤ (C1 + C2) * Θ t + C1 * L t) :
    (∀ t ∈ Icc 0 T, L t ≤ L 0 * Real.exp (C2 * t)) ∧
    (∀ t ∈ Icc 0 T, Θ t + L t ≤ (Θ 0 + L 0) * Real.exp ((C1 + C2) * t)) :=
/- SWARM_PROOF_BEGIN -/
by
  -- Integrating factor μ_C(t) = exp(-C t): never divide by the scalar (which may vanish).
  have bound_of_deriv_le :
      ∀ (y : ℝ → ℝ) (C : ℝ),
        ContinuousOn y (Icc 0 T) →
        (∀ t ∈ Ioo 0 T, ∃ y' : ℝ, HasDerivAt y y' t ∧ y' ≤ C * y t) →
        ∀ t ∈ Icc 0 T, y t ≤ y 0 * Real.exp (C * t) := by
    intro y C hycont hybound t ht
    set μ : ℝ → ℝ := fun x => Real.exp (-C * x)
    set F : ℝ → ℝ := fun x => μ x * y x
    have hμderiv : ∀ x, HasDerivAt μ (-C * μ x) x := fun x =>
      ((hasDerivAt_id' x).const_mul (-C)).exp.congr_deriv (by ring)
    have hμcont : Continuous μ :=
      continuous_iff_continuousAt.2 fun x => (hμderiv x).continuousAt
    have hFcont : ContinuousOn F (Icc 0 T) := hμcont.continuousOn.mul hycont
    have hanti : AntitoneOn F (Icc 0 T) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFcont
      · rw [interior_Icc]
        intro x hx
        obtain ⟨y', hyd, -⟩ := hybound x hx
        exact ((hμderiv x).mul hyd).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        obtain ⟨y', hyd, hyle⟩ := hybound x hx
        have hFd : HasDerivAt F (μ x * (y' - C * y x)) x :=
          ((hμderiv x).mul hyd).congr_deriv (by ring)
        rw [hFd.deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hyle)
    have hF0 : F 0 = y 0 := by simp [F, μ]
    have hle : μ t * y t ≤ y 0 := by simpa [F, hF0] using hanti ⟨le_rfl, hT⟩ ht ht.1
    have hμinv : μ t * Real.exp (C * t) = 1 := by simp [μ, ← Real.exp_add]
    calc
      y t = 1 * y t := (one_mul _).symm
      _ = (μ t * Real.exp (C * t)) * y t := by rw [hμinv]
      _ = (μ t * y t) * Real.exp (C * t) := by ring
      _ ≤ y 0 * Real.exp (C * t) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  have hScont : ContinuousOn (fun s => Θ s + L s) (Icc 0 T) := hΘcont.add hLcont
  have hSbound : ∀ s ∈ Ioo 0 T, ∃ S' : ℝ,
      HasDerivAt (fun u => Θ u + L u) S' s ∧ S' ≤ (C1 + C2) * (Θ s + L s) := by
    intro s hs
    obtain ⟨L', hLd, hLle⟩ := hLbound s hs
    obtain ⟨Θ', hΘd, hΘle⟩ := hΘbound s hs
    refine ⟨Θ' + L', hΘd.add hLd, ?_⟩
    calc
      Θ' + L' ≤ (C1 + C2) * Θ s + C1 * L s + C2 * L s := add_le_add hΘle hLle
      _ = (C1 + C2) * (Θ s + L s) := by ring
  have _ := hLnn
  have _ := hΘnn
  exact ⟨bound_of_deriv_le L C2 hLcont hLbound,
    bound_of_deriv_le (fun s => Θ s + L s) (C1 + C2) hScont hSbound⟩
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
