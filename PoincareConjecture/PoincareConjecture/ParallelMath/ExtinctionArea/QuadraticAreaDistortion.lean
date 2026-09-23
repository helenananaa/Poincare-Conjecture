import PoincareConjecture.ParallelMath.Transfer.Core
import PoincareConjecture.ParallelMath.Transfer.GramDegenerate
import PoincareConjecture.ParallelMath.Transfer.GramFrame
import PoincareConjecture.ParallelMath.Transfer.GramShear
import PoincareConjecture.ParallelMath.Transport.PSDDetMonotone
import PoincareConjecture.ParallelMath.Variational.QuadraticDiscriminant

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath.ExtinctionArea

private theorem scalarArea_twoSided_of_quadraticBounds
    (a₀ b₀ c₀ a b c l u : ℝ)
    (hl : 0 ≤ l) (hu : 0 ≤ u)
    (h₀ : ∀ s t : ℝ, 0 ≤ a₀ * s ^ 2 + 2 * b₀ * s * t + c₀ * t ^ 2)
    (h : ∀ s t : ℝ,
      l * (a₀ * s ^ 2 + 2 * b₀ * s * t + c₀ * t ^ 2) ≤
        a * s ^ 2 + 2 * b * s * t + c * t ^ 2 ∧
      a * s ^ 2 + 2 * b * s * t + c * t ^ 2 ≤
        u * (a₀ * s ^ 2 + 2 * b₀ * s * t + c₀ * t ^ 2)) :
    l * Real.sqrt (a₀ * c₀ - b₀ ^ 2) ≤ Real.sqrt (a * c - b ^ 2) ∧
      Real.sqrt (a * c - b ^ 2) ≤ u * Real.sqrt (a₀ * c₀ - b₀ ^ 2) := by
  have h₀det :=
    PoincareConjecture.ParallelMath.Variational.quadratic_nonneg_det a₀ b₀ c₀ h₀
  have h₀disc : 0 ≤ a₀ * c₀ - b₀ ^ 2 := sub_nonneg.mpr h₀det.2.2
  have hscale (μ s t : ℝ) :
      (μ * a₀) * s ^ 2 + 2 * (μ * b₀) * s * t + (μ * c₀) * t ^ 2 =
        μ * (a₀ * s ^ 2 + 2 * b₀ * s * t + c₀ * t ^ 2) := by
    ring
  have hdetScale (μ : ℝ) :
      (μ * a₀) * (μ * c₀) - (μ * b₀) ^ 2 = μ ^ 2 * (a₀ * c₀ - b₀ ^ 2) := by
    ring
  have hLowerPsd : ∀ s t : ℝ,
      0 ≤ (l * a₀) * s ^ 2 + 2 * (l * b₀) * s * t + (l * c₀) * t ^ 2 := by
    intro s t
    rw [hscale]
    exact mul_nonneg hl (h₀ s t)
  have hLower : ∀ s t : ℝ,
      (l * a₀) * s ^ 2 + 2 * (l * b₀) * s * t + (l * c₀) * t ^ 2 ≤
        a * s ^ 2 + 2 * b * s * t + c * t ^ 2 := by
    intro s t
    rw [hscale]
    exact (h s t).1
  have hPsd : ∀ s t : ℝ, 0 ≤ a * s ^ 2 + 2 * b * s * t + c * t ^ 2 := by
    intro s t
    exact (hLowerPsd s t).trans (hLower s t)
  have hUpper : ∀ s t : ℝ,
      a * s ^ 2 + 2 * b * s * t + c * t ^ 2 ≤
        (u * a₀) * s ^ 2 + 2 * (u * b₀) * s * t + (u * c₀) * t ^ 2 := by
    intro s t
    rw [hscale]
    exact (h s t).2
  have hdetLower :=
    PoincareConjecture.ParallelMath.Transport.psd2_determinant_monotone
      (l * a₀) (l * b₀) (l * c₀) a b c hLowerPsd hLower
  have hdetUpper :=
    PoincareConjecture.ParallelMath.Transport.psd2_determinant_monotone
      a b c (u * a₀) (u * b₀) (u * c₀) hPsd hUpper
  rw [hdetScale l] at hdetLower
  rw [hdetScale u] at hdetUpper
  constructor
  · have hsqrt := Real.sqrt_le_sqrt hdetLower
    rwa [Real.sqrt_mul' _ h₀disc, Real.sqrt_sq hl] at hsqrt
  · have hsqrt := Real.sqrt_le_sqrt hdetUpper
    rwa [Real.sqrt_mul' _ h₀disc, Real.sqrt_sq hu] at hsqrt

/-- Independent lower and upper Loewner bounds on a positive definite
reference bilinear form control Gram area for every pair, including dependent
pairs.  The separate factors are needed for the asymmetric factors
`exp(-c |t-s|)` and `exp(c |t-s|)` in Ricci-flow metric comparison. -/
theorem gramArea_twoSided_quadratic_comparison {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (G₀ G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h₀sym : ∀ x y, G₀ x y = G₀ y x)
    (hsym : ∀ x y, G x y = G y x)
    (h₀pos : ∀ x : V, x ≠ 0 → 0 < G₀ x x)
    (l u : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hbound : ∀ x : V,
      l * G₀ x x ≤ G x x ∧ G x x ≤ u * G₀ x x)
    (v w : V) :
    l * PoincareConjecture.ParallelMath.Transfer.gramArea G₀ v w ≤
        PoincareConjecture.ParallelMath.Transfer.gramArea G v w ∧
      PoincareConjecture.ParallelMath.Transfer.gramArea G v w ≤
        u * PoincareConjecture.ParallelMath.Transfer.gramArea G₀ v w := by
  rcases PoincareConjecture.ParallelMath.Transfer.pair_degenerate_or_orthonormal
      G₀ h₀sym h₀pos v w with hdeg | hframe
  · have h₀area : PoincareConjecture.ParallelMath.Transfer.gramArea G₀ v w = 0 :=
      PoincareConjecture.ParallelMath.Transfer.gramArea_degenerate G₀ v w hdeg
    have harea : PoincareConjecture.ParallelMath.Transfer.gramArea G v w = 0 :=
      PoincareConjecture.ParallelMath.Transfer.gramArea_degenerate G v w hdeg
    rw [h₀area, harea]
    simp
  · rcases hframe with ⟨e, f, α, β, γ, hα, hγ, hₑₑ, hff, hₑf, hv, hw⟩
    have hexpand (H : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
        (hH : ∀ x y, H x y = H y x) (s t : ℝ) :
        H (s • e + t • f) (s • e + t • f) =
          H e e * s ^ 2 + 2 * H e f * s * t + H f f * t ^ 2 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [hH f e]
      ring
    have h₀norm (s t : ℝ) :
        G₀ (s • e + t • f) (s • e + t • f) = s ^ 2 + t ^ 2 := by
      rw [hexpand G₀ h₀sym s t, hₑₑ, hff, hₑf]
      ring
    have hplane : ∀ s t : ℝ,
        l * (s ^ 2 + t ^ 2) ≤
            G e e * s ^ 2 + 2 * G e f * s * t + G f f * t ^ 2 ∧
          G e e * s ^ 2 + 2 * G e f * s * t + G f f * t ^ 2 ≤
            u * (s ^ 2 + t ^ 2) := by
      intro s t
      have hb := hbound (s • e + t • f)
      rw [h₀norm s t, hexpand G hsym s t] at hb
      exact hb
    have h₀plane : ∀ s t : ℝ, 0 ≤ (1 : ℝ) * s ^ 2 + 2 * 0 * s * t + 1 * t ^ 2 := by
      intro s t
      simpa only [one_mul, mul_zero, zero_mul, add_zero] using add_nonneg (sq_nonneg s) (sq_nonneg t)
    have hplane' : ∀ s t : ℝ,
        l * (1 * s ^ 2 + 2 * 0 * s * t + 1 * t ^ 2) ≤
          G e e * s ^ 2 + 2 * G e f * s * t + G f f * t ^ 2 ∧
        G e e * s ^ 2 + 2 * G e f * s * t + G f f * t ^ 2 ≤
          u * (1 * s ^ 2 + 2 * 0 * s * t + 1 * t ^ 2) := by
      intro s t
      simpa only [one_mul, mul_zero, zero_mul, add_zero] using hplane s t
    have hareaFrame := scalarArea_twoSided_of_quadraticBounds
      1 0 1 (G e e) (G e f) (G f f) l u hl hu h₀plane hplane'
    have hareaFrame' :
        l ≤ PoincareConjecture.ParallelMath.Transfer.gramArea G e f ∧
          PoincareConjecture.ParallelMath.Transfer.gramArea G e f ≤ u := by
      simpa [PoincareConjecture.ParallelMath.Transfer.gramArea] using hareaFrame
    have h₀ef : PoincareConjecture.ParallelMath.Transfer.gramArea G₀ e f = 1 := by
      unfold PoincareConjecture.ParallelMath.Transfer.gramArea
      rw [hₑₑ, hff, hₑf]
      norm_num
    rw [hv, hw,
      PoincareConjecture.ParallelMath.Transfer.gramArea_triangular_change
        G₀ h₀sym e f α β γ,
      PoincareConjecture.ParallelMath.Transfer.gramArea_triangular_change
        G hsym e f α β γ,
      h₀ef]
    simp only [mul_one]
    constructor
    · rw [mul_comm l]
      exact mul_le_mul_of_nonneg_left hareaFrame'.1 (abs_nonneg _)
    · rw [mul_comm u]
      exact mul_le_mul_of_nonneg_left hareaFrame'.2 (abs_nonneg _)

end PoincareConjecture.ParallelMath.ExtinctionArea
