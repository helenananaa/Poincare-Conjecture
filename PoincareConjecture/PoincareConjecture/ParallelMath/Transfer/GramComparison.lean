import PoincareConjecture.ParallelMath.Transfer.GramShear
import PoincareConjecture.ParallelMath.Transfer.GramDegenerate
import PoincareConjecture.ParallelMath.Transfer.GramFrame
import PoincareConjecture.ParallelMath.Variational.PlaneAreaDistortion
import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A uniform quadratic metric bound controls area for arbitrary, possibly dependent pairs. -/
theorem gramArea_metric_comparison {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G0 G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h0s : ∀ v w, G0 v w = G0 w v) (hs : ∀ v w, G v w = G w v)
    (h0p : ∀ v : V, v ≠ 0 → 0 < G0 v v)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hbound : ∀ v : V, (1-ε)*G0 v v ≤ G v v ∧ G v v ≤ (1+ε)*G0 v v)
    (v w : V) :
    (1-ε)*gramArea G0 v w ≤ gramArea G v w ∧
      gramArea G v w ≤ (1+ε)*gramArea G0 v w :=
/- SWARM_PROOF_BEGIN -/
by
  rcases pair_degenerate_or_orthonormal G0 h0s h0p v w with hdeg | hframe
  · -- Rank below two: both Gram areas vanish.
    have hG0 : gramArea G0 v w = 0 := gramArea_degenerate G0 v w hdeg
    have hG : gramArea G v w = 0 := gramArea_degenerate G v w hdeg
    rw [hG0, hG]
    simp
  · -- Orthonormal pair for G0, with triangular coordinates of (v, w).
    rcases hframe with ⟨e, f, a, b, c, _ha, _hc, hGee, hGff, hGef, hv, hw⟩
    -- Expand a general bilinear form on the plane spanned by e, f.
    have hexpand (H : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ x y, H x y = H y x)
        (s t : ℝ) :
        H (s • e + t • f) (s • e + t • f)
          = H e e * s ^ 2 + 2 * H e f * s * t + H f f * t ^ 2 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [hsym f e]
      ring
    have hG0norm (s t : ℝ) :
        G0 (s • e + t • f) (s • e + t • f) = s ^ 2 + t ^ 2 := by
      rw [hexpand G0 h0s s t, hGee, hGff, hGef]
      ring
    -- Quadratic-form bound on the orthonormal plane.
    have hplane : ∀ s t : ℝ,
        (1 - ε) * (s ^ 2 + t ^ 2)
            ≤ G e e * s ^ 2 + 2 * G e f * s * t + G f f * t ^ 2 ∧
          G e e * s ^ 2 + 2 * G e f * s * t + G f f * t ^ 2
            ≤ (1 + ε) * (s ^ 2 + t ^ 2) := by
      intro s t
      have hb := hbound (s • e + t • f)
      rwa [hG0norm s t, hexpand G hs s t] at hb
    have hjac :=
      PoincareConjecture.ParallelMath.Variational.plane_area_distortion
        (G e e) (G e f) (G f f) ε hε0 hε1 hplane
    have hjac' : 1 - ε ≤ gramArea G e f ∧ gramArea G e f ≤ 1 + ε := by
      simpa [gramArea] using hjac
    have hG0ef : gramArea G0 e f = 1 := by
      unfold gramArea
      rw [hGee, hGff, hGef]
      norm_num
    -- Scale both sides by the nonnegative factor |a * c|.
    have hac : 0 ≤ |a * c| := abs_nonneg _
    rw [hv, hw, gramArea_triangular_change G0 h0s e f a b c,
      gramArea_triangular_change G hs e f a b c, hG0ef, mul_one]
    constructor
    · rw [mul_comm (1 - ε)]
      exact mul_le_mul_of_nonneg_left hjac'.1 hac
    · rw [mul_comm (1 + ε)]
      exact mul_le_mul_of_nonneg_left hjac'.2 hac
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
