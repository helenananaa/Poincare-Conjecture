import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Gram area scales by the absolute determinant of a triangular basis change, for any symmetric form. -/
theorem gramArea_triangular_change {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, G x y = G y x)
    (v w : V) (a b c : ℝ) :
    gramArea G (a • v) (b • v + c • w) = |a*c| * gramArea G v w :=
/- SWARM_PROOF_BEGIN -/
by
  unfold gramArea
  -- The sheared Gram determinant is (a*c)^2 times the original determinant.
  have hdet :
      G (a • v) (a • v) * G (b • v + c • w) (b • v + c • w)
        - G (a • v) (b • v + c • w) ^ 2
      = (a * c) ^ 2 * (G v v * G w w - G v w ^ 2) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hs w v]
    ring
  rw [hdet]
  -- Square factor is nonnegative, so `sqrt_mul` applies even if the original
  -- Gram determinant is negative (indefinite form).
  rw [Real.sqrt_mul (sq_nonneg (a * c)), Real.sqrt_sq_eq_abs]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
