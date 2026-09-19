import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Differential rank below two has zero Gram area in every bilinear form. -/
theorem gramArea_degenerate {V : Type*} [AddCommGroup V] [Module ℝ V] (G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V)
    (h : v = 0 ∨ ∃ t : ℝ, w = t • v) : gramArea G v w = 0 :=
/- SWARM_PROOF_BEGIN -/
by
  unfold gramArea
  rcases h with hv | ⟨t, hw⟩
  · -- v = 0: left-linearity sends G v v and G v w to 0
    subst hv
    simp
  · -- w = t • v: expand both slots by LinearMap linearity
    subst hw
    have hright : (G v) (t • v) = t * (G v) v := by
      simp [map_smul, smul_eq_mul]
    have hleft : G (t • v) = t • G v := map_smul G t v
    have hww : (G (t • v)) (t • v) = t * (t * (G v) v) := by
      rw [hleft, LinearMap.smul_apply, hright, smul_eq_mul]
    rw [hright, hww]
    have hdet : (G v) v * (t * (t * (G v) v)) - (t * (G v) v) ^ 2 = 0 := by
      ring
    rw [hdet, Real.sqrt_zero]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
