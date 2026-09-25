import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.C3IteratedNormIdentification
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance stdGroup0 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance stdSpace0 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance stdGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdGroup2 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace2 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
theorem c3_iterated_norms
    (u : E3 → E6) (x : E3) :

    ‖iteratedFDeriv ℝ 0 u x‖=‖u x‖ ∧
    ‖iteratedFDeriv ℝ 1 u x‖=‖fderiv ℝ u x‖ ∧
    ‖iteratedFDeriv ℝ 2 u x‖=‖fderiv ℝ (fderiv ℝ u) x‖ ∧
    ‖iteratedFDeriv ℝ 3 u x‖=‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · exact norm_iteratedFDeriv_zero
  constructor
  · exact norm_iteratedFDeriv_one u
  constructor
  · simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := u) (x := x)).symm
  · have h₁ := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 2) (f := u) (x := x)
    have h₂ := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1)
      (f := fderiv ℝ u) (x := x)
    rw [norm_iteratedFDeriv_one] at h₂
    exact (h₂.trans h₁).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.C3IteratedNormIdentification
