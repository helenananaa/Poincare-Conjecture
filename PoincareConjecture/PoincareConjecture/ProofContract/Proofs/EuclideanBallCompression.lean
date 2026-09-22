import PoincareConjecture.ProofContract.Proofs.BufferedRadiusProfile
import PoincareConjecture.ProofContract.Proofs.RadialHomeomorphLift
import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Compress the unit ball by a prescribed scale, fixing all points outside radius two. -/
theorem euclidean_buffered_ball_compression (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ H : Euclidean3 ≃ₜ Euclidean3,
      (∀ x : Euclidean3, ‖x‖ ≤ 1 → H x = r • x) ∧
      (∀ x : Euclidean3, 2 ≤ ‖x‖ → H x = x) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨p, hp, hp0, hp1, hp2⟩ := buffered_radius_profile r hr hr1
  obtain ⟨H, hH0, hHx⟩ := radial_homeomorph_lift p hp hp0
  refine ⟨H, ?_, ?_⟩
  · intro x hx
    by_cases hzero : x = 0
    · rw [hzero, hH0]
      simp
    · rw [hHx x hzero, hp1 ‖x‖ hx]
      field_simp [norm_ne_zero_iff.mpr hzero]
  · intro x hx
    have hzero : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      linarith
    rw [hHx x hzero, hp2 ‖x‖ hx]
    field_simp [norm_ne_zero_iff.mpr hzero]
    simp
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
