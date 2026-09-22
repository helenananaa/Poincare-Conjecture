import PoincareConjecture.ProofContract.Proofs.CoordinateOpenExterior
import PoincareConjecture.ProofContract.Proofs.ShrunkCoordinateComplement
import PoincareConjecture.ProofContract.Proofs.CompactChartSqueeze
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.RelativeCompactCollapse
import PoincareConjecture.ProofContract.Proofs.MarkedCollapseRecognition
import PoincareConjecture.ProofContract.Proofs.ConnectedSumSphereReduction
import Mathlib
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- The accepted open-exterior theorem applies at every smaller positive chart radius. -/
theorem scaled_coordinate_open_exterior (M : ClosedThreeManifold.{u})
    (e : M ≃ₜ Sphere3) (a : CoordinateBall M) (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    Nonempty ({x : M // x ∉ a.parametrization '' Metric.closedBall (0:Euclidean3) r} ≃ₜ Euclidean3) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨b, hb, _⟩ := shrunk_coordinate_complement_homeomorph a r hr hr1
  have himage : b.parametrization '' Metric.closedBall (0 : Euclidean3) 1 =
      a.parametrization '' Metric.closedBall (0 : Euclidean3) r := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨r • z, ?_, (hb z).symm⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
      have hz' : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      nlinarith
    · rintro ⟨y, hy, rfl⟩
      refine ⟨r⁻¹ • y, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
        simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hr]
        have hy' : ‖y‖ ≤ r := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hy
        calc
          r⁻¹ * ‖y‖ ≤ r⁻¹ * r :=
            mul_le_mul_of_nonneg_left hy' (inv_pos.mpr hr).le
          _ = 1 := inv_mul_cancel₀ hr.ne'
      · rw [hb]
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  obtain ⟨H⟩ := coordinate_open_exterior_euclidean M e b
  have hcomp : {x : M | x ∉ b.parametrization '' Metric.closedBall (0 : Euclidean3) 1} =
      {x : M | x ∉ a.parametrization '' Metric.closedBall (0 : Euclidean3) r} := by
    rw [himage]
  exact ⟨(Homeomorph.setCongr hcomp.symm).trans H⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
