import PoincareConjecture.ProofContract.Proofs.HalfComplementBall
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
/-- The existing relative closed-ball obligation, with no additional hypotheses. -/
theorem sphere_complement_ball_proved : SphereComplementBallStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro M hM a
  rcases hM with ⟨e⟩
  obtain ⟨r, hrboundary⟩ := half_coordinate_complement_ball M e a
  obtain ⟨b, hbparam, q, hq⟩ :=
    shrunk_coordinate_complement_homeomorph a (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hremoved : b.removed =
      a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(1 / 2 : ℝ) • z, ?_, (hbparam z).symm⟩
      rw [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (by norm_num)]
      have hz' : ‖z‖ < (1 : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      nlinarith
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(2 : ℝ) • z, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (by norm_num)]
        have hz' : ‖z‖ < (1 / 2 : ℝ) := by
          simpa [Metric.mem_ball, dist_zero_right] using hz
        nlinarith
      · rw [hbparam]
        congr 1
        module
  have hiff : ∀ x : M,
      x ∉ b.removed ↔ x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2) := by
    intro x
    rw [hremoved]
  let C : Type u :=
    {x : M // x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)}
  let t : b.Complement ≃ₜ C :=
    (Homeomorph.refl M).subtype (hiff ·)
  let F : a.Complement ≃ₜ DoubleBall.Ball := q.trans (t.trans r)
  refine ⟨F, Homeomorph.refl Sphere2, ?_⟩
  intro s
  apply Subtype.ext
  change (r (t (q (a.boundary s))) : Euclidean3) = (s : Euclidean3)
  rw [hq s]
  apply hrboundary
  change (b.boundary s : M) = a.parametrization ((1 / 2 : ℝ) • (s : Euclidean3))
  exact hbparam (s : Euclidean3)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
