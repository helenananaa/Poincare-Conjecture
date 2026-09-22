import PoincareConjecture.ProofContract.Proofs.ExteriorCover
import PoincareConjecture.ProofContract.Proofs.OpenCoverConnectedPiece
import PoincareConjecture.ProofContract.Proofs.OpenAnnulus
import PoincareConjecture.ProofContract.Proofs.PunctureCoverConnected
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- The genuine exterior cover satisfies all van Kampen surjectivity hypotheses. -/
theorem exterior_cover_connectivity {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    IsPathConnected (exteriorU b) ∧ IsSimplyConnected (punctureV b) ∧
    IsPathConnected (exteriorU b ∩ punctureV b) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases exterior_cover_sets b with ⟨hopenU, hcover, -, hinter⟩
  rcases puncture_cover_sets b with ⟨-, hopenV, -, -, -⟩
  rcases puncture_cover_connectivity b with ⟨-, hVsimply, -⟩
  have hsourceA : {x : Euclidean3 | (1 : ℝ) < ‖x‖ ∧
      ‖x‖ < (3 / 2 : ℝ)} ⊆ b.parametrization.source := by
    intro x hx
    apply b.contains_two
    simpa [Metric.mem_closedBall] using (show ‖x‖ ≤ (2 : ℝ) by linarith [hx.2])
  have hannulus : IsPathConnected
      (b.parametrization ''
        {x : Euclidean3 | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)}) :=
    (open_annulus_path_connected (1 : ℝ) (3 / 2 : ℝ) (by norm_num) (by norm_num)).2.image'
      (b.parametrization.continuousOn.mono hsourceA)
  have hinter_pre : IsPreconnected (exteriorU b ∩ punctureV b) := by
    rw [hinter]
    exact hannulus.isConnected.isPreconnected
  have hinter_nonempty : (exteriorU b ∩ punctureV b).Nonempty := by
    rw [hinter]
    exact hannulus.nonempty
  have hpre : IsPreconnected (exteriorU b) :=
    open_piece_preconnected (exteriorU b) (punctureV b) hopenU hopenV hcover hinter_pre
  have hconn : IsConnected (exteriorU b) :=
    ⟨hinter_nonempty.mono inter_subset_left, hpre⟩
  have hU_path : IsPathConnected (exteriorU b) :=
    hopenU.isConnected_iff_isPathConnected.mp hconn
  exact ⟨hU_path, hVsimply, by rw [hinter]; exact hannulus⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
