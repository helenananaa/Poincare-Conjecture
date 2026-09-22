import PoincareConjecture.ProofContract.Proofs.PunctureCover
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
def exteriorU {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) : Set M := (closure b.removed)ᶜ
/-- The open exterior lies inside the actual punctured complement. -/
theorem exterior_cover_sets {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    IsOpen (exteriorU b) ∧ exteriorU b ∪ punctureV b = univ ∧
    (∀ x : exteriorU b, (x:M) ∉ b.removed) ∧
    exteriorU b ∩ punctureV b = b.parametrization ''
      {x : Euclidean3 | 1 < ‖x‖ ∧ ‖x‖ < (3/2 : ℝ)} :=
/- SWARM_PROOF_BEGIN -/
by
  have hclosure : closure b.removed =
      b.parametrization '' Metric.closedBall (0 : Euclidean3) 1 :=
    (coordinate_closure_frontier b).1
  have hopen_source : Metric.ball (0 : Euclidean3) (3 / 2 : ℝ) ⊆
      b.parametrization.source := by
    intro x hx
    apply b.contains_two
    have hxnorm : ‖x‖ < (3 / 2 : ℝ) := by
      simpa [Metric.mem_ball] using hx
    simpa [Metric.mem_closedBall] using (show ‖x‖ ≤ 2 by linarith)
  have hAB : Metric.closedBall (0 : Euclidean3) 1 ⊆
      Metric.ball 0 (3 / 2 : ℝ) := by
    intro x hx
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hx
    simpa [Metric.mem_ball] using (show ‖x‖ < (3 / 2 : ℝ) by linarith)
  have hinj : Set.InjOn b.parametrization
      (Metric.ball (0 : Euclidean3) (3 / 2 : ℝ)) := by
    intro x hx y hy hxy
    have h := congrArg b.parametrization.symm hxy
    simpa only [b.parametrization.left_inv (hopen_source hx),
      b.parametrization.left_inv (hopen_source hy)] using h
  have hinter : exteriorU b ∩ punctureV b = b.parametrization ''
      {x : Euclidean3 | 1 < ‖x‖ ∧ ‖x‖ < (3/2 : ℝ)} := by
    calc
      exteriorU b ∩ punctureV b =
          (b.parametrization '' Metric.ball 0 (3 / 2 : ℝ)) \
            (b.parametrization '' Metric.closedBall 0 1) := by
        ext x
        simp [exteriorU, punctureV, hclosure, and_comm]
      _ = b.parametrization ''
          (Metric.ball 0 (3 / 2 : ℝ) \ Metric.closedBall 0 1) :=
        (Set.image_sdiff_of_injOn hinj hAB).symm
      _ = b.parametrization ''
          {x : Euclidean3 | 1 < ‖x‖ ∧ ‖x‖ < (3/2 : ℝ)} := by
        congr 1
        ext x
        simp only [mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
          dist_zero_right, not_le]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩
  refine ⟨isClosed_closure.isOpen_compl, ?_, ?_, hinter⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x ∈ closure b.removed
    · right
      rw [hclosure] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hAB hy, rfl⟩
    · left
      exact hx
  · intro x hx
    exact x.property (subset_closure hx)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
