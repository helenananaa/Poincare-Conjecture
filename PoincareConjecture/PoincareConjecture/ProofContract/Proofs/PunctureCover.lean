import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
def punctureU {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) : Set M :=
  (b.parametrization '' Metric.closedBall 0 (1/2 : ℝ))ᶜ
def punctureV {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) : Set M :=
  b.parametrization '' Metric.ball 0 (3/2 : ℝ)
/-- Exact genuine open cover for removing a coordinate ball. -/
theorem puncture_cover_sets {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    IsOpen (punctureU b) ∧ IsOpen (punctureV b) ∧ punctureU b ∪ punctureV b = Set.univ ∧
    (∀ x : b.Complement, (x : M) ∈ punctureU b) ∧
    punctureU b ∩ punctureV b = b.parametrization ''
      {x : Euclidean3 | (1/2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3/2 : ℝ)} :=
/- SWARM_PROOF_BEGIN -/
by
  have hclosed_source : Metric.closedBall (0 : Euclidean3) (1 / 2 : ℝ) ⊆
      b.parametrization.source := by
    intro x hx
    apply b.contains_two
    have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall] using hx
    simpa [Metric.mem_closedBall] using (show ‖x‖ ≤ 2 by linarith)
  have hopen_source : Metric.ball (0 : Euclidean3) (3 / 2 : ℝ) ⊆
      b.parametrization.source := by
    intro x hx
    apply b.contains_two
    have hxnorm : ‖x‖ < (3 / 2 : ℝ) := by
      simpa [Metric.mem_ball] using hx
    simpa [Metric.mem_closedBall] using (show ‖x‖ ≤ 2 by linarith)
  have hcompact : IsCompact
      (b.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2 : ℝ)) :=
    (isCompact_closedBall (0 : Euclidean3) (1 / 2 : ℝ)).image_of_continuousOn
      (b.parametrization.continuousOn.mono hclosed_source)
  have hclosed : IsClosed
      (b.parametrization '' Metric.closedBall (0 : Euclidean3) (1 / 2 : ℝ)) :=
    hcompact.isClosed
  have hAB : Metric.closedBall (0 : Euclidean3) (1 / 2 : ℝ) ⊆
      Metric.ball 0 (3 / 2 : ℝ) := by
    intro x hx
    have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall] using hx
    simpa [Metric.mem_ball] using (show ‖x‖ < (3 / 2 : ℝ) by linarith)
  have hinj : Set.InjOn b.parametrization
      (Metric.ball (0 : Euclidean3) (3 / 2 : ℝ)) := by
    intro x hx y hy hxy
    have h := congrArg b.parametrization.symm hxy
    simpa only [b.parametrization.left_inv (hopen_source hx),
      b.parametrization.left_inv (hopen_source hy)] using h
  have hopenU : IsOpen (punctureU b) := by
    exact hclosed.isOpen_compl
  have hopenV : IsOpen (punctureV b) := by
    exact b.parametrization.isOpen_image_of_subset_source Metric.isOpen_ball
      hopen_source
  have hcover : punctureU b ∪ punctureV b = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x ∈ b.parametrization '' Metric.closedBall 0 (1 / 2 : ℝ)
    · right
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hAB hy, rfl⟩
    · left
      exact hx
  have hcomp : ∀ x : b.Complement, (x : M) ∈ punctureU b := by
    intro x
    change (x : M) ∉ b.parametrization '' Metric.closedBall 0 (1 / 2 : ℝ)
    intro hx
    apply x.property
    change (x : M) ∈ b.parametrization '' Metric.ball 0 1
    obtain ⟨y, hy, heq⟩ := hx
    refine ⟨y, ?_, heq⟩
    have hynorm : ‖y‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall] using hy
    simpa [Metric.mem_ball] using (show ‖y‖ < (1 : ℝ) by linarith)
  have hinter : punctureU b ∩ punctureV b = b.parametrization ''
      {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)} := by
    calc
      punctureU b ∩ punctureV b =
          (b.parametrization '' Metric.ball 0 (3 / 2 : ℝ)) \
            (b.parametrization '' Metric.closedBall 0 (1 / 2 : ℝ)) := by
        ext x
        simp [punctureU, punctureV, and_comm]
      _ = b.parametrization ''
          (Metric.ball 0 (3 / 2 : ℝ) \ Metric.closedBall 0 (1 / 2 : ℝ)) :=
        (Set.image_sdiff_of_injOn hinj hAB).symm
      _ = b.parametrization ''
          {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)} := by
        congr 1
        ext x
        simp only [mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
          not_le]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩
  exact ⟨hopenU, hopenV, hcover, hcomp, hinter⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
