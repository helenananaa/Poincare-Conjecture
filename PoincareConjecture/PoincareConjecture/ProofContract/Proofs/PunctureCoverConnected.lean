import PoincareConjecture.ProofContract.Proofs.PunctureCover
import PoincareConjecture.ProofContract.Proofs.OpenAnnulus
import PoincareConjecture.ProofContract.Proofs.ComplementConnected
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Genuine connectedness and contractibility facts for the specified cover. -/
theorem puncture_cover_connectivity {M : ClosedThreeManifold.{u}} (b : CoordinateBall M) :
    IsPathConnected (punctureU b) ∧ IsSimplyConnected (punctureV b) ∧
    IsPathConnected (punctureU b ∩ punctureV b) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases puncture_cover_sets b with ⟨hopenU, hopenV, hcover, hcomp_points, hinter⟩
  have hsourceV : Metric.ball (0 : Euclidean3) (3 / 2 : ℝ) ⊆
      b.parametrization.source := by
    intro x hx
    apply b.contains_two
    have hxnorm : ‖x‖ < (3 / 2 : ℝ) := by
      simpa [Metric.mem_ball] using hx
    simpa [Metric.mem_closedBall] using (show ‖x‖ ≤ 2 by linarith)
  have hsourceA : {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧
      ‖x‖ < (3 / 2 : ℝ)} ⊆ b.parametrization.source := by
    intro x hx
    apply hsourceV
    simpa [Metric.mem_ball] using hx.2
  have hAB : Metric.ball (0 : Euclidean3) 1 ⊆
      Metric.ball 0 (3 / 2 : ℝ) := by
    intro x hx
    have hxnorm : ‖x‖ < (1 : ℝ) := by
      simpa [Metric.mem_ball] using hx
    simpa [Metric.mem_ball] using (show ‖x‖ < (3 / 2 : ℝ) by linarith)
  have hcomp : IsConnected b.removedᶜ := by
    rw [isConnected_iff_connectedSpace]
    exact coordinate_complement_connected b
  have hannulus : IsPathConnected
      (b.parametrization ''
        {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)}) :=
    (open_annulus_path_connected (1 / 2 : ℝ) (3 / 2 : ℝ) (by norm_num) (by norm_num)).2.image'
      (b.parametrization.continuousOn.mono hsourceA)
  have hannulus_subset : b.parametrization ''
      {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)} ⊆ punctureU b := by
    rw [← hinter]
    exact inter_subset_left
  have hUeq : punctureU b = b.removedᶜ ∪
      b.parametrization ''
        {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)} := by
    ext x
    constructor
    · intro hx
      by_cases hxc : x ∈ b.removedᶜ
      · exact Or.inl hxc
      · right
        have hxr : x ∈ b.removed := by
          by_contra h
          exact hxc h
        obtain ⟨y, hy, rfl⟩ := hxr
        have hyV : y ∈ Metric.ball (0 : Euclidean3) (3 / 2 : ℝ) := hAB hy
        have hxV : b.parametrization y ∈ punctureV b := ⟨y, hyV, rfl⟩
        have hxUV : b.parametrization y ∈ punctureU b ∩ punctureV b :=
          ⟨hx, hxV⟩
        rw [hinter] at hxUV
        exact hxUV
    · rintro (hxc | hxa)
      · change x ∉ b.parametrization '' Metric.closedBall 0 (1 / 2 : ℝ)
        intro hxclosed
        apply hxc
        change x ∈ b.parametrization '' Metric.ball 0 1
        obtain ⟨y, hy, rfl⟩ := hxclosed
        refine ⟨y, ?_, rfl⟩
        have hynorm : ‖y‖ ≤ (1 / 2 : ℝ) := by
          simpa [Metric.mem_closedBall] using hy
        simpa [Metric.mem_ball] using (show ‖y‖ < (1 : ℝ) by linarith)
      · exact hannulus_subset hxa
  obtain ⟨s0, hs0⟩ : (Metric.sphere (0 : Euclidean3) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  let s0' : Sphere2 := ⟨s0, hs0⟩
  have hinter_nonempty : (b.removedᶜ ∩
      b.parametrization ''
        {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)}).Nonempty := by
    refine ⟨(b.boundary s0' : M), (b.boundary s0').property, ?_⟩
    change b.parametrization (s0' : Euclidean3) ∈
      b.parametrization ''
        {x : Euclidean3 | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)}
    refine ⟨(s0' : Euclidean3), ?_, rfl⟩
    have hs0norm : ‖(s0 : Euclidean3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using s0'.property
    exact ⟨by linarith, by linarith⟩
  have hUconn : IsConnected (punctureU b) := by
    rw [hUeq]
    exact IsConnected.union hinter_nonempty hcomp hannulus.isConnected
  have hUpath : IsPathConnected (punctureU b) :=
    hopenU.isConnected_iff_isPathConnected.mp hUconn
  let eV : Metric.ball (0 : Euclidean3) (3 / 2 : ℝ) ≃ₜ punctureV b :=
    b.parametrization.homeomorphOfImageSubsetSource hsourceV (by rfl)
  have hVsimply : IsSimplyConnected (punctureV b) := by
    change SimplyConnectedSpace (punctureV b)
    letI : ContractibleSpace (Metric.ball (0 : Euclidean3) (3 / 2 : ℝ)) :=
      Metric.contractibleSpace_ball (by norm_num)
    exact eV.symm.toHomotopyEquiv.simplyConnectedSpace
  refine ⟨hUpath, hVsimply, ?_⟩
  rw [hinter]
  exact hannulus
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
