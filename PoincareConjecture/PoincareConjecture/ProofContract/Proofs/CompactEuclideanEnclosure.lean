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
/-- A compact set in an open Euclidean chart fits in a buffered coordinate ball there. -/
theorem compact_euclidean_chart_enclosure (M : ClosedThreeManifold.{u})
    (U : TopologicalSpace.Opens M) (e : U ≃ₜ Euclidean3)
    (K : Set M) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ b : CoordinateBall M, K ⊆ b.removed ∧
      b.parametrization '' Metric.closedBall (0:Euclidean3) 2 ⊆ U :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : Nonempty U := ⟨e.symm 0⟩
  let inc : OpenPartialHomeomorph U M :=
    U.openPartialHomeomorphSubtypeCoe inferInstance
  let g : OpenPartialHomeomorph Euclidean3 M :=
    e.symm.toOpenPartialHomeomorph.trans inc
  let KU : Set U := (fun x : U => (x : M)) ⁻¹' K
  have hKUcompact : IsCompact KU := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have himage : (fun x : U => (x : M)) '' KU = K := by
      rw [Set.image_preimage_eq_of_subset]
      intro x hx
      exact ⟨⟨x, hKU hx⟩, rfl⟩
    rw [himage]
    exact hK
  let S : Set Euclidean3 := e '' KU
  have hScompact : IsCompact S := hKUcompact.image e.continuous
  obtain ⟨ρ, hρ⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Euclidean3)).mp hScompact.isBounded
  let r : ℝ := max 1 ρ + 1
  have hr : 0 < r := by
    dsimp [r]
    linarith [le_max_left (1 : ℝ) ρ]
  have hSr : S ⊆ Metric.ball (0 : Euclidean3) r := by
    intro z hz
    have hzρ : z ∈ Metric.closedBall (0 : Euclidean3) ρ := hρ hz
    have hznorm : ‖z‖ ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzρ
    have hzmax : ρ ≤ max 1 ρ := le_max_right _ _
    have hzr : ‖z‖ < r := by
      dsimp [r]
      linarith
    simpa [Metric.mem_ball, dist_zero_right] using hzr
  let h : Euclidean3 ≃ₜ Euclidean3 := Homeomorph.smulOfNeZero r hr.ne'
  let p : OpenPartialHomeomorph Euclidean3 M := h.toOpenPartialHomeomorph.trans g
  have hsource : Metric.closedBall (0 : Euclidean3) 2 ⊆ p.source := by
    rw [OpenPartialHomeomorph.trans_source]
    intro z hz
    constructor
    · simp
    · change h z ∈ g.source
      simp [g, inc]
  let b : CoordinateBall M := ⟨p, hsource⟩
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    have hxU : (⟨x, hKU hx⟩ : U) ∈ KU := hx
    have hex : e ⟨x, hKU hx⟩ ∈ S := ⟨⟨x, hKU hx⟩, hxU, rfl⟩
    have hexball : e ⟨x, hKU hx⟩ ∈ Metric.ball (0 : Euclidean3) r := hSr hex
    have hexnorm : ‖e ⟨x, hKU hx⟩‖ < r := by
      simpa [Metric.mem_ball, dist_zero_right] using hexball
    have hscalednorm : ‖r⁻¹ • e ⟨x, hKU hx⟩‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      calc
        r⁻¹ * ‖e ⟨x, hKU hx⟩‖ < r⁻¹ * r :=
          mul_lt_mul_of_pos_left hexnorm (inv_pos.mpr hr)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    refine ⟨r⁻¹ • e ⟨x, hKU hx⟩, ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_zero_right] using hscalednorm
    · change (e.symm (h (r⁻¹ • e ⟨x, hKU hx⟩)) : M) = x
      have hscale : h (r⁻¹ • e ⟨x, hKU hx⟩) = e ⟨x, hKU hx⟩ := by
        change r • (r⁻¹ • e ⟨x, hKU hx⟩) = e ⟨x, hKU hx⟩
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      rw [hscale]
      exact congrArg (fun y : U => (y : M)) (e.left_inv ⟨x, hKU hx⟩)
  · rintro z ⟨y, hy, rfl⟩
    change (e.symm (h y) : M) ∈ U
    exact (e.symm (h y)).property
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
