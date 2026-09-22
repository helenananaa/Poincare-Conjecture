import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A homeomorphism supported in a buffered coordinate ball extends to the ambient manifold. -/
theorem chart_supported_homeomorph {M : ClosedThreeManifold.{u}} (b : CoordinateBall M)
    (h : Euclidean3 ≃ₜ Euclidean3) (hfix : ∀ z : Euclidean3, 2 ≤ ‖z‖ → h z = z) :
    ∃ F : M ≃ₜ M,
      (∀ z ∈ b.parametrization.source, F (b.parametrization z) = b.parametrization (h z)) ∧
      (∀ x : M, x ∉ b.parametrization.target → F x = x) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let p : OpenPartialHomeomorph Euclidean3 M := b.parametrization
  let B : Set Euclidean3 := Metric.closedBall 0 2
  let K : Set M := p '' B
  have hBsource : B ⊆ p.source := by
    intro z hz
    exact b.contains_two hz
  have preserve_closedBall : ∀ (g : Euclidean3 ≃ₜ Euclidean3),
      (∀ z : Euclidean3, 2 ≤ ‖z‖ → g z = z) → MapsTo g B B := by
    intro g hgf z hz
    by_contra hgz
    have hgz_norm : 2 ≤ ‖g z‖ := by
      have : ¬ ‖g z‖ ≤ 2 := by
        simpa [B, Metric.mem_closedBall] using hgz
      exact le_of_lt (lt_of_not_ge this)
    have hfixgz : g (g z) = g z := hgf (g z) hgz_norm
    have hzg : z = g z := by
      calc
        z = g.symm (g z) := (g.symm_apply_apply z).symm
        _ = g.symm (g (g z)) := by rw [hfixgz]
        _ = g z := g.symm_apply_apply (g z)
    exact hgz (hzg ▸ hz)
  have hfix_symm : ∀ z : Euclidean3, 2 ≤ ‖z‖ → h.symm z = z := by
    intro z hz
    have hz' : h z = z := hfix z hz
    calc
      h.symm z = h.symm (h z) := by rw [hz']
      _ = z := h.symm_apply_apply z
  have hB : MapsTo h B B := preserve_closedBall h hfix
  have hB_symm : MapsTo h.symm B B := preserve_closedBall h.symm hfix_symm
  have hsource : MapsTo h p.source p.source := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact hBsource (hB hzB)
    · have hz_norm : 2 ≤ ‖z‖ := by
        have : ¬ ‖z‖ ≤ 2 := by simpa [B, Metric.mem_closedBall] using hzB
        exact le_of_lt (lt_of_not_ge this)
      simpa [hfix z hz_norm] using hz
  have hsource_symm : MapsTo h.symm p.source p.source := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact hBsource (hB_symm hzB)
    · have hz_norm : 2 ≤ ‖z‖ := by
        have : ¬ ‖z‖ ≤ 2 := by simpa [B, Metric.mem_closedBall] using hzB
        exact le_of_lt (lt_of_not_ge this)
      simpa [hfix_symm z hz_norm] using hz
  have hKcompact : IsCompact K := by
    dsimp [K, B]
    exact (isCompact_closedBall (0 : Euclidean3) 2).image_of_continuousOn
      (p.continuousOn.mono hBsource)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKtarget : K ⊆ p.target := by
    rintro x ⟨z, hz, rfl⟩
    exact p.map_source (hBsource hz)
  have himage : p.IsImage B K := by
    intro z hz
    constructor
    · rintro ⟨y, hy, hzy⟩
      have hyz : y = z := by
        have hh := congrArg p.symm hzy.symm
        simpa only [p.left_inv (hBsource hy), p.left_inv hz] using hh.symm
      simpa [hyz] using hy
    · intro hzB
      exact ⟨z, hzB, rfl⟩
  have hfront : p.IsImage (frontier B) (frontier K) := himage.frontier
  have hfix_frontier : ∀ x ∈ frontier K, p (h (p.symm x)) = x := by
    intro x hx
    have hxK : x ∈ K := hKclosed.frontier_subset hx
    obtain ⟨z, hzB, rfl⟩ := hxK
    have hzfront : z ∈ frontier B := by
      have hzfront' := (hfront.symm_apply_mem_iff (p.map_source (hBsource hzB))).2 hx
      simpa only [p.left_inv (hBsource hzB)] using hzfront'
    have hzsphere : z ∈ Metric.sphere (0 : Euclidean3) 2 :=
      Metric.frontier_closedBall_subset_sphere hzfront
    have hznorm : ‖z‖ = 2 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hzsphere
    rw [p.left_inv (hBsource hzB), hfix z hznorm.ge]
  have hfix_frontier_symm : ∀ x ∈ frontier K, p (h.symm (p.symm x)) = x := by
    intro x hx
    have hxK : x ∈ K := hKclosed.frontier_subset hx
    obtain ⟨z, hzB, rfl⟩ := hxK
    have hzfront : z ∈ frontier B := by
      have hzfront' := (hfront.symm_apply_mem_iff (p.map_source (hBsource hzB))).2 hx
      simpa only [p.left_inv (hBsource hzB)] using hzfront'
    have hzsphere : z ∈ Metric.sphere (0 : Euclidean3) 2 :=
      Metric.frontier_closedBall_subset_sphere hzfront
    have hznorm : ‖z‖ = 2 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hzsphere
    rw [p.left_inv (hBsource hzB), hfix_symm z hznorm.ge]
  let f : M → M := fun x => p (h (p.symm x))
  let g : M → M := fun x => p (h.symm (p.symm x))
  have hfK : ContinuousOn f K := by
    have hpK : ContinuousOn p.symm K := p.symm.continuousOn.mono hKtarget
    have hcomp : ContinuousOn (fun x : M => h (p.symm x)) K :=
      h.continuous.comp_continuousOn hpK
    apply (p.continuousOn.mono hBsource).comp' hcomp
    intro x hx
    exact hB ((himage.symm_apply_mem_iff (hKtarget hx)).2 hx)
  have hgK : ContinuousOn g K := by
    have hpK : ContinuousOn p.symm K := p.symm.continuousOn.mono hKtarget
    have hcomp : ContinuousOn (fun x : M => h.symm (p.symm x)) K :=
      h.symm.continuous.comp_continuousOn hpK
    apply (p.continuousOn.mono hBsource).comp' hcomp
    intro x hx
    exact hB_symm ((himage.symm_apply_mem_iff (hKtarget hx)).2 hx)
  let F : M → M := K.piecewise f id
  let G : M → M := K.piecewise g id
  have hFcont : Continuous F := by
    apply continuous_piecewise
    · exact hfix_frontier
    · simpa [hKclosed.closure_eq] using hfK
    · exact continuous_id.continuousOn
  have hGcont : Continuous G := by
    apply continuous_piecewise
    · exact hfix_frontier_symm
    · simpa [hKclosed.closure_eq] using hgK
    · exact continuous_id.continuousOn
  have hFmem : ∀ x ∈ K, F x = f x := by
    intro x hx
    simp [F, hx]
  have hGmem : ∀ x ∈ K, G x = g x := by
    intro x hx
    simp [G, hx]
  have hFnotmem : ∀ x ∉ K, F x = x := by
    intro x hx
    simp [F, hx]
  have hGnotmem : ∀ x ∉ K, G x = x := by
    intro x hx
    simp [G, hx]
  have hleft : Function.LeftInverse G F := by
    intro x
    by_cases hx : x ∈ K
    · have hxB : p.symm x ∈ B :=
        (himage.symm_apply_mem_iff (hKtarget hx)).2 hx
      have hFxK : F x ∈ K := by
        rw [hFmem x hx]
        exact ⟨h (p.symm x), hB hxB, rfl⟩
      rw [hGmem (F x) hFxK, hFmem x hx]
      change p (h.symm (p.symm (p (h (p.symm x))))) = x
      rw [p.left_inv (hBsource (hB hxB)), h.symm_apply_apply]
      exact p.right_inv (hKtarget hx)
    · rw [hFnotmem x hx, hGnotmem x hx]
  have hright : Function.RightInverse G F := by
    intro x
    by_cases hx : x ∈ K
    · have hxB : p.symm x ∈ B :=
        (himage.symm_apply_mem_iff (hKtarget hx)).2 hx
      have hGxK : G x ∈ K := by
        rw [hGmem x hx]
        exact ⟨h.symm (p.symm x), hB_symm hxB, rfl⟩
      rw [hFmem (G x) hGxK, hGmem x hx]
      change p (h (p.symm (p (h.symm (p.symm x))))) = x
      rw [p.left_inv (hBsource (hB_symm hxB)), h.apply_symm_apply]
      exact p.right_inv (hKtarget hx)
    · rw [hGnotmem x hx, hFnotmem x hx]
  let e : M ≃ M := ⟨F, G, hleft, hright⟩
  refine ⟨Homeomorph.mk e hFcont hGcont, ?_, ?_⟩
  · intro z hz
    change F (p z) = p (h z)
    by_cases hzB : z ∈ B
    · have hpzK : p z ∈ K := ⟨z, hzB, rfl⟩
      rw [hFmem (p z) hpzK]
      change p (h (p.symm (p z))) = p (h z)
      rw [p.left_inv (hBsource hzB)]
    · have hpzK : p z ∉ K := by
        intro hpz
        obtain ⟨y, hyB, hzy⟩ := hpz
        have hyz : y = z := by
          have hh := congrArg p.symm hzy.symm
          simpa only [p.left_inv (hBsource hyB), p.left_inv hz] using hh.symm
        exact hzB (hyz ▸ hyB)
      have hz_norm : 2 ≤ ‖z‖ := by
        have : ¬ ‖z‖ ≤ 2 := by simpa [B, Metric.mem_closedBall] using hzB
        exact le_of_lt (lt_of_not_ge this)
      rw [hFnotmem (p z) hpzK, hfix z hz_norm]
  · intro x hx
    have hxK : x ∉ K := fun hxK => hx (hKtarget hxK)
    exact hFnotmem x hxK
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
