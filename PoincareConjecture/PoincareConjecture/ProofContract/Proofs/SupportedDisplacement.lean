import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open Set Function Filter Topology
open scoped Topology
theorem supported_homeomorph_displacement {X : Type u} [MetricSpace X]
    (h : X ≃ₜ X) (U : Set X) (eps : ℝ) (heps : 0 ≤ eps)
    (hfix : ∀ x, x ∉ U → h x=x)
    (hdiam : ∀ x∈U, ∀ y∈U, dist x y ≤ eps) :
    h '' U=U ∧ (∀ x, dist (h x) x ≤ eps) ∧ (∀ x, dist (h.symm x) x ≤ eps) :=
/- SWARM_PROOF_BEGIN -/
by
  have hmap : ∀ x, x ∈ U → h x ∈ U := by
    intro x hx
    by_contra hnot
    have hfixed : h (h x) = h x := hfix (h x) hnot
    have hxeq : x = h x := h.injective hfixed.symm
    exact hnot (hxeq ▸ hx)
  have hmap_symm : ∀ x, x ∈ U → h.symm x ∈ U := by
    intro x hx
    by_contra hnot
    have hfixed : h (h.symm x) = h.symm x := hfix (h.symm x) hnot
    have hxeq : x = h.symm x := by
      calc
        x = h (h.symm x) := (h.apply_symm_apply x).symm
        _ = h.symm x := hfixed
    exact hnot (hxeq ▸ hx)
  have hfix_symm : ∀ x, x ∉ U → h.symm x = x := by
    intro x hx
    apply h.injective
    calc
      h (h.symm x) = x := h.apply_symm_apply x
      _ = h x := (hfix x hx).symm
  refine ⟨Set.Subset.antisymm ?_ ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hmap y hy
  · intro x hx
    exact ⟨h.symm x, hmap_symm x hx, h.apply_symm_apply x⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hdiam (h x) (hmap x hx) x hx
    · rw [hfix x hx, dist_self]
      exact heps
  · intro x
    by_cases hx : x ∈ U
    · exact hdiam (h.symm x) (hmap_symm x hx) x hx
    · rw [hfix_symm x hx, dist_self]
      exact heps
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
