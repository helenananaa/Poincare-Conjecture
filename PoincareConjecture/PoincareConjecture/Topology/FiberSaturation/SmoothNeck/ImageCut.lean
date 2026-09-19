import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

variable {V W G X N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace G]
  [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace V X] [ChartedSpace G N]
  {J : ModelWithCorners ℝ W G}

/-- The actual local surgery-set image identity implies pointwise sidedness. -/
theorem neck_cut_membership_of_image
    (Ψ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞)
    (C : Set N) (c s : ℝ)
    (hcut : C ∩ Ψ.target = Ψ '' (Ψ.source ∩ {z | s*(z.2-c) ≤ 0})) :
    ∀ z ∈ Ψ.source, Ψ z ∈ C ↔ s*(z.2-c) ≤ 0 :=
/- SWARM_PROOF_BEGIN -/
by
  intro z hz
  constructor
  · intro hzC
    have hzT : Ψ z ∈ Ψ.target := Ψ.map_source hz
    have himg : Ψ z ∈ Ψ '' (Ψ.source ∩ {w | s * (w.2 - c) ≤ 0}) := by
      rw [← hcut]
      exact ⟨hzC, hzT⟩
    obtain ⟨w, ⟨hw_source, hw_side⟩, hΨ⟩ := himg
    have hzw : z = w := Ψ.injOn hz hw_source hΨ.symm
    exact hzw ▸ hw_side
  · intro hside
    have himg : Ψ z ∈ Ψ '' (Ψ.source ∩ {w | s * (w.2 - c) ≤ 0}) :=
      ⟨z, ⟨hz, hside⟩, rfl⟩
    have : Ψ z ∈ C ∩ Ψ.target := by
      rwa [hcut]
    exact this.1
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
