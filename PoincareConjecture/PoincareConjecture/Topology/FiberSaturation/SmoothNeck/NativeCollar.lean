import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeFiniteChart
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.OrientedCollar
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A native finite epsilon-neck cut at any interior level yields the exact
normalized smooth collar needed by the complementary-closure theorem. -/
theorem exists_smoothCollar_of_native_neck_cut
    {W G N : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    (J : ModelWithCorners ℝ W G) (epsilon : ℝ) (heps : 0 < epsilon)
    (Q : TopologicalSpace.Opens N)
    (φ : Diffeomorph NativeCylinderModel J (nativeNeckDomain epsilon) Q ∞)
    (C : Set N) (c s : ℝ) (hc : c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hs : s = 1 ∨ s = -1)
    (hcut : ∀ z : nativeNeckDomain epsilon, (φ z : N) ∈ C ↔ s*(z.1.2 0-c) ≤ 0) :
    ∃ Φ : PartialDiffeomorph ((𝓡 2).prod (𝓘(ℝ,ℝ))) J (Sphere2 × ℝ) N ∞,
      Φ.source = (univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1 ∧
      (∀ z ∈ Φ.source, Φ z ∈ C ↔ z.2 ≤ 0) ∧
      (∀ x : Sphere2, Φ (x,0) =
        (φ (scalarToNative (⟨(x,c), ⟨mem_univ _, hc⟩⟩ : scalarNeckDomain epsilon)) : N)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨Ψ, hsource, _, hfwd⟩ :=
    exists_partialChart_of_native_neck J epsilon heps Q φ
  have ha : -epsilon⁻¹ < c := hc.1
  have hb : c < epsilon⁻¹ := hc.2
  have hcutΨ : ∀ z ∈ Ψ.source, Ψ z ∈ C ↔ s * (z.2 - c) ≤ 0 := by
    intro z hz
    have hzU : z ∈ (univ : Set Sphere2) ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
      rwa [hsource] at hz
    rw [hfwd ⟨z, hzU⟩, hcut]
    simp [scalarToNative]
  obtain ⟨Φ, hΦsrc, hΦcut, hΦzero⟩ :=
    exists_smoothCollar_of_oriented_neck Ψ C (-epsilon⁻¹) epsilon⁻¹ c s
      ha hb hs hsource hcutΨ
  refine ⟨Φ, hΦsrc, hΦcut, ?_⟩
  intro x
  rw [hΦzero]
  exact hfwd ⟨(x, c), ⟨mem_univ _, hc⟩⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
