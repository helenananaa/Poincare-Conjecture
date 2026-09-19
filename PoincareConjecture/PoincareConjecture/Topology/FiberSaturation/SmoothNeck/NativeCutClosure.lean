import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeCollar
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Native spherical epsilon-neck parameterizations around the continuing
frontier suffice to construct the smooth complementary closure, with cut data explicit. -/
theorem exists_smoothClosure_of_native_neck_cut_cover
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) N]
    [IsManifold (𝓘(ℝ,EuclideanSpace ℝ (Fin 2) × ℝ)) ∞ N] [LocallyConnectedSpace N]
    {C : Set N} (hC : IsClosed C) {p : N} (hp : p ∉ C)
    (hcover : ∀ y ∈ frontier C, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Q : TopologicalSpace.Opens N,
      ∃ φ : Diffeomorph NativeCylinderModel (𝓘(ℝ,EuclideanSpace ℝ (Fin 2) × ℝ))
          (nativeNeckDomain epsilon) Q ∞,
      ∃ c s : ℝ, c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧ (s = 1 ∨ s = -1) ∧
        (∀ z : nativeNeckDomain epsilon, (φ z : N) ∈ C ↔ s*(z.1.2 0-c) ≤ 0) ∧
        ∃ z : nativeNeckDomain epsilon, (φ z : N) = y ∧ z.1.2 0 = c) :
    ∃ cs : ChartedSpace (SmoothCollar.HalfSpace (EuclideanSpace ℝ (Fin 2)))
        (closure (connectedComponentIn Cᶜ p)),
      letI : ChartedSpace (SmoothCollar.HalfSpace (EuclideanSpace ℝ (Fin 2)))
        (closure (connectedComponentIn Cᶜ p)) := cs
      IsManifold (SmoothCollar.halfSpaceModel (EuclideanSpace ℝ (Fin 2))) ∞
        (closure (connectedComponentIn Cᶜ p)) ∧
      IsSmoothEmbedding (SmoothCollar.halfSpaceModel (EuclideanSpace ℝ (Fin 2)))
        (𝓘(ℝ,EuclideanSpace ℝ (Fin 2) × ℝ)) ∞
        (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ∧
      (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ''
        (SmoothCollar.halfSpaceModel (EuclideanSpace ℝ (Fin 2))).boundary
          (closure (connectedComponentIn Cᶜ p)) = frontier (connectedComponentIn Cᶜ p) ∧
      connectedComponentIn Cᶜ p = interior (closure (connectedComponentIn Cᶜ p)) :=
/- SWARM_PROOF_BEGIN -/
by
  have hfront : frontier (connectedComponentIn Cᶜ p) ⊆ frontier C :=
    complementary_component_frontier_subset hC hp
  refine SmoothCollar.exists_smoothClosure_of_smoothCollar_cover
    (X := Sphere2) (V := EuclideanSpace ℝ (Fin 2)) (p := p) hC ?cover
  intro y hy
  have hyC : y ∈ frontier C := hfront hy
  obtain ⟨epsilon, heps, Q, φ, c, s, hc, hs, hcut, z, hzy, hzc⟩ := hcover y hyC
  obtain ⟨Φ, hΦsrc, hΦside, hΦzero⟩ :=
    exists_smoothCollar_of_native_neck_cut
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)) epsilon heps Q φ C c s hc hs hcut
  refine ⟨Φ, hΦsrc, hΦside, z.1.1, ?_⟩
  have hax : nativeAxis c = z.1.2 := by
    refine PiLp.ext fun i => ?_
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    exact (nativeAxis_zero c).trans hzc.symm
  rw [hΦzero, ← hzy]
  refine congrArg (fun w : nativeNeckDomain epsilon => (φ w : N)) ?_
  apply Subtype.ext
  dsimp [scalarToNative]
  exact Prod.ext rfl hax
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
