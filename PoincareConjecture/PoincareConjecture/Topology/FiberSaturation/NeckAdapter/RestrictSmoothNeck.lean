import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.NeckAdapter
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Shrinking an actual smooth neck keeps its forward and inverse smoothness. -/
theorem exists_restricted_smooth_neck {V H X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (I : ModelWithCorners ℝ V H) [IsManifold I ∞ X]
    {W G N : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    (J : ModelWithCorners ℝ W G) [IsManifold J ∞ N]
    (F : OpenPartialHomeomorph (X × ℝ) N) (c r : ℝ) (hr : 0 < r)
    (hsource : (univ ×ˢ Ioo (c-r) (c+r) : Set (X × ℝ)) ⊆ F.source)
    (hF : ContMDiffOn (I.prod (𝓘(ℝ, ℝ))) J ∞ F F.source)
    (hFi : ContMDiffOn J (I.prod (𝓘(ℝ, ℝ))) ∞ F.symm F.target) :
    ∃ E : OpenPartialHomeomorph (X × ℝ) N,
      E.source = (univ ×ˢ Ioo (c-r) (c+r)) ∧
      (∀ z, E z = F z) ∧ (∀ y, E.symm y = F.symm y) ∧
      ContMDiffOn (I.prod (𝓘(ℝ, ℝ))) J ∞ E E.source ∧
      ContMDiffOn J (I.prod (𝓘(ℝ, ℝ))) ∞ E.symm E.target :=
/- SWARM_PROOF_BEGIN -/
by
  let s : Set (X × ℝ) := univ ×ˢ Ioo (c - r) (c + r)
  have hs : IsOpen s := isOpen_univ.prod isOpen_Ioo
  refine ⟨F.restrOpen s hs, ?_, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact inter_eq_right.mpr hsource
  · exact hF.mono <| by
      rw [OpenPartialHomeomorph.restrOpen_source]
      exact inter_subset_left
  · exact hFi.mono inter_subset_left
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.NeckAdapter
