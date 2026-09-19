import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.OpenDomain
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeDomain
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Convert a finite native epsilon-neck parameterization into the real-axis
partial chart consumed by the collar normalization, preserving its target region. -/
theorem exists_partialChart_of_native_neck
    {W G N : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    (J : ModelWithCorners ℝ W G) (epsilon : ℝ) (heps : 0 < epsilon)
    (Q : TopologicalSpace.Opens N)
    (φ : Diffeomorph NativeCylinderModel J (nativeNeckDomain epsilon) Q ∞) :
    ∃ Ψ : PartialDiffeomorph ((𝓡 2).prod (𝓘(ℝ,ℝ))) J (Sphere2 × ℝ) N ∞,
      Ψ.source = (univ : Set Sphere2) ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧
      Ψ.target = (Q : Set N) ∧
      (∀ z : scalarNeckDomain epsilon, Ψ z = (φ (scalarToNative z) : N)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨e, he⟩ := exists_native_domain_diffeomorph epsilon
  let φcomp := e.trans φ
  have hpos : (0 : ℝ) < epsilon⁻¹ := inv_pos.mpr heps
  obtain ⟨p⟩ : Nonempty Sphere2 := inferInstance
  haveI : Nonempty (scalarNeckDomain epsilon) := by
    refine ⟨⟨(p, 0), ?_⟩⟩
    exact ⟨mem_univ _, ⟨neg_lt_zero.mpr hpos, hpos⟩⟩
  obtain ⟨Ψ, hsource, htarget, hfwd, _⟩ :=
    exists_partialDiffeomorph_of_open_subspaces (scalarNeckDomain epsilon) Q φcomp
  refine ⟨Ψ, hsource, htarget, ?_⟩
  intro z
  rw [hfwd, Diffeomorph.coe_trans, Function.comp_apply, he]
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
