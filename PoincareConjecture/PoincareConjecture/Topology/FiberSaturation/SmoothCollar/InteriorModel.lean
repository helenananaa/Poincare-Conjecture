import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.TranslateChart

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Every interior point admits a smooth local set model for the SAME corners model as the boundary. -/
theorem interior_point_has_ambient_model
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold (𝓘(ℝ, E)) ∞ N] (I : ModelWithCorners ℝ E H)
    {K : Set N} {p : N} (hp : p ∈ interior K) :
    ∃ e : OpenPartialHomeomorph N E,
      p ∈ e.source ∧ e ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N ∧
      e.IsImage K (range I) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨v, hv⟩ := I.nonempty_interior
  let a := chartAt E p
  let w := v - a p
  let φ := a.trans (Homeomorph.addRight w).toOpenPartialHomeomorph
  have hφ_atlas : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ N :=
    translated_chart_mem_maximalAtlas a (IsManifold.chart_mem_maximalAtlas p) w
  have hpφ : p ∈ φ.source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source E p, mem_univ _⟩
  have hφp : φ p = v := by
    change a p + w = v
    simp [w]
  let S : Set N := interior K ∩ (φ.source ∩ φ ⁻¹' interior (range I))
  have hS : IsOpen S :=
    isOpen_interior.inter (φ.isOpen_inter_preimage isOpen_interior)
  let e := φ.restr S
  have hpe : p ∈ e.source := by
    rw [φ.restr_source' S hS]
    refine ⟨hpφ, hp, hpφ, ?_⟩
    change φ p ∈ interior (range I)
    rwa [hφp]
  refine ⟨e, hpe, ?_, ?_⟩
  · exact restr_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ, E)) hφ_atlas hS
  · intro x hx
    have hx' : x ∈ φ.source ∩ S := by
      rwa [φ.restr_source' S hS] at hx
    have hxK : x ∈ interior K := hx'.2.1
    have hxI : φ x ∈ interior (range I) := hx'.2.2.2
    constructor
    · intro
      exact interior_subset hxK
    · intro
      exact interior_subset hxI
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
