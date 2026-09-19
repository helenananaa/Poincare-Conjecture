import PoincareConjecture.Topology.FiberSaturation.CollarClosureChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Compose a genuine collar with local cross-section coordinates.
This gives actual ambient product coordinates, not only a chart of the closure. -/
theorem oneSidedCollar_exists_ambient_product_chart
    {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace V]
    [PreconnectedSpace X] {C : Set Y} {f : X × NeckParameter → Y}
    (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} {x : X}
    (hx : f (x, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p))
    (a : OpenPartialHomeomorph X V) :
    ∃ e : OpenPartialHomeomorph Y (V × ℝ),
      (∀ z : X × NeckParameter, z.1 ∈ a.source →
        f z ∈ e.source ∧ e (f z) = (a z.1, (z.2 : ℝ))) ∧
      e.source ⊆ range f ∧
      e.IsImage (connectedComponentIn Cᶜ p) {v | 0 < v.2} ∧
      e.IsImage (closure (connectedComponentIn Cᶜ p)) {v | 0 ≤ v.2} :=
/- SWARM_PROOF_BEGIN -/
by
  haveI : Nonempty X := ⟨x⟩
  haveI : Nonempty NeckParameter := ⟨neckCenter⟩
  let b :=
    (isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
      (Subtype.val : NeckParameter → ℝ)
  let F := hf.toOpenPartialHomeomorph f
  let e := F.symm.trans (a.prod b)
  have hfwd (z : X × NeckParameter) : e (f z) = (a z.1, (z.2 : ℝ)) := by
    change (a.prod b) (F.symm (f z)) = (a z.1, (z.2 : ℝ))
    rw [hf.toOpenPartialHomeomorph_left_inv]
    rfl
  have hb_source : b.source = univ :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source
      (Subtype.val : NeckParameter → ℝ)
      (isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)).isOpenEmbedding_subtypeVal
  have hmem_source (z : X × NeckParameter) (hz : z.1 ∈ a.source) : f z ∈ e.source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rw [OpenPartialHomeomorph.symm_source, hf.toOpenPartialHomeomorph_target]
      exact mem_range_self z
    · change F.symm (f z) ∈ (a.prod b).source
      rw [hf.toOpenPartialHomeomorph_left_inv]
      rw [OpenPartialHomeomorph.prod_source, hb_source]
      exact ⟨hz, mem_univ _⟩
  have hsource_subset : e.source ⊆ range f := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      hf.toOpenPartialHomeomorph_target] at hy
    exact hy.1
  refine ⟨e, fun z hz => ⟨hmem_source z hz, hfwd z⟩, hsource_subset, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := hsource_subset hy
    rw [hfwd z]
    exact (oneSidedCollar_mem_component_iff_pos hf hside hx z).symm
  · intro y hy
    obtain ⟨z, rfl⟩ := hsource_subset hy
    rw [hfwd z]
    exact (oneSidedCollar_mem_closure_component_iff_nonneg hf hside hx z).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
