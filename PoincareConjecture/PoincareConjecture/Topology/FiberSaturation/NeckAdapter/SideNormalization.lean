import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.NeckAdapter
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A centered positive-width neck with an actual one-sided set relation supplies normalized collar data. -/
theorem exists_normalized_oneSided_neck
    {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    (F : OpenPartialHomeomorph (X × ℝ) N) (C : Set N) (c r : ℝ) (hr : 0 < r)
    (hsource : (univ ×ˢ Ioo (c-r) (c+r) : Set (X × ℝ)) ⊆ F.source)
    (hside : ∀ z ∈ (univ ×ˢ Ioo (c-r) (c+r) : Set (X × ℝ)),
      F z ∈ C ↔ z.2 ≤ c) :
    ∃ f : X × NeckParameter → N,
      Topology.IsOpenEmbedding f ∧
      (∀ z, f z = F (z.1, c + r*(z.2 : ℝ))) ∧
      (∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) :=
/- SWARM_PROOF_BEGIN -/
by
  let scale : ℝ → ℝ := fun t => c + r * t
  let ιParam : NeckParameter → ℝ := fun t => scale (t : ℝ)
  have hscale : Topology.IsOpenEmbedding scale :=
    ((Homeomorph.mulLeft₀ r hr.ne').trans (Homeomorph.addLeft c)).isOpenEmbedding
  have hιParam : Topology.IsOpenEmbedding ιParam :=
    hscale.comp isOpen_Ioo.isOpenEmbedding_subtypeVal
  let ι : X × NeckParameter → X × ℝ := fun z => (z.1, ιParam z.2)
  have hι : Topology.IsOpenEmbedding ι := by
    change Topology.IsOpenEmbedding (Prod.map (id : X → X) ιParam)
    exact Topology.IsOpenEmbedding.id.prodMap hιParam
  have hIoo : ∀ t : NeckParameter, scale (t : ℝ) ∈ Ioo (c - r) (c + r) := by
    intro t
    have ht := t.property
    refine ⟨?_, ?_⟩
    · have := mul_lt_mul_of_pos_left ht.1 hr
      linarith
    · have := mul_lt_mul_of_pos_left ht.2 hr
      linarith
  have hrange : range ι ⊆ (univ ×ˢ Ioo (c - r) (c + r) : Set (X × ℝ)) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨mem_univ _, hIoo z.2⟩
  have hsrc : ∀ z, ι z ∈ F.source := fun z => hsource (hrange (mem_range_self z))
  let e : X × NeckParameter → F.source := fun z => ⟨ι z, hsrc z⟩
  have he : Topology.IsOpenEmbedding e :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hι.continuous.codRestrict hsrc)
      (fun z w hzw => hι.injective (Subtype.ext_iff.mp hzw))
      (hι.isOpenMap.codRestrict hsrc)
  let f : X × NeckParameter → N := F.source.restrict F ∘ e
  refine ⟨f, F.isOpenEmbedding_restrict.comp he, fun z => rfl, fun z => ?_⟩
  have hz : ι z ∈ (univ ×ˢ Ioo (c - r) (c + r) : Set (X × ℝ)) :=
    ⟨mem_univ _, hIoo z.2⟩
  have hsign : scale (z.2 : ℝ) ≤ c ↔ (z.2 : ℝ) ≤ 0 := by
    constructor
    · intro h
      nlinarith [hr]
    · intro h
      nlinarith [hr]
  simpa [f, e, ι, ιParam, scale, hsign] using hside (ι z) hz
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.NeckAdapter
