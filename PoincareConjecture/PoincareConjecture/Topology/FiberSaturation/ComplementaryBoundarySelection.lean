import PoincareConjecture.Topology.FiberSaturation.OneSidedCollar
import PoincareConjecture.Topology.FiberSaturation.FrontierComponents

set_option autoImplicit false
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The actual central cross-section of an embedded two-sided collar. -/
def collarSection {X Y : Type*} (f : X × NeckParameter → Y) : Set Y :=
  range (fun x => f (x, neckCenter))

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Saturation of a component frontier is derived from one-sided collars.
Neither component saturation nor a global fibration is part of the input. -/
theorem complementary_frontier_selection [PreconnectedSpace X]
    [LocallyConnectedSpace Y] [Finite ι] {C : Set Y} (hC : IsClosed C)
    (f : ι → X × NeckParameter → Y) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hside : ∀ i z, f i z ∈ C ↔ (z.2 : ℝ) ≤ 0)
    (hcover : frontier C = ⋃ i, collarSection (f i)) {p : Y} (hp : p ∉ C)
    (hproper : connectedComponentIn Cᶜ p ≠ connectedComponent p) :
    ∃ A : Set ι, A.Finite ∧ A.Nonempty ∧
      frontier (connectedComponentIn Cᶜ p) = ⋃ i : A, collarSection (f i.1) ∧
      (∀ i ∈ A, collarSection (f i) ⊆ frontier (connectedComponentIn Cᶜ p)) ∧
      (∀ i ∉ A, Disjoint (collarSection (f i)) (frontier (connectedComponentIn Cᶜ p))) := by
  let D := connectedComponentIn Cᶜ p
  let A : Set ι := {i | (collarSection (f i) ∩ frontier D).Nonempty}
  have hsub (i : ι) (hi : i ∈ A) : collarSection (f i) ⊆ frontier D := by
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hi
    rintro _ ⟨y, rfl⟩
    exact oneSidedCollar_frontier_saturated (hf i) (hside i) hx y
  have hDC : frontier D ⊆ frontier C := complementary_component_frontier_subset hC hp
  have hAne : A.Nonempty := by
    obtain ⟨z, hz⟩ := proper_complementary_component_frontier_nonempty hp hproper
    have hzC := hDC hz
    rw [hcover] at hzC
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzC
    exact ⟨i, z, hzi, hz⟩
  refine ⟨A, Set.toFinite A, hAne, ?_, hsub, ?_⟩
  · apply Subset.antisymm
    · intro z hz
      have hzC := hDC hz
      rw [hcover] at hzC
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hzC
      exact mem_iUnion.mpr ⟨⟨i, z, hzi, hz⟩, hzi⟩
    · intro z hz
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
      exact hsub i.1 i.2 hzi
  · intro i hi
    exact Set.disjoint_left.mpr (fun z hzS hzD => hi ⟨z, hzS, hzD⟩)

/-- For compact connected cross-sections, the selected sections are exactly
whole frontier components; finiteness and pairwise disjointness are explicit. -/
theorem collared_complement_frontier_components [ConnectedSpace X] [CompactSpace X]
    [LocallyConnectedSpace Y] [T2Space Y] [Finite ι] {C : Set Y} (hC : IsClosed C)
    (f : ι → X × NeckParameter → Y) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hside : ∀ i z, f i z ∈ C ↔ (z.2 : ℝ) ≤ 0)
    (hcover : frontier C = ⋃ i, collarSection (f i))
    (hdis : Pairwise (fun i j => Disjoint (collarSection (f i)) (collarSection (f j))))
    {p : Y} (hp : p ∉ C) (hproper : connectedComponentIn Cᶜ p ≠ connectedComponent p) :
    ∃ A : Set ι, A.Finite ∧ A.Nonempty ∧
      frontier (connectedComponentIn Cᶜ p) = ⋃ i : A, collarSection (f i.1) ∧
      (∀ i : A, IsConnected (collarSection (f i.1)) ∧
        ∀ z ∈ collarSection (f i.1),
          connectedComponentIn (frontier (connectedComponentIn Cᶜ p)) z = collarSection (f i.1)) ∧
      (∀ i ∉ A, Disjoint (collarSection (f i)) (frontier (connectedComponentIn Cᶜ p))) := by
  obtain ⟨A, hfinite, hne, hfront, _, hnone⟩ :=
    complementary_frontier_selection hC f hf hside hcover hp hproper
  have hc (i : ι) : Continuous (fun x => f i (x, neckCenter)) :=
    (hf i).continuous.comp (continuous_id.prodMk continuous_const)
  have hsconn (i : ι) : IsConnected (collarSection (f i)) := by
    simpa only [image_univ, collarSection] using isConnected_univ.image _ (hc i).continuousOn
  have hsclosed (i : ι) : IsClosed (collarSection (f i)) := by
    exact (isCompact_range (hc i)).isClosed
  refine ⟨A, hfinite, hne, hfront, ?_, hnone⟩
  intro i
  refine ⟨hsconn i.1, ?_⟩
  intro z hz
  rw [hfront]
  exact componentIn_finite_disjoint_closed (fun j : A => collarSection (f j.1))
    (fun j => hsclosed j.1) (fun j => (hsconn j.1).isPreconnected)
    (fun j k hjk => hdis (fun h => hjk (Subtype.ext h))) i hz

/-- Actual unit two-sphere specialization. Compactness and connectedness of
the fibers are supplied by proved Mathlib results, not new hypotheses. -/
theorem sphere_collared_complement_frontier_components
    [LocallyConnectedSpace Y] [T2Space Y] [Finite ι] {C : Set Y} (hC : IsClosed C)
    (f : ι → Sphere2 × NeckParameter → Y) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hside : ∀ i z, f i z ∈ C ↔ (z.2 : ℝ) ≤ 0)
    (hcover : frontier C = ⋃ i, collarSection (f i))
    (hdis : Pairwise (fun i j => Disjoint (collarSection (f i)) (collarSection (f j))))
    {p : Y} (hp : p ∉ C) (hproper : connectedComponentIn Cᶜ p ≠ connectedComponent p) :
    ∃ A : Set ι, A.Finite ∧ A.Nonempty ∧
      frontier (connectedComponentIn Cᶜ p) = ⋃ i : A, collarSection (f i.1) ∧
      (∀ i : A, IsConnected (collarSection (f i.1)) ∧
        ∀ z ∈ collarSection (f i.1),
          connectedComponentIn (frontier (connectedComponentIn Cᶜ p)) z = collarSection (f i.1)) ∧
      (∀ i ∉ A, Disjoint (collarSection (f i)) (frontier (connectedComponentIn Cᶜ p))) := by
  letI : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  exact collared_complement_frontier_components hC f hf hside hcover hdis hp hproper

end PoincareConjecture.Topology.FiberSaturation
