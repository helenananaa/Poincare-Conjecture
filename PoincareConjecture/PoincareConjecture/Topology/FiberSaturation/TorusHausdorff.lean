import PoincareConjecture.Topology.FiberSaturation.CanonicalCircleProjection

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set Function
variable {X : Type*} [TopologicalSpace X]

/-- The integer-deck quotient is Hausdorff for a Hausdorff fiber and a positive
period. Local homeomorphism alone would not justify this separation property. -/
theorem space_t2Space [T2Space X] (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L) :
    T2Space (Space φ L) := by
  letI : Fact (0 < L) := ⟨hL⟩
  constructor
  intro a b hab
  by_cases hh : circleProjection φ L a = circleProjection φ L b
  · obtain ⟨⟨x,t⟩,rfl⟩ := proj_surjective φ L a
    have hb : b ∈ circleProjection φ L ⁻¹' ({(t : AddCircle L)} : Set (AddCircle L)) := hh.symm
    rw [← image_height_fiber] at hb
    obtain ⟨⟨y,s⟩,⟨_,hs⟩,rfl⟩ := hb
    have hst : s = t := hs
    subst s
    let U : Set (X × ℝ) := univ ×ˢ Ioo (t-L/3) (t+L/3)
    have hmem (z : X) : (z,t) ∈ U := ⟨mem_univ _, by constructor <;> linarith⟩
    let ux : U := ⟨(x,t),hmem x⟩
    let uy : U := ⟨(y,t),hmem y⟩
    let f : U → Space φ L := fun p => proj φ L p.1
    have hf : _root_.Topology.IsOpenEmbedding f :=
      proj_isOpenEmbedding_openStrip φ hL (by linarith)
    have hxy : ux ≠ uy := fun he => hab (congrArg f he)
    obtain ⟨u,v,hu,hv,hxu,hyv,hd⟩ := t2_separation hxy
    refine ⟨f '' u, f '' v, hf.isOpenMap _ hu, hf.isOpenMap _ hv,
      ⟨ux,hxu,rfl⟩,⟨uy,hyv,rfl⟩,?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨p,hp,rfl⟩ ⟨q,hq,hqp⟩
    exact Set.disjoint_left.mp hd hp (hf.injective hqp ▸ hq)
  · obtain ⟨u,v,hu,hv,hau,hbv,hd⟩ := t2_separation hh
    refine ⟨circleProjection φ L ⁻¹' u, circleProjection φ L ⁻¹' v,
      hu.preimage (continuous_circleProjection φ L),
      hv.preimage (continuous_circleProjection φ L),hau,hbv,?_⟩
    exact Set.disjoint_left.mpr (fun _ hp hq => Set.disjoint_left.mp hd hp hq)

/-- Compactness of the fiber implies compactness of the actual deck quotient. -/
theorem space_compactSpace [CompactSpace X] (φ : X ≃ₜ X) {L : ℝ} (hL : 0 < L) :
    CompactSpace (Space φ L) := by
  constructor
  rw [← image_period_closedStrip φ hL (0 : ℝ)]
  exact (isCompact_univ.prod isCompact_Icc).image (continuous_proj φ L)

end PoincareConjecture.Topology.FiberSaturation.MappingTorus
