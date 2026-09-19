import PoincareConjecture.Topology.FiberSaturation.SmoothProductRegion

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff

variable {E F H G X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ F G}
  [IsManifold I ∞ X]

/-- The relative closed cylinder keeps the supplied closure structure and the
standard structure on the open parameter domain. Both smooth directions are
checked through genuine immersions; no general embedding-composition rule is used. -/
def relativeClosedCylinderDiffeomorph (J : TopologicalSpace.Opens ℝ)
    {a b : ℝ} [Fact (a < b)] (hsub : Icc a b ⊆ (J : Set ℝ))
    {U : Set (X × J)} [ChartedSpace G (closure U)] [IsManifold K ∞ (closure U)]
    (hcl : closure U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc a b))
    (hf : IsSmoothEmbedding K (I.prod 𝓘(ℝ,ℝ)) ∞ (Subtype.val : closure U → X × J)) :
    ↥(closure U) ≃ₘ⟮K,I.prod (𝓡∂ 1)⟯ (X × Icc a b) := by
  let inc : X × J → X × ℝ := fun z => (z.1,(z.2 : ℝ))
  have hi : IsSmoothEmbedding (I.prod 𝓘(ℝ,ℝ)) (I.prod 𝓘(ℝ,ℝ)) ∞ inc :=
    IsSmoothEmbedding.id.prodMap (IsSmoothEmbedding.of_opens J)
  let e : ↥(closure U) ≃ₜ (X × Icc a b) :=
    (Homeomorph.setCongr hcl).trans (relativeClosedCylinderHomeomorph hsub)
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.iff_comp_isImmersion
      (cylinder_inclusion_smoothEmbedding I a b).isImmersion).mpr
    refine ⟨e.continuous, ?_⟩
    change ContMDiff K (I.prod 𝓘(ℝ,ℝ)) ∞ (fun z : closure U => (z.1.1,(z.1.2 : ℝ)))
    exact hi.contMDiff.comp hf.contMDiff
  · apply (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr
    refine ⟨e.symm.continuous, ?_⟩
    apply (ContMDiff.iff_comp_isImmersion hi.isImmersion).mpr
    refine ⟨hf.contMDiff.continuous.comp e.symm.continuous, ?_⟩
    change ContMDiff (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ,ℝ)) ∞
      (fun z : X × Icc a b => (z.1,(z.2 : ℝ)))
    exact (cylinder_inclusion_smoothEmbedding I a b).contMDiff

/-- Smooth classification for any open interval with its inherited structure.
Closure and frontier are taken in the actual relative ambient space X × J. -/
theorem relative_product_region_diffeomorph [PreconnectedSpace X]
    (J : TopologicalSpace.Opens ℝ) (hinterval : OrdConnected (J : Set ℝ))
    {U : Set (X × J)} [ChartedSpace G (closure U)] [IsManifold K ∞ (closure U)]
    (hU : IsOpen U) (hc : IsConnected U) (hfront : FiberSaturated (frontier U))
    (hcompact : IsCompact (closure U))
    (hf : IsSmoothEmbedding K (I.prod 𝓘(ℝ,ℝ)) ∞ (Subtype.val : closure U → X × J)) :
    Nonempty (↥(closure U) ≃ₘ⟮K,I.prod (𝓡∂ 1)⟯ (X × Icc (0 : ℝ) 1)) := by
  obtain ⟨a,b,hab,ha,hb,hu,_⟩ :=
    exists_interval_of_compact_closure J.isOpen hU hc hfront hcompact
  letI : Fact (a < b) := ⟨hab⟩
  have hcl : closure U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc a b) := by
    rw [hu, closure_prod_eq, closure_univ,
      ← J.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val, closure_Ioo hab.ne]
    rfl
  exact ⟨(relativeClosedCylinderDiffeomorph J (hinterval.out ha hb) hcl hf).trans
    (cylinderDiffeomorphUnit I a b)⟩

end PoincareConjecture.Topology.FiberSaturation
