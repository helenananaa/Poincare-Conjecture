import PoincareConjecture

open Set Manifold PoincareConjecture.Topology.FiberSaturation
open scoped Manifold ContDiff
noncomputable section

/-- A bounded open parameter interval, with the inherited standard atlas. -/
def boundedParameter : TopologicalSpace.Opens ℝ := ⟨Ioo (-2 : ℝ) 2,isOpen_Ioo⟩
def rayParameter : TopologicalSpace.Opens ℝ := ⟨Ioi (0 : ℝ),isOpen_Ioi⟩

example : IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ,ℝ)) ((𝓡 2).prod 𝓘(ℝ,ℝ)) ∞
    (fun z : Sphere2 × boundedParameter => (z.1,(z.2 : ℝ))) :=
  IsSmoothEmbedding.id.prodMap (IsSmoothEmbedding.of_opens boundedParameter)

example : IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ,ℝ)) ((𝓡 2).prod 𝓘(ℝ,ℝ)) ∞
    (fun z : Sphere2 × rayParameter => (z.1,(z.2 : ℝ))) :=
  IsSmoothEmbedding.id.prodMap (IsSmoothEmbedding.of_opens rayParameter)

local instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩

def cylinderIntoBounded (z : Sphere2 × Icc (-1 : ℝ) 1) : Sphere2 × boundedParameter :=
  (z.1,⟨z.2,by constructor <;> linarith [z.2.2.1,z.2.2.2]⟩)

/-- The actual closed cylinder maps smoothly into the bounded relative ambient. -/
theorem cylinderIntoBounded_smooth : ContMDiff ((𝓡 2).prod (𝓡∂ 1))
    ((𝓡 2).prod 𝓘(ℝ,ℝ)) ∞ cylinderIntoBounded := by
  have hi : IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ,ℝ)) ((𝓡 2).prod 𝓘(ℝ,ℝ)) ∞
      (fun z : Sphere2 × boundedParameter => (z.1,(z.2 : ℝ))) :=
    IsSmoothEmbedding.id.prodMap (IsSmoothEmbedding.of_opens boundedParameter)
  apply (ContMDiff.iff_comp_isImmersion hi.isImmersion).mpr
  refine ⟨by unfold cylinderIntoBounded; fun_prop, ?_⟩
  exact (cylinder_inclusion_smoothEmbedding (𝓡 2) (-1) 1).contMDiff

example (x : Sphere2) : ((cylinderIntoBounded (x,⟨-1,by norm_num⟩)).2 : ℝ) = -1 := rfl
example (x : Sphere2) : ((cylinderIntoBounded (x,⟨1,by norm_num⟩)).2 : ℝ) = 1 := rfl

/-- Relative and larger-ambient frontiers are intentionally not identified. -/
example : frontier (univ : Set (Sphere2 × boundedParameter)) = ∅ := frontier_univ
example : frontier ((univ : Set Sphere2) ×ˢ Ioo (-2 : ℝ) 2) =
    univ ×ˢ ({(-2 : ℝ),2} : Set ℝ) := by
  rw [frontier_univ_prod_eq,frontier_Ioo (by norm_num : (-2 : ℝ) < 2)]

example : frontier ((univ : Set Sphere2) ×ˢ
    ((Subtype.val : boundedParameter → ℝ) ⁻¹' Ioo (-1 : ℝ) 1)) =
    univ ×ˢ ((Subtype.val : boundedParameter → ℝ) ⁻¹' ({(-1 : ℝ),1} : Set ℝ)) := by
  have hpre : frontier ((Subtype.val : boundedParameter → ℝ) ⁻¹' Ioo (-1 : ℝ) 1) =
      (Subtype.val : boundedParameter → ℝ) ⁻¹' frontier (Ioo (-1 : ℝ) 1) :=
    (boundedParameter.isOpen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val (Ioo (-1 : ℝ) 1)).symm
  rw [frontier_univ_prod_eq,hpre,frontier_Ioo (by norm_num : (-1 : ℝ) < 1)]

/-- A genuine compact relative closure; compactness is not a vacuous premise. -/
example : IsCompact (closure ((univ : Set Sphere2) ×ˢ
    ((Subtype.val : boundedParameter → ℝ) ⁻¹' Ioo (-1 : ℝ) 1))) := by
  letI : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  have hcl : closure ((univ : Set Sphere2) ×ˢ
      ((Subtype.val : boundedParameter → ℝ) ⁻¹' Ioo (-1 : ℝ) 1)) =
      univ ×ˢ ((Subtype.val : boundedParameter → ℝ) ⁻¹' Icc (-1 : ℝ) 1) := by
    have hpre : closure ((Subtype.val : boundedParameter → ℝ) ⁻¹' Ioo (-1 : ℝ) 1) =
        (Subtype.val : boundedParameter → ℝ) ⁻¹' closure (Ioo (-1 : ℝ) 1) :=
      (boundedParameter.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val (Ioo (-1 : ℝ) 1)).symm
    rw [closure_prod_eq,closure_univ,hpre,closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  have hrange : range cylinderIntoBounded = (univ : Set Sphere2) ×ˢ
      ((Subtype.val : boundedParameter → ℝ) ⁻¹' Icc (-1 : ℝ) 1) := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨mem_univ _,w.2.2⟩
    · intro hz
      exact ⟨(z.1,⟨z.2,hz.2⟩),rfl⟩
  rw [hcl,← hrange]
  exact isCompact_range cylinderIntoBounded_smooth.continuous
