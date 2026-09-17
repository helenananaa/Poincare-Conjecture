import PoincareConjecture.Topology.FiberSaturation.EmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff

/-- Translation in the original smooth structure of the real line. -/
def realTranslation (c : ℝ) : ℝ ≃ₘ[ℝ] ℝ where
  toEquiv := (Homeomorph.addRight c).toEquiv
  contMDiff_toFun := by change ContMDiff _ _ ∞ (fun x : ℝ => x+c); apply ContDiff.contMDiff; fun_prop
  contMDiff_invFun := by change ContMDiff _ _ ∞ (fun x : ℝ => x-c); apply ContDiff.contMDiff; fun_prop

/-- Reflection about c/2, used for the right endpoint chart. -/
def realReflection (c : ℝ) : ℝ ≃ₘ[ℝ] ℝ where
  toEquiv := (Homeomorph.neg ℝ |>.trans (Homeomorph.addRight c)).toEquiv
  contMDiff_toFun := by change ContMDiff _ _ ∞ (fun x : ℝ => -x+c); apply ContDiff.contMDiff; fun_prop
  contMDiff_invFun := by change ContMDiff _ _ ∞ (fun x : ℝ => -(x-c)); apply ContDiff.contMDiff; fun_prop

/-- A global real diffeomorphism supplies a member of the maximal atlas. -/
theorem realDiffeomorph_mem_maximalAtlas (e : ℝ ≃ₘ[ℝ] ℝ) :
    e.toHomeomorph.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℝ) ∞ ℝ :=
  OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
    e.contMDiff.contMDiffOn e.symm.contMDiff.contMDiffOn

/-- The standard interval inclusion is smooth at both endpoints as well as
in the interior. No replacement charted structure is introduced. -/
theorem Icc_subtype_smoothEmbedding (a b : ℝ) [hab : Fact (a < b)] :
    IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (Subtype.val : Icc a b → ℝ) := by
  refine ⟨⟨PUnit, inferInstance, inferInstance, ?_⟩, .subtypeVal⟩
  intro p
  let l : (EuclideanSpace ℝ (Fin 1) × PUnit) ≃L[ℝ] ℝ :=
    (ContinuousLinearEquiv.prodUnique ℝ _ PUnit).trans
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))
  by_cases hp : (p : ℝ) < b
  · let d := IccLeftChart a b
    let c := (realTranslation (-a)).toHomeomorph.toOpenPartialHomeomorph
    apply IsImmersionAtOfComplement.mk_of_charts l d c hp (by simp [c])
      (IsManifold.subset_maximalAtlas (by change d ∈ {IccLeftChart a b, IccRightChart a b}; exact Or.inl rfl))
      (realDiffeomorph_mem_maximalAtlas _) (by simp [c])
    intro y hy
    have hz := (d.extend (𝓡∂ 1)).right_inv hy
    have hz0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hz
    change (((d.extend (𝓡∂ 1)).symm y : Icc a b) : ℝ) - a = y 0 at hz0
    change (((d.extend (𝓡∂ 1)).symm y : Icc a b) : ℝ) + (-a) = y 0
    simpa only [sub_eq_add_neg] using hz0
  · let d := IccRightChart a b
    let c := (realReflection b).toHomeomorph.toOpenPartialHomeomorph
    have hpa : a < (p : ℝ) := hab.out.trans_le (le_of_not_gt hp)
    apply IsImmersionAtOfComplement.mk_of_charts l d c hpa (by simp [c])
      (IsManifold.subset_maximalAtlas (by change d ∈ {IccLeftChart a b, IccRightChart a b}; exact Or.inr rfl))
      (realDiffeomorph_mem_maximalAtlas _) (by simp [c])
    intro y hy
    have hz := (d.extend (𝓡∂ 1)).right_inv hy
    have hz0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hz
    change b - (((d.extend (𝓡∂ 1)).symm y : Icc a b) : ℝ) = y 0 at hz0
    change -(((d.extend (𝓡∂ 1)).symm y : Icc a b) : ℝ) + b = y 0
    linarith

end PoincareConjecture.Topology.FiberSaturation
