import PoincareConjecture.Topology.FiberSaturation.SmoothInterval

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff

/-- The usual affine normalization is a diffeomorphism for Mathlib's standard
manifold-with-boundary structures on both closed intervals. -/
def iccDiffeomorphUnit (a b : ℝ) [hab : Fact (a < b)] :
    Icc a b ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1 where
  toEquiv := (iccHomeoI a b hab.out).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.iff_comp_isImmersion (Icc_subtype_smoothEmbedding 0 1).isImmersion).mpr
    refine ⟨(iccHomeoI a b hab.out).continuous, ?_⟩
    exact (show ContDiff ℝ ∞ (fun t : ℝ => (t-a)/(b-a)) by fun_prop).contMDiff.comp
      (Icc_subtype_smoothEmbedding a b).contMDiff
  contMDiff_invFun := by
    apply (ContMDiff.iff_comp_isImmersion (Icc_subtype_smoothEmbedding a b).isImmersion).mpr
    refine ⟨(iccHomeoI a b hab.out).symm.continuous, ?_⟩
    exact (show ContDiff ℝ ∞ (fun t : ℝ => (b-a)*t+a) by fun_prop).contMDiff.comp
      (Icc_subtype_smoothEmbedding 0 1).contMDiff

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ X]

/-- Standard product-cylinder inclusion, including its two boundary fibers. -/
theorem cylinder_inclusion_smoothEmbedding (a b : ℝ) [Fact (a < b)] :
    IsSmoothEmbedding (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : X × Icc a b => (p.1, (p.2 : ℝ))) :=
  IsSmoothEmbedding.id.prodMap (Icc_subtype_smoothEmbedding a b)

/-- Unit-cylinder normalization without changing either smooth structure. -/
def cylinderDiffeomorphUnit (a b : ℝ) [Fact (a < b)] :
    (X × Icc a b) ≃ₘ⟮I.prod (𝓡∂ 1), I.prod (𝓡∂ 1)⟯ (X × Icc (0 : ℝ) 1) :=
  (Diffeomorph.refl I X ∞).prodCongr (iccDiffeomorphUnit a b)

omit [IsManifold I ∞ X] in
@[simp] theorem cylinderDiffeomorphUnit_apply (a b : ℝ) [hab : Fact (a < b)]
    (p : X × Icc a b) :
    cylinderDiffeomorphUnit I a b p = (p.1, iccHomeoI a b hab.out p.2) := rfl

end PoincareConjecture.Topology.FiberSaturation
