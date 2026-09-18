import PoincareConjecture.Topology.FiberSaturation.BundlePullbackComparison

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CoverPullback
open Set Bundle Manifold
open scoped Manifold ContDiff
variable {B R F V H : Type*} (E : B → Type*) (c : R → B)
  [TopologicalSpace R] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  [ChartedSpace H (TotalSpace F E)]
  (hc : IsLocalHomeomorph c) (hp : Continuous (TotalSpace.proj (F := F) (E := E)))

/-- The standard Mathlib pullback total space receives the pulled-back atlas. -/
@[implicit_reducible] def bundleChartedSpace : ChartedSpace H (TotalSpace F (c *ᵖ E)) :=
  CoverLift.chartedSpace (H := H) (bundle_lift_isLocalHomeomorph E c hc hp)

variable (I : ModelWithCorners ℝ V H) [IsManifold I ∞ (TotalSpace F E)]

theorem bundle_isManifold :
    letI := bundleChartedSpace (H := H) E c hc hp; IsManifold I ∞ (TotalSpace F (c *ᵖ E)) :=
  CoverLift.isManifold I (bundle_lift_isLocalHomeomorph E c hc hp)

theorem bundle_lift_isLocalDiffeomorph :
    letI := bundleChartedSpace (H := H) E c hc hp;
    IsLocalDiffeomorph I I ∞ (Pullback.lift c : TotalSpace F (c *ᵖ E) → TotalSpace F E) :=
  CoverLift.isLocalDiffeomorph I (bundle_lift_isLocalHomeomorph E c hc hp)

/-- The native dependent pullback and concrete fiber-product model agree
smoothly, because both use exactly the original target's smooth charts. -/
def bundleComparisonDiffeomorph :
    letI := bundleChartedSpace (H := H) E c hc hp;
    letI := CoverLift.chartedSpace (H := H) (forget_isLocalHomeomorph hc hp);
    (TotalSpace F (c *ᵖ E)) ≃ₘ⟮I,I⟯ (Space c (TotalSpace.proj (F := F) (E := E))) := by
  letI := bundleChartedSpace (H := H) E c hc hp
  letI := CoverLift.chartedSpace (H := H) (forget_isLocalHomeomorph hc hp)
  let h := bundleHomeomorph (F := F) E c
  have hg := CoverLift.isLocalDiffeomorph I (forget_isLocalHomeomorph hc hp)
  have hb := bundle_lift_isLocalDiffeomorph E c hc hp I
  refine { toEquiv := h.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact contMDiff_of_localDiffeomorph_comp hg h.continuous hb.contMDiff
  · apply contMDiff_of_localDiffeomorph_comp hb h.symm.continuous
    apply hg.contMDiff.congr
    intro z
    change Pullback.lift c (h.symm z) = forget z
    rw [← forget_bundleHomeomorph E c]
    exact congrArg forget (h.apply_symm_apply z)

end PoincareConjecture.Topology.FiberSaturation.CoverPullback
