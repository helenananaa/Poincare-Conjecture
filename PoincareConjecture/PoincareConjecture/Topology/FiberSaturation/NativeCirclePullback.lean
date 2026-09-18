import PoincareConjecture.Topology.FiberSaturation.BundlePullbackSmooth

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CoverPullback
open Set Bundle
open scoped Manifold ContDiff
variable {L : ℝ} {F V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] (E : AddCircle L → Type*)
  [TopologicalSpace (TotalSpace F E)] [ChartedSpace H (TotalSpace F E)]
  (hp : Continuous (TotalSpace.proj (F := F) (E := E)))
  (I : ModelWithCorners ℝ V H) [IsManifold I ∞ (TotalSpace F E)]

/-- A constructed smooth period shift on the standard dependent pullback.
No deck transformation or smoothness proof is supplied by the caller. -/
def nativeCircleDeck :
    letI := bundleChartedSpace (H := H) E ((↑) : ℝ → AddCircle L)
      (AddCircle.isLocalHomeomorph_coe L) hp;
    (TotalSpace F (((↑) : ℝ → AddCircle L) *ᵖ E)) ≃ₘ⟮I,I⟯
      (TotalSpace F (((↑) : ℝ → AddCircle L) *ᵖ E)) := by
  letI := bundleChartedSpace (H := H) E ((↑) : ℝ → AddCircle L)
    (AddCircle.isLocalHomeomorph_coe L) hp
  letI := circleChartedSpace (H := H) (TotalSpace.proj (F := F) (E := E)) hp
  let e := bundleComparisonDiffeomorph E ((↑) : ℝ → AddCircle L)
    (AddCircle.isLocalHomeomorph_coe L) hp I
  exact (e.trans (circleDeckDiffeomorph (TotalSpace.proj (F := F) (E := E)) I hp)).trans e.symm

/-- The constructed native deck transformation fixes the original total-space point. -/
theorem nativeCircleDeck_lift (z : TotalSpace F (((↑) : ℝ → AddCircle L) *ᵖ E)) :
    Pullback.lift ((↑) : ℝ → AddCircle L) (nativeCircleDeck E hp I z) =
      Pullback.lift ((↑) : ℝ → AddCircle L) z := by
  let h := bundleHomeomorph (F := F) E ((↑) : ℝ → AddCircle L)
  change forget (h (h.symm (circleDeck (TotalSpace.proj (F := F) (E := E)) (h z)))) = forget (h z)
  rw [h.apply_symm_apply]
  rfl

/-- Its height increases by exactly one real period. -/
theorem nativeCircleDeck_height (z : TotalSpace F (((↑) : ℝ → AddCircle L) *ᵖ E)) :
    (nativeCircleDeck E hp I z).proj = z.proj + L := by
  let h := bundleHomeomorph (F := F) E ((↑) : ℝ → AddCircle L)
  change height (h (h.symm (circleDeck (TotalSpace.proj (F := F) (E := E)) (h z)))) = height (h z)+L
  rw [h.apply_symm_apply]
  rfl

end PoincareConjecture.Topology.FiberSaturation.CoverPullback
