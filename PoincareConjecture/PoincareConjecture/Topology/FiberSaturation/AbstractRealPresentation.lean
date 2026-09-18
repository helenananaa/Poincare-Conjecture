import PoincareConjecture.Topology.FiberSaturation.ClosedRealComparison

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Function Bundle
variable (F : Type*) [TopologicalSpace F] [CompactSpace F] [T2Space F] {L : ℝ}
  (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [T2Space (TotalSpace F E)] [∀ z, Nonempty (E z)]

/-- The actual bundle total space is identified with the all-integer quotient,
not just the finite seam quotient. The monodromy is constructed from the bundle. -/
def realBundleHomeomorph (hL : 0 < L) :
    MappingTorus.Space (monodromy F E hL).symm L ≃ₜ TotalSpace F E :=
  (closedRealHomeomorph (monodromy F E hL) hL).symm.trans (closedBundleHomeomorph F E hL)

@[simp] theorem realBundleHomeomorph_fundamental (hL : 0 < L)
    (p : F × Icc (0 : ℝ) L) :
    realBundleHomeomorph F E hL (fundamentalProjection (monodromy F E hL) L p) =
      cutMap F E p := by
  rw [← closedRealHomeomorph_mk (monodromy F E hL) hL p]
  exact congrArg (closedBundleHomeomorph F E hL)
    ((closedRealHomeomorph (monodromy F E hL) hL).symm_apply_apply (Quot.mk _ p))

theorem realBundleHomeomorph_base (hL : 0 < L)
    (z : MappingTorus.Space (monodromy F E hL).symm L) :
    (realBundleHomeomorph F E hL z).proj =
      MappingTorus.circleProjection (monodromy F E hL).symm L z := by
  obtain ⟨p,rfl⟩ := surjective_fundamentalProjection (monodromy F E hL) hL z
  rw [realBundleHomeomorph_fundamental]
  rfl

/-- A continuous presentation on the whole real axis, constructed from the
abstract bundle. Its continuity includes the integer-period seams. -/
def realPresentation (hL : 0 < L) : F × ℝ → TotalSpace F E :=
  fun p => realBundleHomeomorph F E hL (MappingTorus.proj (monodromy F E hL).symm L p)

theorem continuous_realPresentation (hL : 0 < L) : Continuous (realPresentation F E hL) :=
  (realBundleHomeomorph F E hL).continuous.comp
    (MappingTorus.continuous_proj (monodromy F E hL).symm L)

theorem surjective_realPresentation (hL : 0 < L) : Surjective (realPresentation F E hL) :=
  (realBundleHomeomorph F E hL).surjective.comp
    (MappingTorus.proj_surjective (monodromy F E hL).symm L)

theorem realPresentation_base (hL : 0 < L) (p : F × ℝ) :
    (realPresentation F E hL p).proj = (p.2 : AddCircle L) :=
  realBundleHomeomorph_base F E hL _

theorem realPresentation_fiber_injective (hL : 0 < L) (t : ℝ) :
    Injective (fun x : F => realPresentation F E hL (x,t)) :=
  (realBundleHomeomorph F E hL).injective.comp
    (MappingTorus.proj_fiber_injective (monodromy F E hL).symm hL t)

theorem realPresentation_glue (hL : 0 < L) (x : F) (t : ℝ) :
    realPresentation F E hL (x,t+L) = realPresentation F E hL (monodromy F E hL x,t) := by
  apply congrArg (realBundleHomeomorph F E hL)
  simpa using MappingTorus.period_endpoint_identification (monodromy F E hL).symm L t
    (monodromy F E hL x)

/-- Agreement with the original cut map holds also at both ends of the period. -/
theorem realPresentation_cut (hL : 0 < L) (p : F × Icc (0 : ℝ) L) :
    realPresentation F E hL (p.1,(p.2 : ℝ)) = cutMap F E p :=
  realBundleHomeomorph_fundamental F E hL p

/-- Local topological invertibility, including seams, is derived from quotient charts. -/
theorem realPresentation_isLocalHomeomorph (hL : 0 < L) :
    IsLocalHomeomorph (realPresentation F E hL) :=
  (realBundleHomeomorph F E hL).isOpenEmbedding.isLocalHomeomorph.comp
    (MappingTorus.proj_isLocalHomeomorph (monodromy F E hL).symm hL)

end PoincareConjecture.Topology.FiberSaturation.CircleBundle

namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Function Bundle

/-- A whole-axis presentation is an output of a genuine abstract compact-fiber
bundle. All fiber nonemptiness witnesses are derived rather than extra inputs. -/
theorem abstract_bundle_real_presentation
    (F : Type*) [TopologicalSpace F] [CompactSpace F] [T2Space F] [Nonempty F]
    {L : ℝ} (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [T2Space (TotalSpace F E)]
    (hL : 0 < L) :
    ∃ φ : F ≃ₜ F, ∃ q : F × ℝ → TotalSpace F E,
      Continuous q ∧ Surjective q ∧ (∀ p, (q p).proj = (p.2 : AddCircle L)) ∧
      (∀ t, Injective (fun x : F => q (x,t))) ∧
      (∀ x t, q (x,t+L) = q (φ x,t)) ∧ IsLocalHomeomorph q := by
  letI : ∀ z, Nonempty (E z) := fun z =>
    ⟨(FiberBundle.homeomorphAt F E z).symm (Classical.choice (inferInstance : Nonempty F))⟩
  exact ⟨monodromy F E hL,realPresentation F E hL,
    continuous_realPresentation F E hL,surjective_realPresentation F E hL,
    realPresentation_base F E hL,realPresentation_fiber_injective F E hL,
    realPresentation_glue F E hL,realPresentation_isLocalHomeomorph F E hL⟩

/-- Actual sphere specialization, retaining the original total-space topology. -/
theorem abstract_sphere_bundle_real_presentation
    {L : ℝ} (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
    [TopologicalSpace (TotalSpace Sphere2 E)] [FiberBundle Sphere2 E]
    [T2Space (TotalSpace Sphere2 E)] (hL : 0 < L) :
    ∃ φ : Sphere2 ≃ₜ Sphere2, ∃ q : Sphere2 × ℝ → TotalSpace Sphere2 E,
      Continuous q ∧ Surjective q ∧ (∀ p, (q p).proj = (p.2 : AddCircle L)) ∧
      (∀ t, Injective (fun x : Sphere2 => q (x,t))) ∧
      (∀ x t, q (x,t+L) = q (φ x,t)) ∧ IsLocalHomeomorph q := by
  letI : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  exact abstract_bundle_real_presentation Sphere2 E hL

end PoincareConjecture.Topology.FiberSaturation.CircleBundle
