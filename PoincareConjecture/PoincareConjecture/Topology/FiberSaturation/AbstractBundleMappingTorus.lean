import PoincareConjecture.Topology.FiberSaturation.BundleCutRelation

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Bundle Function

/-- Closed-cylinder mapping torus using only the explicit endpoint relation.
This definition contains no bundle projection and no equality-kernel shortcut. -/
abbrev ClosedMappingTorus {F : Type*} [TopologicalSpace F] (φ : F ≃ₜ F) (L : ℝ) :=
  Quot (@Seam F _ L φ)

variable (F : Type*) [TopologicalSpace F] {L : ℝ}
  (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [∀ z, Nonempty (E z)]

/-- The cut map descends to the explicitly glued cylinder. -/
def closedDescent (hL : 0 < L) : ClosedMappingTorus (monodromy F E hL) L → TotalSpace F E :=
  Quot.lift (cutMap F E) (fun p r h => (cutMap_eq_iff_seam F E hL p r).mpr h)

@[simp] theorem closedDescent_mk (hL : 0 < L) (p : F × Icc (0 : ℝ) L) :
    closedDescent F E hL (Quot.mk _ p) = cutMap F E p := rfl

theorem continuous_closedDescent (hL : 0 < L) : Continuous (closedDescent F E hL) :=
  continuous_quot_lift _ (continuous_cutMap F E)

theorem bijective_closedDescent (hL : 0 < L) : Bijective (closedDescent F E hL) := by
  constructor
  · intro a b
    induction a using Quot.inductionOn with
    | h p =>
      induction b using Quot.inductionOn with
      | h r =>
        intro he
        exact Quot.sound ((cutMap_eq_iff_seam F E hL p r).mp he)
  · intro z
    obtain ⟨p,hp⟩ := surjective_cutMap F E hL z
    exact ⟨Quot.mk _ p,hp⟩

/-- Compactness supplies continuity of the inverse; both topologies are the
original ones. No smooth structure is changed or asserted here. -/
def closedBundleHomeomorph [CompactSpace F] [T2Space (TotalSpace F E)] (hL : 0 < L) :
    ClosedMappingTorus (monodromy F E hL) L ≃ₜ TotalSpace F E :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (closedDescent F E hL) (bijective_closedDescent F E hL))
    (continuous_closedDescent F E hL)

@[simp] theorem closedBundleHomeomorph_mk [CompactSpace F] [T2Space (TotalSpace F E)]
    (hL : 0 < L) (p : F × Icc (0 : ℝ) L) :
    closedBundleHomeomorph F E hL (Quot.mk _ p) = cutMap F E p := rfl

end PoincareConjecture.Topology.FiberSaturation.CircleBundle

namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Bundle

/-- An abstract compact-fiber bundle over the circle has a closed mapping-torus
presentation. The twist and total-space homeomorphism are outputs, not inputs.
The representative formula also proves compatibility with the base projection. -/
theorem abstract_bundle_closed_mappingTorus
    (F : Type*) [TopologicalSpace F] [CompactSpace F] [Nonempty F]
    {L : ℝ} (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [T2Space (TotalSpace F E)]
    (hL : 0 < L) :
    ∃ φ : F ≃ₜ F, ∃ e : ClosedMappingTorus φ L ≃ₜ TotalSpace F E,
      ∀ p : F × Icc (0 : ℝ) L, (e (Quot.mk _ p)).proj = ((p.2 : ℝ) : AddCircle L) := by
  letI : ∀ z, Nonempty (E z) := fun z =>
    ⟨(FiberBundle.homeomorphAt F E z).symm (Classical.choice (inferInstance : Nonempty F))⟩
  exact ⟨monodromy F E hL, closedBundleHomeomorph F E hL, fun _ => rfl⟩

/-- Actual two-sphere specialization; compactness comes from the Euclidean sphere. -/
theorem abstract_sphere_bundle_closed_mappingTorus
    {L : ℝ} (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
    [TopologicalSpace (TotalSpace Sphere2 E)] [FiberBundle Sphere2 E]
    [T2Space (TotalSpace Sphere2 E)] (hL : 0 < L) :
    ∃ φ : Sphere2 ≃ₜ Sphere2, ∃ e : ClosedMappingTorus φ L ≃ₜ TotalSpace Sphere2 E,
      ∀ p : Sphere2 × Icc (0 : ℝ) L, (e (Quot.mk _ p)).proj = ((p.2 : ℝ) : AddCircle L) := by
  letI : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  exact abstract_bundle_closed_mappingTorus Sphere2 E hL

end PoincareConjecture.Topology.FiberSaturation.CircleBundle
