import PoincareConjecture.Topology.FiberSaturation.CirclePullbackDeck
import Mathlib.Topology.FiberBundle.Constructions

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CoverPullback
open Set Bundle Function
variable {B R F : Type*} (E : B → Type*) (c : R → B)
  [TopologicalSpace R] [TopologicalSpace (TotalSpace F E)]

/-- The canonical comparison with Mathlib's dependent-type pullback total space. -/
def bundleToSpace (z : TotalSpace F (c *ᵖ E)) : Space c (TotalSpace.proj (F := F) (E := E)) :=
  ⟨(z.proj, Pullback.lift c z), rfl⟩

omit [TopologicalSpace R] [TopologicalSpace (TotalSpace F E)] in
theorem bundleToSpace_bijective : Bijective (bundleToSpace (F := F) E c) := by
  constructor
  · rintro ⟨t,x⟩ ⟨s,y⟩ heq
    have ht : t = s := congrArg (fun z => z.1.1) heq
    subst s
    have hv : TotalSpace.mk (F := F) (c t) x = TotalSpace.mk (c t) y :=
      congrArg (fun z => z.1.2) heq
    have hxy := TotalSpace.mk_injective (c t) hv
    subst y
    rfl
  · rintro ⟨⟨t,⟨b,x⟩⟩,h⟩
    change c t = b at h
    subst b
    exact ⟨⟨t,x⟩,rfl⟩

/-- The comparison respects the actual existing pullback topology. -/
def bundleHomeomorph : TotalSpace F (c *ᵖ E) ≃ₜ Space c (TotalSpace.proj (F := F) (E := E)) :=
  (Equiv.ofBijective (bundleToSpace E c) (bundleToSpace_bijective E c)).toHomeomorphOfIsInducing
    (Topology.IsInducing.subtypeVal.of_comp_iff.mp (inducing_pullbackTotalSpaceEmbedding F E c))

@[simp] theorem forget_bundleHomeomorph (z : TotalSpace F (c *ᵖ E)) :
    forget (bundleHomeomorph E c z) = Pullback.lift c z := rfl

@[simp] theorem height_bundleHomeomorph (z : TotalSpace F (c *ᵖ E)) :
    height (bundleHomeomorph E c z) = z.proj := rfl

variable [TopologicalSpace B]

/-- The usual Mathlib pullback lift is a local homeomorphism, not merely a
map between two newly invented models. -/
theorem bundle_lift_isLocalHomeomorph (hc : IsLocalHomeomorph c)
    (hp : Continuous (TotalSpace.proj (F := F) (E := E))) :
    IsLocalHomeomorph (Pullback.lift c : TotalSpace F (c *ᵖ E) → TotalSpace F E) := by
  have h := (forget_isLocalHomeomorph hc hp).comp (bundleHomeomorph (F := F) E c).isLocalHomeomorph
  exact h

end PoincareConjecture.Topology.FiberSaturation.CoverPullback
