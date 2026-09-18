import PoincareConjecture.Topology.FiberSaturation.SmoothProductRegion
import Mathlib.Topology.FiberBundle.Constructions

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Bundle Function

/-- The actual universal-cover map to the additive circle. -/
def cover (L : ℝ) : C(ℝ, AddCircle L) :=
  ⟨fun t => (t : AddCircle L), AddCircle.continuous_mk' L⟩

variable (F : Type*) [TopologicalSpace F] {L : ℝ}
  (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [∀ z, Nonempty (E z)]

abbrev Lifted := TotalSpace F ((cover L : ℝ → AddCircle L) *ᵖ E)

/-- Chosen from Mathlib's closed-interval theorem, not supplied as a hypothesis. -/
def cutTrivialization : Trivialization F (TotalSpace.proj : Lifted F E → ℝ) :=
  Classical.choose (FiberBundle.exists_trivialization_Icc_subset F
    ((cover L : ℝ → AddCircle L) *ᵖ E) 0 L)

theorem cutTrivialization_covers : Icc (0 : ℝ) L ⊆ (cutTrivialization F E).baseSet :=
  Classical.choose_spec (FiberBundle.exists_trivialization_Icc_subset F
    ((cover L : ℝ → AddCircle L) *ᵖ E) 0 L)

/-- A trivialization of the actual cut-open pullback total space. -/
def cutHomeomorph :
    ↥((TotalSpace.proj : Lifted F E → ℝ) ⁻¹' Icc 0 L) ≃ₜ (Icc (0 : ℝ) L × F) :=
  (cutTrivialization F E).preimageHomeomorph (cutTrivialization_covers F E)

/-- The cylinder map obtained by forgetting the real lift of the base point. -/
def cutMap (p : F × Icc (0 : ℝ) L) : TotalSpace F E :=
  ⟨(p.2 : ℝ), (cutTrivialization F E).symm (p.2 : ℝ) p.1⟩

theorem cutMap_proj (p : F × Icc (0 : ℝ) L) :
    (cutMap F E p).proj = ((p.2 : ℝ) : AddCircle L) := rfl

theorem continuous_cutMap : Continuous (cutMap F E) := by
  have heq : cutMap F E = fun p : F × Icc (0 : ℝ) L =>
      Pullback.lift (cover L) ((cutHomeomorph F E).symm (p.2, p.1)).1 := by
    funext p
    change TotalSpace.mk ((p.2 : ℝ) : AddCircle L)
      ((cutTrivialization F E).symm (p.2 : ℝ) p.1) =
        Pullback.lift (cover L) ((cutTrivialization F E).toOpenPartialHomeomorph.symm (p.2, p.1))
    rw [← (cutTrivialization F E).mk_symm (cutTrivialization_covers F E p.2.2)]
    rfl
  rw [heq]
  exact (Pullback.continuous_lift F E (cover L)).comp
    (continuous_subtype_val.comp ((cutHomeomorph F E).symm.continuous.comp continuous_swap))

/-- The specific fiber chart induced by the cut trivialization. -/
def cutFiberChart (t : Icc (0 : ℝ) L) : E ((t : ℝ) : AddCircle L) ≃ₜ F :=
  (((FiberBundle.totalSpaceMk_isEmbedding F
      ((cover L : ℝ → AddCircle L) *ᵖ E) (t : ℝ)).toHomeomorph.trans
        (Homeomorph.setCongr (TotalSpace.range_mk (t : ℝ)))).trans
    ((cutTrivialization F E).preimageSingletonHomeomorph (cutTrivialization_covers F E t.2)))

theorem cutFiberChart_apply (t : Icc (0 : ℝ) L) (x : E ((t : ℝ) : AddCircle L)) :
    cutFiberChart F E t x = ((cutTrivialization F E) ⟨t, x⟩).2 := rfl

theorem cutFiberChart_symm (t : Icc (0 : ℝ) L) (x : F) :
    (cutFiberChart F E t).symm x = (cutTrivialization F E).symm (t : ℝ) x := by
  apply (cutFiberChart F E t).injective
  rw [(cutFiberChart F E t).apply_symm_apply, cutFiberChart_apply,
    (cutTrivialization F E).apply_mk_symm (cutTrivialization_covers F E t.2)]

theorem cutMap_fiber_injective (t : Icc (0 : ℝ) L) :
    Injective (fun x : F => cutMap F E (x,t)) := by
  intro x y h
  have he := TotalSpace.mk_injective ((t : ℝ) : AddCircle L) h
  rw [← cutFiberChart_symm F E t x, ← cutFiberChart_symm F E t y] at he
  exact (cutFiberChart F E t).symm.injective he

end PoincareConjecture.Topology.FiberSaturation.CircleBundle
