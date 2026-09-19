import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- The normalized restriction of an actual full open collar is an open embedding onto its target. -/
theorem collarRestriction_isOpenEmbedding
    {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    (F : OpenPartialHomeomorph (X × ℝ) N)
    (hsource : F.source = (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1) :
    Topology.IsOpenEmbedding (collarRestriction F) ∧ range (collarRestriction F) = F.target :=
/- SWARM_PROOF_BEGIN -/
by
  let e : X × NeckParameter ≃ₜ F.source :=
    { toFun := fun z =>
        ⟨(z.1, (z.2 : ℝ)), by
          rw [hsource]
          exact ⟨mem_univ _, z.2.property⟩⟩
      invFun := fun z =>
        (z.1.1, ⟨z.1.2, by
          have hz : z.val ∈ (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1 := by
            rw [← hsource]
            exact z.property
          exact hz.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk fun z => by
          rw [hsource]
          exact ⟨mem_univ _, z.2.property⟩
      continuous_invFun :=
        continuous_subtype_val.fst.prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk fun z => by
            have hz : z.val ∈ (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1 := by
              rw [← hsource]
              exact z.property
            exact hz.2) }
  have hcomp : collarRestriction F = F.source.restrict F ∘ e := rfl
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact F.isOpenEmbedding_restrict.comp e.isOpenEmbedding
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact F.map_source (by
        rw [hsource]
        exact ⟨mem_univ _, z.2.property⟩)
    · intro hy
      refine ⟨((F.symm y).1, ⟨(F.symm y).2, ?_⟩), ?_⟩
      · have hz : F.symm y ∈ F.source := F.map_target hy
        rw [hsource] at hz
        exact hz.2
      · change F (F.symm y) = y
        exact F.right_inv hy
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
