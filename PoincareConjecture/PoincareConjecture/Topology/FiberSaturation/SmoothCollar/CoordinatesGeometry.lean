import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Restriction
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.HalfSpaceRange

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Exact zero-contact collar coordinates straighten the actual complementary closure. -/
theorem collarCoordinates_component_geometry {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] [PreconnectedSpace X]
    (F : OpenPartialHomeomorph (X × ℝ) N)
    (hsource : F.source = (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1)
    {C : Set N} (hside : ∀ z ∈ F.source, F z ∈ C ↔ z.2 ≤ 0)
    {p : N} {x : X} (hx : F (x, 0) ∈ frontier (connectedComponentIn Cᶜ p))
    (a : OpenPartialHomeomorph X V) :
    (∀ z : X × NeckParameter, z.1 ∈ a.source →
      collarRestriction F z ∈ (collarCoordinates F a).source ∧
      collarCoordinates F a (collarRestriction F z) = (a z.1, (z.2 : ℝ))) ∧
    (collarCoordinates F a).IsImage (closure (connectedComponentIn Cᶜ p))
      (range (halfSpaceModel V)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨hf, _hrange⟩ := collarRestriction_isOpenEmbedding F hsource
  have hstrip (z : X × NeckParameter) : (z.1, (z.2 : ℝ)) ∈ F.source := by
    rw [hsource]
    exact ⟨mem_univ _, z.2.property⟩
  have hside' : ∀ z, collarRestriction F z ∈ C ↔ (z.2 : ℝ) ≤ 0 :=
    fun z => hside (z.1, (z.2 : ℝ)) (hstrip z)
  have hx' : collarRestriction F (x, neckCenter) ∈
      frontier (connectedComponentIn Cᶜ p) := by
    change F (x, (neckCenter : ℝ)) ∈ _
    simp [neckCenter]
    exact hx
  have hcl (z : X × NeckParameter) :
      collarRestriction F z ∈ closure (connectedComponentIn Cᶜ p) ↔ 0 ≤ (z.2 : ℝ) :=
    oneSidedCollar_mem_closure_component_iff_nonneg hf hside' hx' z
  have hcoord (z : X × NeckParameter) (hz : z.1 ∈ a.source) :
      collarRestriction F z ∈ (collarCoordinates F a).source ∧
        collarCoordinates F a (collarRestriction F z) = (a z.1, (z.2 : ℝ)) := by
    have hleft : F.symm (collarRestriction F z) = (z.1, (z.2 : ℝ)) :=
      F.left_inv (hstrip z)
    constructor
    · rw [collarCoordinates, OpenPartialHomeomorph.trans_source]
      constructor
      · rw [OpenPartialHomeomorph.symm_source]
        exact F.map_source (hstrip z)
      · change F.symm (collarRestriction F z) ∈
            (a.prod (Homeomorph.refl ℝ).toOpenPartialHomeomorph).source
        rw [hleft, OpenPartialHomeomorph.prod_source]
        exact ⟨hz, mem_univ _⟩
    · change (a.prod (Homeomorph.refl ℝ).toOpenPartialHomeomorph)
        (F.symm (collarRestriction F z)) = (a z.1, (z.2 : ℝ))
      rw [hleft, OpenPartialHomeomorph.prod_apply]
      rfl
  refine ⟨hcoord, fun y hy => ?_⟩
  rw [collarCoordinates, OpenPartialHomeomorph.trans_source] at hy
  have hyF : y ∈ F.target := by
    rw [OpenPartialHomeomorph.symm_source] at hy
    exact hy.1
  have hzIoo : (F.symm y).2 ∈ Ioo (-1 : ℝ) 1 := by
    have hzF : F.symm y ∈ F.source := F.map_target hyF
    rw [hsource] at hzF
    exact hzF.2
  set z : X × NeckParameter := ((F.symm y).1, ⟨(F.symm y).2, hzIoo⟩)
  have hza : z.1 ∈ a.source := by
    have hprod : F.symm y ∈
        (a.prod (Homeomorph.refl ℝ).toOpenPartialHomeomorph).source := hy.2
    rw [OpenPartialHomeomorph.prod_source] at hprod
    exact hprod.1
  have hyz : y = collarRestriction F z := (F.right_inv hyF).symm
  rw [hyz, (hcoord z hza).2, (halfSpaceModel_range_geometry (V := V)).1]
  exact (hcl z).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
