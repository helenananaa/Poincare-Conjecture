import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import PoincareConjecture.Topology.FiberSaturation.CollarClosureHalfSpace
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- A central collar point is a genuine frontier point of the complementary closure. -/
theorem oneSidedCollar_center_mem_frontier_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace X]
    {C : Set Y} {f : X × NeckParameter → Y} (hf : Topology.IsOpenEmbedding f)
    (hside : ∀ z, f z ∈ C ↔ (z.2 : ℝ) ≤ 0) {p : Y} {x : X}
    (hx : f (x, neckCenter) ∈ frontier (connectedComponentIn Cᶜ p)) (y : X) :
    f (y, neckCenter) ∈ frontier (closure (connectedComponentIn Cᶜ p)) :=
/- SWARM_PROOF_BEGIN -/
by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨?_, ?_⟩
  · rw [closure_closure]
    exact frontier_subset_closure (oneSidedCollar_frontier_saturated hf hside hx y)
  · let Neg : Set (X × NeckParameter) :=
      univ ×ˢ ((Subtype.val : NeckParameter → ℝ) ⁻¹' Ioo (-1 : ℝ) 0)
    have hyNeg : (y, neckCenter) ∈ closure Neg := by
      rw [closure_prod_eq, closure_univ]
      refine ⟨mem_univ _, ?_⟩
      have h :=
        (isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)).isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
          continuous_subtype_val (Ioo (-1 : ℝ) 0)
      rw [← h]
      change (0 : ℝ) ∈ closure (Ioo (-1 : ℝ) 0)
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
      constructor <;> norm_num
    have hlimit : f (y, neckCenter) ∈ closure (f '' Neg) :=
      image_closure_subset_closure_image hf.continuous ⟨(y, neckCenter), hyNeg, rfl⟩
    have hNeg : f '' Neg ⊆ (closure (connectedComponentIn Cᶜ p))ᶜ := by
      rintro _ ⟨z, hz, rfl⟩ hcl
      exact oneSidedCollar_negative_not_mem_closure hf hside z hz.2.2 hcl
    exact closure_mono hNeg hlimit
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
