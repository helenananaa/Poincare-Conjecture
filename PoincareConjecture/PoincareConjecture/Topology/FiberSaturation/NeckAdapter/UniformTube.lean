import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.NeckAdapter
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Compactness of the central slice gives a uniform positive-width collar inside an open neck. -/
theorem compact_cross_section_uniform_neck_width
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (U : Set (X × ℝ)) (hU : IsOpen U) (c : ℝ)
    (hcenter : ∀ x : X, (x,c) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ (univ ×ˢ Ioo (c-r) (c+r) : Set (X × ℝ)) ⊆ U :=
/- SWARM_PROOF_BEGIN -/
by
  -- Vacuous when the cross-section is empty: any positive width works.
  by_cases hX : IsEmpty X
  · refine ⟨1, one_pos, ?_⟩
    intro p hp
    exact (hX.false p.1).elim
  -- Compact slice `{c}` and compact `univ` give a product neighborhood inside `U`.
  have hslice : (univ : Set X) ×ˢ ({c} : Set ℝ) ⊆ U := by
    simpa [prod_singleton, range_subset_iff] using hcenter
  obtain ⟨W, V, -, hV, hW, hsing, hWV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU hslice
  -- Fit a symmetric open interval into the uniform neighborhood of `c`.
  obtain ⟨a, b, hcI, hIV⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds (hsing (mem_singleton c)))
  refine ⟨min (c - a) (b - c), lt_min (sub_pos.mpr hcI.1) (sub_pos.mpr hcI.2), ?_⟩
  refine (prod_mono hW ?_).trans hWV
  refine (Ioo_subset_Ioo ?_ ?_).trans hIV
  · linarith [min_le_left (c - a) (b - c)]
  · linarith [min_le_right (c - a) (b - c)]
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.NeckAdapter
