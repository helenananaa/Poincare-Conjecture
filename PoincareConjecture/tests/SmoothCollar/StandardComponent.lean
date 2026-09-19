import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- The nontrivial complementary component and its frontier in the Euclidean test case. -/
theorem standard_upper_component_geometry
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    connectedComponentIn ({z : V × ℝ | z.2 ≤ 0}ᶜ) (0, 1) = {z | 0 < z.2} ∧
    frontier (connectedComponentIn ({z : V × ℝ | z.2 ≤ 0}ᶜ) (0, 1)) =
      {z | z.2 = 0} :=
/- SWARM_PROOF_BEGIN -/
by
  have hcompl : ({z : V × ℝ | z.2 ≤ 0}ᶜ : Set (V × ℝ)) = univ ×ˢ Ioi (0 : ℝ) := by
    ext z
    simp
  have hupper : ({z : V × ℝ | 0 < z.2} : Set (V × ℝ)) = univ ×ˢ Ioi (0 : ℝ) := by
    ext z
    simp
  have hpre : IsPreconnected ((univ : Set V) ×ˢ Ioi (0 : ℝ)) :=
    isPreconnected_univ.prod isPreconnected_Ioi
  have hmem : ((0 : V), (1 : ℝ)) ∈ (univ : Set V) ×ˢ Ioi (0 : ℝ) :=
    ⟨mem_univ _, by norm_num⟩
  constructor
  · rw [hcompl, hupper]
    exact hpre.connectedComponentIn hmem
  · rw [hcompl, hpre.connectedComponentIn hmem, frontier, closure_prod_eq, interior_prod_eq,
      closure_univ, interior_univ, closure_Ioi, interior_Ioi]
    ext z
    simp [and_comm, le_antisymm_iff]
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
