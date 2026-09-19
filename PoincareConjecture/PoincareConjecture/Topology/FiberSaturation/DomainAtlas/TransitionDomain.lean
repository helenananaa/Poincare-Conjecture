import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- Intrinsic overlap points lie in the genuine ambient transition domain. -/
theorem transitionDomain_subset_ambient (a b : ModelDomainChart I K) :
    transitionDomain a b ⊆ (a.ambient.symm.trans b.ambient).source :=
/- SWARM_PROOF_BEGIN -/
by
  intro z hz
  obtain ⟨hz_src, hz_range⟩ := hz
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz_src ⊢
  obtain ⟨h_tgt, h_src⟩ := hz_src
  have hI : I (I.symm z) = z := I.right_inv hz_range
  constructor
  · rw [a.target_eq] at h_tgt
    simpa [hI] using h_tgt
  · have hy : I.symm z ∈ a.intrinsic.target := h_tgt
    rw [b.source_eq] at h_src
    simpa [a.inverse_eq (I.symm z) hy, hI] using h_src
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
