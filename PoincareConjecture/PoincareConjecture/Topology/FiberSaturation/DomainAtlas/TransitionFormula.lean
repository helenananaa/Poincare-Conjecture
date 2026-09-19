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

/-- The extended intrinsic transition is exactly the ambient one on its domain. -/
theorem transition_model_eq_ambient (a b : ModelDomainChart I K) :
    EqOn (I ∘ (a.intrinsic.symm.trans b.intrinsic) ∘ I.symm)
      (b.ambient ∘ a.ambient.symm) (transitionDomain a b) :=
/- SWARM_PROOF_BEGIN -/
by
  intro x hx
  have hxI : x ∈ range I := hx.2
  have hsrc : I.symm x ∈ a.intrinsic.target ∧
      a.intrinsic.symm (I.symm x) ∈ b.intrinsic.source := by
    simpa [OpenPartialHomeomorph.trans_source] using hx.1
  simp only [comp_apply, OpenPartialHomeomorph.trans_apply]
  rw [b.forward_eq _ hsrc.2, a.inverse_eq _ hsrc.1, I.right_inv hxI]
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
