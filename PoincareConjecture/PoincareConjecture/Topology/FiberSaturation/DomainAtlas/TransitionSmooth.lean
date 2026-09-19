import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.TransitionDomain
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.TransitionFormula
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- Smooth ambient transitions restrict to the original corner model. -/
theorem restricted_transition_contDiffOn (a b : ModelDomainChart I K)
    (hs : ContDiffOn ℝ ∞ (b.ambient ∘ a.ambient.symm)
      (a.ambient.symm.trans b.ambient).source) :
    ContDiffOn ℝ ∞ (I ∘ (a.intrinsic.symm.trans b.intrinsic) ∘ I.symm)
      (transitionDomain a b) :=
/- SWARM_PROOF_BEGIN -/
by
  have hrestrict := hs.mono (transitionDomain_subset_ambient a b)
  exact hrestrict.congr (transition_model_eq_ambient a b)
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
