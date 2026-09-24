import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
 theorem forcing_jet_eq_of_value_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T alpha : ℝ) (a b : ForcingJet V T)
    (ha : a ∈ forcingGraph V T alpha) (hb : b ∈ forcingGraph V T alpha)
    (h : ∀ p : Slab T, a.1 p = b.1 p) :
    a = b :=
/- SWARM_PROOF_BEGIN -/
by
  apply Prod.ext
  · apply BoundedContinuousFunction.ext
    exact h
  · apply BoundedContinuousFunction.ext
    intro p
    rw [ha p, hb p, h p.1.1, h p.1.2]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
