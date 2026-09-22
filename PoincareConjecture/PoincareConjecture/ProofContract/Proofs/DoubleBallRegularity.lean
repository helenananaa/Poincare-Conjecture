import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- Both concrete hemisphere parametrizations are continuous and injective. -/
theorem doubleBall_raw_regular (upper : Bool) : Continuous (raw upper) ∧ Injective (raw upper) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · unfold raw
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ ?_ i
    · dsimp
      fun_prop
    · intro i
      exact (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  · intro x y h
    apply Subtype.ext
    have ht := congrArg tail h
    simpa only [tail_raw] using ht
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
