import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- The explicit upper/lower hemisphere map lands on the actual unit sphere. -/
theorem doubleBall_raw_norm (upper : Bool) (x : Ball) : ‖raw upper x‖ = 1 :=
/- SWARM_PROOF_BEGIN -/
by
  have hx : ‖(x : Euclidean3)‖ ≤ 1 := by
    have hp : dist (x : Euclidean3) 0 ≤ 1 := by
      simpa only [Metric.mem_closedBall] using x.property
    simpa only [dist_zero_right] using hp
  have hrad : 0 ≤ 1 - ‖(x : Euclidean3)‖ ^ 2 := by
    nlinarith [norm_nonneg (x : Euclidean3)]
  have hsqrt : (Real.sqrt (1 - ‖(x : Euclidean3)‖ ^ 2)) ^ 2 =
      1 - ‖(x : Euclidean3)‖ ^ 2 := by
    exact Real.sq_sqrt hrad
  have hsq : ‖raw upper x‖ ^ 2 = 1 := by
    rw [norm_sq_split]
    rw [tail_raw]
    cases upper <;> simp [raw, hsqrt]
  cases upper with
  | false =>
      nlinarith [norm_nonneg (raw false x)]
  | true =>
      nlinarith [norm_nonneg (raw true x)]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
