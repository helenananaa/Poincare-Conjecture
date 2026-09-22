import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- The two explicit hemispheres cover every point of the actual three-sphere. -/
theorem doubleBall_raw_covers (p : Sphere3) :
    ∃ (upper : Bool) (x : Ball), raw upper x = (p : E4) :=
/- SWARM_PROOF_BEGIN -/
by
  let q : E4 := (p : E4)
  let x : Euclidean3 := tail q
  have hqnorm : ‖q‖ = 1 := by
    simpa [q, Metric.mem_sphere, dist_zero_right] using p.property
  have hqnorm_sq : ‖q‖ ^ 2 = 1 := by
    rw [hqnorm]
    norm_num
  have hsplit := norm_sq_split q
  have hxnorm_sq : ‖x‖ ^ 2 ≤ 1 := by
    dsimp [x]
    nlinarith [sq_nonneg (q 0)]
  have hxnorm : ‖x‖ ≤ 1 := by
    have hxnonneg : 0 ≤ ‖x‖ := norm_nonneg x
    nlinarith
  have hrad : 0 ≤ 1 - ‖x‖ ^ 2 := by
    linarith
  have hq0sq : (q 0) ^ 2 = 1 - ‖x‖ ^ 2 := by
    dsimp [x]
    nlinarith
  have hroot : Real.sqrt (1 - ‖x‖ ^ 2) = |q 0| := by
    have hsqrt : 0 ≤ Real.sqrt (1 - ‖x‖ ^ 2) := Real.sqrt_nonneg _
    have habs : 0 ≤ |q 0| := abs_nonneg _
    have habssq : |q 0| ^ 2 = (q 0) ^ 2 := by simp
    nlinarith [Real.sq_sqrt hrad]
  rcases le_total 0 (q 0) with hp | hn
  · refine ⟨true, ⟨x, ?_⟩, ?_⟩
    · simpa [Metric.mem_closedBall, dist_zero_right] using hxnorm
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [raw, hroot, abs_of_nonneg hp]
        rfl
      · rfl
  · refine ⟨false, ⟨x, ?_⟩, ?_⟩
    · simpa [Metric.mem_closedBall, dist_zero_right] using hxnorm
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [raw, hroot, abs_of_nonpos hn]
        rfl
      · rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
