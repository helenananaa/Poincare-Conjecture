import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Every allowed manifold has a coordinate ball with the required larger chart neighborhood. -/
theorem coordinate_ball_exists (M : ClosedThreeManifold.{u}) : Nonempty (CoordinateBall M) :=
/- SWARM_PROOF_BEGIN -/
by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  let c : OpenPartialHomeomorph M Euclidean3 := chartAt Euclidean3 x
  have hx : x ∈ c.source := by
    exact mem_chart_source Euclidean3 x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) (c.map_source hx)
  let a : ℝ := r / 3
  have ha : 0 < a := by positivity
  let h : Euclidean3 ≃ₜ Euclidean3 :=
    (Homeomorph.smulOfNeZero a ha.ne').trans (Homeomorph.addLeft (c x))
  let p : OpenPartialHomeomorph Euclidean3 M := h.toOpenPartialHomeomorph.trans c.symm
  have hclosed : Metric.closedBall 0 2 ⊆ p.source := by
    rw [OpenPartialHomeomorph.trans_source]
    intro y hy
    have hy' : y ∈ h ⁻¹' c.symm.source := by
      change h y ∈ c.symm.source
      change h y ∈ c.target
      apply hball
      rw [Metric.mem_ball]
      change dist (c x + a • y) (c x) < r
      rw [dist_comm, dist_eq_norm]
      rw [show c x - (c x + a • y) = -(a • y) by abel, norm_neg]
      calc
        ‖a • y‖ = a * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg ha.le]
        _ ≤ a * 2 :=
          (mul_le_mul_of_nonneg_left
            (by simpa [Metric.mem_closedBall] using hy : ‖y‖ ≤ 2) ha.le)
        _ < r := by dsimp [a]; linarith
    exact ⟨by simp, hy'⟩
  exact ⟨⟨p, hclosed⟩⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
