import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Arbitrarily small buffered coordinate balls centered at a prescribed point. -/
theorem coordinate_ball_in_neighborhood (M : ClosedThreeManifold.{u})
    (x : M) (U : Set M) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ b : CoordinateBall M, b.parametrization 0 = x ∧
      b.parametrization '' Metric.closedBall (0 : Euclidean3) 2 ⊆ U :=
/- SWARM_PROOF_BEGIN -/
by
  let c : OpenPartialHomeomorph M Euclidean3 := chartAt Euclidean3 x
  have hxsource : x ∈ c.source := by
    exact mem_chart_source Euclidean3 x
  let V : Set Euclidean3 := c '' (U ∩ c.source)
  have hVopen : IsOpen V := by
    exact c.isOpen_image_of_subset_source (hU.inter c.open_source) inter_subset_right
  have hcx : c x ∈ V := by
    exact ⟨x, ⟨hx, hxsource⟩, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVopen (c x) hcx
  let a : ℝ := r / 3
  have ha : 0 < a := by positivity
  let h : Euclidean3 ≃ₜ Euclidean3 :=
    (Homeomorph.smulOfNeZero a ha.ne').trans (Homeomorph.addLeft (c x))
  let p : OpenPartialHomeomorph Euclidean3 M := h.toOpenPartialHomeomorph.trans c.symm
  have hclosed : Metric.closedBall 0 2 ⊆ p.source := by
    rw [OpenPartialHomeomorph.trans_source]
    intro y hy
    have hyV : h y ∈ V := by
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
    have hyV' : h y ∈ c.target := by
      rcases hyV with ⟨z, hz, hzy⟩
      exact hzy ▸ c.map_source hz.2
    exact ⟨by simp, hyV'⟩
  let b : CoordinateBall M := ⟨p, hclosed⟩
  refine ⟨b, ?_, ?_⟩
  · change c.symm (h 0) = x
    dsimp [h]
    simpa using c.left_inv hxsource
  · rintro z ⟨q, hq, rfl⟩
    change p q ∈ U
    have hzV : h q ∈ V := by
      apply hball
      rw [Metric.mem_ball]
      change dist (c x + a • q) (c x) < r
      rw [dist_comm, dist_eq_norm]
      rw [show c x - (c x + a • q) = -(a • q) by abel, norm_neg]
      calc
        ‖a • q‖ = a * ‖q‖ := by rw [norm_smul, Real.norm_of_nonneg ha.le]
        _ ≤ a * 2 :=
          (mul_le_mul_of_nonneg_left
            (by simpa [Metric.mem_closedBall] using hq : ‖q‖ ≤ 2) ha.le)
        _ < r := by dsimp [a]; linarith
    rcases hzV with ⟨w, hw, hzw⟩
    have hwsource : w ∈ c.source := hw.2
    change c.symm (h q) ∈ U
    have : c.symm (h q) = w := by
      rw [← hzw]
      exact c.left_inv hwsource
    rw [this]
    exact hw.1
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
