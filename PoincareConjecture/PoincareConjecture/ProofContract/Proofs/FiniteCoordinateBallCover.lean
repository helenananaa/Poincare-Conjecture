import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.OpenAnnulus
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Compactness gives a finite cover by actual relatively buffered coordinate balls. -/
theorem finite_coordinate_ball_cover (M : ClosedThreeManifold.{u}) :
    ∃ (n : ℕ) (b : Fin n → CoordinateBall M), ∀ x : M, ∃ i, x ∈ (b i).removed :=
/- SWARM_PROOF_BEGIN -/
by
  have hballs : ∀ x : M, ∃ b : CoordinateBall M,
      x ∈ b.removed ∧ IsOpen b.removed := by
    intro x
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
    let b : CoordinateBall M := ⟨p, hclosed⟩
    have hmem : x ∈ b.removed := by
      change x ∈ p '' Metric.ball 0 1
      refine ⟨0, by simp, ?_⟩
      change c.symm (h 0) = x
      dsimp [h]
      simpa using c.left_inv hx
    have hclosed_one : Metric.closedBall (0 : Euclidean3) 1 ⊆
        Metric.closedBall 0 2 := by
      intro y hy
      have hy' : ‖y‖ ≤ (1 : ℝ) := by
        simpa [Metric.mem_closedBall] using hy
      simpa [Metric.mem_closedBall] using (show ‖y‖ ≤ (2 : ℝ) by linarith)
    have hsource : Metric.ball (0 : Euclidean3) 1 ⊆ p.source :=
      Metric.ball_subset_closedBall.trans (hclosed_one.trans hclosed)
    have hopen : IsOpen b.removed := by
      exact p.isOpen_image_of_subset_source Metric.isOpen_ball hsource
    exact ⟨b, hmem, hopen⟩
  choose B hBmem hBopen using hballs
  obtain ⟨t, ht⟩ := finite_cover_nhds (U := fun x : M => (B x).removed) (fun x =>
    (hBopen x).mem_nhds (hBmem x))
  refine ⟨t.card, fun i => B (t.equivFin.symm i).1, ?_⟩
  intro x
  have hx : x ∈ ⋃ y ∈ t, (B y).removed := by
    rw [ht]
    exact Set.mem_univ x
  rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
  rcases Set.mem_iUnion.mp hy with ⟨hyt, hxy⟩
  refine ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
  simpa using hxy
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
