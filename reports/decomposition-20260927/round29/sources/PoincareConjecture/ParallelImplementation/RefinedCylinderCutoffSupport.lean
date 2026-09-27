import PoincareConjecture.ProofContract.Refinement20260927.RadialExtensionLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCylinderCutoffSupport
open PoincareConjecture.ProofContract.Refinement20260927
theorem cylinder_cutoff_support : CylinderCutoffSupportStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro n f
  constructor
  · let K : Set CylinderAmbient :=
      Metric.closedBall (1 / 2 : ℝ) 3 ×ˢ
        Metric.closedBall (0 : PoincareConjecture.ProofContract.V1.Euclidean3) 2
    have hKcompact : IsCompact K := by
      dsimp [K]
      exact (isCompact_closedBall (1 / 2 : ℝ) 3).prod
        (isCompact_closedBall (0 : PoincareConjecture.ProofContract.V1.Euclidean3) 2)
    apply HasCompactSupport.of_support_subset_isCompact hKcompact
    change {z : CylinderAmbient | radialCylinderExtension f z ≠ 0} ⊆ K
    intro z hz
    have hcut : cylinderCutoff z ≠ 0 := by
      intro hzero
      apply hz
      simp [radialCylinderExtension, hzero]
    have htime : cylinderTimeCut z.1 ≠ 0 := by
      intro hzero
      apply hcut
      simp [cylinderCutoff, hzero]
    have hspace : cylinderSpaceCut (‖z.2‖ ^ 2) ≠ 0 := by
      intro hzero
      apply hcut
      simp [cylinderCutoff, hzero]
    have htimeball : z.1 ∈ Metric.ball (1 / 2 : ℝ) 2 := by
      have hm : z.1 ∈ Function.support cylinderTimeCut := by
        change cylinderTimeCut z.1 ≠ 0
        exact htime
      rw [cylinderTimeCut.support_eq] at hm
      simpa [cylinderTimeCut] using hm
    have hspaceball : ‖z.2‖ ^ 2 ∈ Metric.ball (1 : ℝ) (1 / 2) := by
      have hm : ‖z.2‖ ^ 2 ∈ Function.support cylinderSpaceCut := by
        change cylinderSpaceCut (‖z.2‖ ^ 2) ≠ 0
        exact hspace
      rw [cylinderSpaceCut.support_eq] at hm
      simpa [cylinderSpaceCut] using hm
    have htimebound : z.1 ∈ Metric.closedBall (1 / 2 : ℝ) 3 := by
      change dist z.1 (1 / 2 : ℝ) ≤ 3
      exact (Metric.mem_ball.mp htimeball).le.trans (by norm_num)
    have hspacebound : z.2 ∈
        Metric.closedBall (0 : PoincareConjecture.ProofContract.V1.Euclidean3) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hsq : ‖z.2‖ ^ 2 < 3 / 2 := by
        have hdist : |‖z.2‖ ^ 2 - 1| < 1 / 2 := by
          simpa only [Real.dist_eq] using Metric.mem_ball.mp hspaceball
        linarith [abs_lt.mp hdist]
      nlinarith [norm_nonneg z.2]
    exact Set.mem_prod.2 ⟨htimebound, hspacebound⟩
  · intro q hq
    have htarg : q.1 ∈ Metric.closedBall (1 / 2 : ℝ) 1 := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      rcases hq with ⟨h0, h1⟩
      constructor <;> linarith
    have ht : cylinderTimeCut q.1 = 1 := by
      apply cylinderTimeCut.one_of_mem_closedBall
      exact htarg
    have hp : ‖q.2.val‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using q.2.property
    have hsarg : ‖q.2.val‖ ^ 2 ∈ Metric.closedBall (1 : ℝ) (1 / 4) := by
      rw [hp]
      simp [Metric.mem_closedBall]
    have hs : cylinderSpaceCut (‖q.2.val‖ ^ 2) = 1 := by
      apply cylinderSpaceCut.one_of_mem_closedBall
      exact hsarg
    have hd : radialDirection q.2.val = q.2 := radialDirection_unit q.2
    change (cylinderTimeCut q.1 * cylinderSpaceCut (‖q.2.val‖ ^ 2)) •
      f (q.1, radialDirection q.2.val) = f q
    rw [ht, hs, hd]
    simp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCylinderCutoffSupport
