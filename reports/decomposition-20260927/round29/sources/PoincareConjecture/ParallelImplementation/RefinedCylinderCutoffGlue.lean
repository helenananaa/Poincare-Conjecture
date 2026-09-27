import PoincareConjecture.ProofContract.Refinement20260927.RadialExtensionLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCylinderCutoffGlue
open PoincareConjecture.ProofContract.Refinement20260927
theorem cylinder_cutoff_glue : CylinderCutoffGlueStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro n a ha
  have hcut : ContDiff ℝ 1 cylinderCutoff := by
    unfold cylinderCutoff
    have htime : ContDiff ℝ 1 (fun z : CylinderAmbient => cylinderTimeCut z.1) := by
      exact cylinderTimeCut.contDiff.comp contDiff_fst
    have hnorm : ContDiff ℝ 1 (fun z : CylinderAmbient => ‖z.2‖ ^ 2) := by
      exact (contDiff_norm_sq ℝ).comp contDiff_snd
    have hspace : ContDiff ℝ 1 (fun z : CylinderAmbient =>
        cylinderSpaceCut (‖z.2‖ ^ 2)) := by
      exact cylinderSpaceCut.contDiff.comp hnorm
    exact htime.mul hspace
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 = 0
  · have hnear : ∀ᶠ w in nhds z, w.2 ∈ Metric.ball z.2 (1 / 2 : ℝ) :=
      continuous_snd.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by norm_num))
    have hzero : (fun w : CylinderAmbient => cylinderCutoff w • a w) =ᶠ[nhds z]
        fun _ => (0 : ApproxAmbient n) := by
      filter_upwards [hnear] with w hw
      have hn : ‖w.2‖ < (1 / 2 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, hz] using hw
      have hmul₁ : ‖w.2‖ * ‖w.2‖ ≤ ‖w.2‖ * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hn.le (norm_nonneg w.2)
      have hmul₂ : ‖w.2‖ * (1 / 2 : ℝ) < (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_right hn (by norm_num)
      have hsquare : ‖w.2‖ ^ 2 < (1 / 2 : ℝ) ^ 2 := by
        nlinarith
      have hdiff : ‖w.2‖ ^ 2 - 1 ≤ 0 := by
        nlinarith [sq_nonneg ‖w.2‖]
      have hdist : (1 / 2 : ℝ) ≤ |‖w.2‖ ^ 2 - 1| := by
        rw [abs_of_nonpos hdiff]
        nlinarith
      have hout : cylinderSpaceCut.rOut ≤ dist (‖w.2‖ ^ 2) (1 : ℝ) := by
        simpa [cylinderSpaceCut, dist_eq_norm, Real.norm_eq_abs] using hdist
      have hspacezero : cylinderSpaceCut (‖w.2‖ ^ 2) = 0 :=
        cylinderSpaceCut.zero_of_le_dist hout
      simp [cylinderCutoff, hspacezero]
    exact (contDiff_const.contDiffAt : ContDiffAt ℝ 1
      (fun _ : CylinderAmbient => (0 : ApproxAmbient n)) z).congr_of_eventuallyEq hzero
  · exact (hcut.contDiffAt.smul (ha z hz))
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCylinderCutoffGlue
