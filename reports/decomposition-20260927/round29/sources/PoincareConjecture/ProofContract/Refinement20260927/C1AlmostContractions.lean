import PoincareConjecture.ProofContract.Refinement20260927.AcceptedFortyFive
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff
/-- **Math.** Smooth approximation has additive error, even when a source slice has zero energy. -/
theorem C1ClassMap.width_mul_checked {source target : IntrinsicSpectrumData.{u}}
    (h : C1ClassMap source.sweepouts target.sweepouts) (t L : ℝ) (hL : 0 < L)
    (hmetric : TargetMetricBound (source.metric t) (target.metric t) h.map L) :
    (target.spectrum checked_sphere_energy_continuity).width t ≤
      L * (source.spectrum checked_sphere_energy_continuity).width t := by
  let F := source.spectrum checked_sphere_energy_continuity
  let G := target.spectrum checked_sphere_energy_continuity
  have hi (i : source.sweepouts.Representative) : G.width t ≤ L * F.peak i t := by
    apply le_of_forall_pos_le_add
    intro eps heps
    obtain ⟨j,hj⟩ := (h.send i).approximate_checked (target.metric t) eps heps
    apply (G.width_le_peak j t).trans
    apply csSup_le (range_nonempty _)
    rintro _ ⟨s,rfl⟩
    have hs : ContMDiff (𝓡 2) SweepModel 1 (fun p : Sphere2 => ((s:ℝ),p)) :=
      contMDiff_const.prodMk contMDiff_id
    have hf : ContMDiff (𝓡 2) (𝓡 3) 1 (fun p : Sphere2 => i.val.map ((s:ℝ),p)) :=
      (i.val.smooth.of_le (by simp)).comp hs
    have hm := c1_sphere_energy_postcompose_le (source.metric t) (target.metric t)
      h.map h.c1 (fun p => i.val.map ((s:ℝ),p)) hf hmetric
    have hm' : sphereDirichletEnergy target.space (target.metric t)
        (fun p => (h.send i).continuousMap (s,p)) ≤ L * F.energy i t s := by
      change sphereDirichletEnergy target.space (target.metric t)
        (fun p => h.map (i.val.map ((s:ℝ),p))) ≤ L * F.energy i t s
      simpa only [IntrinsicSpectrumData.spectrum,intrinsicSpectrum,Function.comp_def,F] using hm
    exact (hj s).trans (add_le_add (hm'.trans
      (mul_le_mul_of_nonneg_left (F.energy_le_peak i t s) hL.le)) le_rfl)
  have hd : G.width t / L ≤ F.width t := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨i,rfl⟩
    exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hi i)
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hd
/-- **Math.** Class-preserving C1 maps may vary with the error; no limiting map is postulated. -/
def AlmostContractingC1ClassMaps (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ h : C1ClassMap source.sweepouts target.sweepouts,
    TargetMetricBound (source.metric t) (target.metric t) h.map (1+eta)
/-- **Math.** Arbitrarily small tensor distortion gives the exact width jump inequality. -/
theorem almostContractingC1_width_le {source target : IntrinsicSpectrumData.{u}}
    {t : ℝ} (h : AlmostContractingC1ClassMaps source target t) :
    (target.spectrum checked_sphere_energy_continuity).width t ≤
      (source.spectrum checked_sphere_energy_continuity).width t := by
  apply le_of_forall_pos_le_add
  intro eps heps
  let W := (source.spectrum checked_sphere_energy_continuity).width t
  have hW : 0 ≤ W := (source.spectrum checked_sphere_energy_continuity).width_nonneg t
  let eta := eps/(W+1)
  have heta : 0 < eta := div_pos heps (by linarith)
  obtain ⟨map,hmap⟩ := h eta heta
  have hm := map.width_mul_checked t (1+eta) (by linarith) hmap
  have he : eta*(W+1) = eps := div_mul_cancel₀ eps (by linarith)
  change (target.spectrum checked_sphere_energy_continuity).width t ≤ W+eps
  change (target.spectrum checked_sphere_energy_continuity).width t ≤ (1+eta)*W at hm
  nlinarith
#print axioms C1ClassMap.width_mul_checked
#print axioms almostContractingC1_width_le
end PoincareConjecture.ProofContract.Refinement20260927
