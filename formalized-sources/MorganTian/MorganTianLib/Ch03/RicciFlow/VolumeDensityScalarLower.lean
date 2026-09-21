import MorganTianLib.Ch03.RicciFlow.VolumeDistortion

open Set MeasureTheory Riemannian
open scoped ContDiff Manifold Topology ENNReal Bundle

noncomputable section
namespace MorganTianLib

/-- Only a lower scalar bound is needed for an upper volume-density estimate. -/
theorem volumeDensity_upper_of_scalar_lower
    {rho R : ℝ → ℝ} {T C t : ℝ}
    (hderiv : IsVolumeDensityEvolution rho R (Icc 0 T))
    (hlower : ∀ s ∈ Icc (0 : ℝ) T, -C ≤ R s)
    (hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ rho s)
    (ht : t ∈ Icc (0 : ℝ) T) :
    rho t ≤ Real.exp (C * t) * rho 0 := by
/- SWARM_PROOF_BEGIN -/
  let upper : ℝ → ℝ := fun s => Real.exp (-C * s) * rho s
  have hcont : ContinuousOn rho (Icc (0 : ℝ) T) := by
    intro s hs
    exact (hderiv s hs).continuousWithinAt
  have hupperCont : ContinuousOn upper (Icc (0 : ℝ) T) := by
    have he : ContinuousOn (fun s : ℝ => Real.exp (-C * s)) (Icc 0 T) := by
      fun_prop
    exact he.mul hcont
  have hupperDeriv (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      HasDerivWithinAt upper
        (Real.exp (-C * s) * (-C * rho s - R s * rho s))
        (interior (Icc 0 T)) s := by
    have hs' : s ∈ Icc (0 : ℝ) T := interior_subset hs
    have he : HasDerivAt (fun r : ℝ => Real.exp (-C * r))
        (-C * Real.exp (-C * s)) s := by
      convert (((hasDerivAt_id s).const_mul (-C)).exp) using 1 <;> simp [mul_comm]
    have hr : HasDerivAt rho (-R s * rho s) s :=
      (hderiv s hs').hasDerivAt (mem_interior_iff_mem_nhds.mp hs)
    exact ((he.mul hr).congr_deriv (by ring)).hasDerivWithinAt
  have hu (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      Real.exp (-C * s) * (-C * rho s - R s * rho s) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hb := hlower s (interior_subset hs)
    have hp := hpos s (interior_subset hs)
    nlinarith
  have huanti : AntitoneOn upper (Icc (0 : ℝ) T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hupperCont
      hupperDeriv hu
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have huc := huanti hz ht ht.1
  dsimp [upper] at huc
  simp only [mul_zero, Real.exp_zero, one_mul] at huc
  have hcancel : Real.exp (C * t) * Real.exp (-C * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring_nf
  calc
    rho t = Real.exp (C * t) * (Real.exp (-C * t) * rho t) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (C * t) * rho 0 :=
      mul_le_mul_of_nonneg_left huc (Real.exp_pos _).le
/- SWARM_PROOF_END -/

end MorganTianLib
