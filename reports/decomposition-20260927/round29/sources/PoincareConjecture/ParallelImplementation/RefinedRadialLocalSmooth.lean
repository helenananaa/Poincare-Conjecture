import PoincareConjecture.ProofContract.Refinement20260927.RadialExtensionLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedRadialLocalSmooth
open PoincareConjecture.ProofContract.Refinement20260927
theorem radial_local_smooth : RadialLocalSmoothStatement :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro x hx
  let E := PoincareConjecture.ProofContract.V1.Euclidean3
  let S := PoincareConjecture.ProofContract.V1.Sphere2
  letI : Fact (Module.finrank ℝ E = 2 + 1) :=
    ⟨by simp [E, PoincareConjecture.ProofContract.V1.Euclidean3]⟩
  let smoothOrder : WithTop (WithTop Nat) :=
    WithTop.some (⊤ : WithTop Nat)
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let r : ℝ := ‖x‖ / 2
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < ‖x‖ := by dsimp [r]; linarith
  let bump : ContDiffBump x :=
    ⟨‖x‖ / 4, r, by positivity, by dsimp [r]; linarith⟩
  let ψ : E → ℝ := fun y => bump y
  have hψ : ContDiff ℝ smoothOrder ψ := by
    exact bump.contDiff
  have hψbounds (y : E) : 0 ≤ ψ y ∧ ψ y ≤ 1 := by
    constructor
    · exact bump.nonneg
    · exact bump.le_one
  let z : E → E := fun y => x + ψ y • (y - x)
  have hzeroOutside (y : E) (hy : r ≤ dist y x) : ψ y = 0 := by
    change bump y = 0
    exact bump.zero_of_le_dist (by simpa [r] using hy)
  have hdisp (y : E) : dist (z y) x = ψ y * dist y x := by
    calc
      dist (z y) x = ‖z y - x‖ := dist_eq_norm _ _
      _ = ‖ψ y • (y - x)‖ := by
        congr 1
        dsimp [z]
        abel
      _ = ‖ψ y‖ * ‖y - x‖ := norm_smul _ _
      _ = ψ y * dist y x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψbounds y).1, dist_eq_norm]
  have hzNonzero (y : E) : z y ≠ 0 := by
    by_cases hy : dist y x < r
    · have hsmall : dist (z y) x ≤ dist y x := by
        rw [hdisp]
        calc
          ψ y * dist y x ≤ 1 * dist y x :=
            mul_le_mul_of_nonneg_right (hψbounds y).2 (dist_nonneg)
          _ = dist y x := one_mul _
      intro hzy
      have hbad : ‖x‖ < ‖x‖ := by
        calc
          ‖x‖ = dist (0 : E) x := by simp
          _ = dist (z y) x := by rw [hzy]
          _ ≤ dist y x := hsmall
          _ < r := hy
          _ < ‖x‖ := hrlt
      exact (lt_irrefl _ hbad).elim
    · have hψzero : ψ y = 0 := hzeroOutside y (le_of_not_gt hy)
      have hzy : z y = x := by simp [z, hψzero]
      intro h
      rw [hzy] at h
      exact hx h
  have hz : ContDiff ℝ smoothOrder z := by
    exact contDiff_const.add (hψ.smul (contDiff_id.sub contDiff_const))
  let w : E → E := fun y => (‖z y‖⁻¹ : ℝ) • z y
  have hw : ContDiff ℝ smoothOrder w := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hzAt := hz.contDiffAt (x := y)
    have hn : ContDiffAt ℝ smoothOrder (fun u : E => ‖z u‖) y :=
      hzAt.norm ℝ (hzNonzero y)
    have hi : ContDiffAt ℝ smoothOrder (fun u : E => ‖z u‖⁻¹) y :=
      hn.inv (by positivity [norm_pos_iff.mpr (hzNonzero y)])
    exact hi.smul hzAt
  have hwSphere (y : E) : w y ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg (z y)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hzNonzero y))]
  let d : E → S := Set.codRestrict w (Metric.sphere (0 : E) 1) hwSphere
  have hd : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) smoothOrder d := by
    exact ContMDiff.codRestrict_sphere hw.contMDiff hwSphere
  refine ⟨d, hd, ?_⟩
  intro y hy
  have hyball : dist y x < ‖x‖ / 4 := Metric.mem_ball.mp hy
  have hψone : ψ y = 1 := by
    change bump y = 1
    exact bump.one_of_mem_closedBall
      (Metric.mem_closedBall.mpr hyball.le)
  have hzy : z y = y := by simp [z, hψone]
  have hy0 : y ≠ 0 := by
    intro hy0
    have hbad : ‖x‖ < ‖x‖ := by
      calc
        ‖x‖ = dist (0 : E) x := by simp
        _ = dist y x := by rw [hy0]
        _ < ‖x‖ / 4 := hyball
        _ < ‖x‖ := by linarith
    exact (lt_irrefl _ hbad).elim
  apply Subtype.ext
  change (‖z y‖⁻¹ : ℝ) • z y = (radialDirection y : E)
  rw [hzy, radialDirection_coe y hy0]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedRadialLocalSmooth
