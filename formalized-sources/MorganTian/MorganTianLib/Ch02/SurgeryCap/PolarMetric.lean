import MorganTianLib.Ch02.SurgeryCap.PolarDiffeomorphism
import MorganTianLib.Ch02.SurgeryCap.GlobalCapGeometry

open Set Riemannian Bundle Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** Polar coordinates identify the actual global metric with the
constructed warped metric away from the tip. -/
theorem exists_cap_polar_metric_preserving (P : RoundCapProfile) :
    ∃ phi : Diffeomorph PuncturedCapModel (𝓡 3) PuncturedCap ↥capPuncturedSpace ∞,
      (∀ p : PuncturedCap, (phi p : E3) = (p.2 : ℝ) • (p.1 : E3)) ∧
      ∀ (p : PuncturedCap) (u v : TangentSpace PuncturedCapModel p),
        P.puncturedMetric.metricInner p u v =
          P.globalMetric.metricInner (phi p : E3)
            (mfderiv PuncturedCapModel (𝓡 3) (fun q => (phi q : E3)) p u)
            (mfderiv PuncturedCapModel (𝓡 3) (fun q => (phi q : E3)) p v) := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨phi, hphi, _⟩ := exists_cap_polar_diffeomorph
  refine ⟨phi, hphi, ?_⟩
  intro p u v
  rcases p with ⟨sigma, r⟩
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  let u₁T : TangentSpace (𝓡 2) sigma := by
    change TangentSpace (𝓡 2) sigma
    exact u₁
  let v₁T : TangentSpace (𝓡 2) sigma := by
    change TangentSpace (𝓡 2) sigma
    exact v₁
  let uT : TangentSpace PuncturedCapModel (sigma, r) := by
    change TangentSpace PuncturedCapModel (sigma, r)
    exact (u₁, u₂)
  let vT : TangentSpace PuncturedCapModel (sigma, r) := by
    change TangentSpace PuncturedCapModel (sigma, r)
    exact (v₁, v₂)
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let f : PuncturedCap → E3 := fun q => (q.2 : ℝ) • (q.1 : E3)
  have hf : ContMDiff PuncturedCapModel (𝓡 3) ∞ f := by
    exact (contMDiff_subtype_val.comp contMDiff_snd).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  have hfun : (fun q : PuncturedCap => (phi q : E3)) = f := by
    funext q
    exact hphi q
  let D : TangentSpace (𝓡 2) sigma →L[ℝ] E3 :=
    mvfderiv (𝓡 2) ((↑) : EpsilonNeckSphere → E3) sigma
  let K : TangentSpace PuncturedCapModel (sigma, r) → E3 := by
    intro w
    rcases w with ⟨w₁, w₂⟩
    exact (r : ℝ) • D w₁ + w₂ • (sigma : E3)
  have hderiv (w : TangentSpace PuncturedCapModel (sigma, r)) :
      mfderiv PuncturedCapModel (𝓡 3) f (sigma, r) w =
        (NormedSpace.fromTangentSpace (f (sigma, r))).symm
          (K w) := by
    rcases w with ⟨w₁, w₂⟩
    change TangentSpace (𝓡 2) sigma at w₁
    rw [mfderiv_prod_eq_add_apply (hf.mdifferentiableAt (by simp))]
    apply (NormedSpace.fromTangentSpace (f (sigma, r))).injective
    simp only [map_add, mvfderiv, ContinuousLinearMap.comp_apply]
    have hleft : mvfderiv (𝓡 2)
        (fun z : EpsilonNeckSphere => (r : ℝ) • (z : E3)) sigma
          (show TangentSpace (𝓡 2) sigma from w₁) =
        (r : ℝ) • D w₁ := by
      have hconst : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
          (fun _ : EpsilonNeckSphere => (r : ℝ)) sigma :=
        (contMDiff_const : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
          (fun _ : EpsilonNeckSphere => (r : ℝ))).mdifferentiableAt (by simp)
      have hcoe : MDifferentiableAt (𝓡 2) (𝓡 3)
          ((↑) : EpsilonNeckSphere → E3) sigma := by
        exact (contMDiff_coe_sphere (E := E3) (n := 2) (m := ∞)).mdifferentiableAt (by simp)
      have h := congrArg (fun L => L w₁) (mvfderiv_smul hconst hcoe)
      change mvfderiv (𝓡 2)
          ((fun _ : EpsilonNeckSphere => (r : ℝ)) •
            ((↑) : EpsilonNeckSphere → E3)) sigma w₁ = _
      simpa [mvfderiv_const, D] using h
    have hright : mvfderiv 𝓘(ℝ, ℝ)
        (fun t : ↥positiveReal => (t : ℝ) • (sigma : E3)) r
          (show TangentSpace 𝓘(ℝ, ℝ) r from w₂) =
        w₂ • (sigma : E3) := by
      have hval : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (Subtype.val : ↥positiveReal → ℝ) r :=
        (contMDiff_subtype_val_opens : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          (Subtype.val : ↥positiveReal → ℝ)).mdifferentiableAt (by simp)
      have hconst : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3)
          (fun _ : ↥positiveReal => (sigma : E3)) r :=
        (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞
          (fun _ : ↥positiveReal => (sigma : E3))).mdifferentiableAt (by simp)
      let w₂T : TangentSpace 𝓘(ℝ, ℝ) r := by
        change TangentSpace 𝓘(ℝ, ℝ) r
        exact w₂
      change mvfderiv 𝓘(ℝ, ℝ)
          ((Subtype.val : ↥positiveReal → ℝ) •
            (fun _ : ↥positiveReal => (sigma : E3))) r w₂T = _
      rw [mvfderiv_smul hval hconst]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply]
      change (r : ℝ) • (mvfderiv 𝓘(ℝ, ℝ)
          (fun _ : ↥positiveReal => (sigma : E3)) r) w₂T +
        (mvfderiv 𝓘(ℝ, ℝ)
          (Subtype.val : ↥positiveReal → ℝ) r) w₂T • (sigma : E3) = _
      have hscalar :
          (mvfderiv 𝓘(ℝ, ℝ)
            (Subtype.val : ↥positiveReal → ℝ) r) w₂T = w₂ := by
        change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) (r : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
            (Subtype.val : ↥positiveReal → ℝ) r w₂T) = w₂
        rw [mfderiv_subtype_val_opens]
        rfl
      rw [hscalar]
      simp [mvfderiv]
    change mvfderiv (𝓡 2)
        (fun z : EpsilonNeckSphere => (r : ℝ) • (z : E3)) sigma
          (show TangentSpace (𝓡 2) sigma from w₁) +
      mvfderiv 𝓘(ℝ, ℝ)
        (fun t : ↥positiveReal => (t : ℝ) • (sigma : E3)) r
          (show TangentSpace 𝓘(ℝ, ℝ) r from w₂) = _
    rw [hleft, hright]
    simp [K]
  rw [show (phi (sigma, r) : E3) = f (sigma, r) by exact hphi (sigma, r),
    mfderiv_congr hfun]
  rw [hderiv uT, hderiv vT]
  have hfrom_u :
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E3) (f (sigma, r))).symm
          (K uT) = K uT := by
    rfl
  have hfrom_v :
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E3) (f (sigma, r))).symm
          (K vT) = K vT := by
    rfl
  rw [hfrom_u, hfrom_v]
  change (warpedMetric unitRoundSphereMetric P.w P.smooth P.positive).metricInner
      (sigma, r) (u₁, u₂) (v₁, v₂) = _
  rw [warpedMetric_metricInner_prod]
  rw [P.globalMetric_formula]
  · rw [show f (sigma, r) = (r : ℝ) • (sigma : E3) by rfl]
    have hsigma : ‖(sigma : E3)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using sigma.property
    rw [show ‖(r : ℝ) • (sigma : E3)‖ = (r : ℝ) by
      calc
        ‖(r : ℝ) • (sigma : E3)‖ = ‖(r : ℝ)‖ * ‖(sigma : E3)‖ := norm_smul _ _
        _ = (r : ℝ) * 1 := by
          rw [Real.norm_eq_abs, abs_of_pos r.property, hsigma]
        _ = (r : ℝ) := by ring]
    change P.w (r : ℝ) ^ 2 * unitRoundSphereMetric.metricInner sigma u₁T v₁T +
        u₂ * v₂ = _
    have hu : inner ℝ (sigma : E3) (D u₁T) = 0 := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      rw [← range_mfderiv_coe_sphere (E := E3) (n := 2) sigma]
      exact ⟨u₁T, by rfl⟩
    have hv : inner ℝ (sigma : E3) (D v₁T) = 0 := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      rw [← range_mfderiv_coe_sphere (E := E3) (n := 2) sigma]
      exact ⟨v₁T, by rfl⟩
    rw [unitRoundSphereMetric]
    change P.w (r : ℝ) ^ 2 *
        DCInducedForm (DCEuclideanMetric (F := E3))
          ((↑) : EpsilonNeckSphere → E3) sigma u₁T v₁T + u₂ * v₂ = _
    rw [DCInducedForm_apply, DCEuclideanMetric_apply]
    change P.w (r : ℝ) ^ 2 * inner ℝ (D u₁T) (D v₁T) + u₂ * v₂ = _
    change P.w (r : ℝ) ^ 2 * inner ℝ (D u₁T) (D v₁T) + u₂ * v₂ =
      (P.w (r : ℝ) / (r : ℝ)) ^ 2 *
          inner ℝ ((r : ℝ) • D u₁T + u₂ • (sigma : E3))
            ((r : ℝ) • D v₁T + v₂ • (sigma : E3)) +
        (1 - (P.w (r : ℝ) / (r : ℝ)) ^ 2) / (r : ℝ) ^ 2 *
          inner ℝ ((r : ℝ) • (sigma : E3))
              ((r : ℝ) • D u₁T + u₂ • (sigma : E3)) *
          inner ℝ ((r : ℝ) • (sigma : E3))
              ((r : ℝ) • D v₁T + v₂ • (sigma : E3))
    have hss : inner ℝ (sigma : E3) (sigma : E3) = 1 := by
      rw [real_inner_self_eq_norm_sq]
      simpa using hsigma
    have hu' : inner ℝ (D u₁T) (sigma : E3) = 0 := by
      rw [real_inner_comm]
      exact hu
    have hv' : inner ℝ (D v₁T) (sigma : E3) = 0 := by
      rw [real_inner_comm]
      exact hv
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, smul_eq_mul]
    simp only [hu, hv, hu', hv', hss]
    have hr0 : (r : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < (r : ℝ) from r.property)
    field_simp [hr0]
    ring
  · exact (show (r : ℝ) • (sigma : E3) ≠ 0 by
      exact smul_ne_zero (ne_of_gt r.property)
        (Metric.ne_of_mem_sphere sigma.property one_ne_zero))
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
