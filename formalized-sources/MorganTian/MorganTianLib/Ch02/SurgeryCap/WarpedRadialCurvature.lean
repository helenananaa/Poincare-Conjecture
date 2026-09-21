import MorganTianLib.Ch02.SurgeryCap.WarpedRadialConnection
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [T2Space N]
/-- **Math.** Actual radial curvature of the canonical Levi-Civita connection. -/
theorem warpedConnection_radial_curvature (g : RiemannianMetric I N)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hp : ∀ r, 0 < r → 0 < w r)
    (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
    ((warpedConnection g w hw hp).curvature (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N))) q =
        ((deriv (deriv w) q.2 / w q.2) • X q.1, 0) := by
/- SWARM_PROOF_BEGIN -/
  let R := coneRadialField (I := I) (N := N)
  let H := coneHorizontalLift X
  let f : N × ↥positiveReal → ℝ :=
    fun p => deriv w (p.2 : ℝ) / w (p.2 : ℝ)
  have hderiv : ContDiff ℝ ∞ (deriv w) :=
    (contDiff_infty_iff_deriv.mp hw).2
  have hnum : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : N × ↥positiveReal => deriv w (p.2 : ℝ)) :=
    hderiv.contMDiff.comp
      (contMDiff_subtype_val_opens.comp contMDiff_snd)
  have hden : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : N × ↥positiveReal => w (p.2 : ℝ)) :=
    hw.contMDiff.comp
      (contMDiff_subtype_val_opens.comp contMDiff_snd)
  have hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f := by
    dsimp [f]
    convert hnum.mul (hden.inv₀ (fun p => ne_of_gt (hp _ p.2.property))) using 1
    funext p
    rfl
  have hrad := warpedConnection_radial_formulas g w hw hp
  dsimp at hrad
  have hXR :
      (warpedConnection g w hw hp).cov H R =
        SmoothVectorField.smul f hf H := by
    apply SmoothVectorField.ext
    intro p
    rw [SmoothVectorField.smul_apply]
    change ((warpedConnection g w hw hp).cov
      (coneHorizontalLift X) (coneRadialField (I := I) (N := N))).toFun p =
      f p • (X p.1, (0 : ℝ))
    rw [Prod.smul_mk]
    simpa [f] using (hrad.2 X p).1
  have hRH :
      (warpedConnection g w hw hp).cov R H =
        SmoothVectorField.smul f hf H := by
    apply SmoothVectorField.ext
    intro p
    rw [SmoothVectorField.smul_apply]
    change ((warpedConnection g w hw hp).cov
      (coneRadialField (I := I) (N := N)) (coneHorizontalLift X)).toFun p =
      f p • (X p.1, (0 : ℝ))
    rw [Prod.smul_mk]
    simpa [f] using (hrad.2 X p).2
  have hRR :
      (warpedConnection g w hw hp).cov R R = 0 := by
    apply SmoothVectorField.ext
    intro p
    exact hrad.1 p
  have hbr : bracketField H R = 0 := by
    apply SmoothVectorField.ext
    intro p
    change bracketField (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) p = 0
    rw [bracketField_coneHorizontalLift_coneRadialField]
    rfl
  have hderivf (q : N × ↥positiveReal) :
      R.dir f q =
        (deriv (deriv w) (q.2 : ℝ) * w (q.2 : ℝ) -
          deriv w (q.2 : ℝ) * deriv w (q.2 : ℝ)) /
          w (q.2 : ℝ) ^ 2 := by
    have hwd : DifferentiableAt ℝ w (q.2 : ℝ) :=
      (hw.differentiable (by simp)).differentiableAt
    have hderivd : DifferentiableAt ℝ (deriv w) (q.2 : ℝ) :=
      (hderiv.differentiable (by simp)).differentiableAt
    have hquot : HasDerivAt (fun r : ℝ => deriv w r / w r)
        ((deriv (deriv w) (q.2 : ℝ) * w (q.2 : ℝ) -
          deriv w (q.2 : ℝ) * deriv w (q.2 : ℝ)) /
          w (q.2 : ℝ) ^ 2) (q.2 : ℝ) := by
      exact hderivd.hasDerivAt.div hwd.hasDerivAt
        (ne_of_gt (hp _ q.2.property))
    rw [coneRadialField_dir hf q]
    have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun r : ℝ => deriv w r / w r) (q.2 : ℝ)
        (ContinuousLinearMap.toSpanSingleton ℝ
          ((deriv (deriv w) (q.2 : ℝ) * w (q.2 : ℝ) -
            deriv w (q.2 : ℝ) * deriv w (q.2 : ℝ)) /
            w (q.2 : ℝ) ^ 2)) :=
      hquot.hasFDerivAt.hasMFDerivAt
    have hv : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (Subtype.val : ↥positiveReal → ℝ) q.2
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (Subtype.val : ↥positiveReal → ℝ) q.2) :=
      (contMDiff_subtype_val_opens.mdifferentiableAt (by simp)).hasMFDerivAt
    have hc := hmf.comp q.2 hv
    rw [show (fun r : ↥positiveReal => f (q.1, r)) =
        (fun r : ℝ => deriv w r / w r) ∘
          (Subtype.val : ↥positiveReal → ℝ) by rfl]
    rw [hc.mfderiv, ContinuousLinearMap.comp_apply]
    have hval : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (Subtype.val : ↥positiveReal → ℝ) q.2) (1 : ℝ) = (1 : ℝ) := by
      rw [mfderiv_subtype_val_opens]
      rfl
    rw [hval]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  rw [(warpedConnection g w hw hp).curvature_apply H R R]
  rw [hXR, hRR, hbr, (warpedConnection g w hw hp).cov_zero_right,
    (warpedConnection g w hw hp).cov_zero_left,
    (warpedConnection g w hw hp).cov_smul_right hf R H, hRH]
  simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
  rw [hderivf q]
  simp only [H, coneHorizontalLift_apply, sub_zero, add_zero]
  change f q • (f q • (X q.1, (0 : ℝ))) +
      ((deriv (deriv w) (q.2 : ℝ) * w (q.2 : ℝ) -
        deriv w (q.2 : ℝ) * deriv w (q.2 : ℝ)) /
        w (q.2 : ℝ) ^ 2) • (X q.1, (0 : ℝ)) =
      (((deriv (deriv w) (q.2 : ℝ) / w (q.2 : ℝ)) • X q.1), (0 : ℝ))
  dsimp [f]
  apply Prod.ext
  · change
      (deriv w (q.2 : ℝ) / w (q.2 : ℝ)) •
          ((deriv w (q.2 : ℝ) / w (q.2 : ℝ)) • X q.1) +
        ((deriv (deriv w) (q.2 : ℝ) * w (q.2 : ℝ) -
          deriv w (q.2 : ℝ) * deriv w (q.2 : ℝ)) /
          w (q.2 : ℝ) ^ 2) • X q.1 =
      (deriv (deriv w) (q.2 : ℝ) / w (q.2 : ℝ)) • X q.1
    rw [smul_smul, ← add_smul]
    congr 1
    field_simp [ne_of_gt (hp _ q.2.property)]
    ring_nf
  · simp
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
