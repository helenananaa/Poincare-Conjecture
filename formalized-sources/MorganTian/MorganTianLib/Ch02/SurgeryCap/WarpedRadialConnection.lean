import MorganTianLib.Ch02.SurgeryCap.WarpedConnection
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [T2Space N]
/-- **Math.** The radial-sector connection identities for the constructed metric. -/
theorem warpedConnection_radial_formulas (g : RiemannianMetric I N)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hp : ∀ r, 0 < r → 0 < w r) :
    let nabla := warpedConnection g w hw hp
    let radial := coneRadialField (I := I) (N := N)
    (∀ q : N × ↥positiveReal, (nabla.cov radial radial) q = 0) ∧
    ∀ (X : SmoothVectorField I N) (q : N × ↥positiveReal),
      (nabla.cov (coneHorizontalLift X) radial) q =
        ((deriv w q.2 / w q.2) • X q.1, 0) ∧
      (nabla.cov radial (coneHorizontalLift X)) q =
        ((deriv w q.2 / w q.2) • X q.1, 0) := by
/- SWARM_PROOF_BEGIN -/
  let G := warpedMetric g w hw hp
  let R := coneRadialField (I := I) (N := N)
  have hwc : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : N × ↥positiveReal => w (p.2 : ℝ)) :=
    hw.contMDiff.comp (contMDiff_subtype_val_opens.comp contMDiff_snd)
  have hHH (X Y : SmoothVectorField I N) (q : N × ↥positiveReal) :
      G.metricInner q (coneHorizontalLift X q) (coneHorizontalLift Y q) =
        w (q.2 : ℝ) ^ 2 * g.metricInner q.1 (X q.1) (Y q.1) := by
    change (warpedMetric g w hw hp).metricInner q
      (coneHorizontalLift X q) (coneHorizontalLift Y q) = _
    rw [warpedMetric_metricInner_prod]
    simp [coneHorizontalLift_apply]
  have hHR (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
      G.metricInner q (coneHorizontalLift X q) (R q) = 0 := by
    change (warpedMetric g w hw hp).metricInner q
      (coneHorizontalLift X q) (coneRadialField q) = 0
    rw [warpedMetric_metricInner_prod]
    simp [coneHorizontalLift_apply, coneRadialField_apply]
  have hRR (q : N × ↥positiveReal) :
      G.metricInner q (R q) (R q) = 1 := by
    change (warpedMetric g w hw hp).metricInner q
      (coneRadialField q) (coneRadialField q) = 1
    rw [warpedMetric_metricInner_prod]
    simp [coneRadialField_apply]
  have hAnyR (q : N × ↥positiveReal)
      (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
      G.metricInner q v (R q) = v.2 := by
    change (warpedMetric g w hw hp).metricInner q v
      (coneRadialField q) = v.2
    rw [warpedMetric_metricInner_prod]
    simp [coneRadialField_apply, g.metricInner_zero_right]
  have hdirHH (X Y Z : SmoothVectorField I N) (q : N × ↥positiveReal) :
      (coneHorizontalLift X).dir
          (fun p => G.metricInner p (coneHorizontalLift Y p)
            (coneHorizontalLift Z p)) q =
        w (q.2 : ℝ) ^ 2 * X.dir
          (fun p => g.metricInner p (Y p) (Z p)) q.1 := by
    rw [coneHorizontalLift_dir X
      (G.metricInner_field_contMDiff (coneHorizontalLift Y)
        (coneHorizontalLift Z)) q]
    have hslice : (fun x => G.metricInner (x, q.2)
        (coneHorizontalLift Y (x, q.2))
        (coneHorizontalLift Z (x, q.2))) =
        (fun x => w (q.2 : ℝ) ^ 2 *
          g.metricInner x (Y x) (Z x)) := by
      funext x
      exact hHH Y Z (x, q.2)
    rw [hslice]
    exact X.dir_const_mul _ q.1
      (g.metricInner_field_mdifferentiableAt Y Z q.1)
  have hdirHR (A : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) (X : SmoothVectorField I N)
      (q : N × ↥positiveReal) :
      A.dir (fun p => G.metricInner p (coneHorizontalLift X p) (R p)) q = 0 := by
    have hz : (fun p => G.metricInner p (coneHorizontalLift X p) (R p)) =
        (fun _ => 0) := by
      funext p
      exact hHR X p
    rw [hz, SmoothVectorField.dir, mfderiv_const]
    rfl
  have hdirRH (A : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) (X : SmoothVectorField I N)
      (q : N × ↥positiveReal) :
      A.dir (fun p => G.metricInner p (R p) (coneHorizontalLift X p)) q = 0 := by
    have hz : (fun p => G.metricInner p (R p) (coneHorizontalLift X p)) =
        (fun _ => 0) := by
      funext p
      rw [G.metricInner_comm]
      exact hHR X p
    rw [hz, SmoothVectorField.dir, mfderiv_const]
    rfl
  have hdirRR (A : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) (q : N × ↥positiveReal) :
      A.dir (fun p => G.metricInner p (R p) (R p)) q = 0 := by
    have hone : (fun p => G.metricInner p (R p) (R p)) =
        (fun _ => 1) := by
      funext p
      exact hRR p
    rw [hone, SmoothVectorField.dir, mfderiv_const]
    rfl
  have hdirW (q : N × ↥positiveReal) :
      R.dir (fun p => w (p.2 : ℝ)) q = deriv w (q.2 : ℝ) := by
    have hwd : DifferentiableAt ℝ w (q.2 : ℝ) :=
      (hw.differentiable (by simp)).differentiableAt
    have hmf_w : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) w (q.2 : ℝ)
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv w (q.2 : ℝ))) :=
      hwd.hasDerivAt.hasFDerivAt.hasMFDerivAt
    rw [coneRadialField_dir hwc q]
    have hmf : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun r : ↥positiveReal => w (r : ℝ)) q.2 (1 : ℝ) =
          deriv w (q.2 : ℝ) := by
      have hv : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (Subtype.val : ↥positiveReal → ℝ) q.2
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
            (Subtype.val : ↥positiveReal → ℝ) q.2) :=
        (contMDiff_subtype_val_opens.mdifferentiableAt (by simp)).hasMFDerivAt
      have hc := hmf_w.comp q.2 hv
      rw [show (fun r : ↥positiveReal => w (r : ℝ)) =
        w ∘ (Subtype.val : ↥positiveReal → ℝ) by rfl]
      rw [hc.mfderiv, ContinuousLinearMap.comp_apply]
      have hval : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (Subtype.val : ↥positiveReal → ℝ) q.2) (1 : ℝ) = (1 : ℝ) := by
        rw [mfderiv_subtype_val_opens]
        rfl
      rw [hval]
      exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ
        (deriv w (q.2 : ℝ))
    simpa only [Prod.snd] using hmf
  have hdirWsq (q : N × ↥positiveReal) :
      R.dir (fun p => w (p.2 : ℝ) ^ 2) q =
        2 * w (q.2 : ℝ) * deriv w (q.2 : ℝ) := by
    have hmul := R.dir_mul q
      (hwc.mdifferentiableAt (by simp)) (hwc.mdifferentiableAt (by simp))
    have hprod : (fun p : N × ↥positiveReal =>
        w (p.2 : ℝ) * w (p.2 : ℝ)) =
        (fun p => w (p.2 : ℝ) ^ 2) := by
      funext p
      ring
    rw [hprod] at hmul
    rw [hdirW q] at hmul
    calc
      _ = w (q.2 : ℝ) * deriv w (q.2 : ℝ) +
          w (q.2 : ℝ) * deriv w (q.2 : ℝ) := hmul
      _ = _ := by ring
  have hdirRHH (Y Z : SmoothVectorField I N)
      (q : N × ↥positiveReal) :
      R.dir (fun p => G.metricInner p (coneHorizontalLift Y p)
        (coneHorizontalLift Z p)) q =
        2 * w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner q.1 (Y q.1) (Z q.1) := by
    let basePair : N → ℝ := fun p => g.metricInner p (Y p) (Z p)
    have hbase : ContMDiff I 𝓘(ℝ, ℝ) ∞ basePair :=
      g.metricInner_field_contMDiff Y Z
    have hshape :
        (fun p => G.metricInner p (coneHorizontalLift Y p)
          (coneHorizontalLift Z p)) =
        (fun p : N × ↥positiveReal =>
          w (p.2 : ℝ) ^ 2 * (basePair ∘ Prod.fst) p) := by
      funext p
      rw [hHH]
      rfl
    rw [hshape, R.dir_mul q
      (((hwc.pow 2).mdifferentiableAt (by simp)))
      ((hbase.comp contMDiff_fst).mdifferentiableAt (by simp)),
      hdirWsq q, coneRadialField_dir_comp_fst hbase]
    change w (q.2 : ℝ) ^ 2 * 0 +
        g.metricInner q.1 (Y q.1) (Z q.1) *
          (2 * w (q.2 : ℝ) * deriv w (q.2 : ℝ)) = _
    ring
  have hbrHR (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
      DCLieBracket (coneHorizontalLift X) R q = 0 := by
    change bracketField (coneHorizontalLift X) R q = 0
    rw [bracketField_coneHorizontalLift_coneRadialField]
    rfl
  have hbrRH (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
      DCLieBracket R (coneHorizontalLift X) q = 0 := by
    change bracketField R (coneHorizontalLift X) q = 0
    rw [bracketField_coneRadialField_coneHorizontalLift]
    rfl
  have hbrRR (q : N × ↥positiveReal) :
      DCLieBracket R R q = 0 := by
    change bracketField R R q = 0
    rw [bracketField_coneRadialField_self]
    rfl
  have hbrHH (X Y : SmoothVectorField I N) (q : N × ↥positiveReal) :
      DCLieBracket (coneHorizontalLift X) (coneHorizontalLift Y) q =
        coneHorizontalLift (bracketField X Y) q := by
    change bracketField (coneHorizontalLift X) (coneHorizontalLift Y) q = _
    rw [bracketField_coneHorizontalLift_coneHorizontalLift]
  have hK_RHH (X Z : SmoothVectorField I N)
      (q : N × ↥positiveReal) :
      G.koszulRHS (coneRadialField (I := I) (N := N))
          (coneHorizontalLift X) (coneHorizontalLift Z) q =
        2 * w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner q.1 (X q.1) (Z q.1) := by
    unfold RiemannianMetric.koszulRHS
    rw [hdirRHH X Z q]
    rw [hdirHR (coneHorizontalLift X) Z q]
    rw [hdirRH (coneHorizontalLift Z) X q]
    rw [hbrRH Z q]
    rw [hbrHH X Z q]
    have hbrzero := hHR (bracketField X Z) q
    rw [hbrzero]
    rw [hbrRH X q]
    rw [G.metricInner_zero_left q (coneHorizontalLift Z q)]
    rw [G.metricInner_zero_left q (coneHorizontalLift X q)]
    ring
  have hK_HRH (X Z : SmoothVectorField I N)
      (q : N × ↥positiveReal) :
      G.koszulRHS (coneHorizontalLift X) R (coneHorizontalLift Z) q =
        2 * w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner q.1 (X q.1) (Z q.1) := by
    unfold RiemannianMetric.koszulRHS
    rw [hdirRH (coneHorizontalLift X) Z q, hdirRHH Z X q,
      hdirHR (coneHorizontalLift Z) X q, hbrHH X Z q,
      hHR (bracketField X Z) q, hbrRH Z q, hbrHR X q,
      G.metricInner_zero_left, G.metricInner_zero_left]
    rw [g.metricInner_comm q.1 (Z q.1) (X q.1)]
    ring_nf
  have hK_RRH (Z : SmoothVectorField I N) (q : N × ↥positiveReal) :
      G.koszulRHS R R (coneHorizontalLift Z) q = 0 := by
    unfold RiemannianMetric.koszulRHS
    rw [hdirRH R Z q, hdirHR R Z q, hdirRR (coneHorizontalLift Z) q,
      hbrRH Z q, hbrRR q]
    simp
  have hK_HRR (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
      G.koszulRHS (coneHorizontalLift X) R R q = 0 := by
    unfold RiemannianMetric.koszulRHS
    rw [hdirRR (coneHorizontalLift X) q, hdirRH R X q,
      hdirHR R X q, hbrHR X q, hbrRR q]
    simp
  have hK_RHR (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
      G.koszulRHS R (coneHorizontalLift X) R q = 0 := by
    unfold RiemannianMetric.koszulRHS
    rw [hdirHR R X q, hdirRR (coneHorizontalLift X) q,
      hdirRH R X q, hbrRR q, hbrHR X q, hbrRH X q]
    simp
  have hK_RRR (q : N × ↥positiveReal) :
      G.koszulRHS R R R q = 0 := by
    unfold RiemannianMetric.koszulRHS
    rw [hdirRR R q, hbrRR q]
    simp
  dsimp
  constructor
  · intro q
    rw [show (0 : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) =
      ((0 : TangentSpace I q.1), (0 : ℝ)) by rfl]
    apply Prod.ext
    · apply (g.metricInner_eq_iff_eq q.1 _ _).mp
      intro Z
      obtain ⟨W, hW⟩ := exists_smoothVectorField_eq (I := I) q.1 Z
      rw [← hW]
      have hc := G.koszulDualSection_dual R R
        (coneHorizontalLift W) q
      change 2 * G.metricInner q
          ((warpedConnection g w hw hp).cov R R q)
          (coneHorizontalLift W q) = G.koszulRHS R R
            (coneHorizontalLift W) q at hc
      rw [hK_RRH W q, warpedMetric_metricInner_prod,
        coneHorizontalLift_apply] at hc
      simp only [mul_zero, add_zero] at hc
      change g.metricInner q.1
          (((warpedConnection g w hw hp).cov
            (coneRadialField (I := I) (N := N))
            (coneRadialField (I := I) (N := N)) q).1) (W q.1) =
        g.metricInner q.1 (0 : TangentSpace I q.1) (W q.1)
      rw [g.metricInner_zero_left]
      have hw2 : 0 < w (q.2 : ℝ) ^ 2 :=
        sq_pos_of_pos (hp _ q.2.property)
      nlinarith
    · change ((warpedConnection g w hw hp).cov R R q).2 = 0
      have hc := G.koszulDualSection_dual R R R q
      change 2 * G.metricInner q
          ((warpedConnection g w hw hp).cov R R q) (R q) =
        G.koszulRHS R R R q at hc
      rw [hK_RRR q, hAnyR q] at hc
      linarith
  · intro X q
    constructor
    · apply Prod.ext
      · apply (g.metricInner_eq_iff_eq q.1 _ _).mp
        intro Z
        obtain ⟨W, hW⟩ := exists_smoothVectorField_eq (I := I) q.1 Z
        rw [← hW]
        have hc := G.koszulDualSection_dual R (coneHorizontalLift X)
          (coneHorizontalLift W) q
        change 2 * G.metricInner q
            ((warpedConnection g w hw hp).cov (coneHorizontalLift X) R q)
            (coneHorizontalLift W q) = G.koszulRHS R
              (coneHorizontalLift X) (coneHorizontalLift W) q at hc
        rw [hK_RHH X W q, warpedMetric_metricInner_prod,
          coneHorizontalLift_apply] at hc
        simp only [mul_zero, add_zero] at hc
        rw [g.metricInner_smul_left, div_mul_eq_mul_div]
        apply (eq_div_iff (ne_of_gt (hp _ q.2.property))).2
        have hcancel :
            (2 * w (q.2 : ℝ)) *
                (g.metricInner q.1
                  (((warpedConnection g w hw hp).cov
                    (coneHorizontalLift X) R (q.1, q.2)).1) (W q.1) *
                  w (q.2 : ℝ)) =
              (2 * w (q.2 : ℝ)) *
                (deriv w (q.2 : ℝ) * g.metricInner q.1 (X q.1) (W q.1)) := by
          calc
            _ = 2 * (w (q.2 : ℝ) ^ 2 *
                g.metricInner q.1
                  (((warpedConnection g w hw hp).cov
                    (coneHorizontalLift X) R (q.1, q.2)).1) (W q.1)) := by ring
            _ = _ := by simpa only [Prod.eta, mul_assoc] using hc
        exact mul_left_cancel₀
          (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
            (ne_of_gt (hp _ q.2.property))) hcancel
      · change ((warpedConnection g w hw hp).cov
            (coneHorizontalLift X) R q).2 = 0
        have hc := G.koszulDualSection_dual R (coneHorizontalLift X) R q
        change 2 * G.metricInner q
            ((warpedConnection g w hw hp).cov (coneHorizontalLift X) R q) (R q) =
          G.koszulRHS R (coneHorizontalLift X) R q at hc
        rw [hK_RHR X q, hAnyR q] at hc
        linarith
    · apply Prod.ext
      · apply (g.metricInner_eq_iff_eq q.1 _ _).mp
        intro Z
        obtain ⟨W, hW⟩ := exists_smoothVectorField_eq (I := I) q.1 Z
        rw [← hW]
        have hc := G.koszulDualSection_dual
          (coneHorizontalLift X) R (coneHorizontalLift W) q
        change 2 * G.metricInner q
            ((warpedConnection g w hw hp).cov R (coneHorizontalLift X) q)
            (coneHorizontalLift W q) = G.koszulRHS
              (coneHorizontalLift X) R (coneHorizontalLift W) q at hc
        rw [hK_HRH X W q, warpedMetric_metricInner_prod,
          coneHorizontalLift_apply] at hc
        simp only [mul_zero, add_zero] at hc
        rw [g.metricInner_smul_left, div_mul_eq_mul_div]
        apply (eq_div_iff (ne_of_gt (hp _ q.2.property))).2
        have hcancel :
            (2 * w (q.2 : ℝ)) *
                (g.metricInner q.1
                  (((warpedConnection g w hw hp).cov R
                    (coneHorizontalLift X) (q.1, q.2)).1) (W q.1) *
                  w (q.2 : ℝ)) =
              (2 * w (q.2 : ℝ)) *
                (deriv w (q.2 : ℝ) * g.metricInner q.1 (X q.1) (W q.1)) := by
          calc
            _ = 2 * (w (q.2 : ℝ) ^ 2 *
                g.metricInner q.1
                  (((warpedConnection g w hw hp).cov R
                    (coneHorizontalLift X) (q.1, q.2)).1) (W q.1)) := by ring
            _ = _ := by simpa only [Prod.eta, mul_assoc] using hc
        exact mul_left_cancel₀
          (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
            (ne_of_gt (hp _ q.2.property))) hcancel
      · change ((warpedConnection g w hw hp).cov R
            (coneHorizontalLift X) q).2 = 0
        have hc := G.koszulDualSection_dual
          (coneHorizontalLift X) R R q
        change 2 * G.metricInner q
            ((warpedConnection g w hw hp).cov R (coneHorizontalLift X) q) (R q) =
          G.koszulRHS (coneHorizontalLift X) R R q at hc
        rw [hK_HRR X q, hAnyR q] at hc
        linarith
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
