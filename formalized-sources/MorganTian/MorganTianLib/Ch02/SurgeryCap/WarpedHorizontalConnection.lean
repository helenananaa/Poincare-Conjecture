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
/-- **Math.** The horizontal-horizontal covariant derivative for the actual
warped Levi-Civita connection, including its radial correction. -/
theorem warpedConnection_horizontal_formula (g : RiemannianMetric I N)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hp : ∀ r, 0 < r → 0 < w r)
    (X Y : SmoothVectorField I N) (q : N × ↥positiveReal) :
    ((warpedConnection g w hw hp).cov (coneHorizontalLift X) (coneHorizontalLift Y)) q =
      (((leviCivitaConnectionGeneral g).cov X Y) q.1,
        -(w q.2 * deriv w q.2 * g.metricInner q.1 (X q.1) (Y q.1))) := by
/- SWARM_PROOF_BEGIN -/
  let wm := warpedMetric g w hw hp
  let R : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) :=
    coneRadialField (I := I) (N := N)
  have hmetricHH (A B : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
      wm.metricInner (x, r) (coneHorizontalLift A (x, r))
          (coneHorizontalLift B (x, r)) =
        (w (r : ℝ)) ^ 2 * g.metricInner x (A x) (B x) := by
    rw [show wm = warpedMetric g w hw hp from rfl]
    change (warpedMetric g w hw hp).metricInner (x, r) (A x, 0) (B x, 0) = _
    rw [warpedMetric_metricInner_mk]
    simp
  have hmetricHR (A : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
      wm.metricInner (x, r) (coneHorizontalLift A (x, r)) (R (x, r)) = 0 := by
    rw [show wm = warpedMetric g w hw hp from rfl]
    change (warpedMetric g w hw hp).metricInner (x, r) (A x, 0) (0, 1) = 0
    rw [warpedMetric_metricInner_mk]
    change (w (r : ℝ)) ^ 2 * g.metricInner x (A x) 0 + 0 * 1 = 0
    rw [g.metricInner_zero_right]
    ring
  have hmetricRH (A : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
      wm.metricInner (x, r) (R (x, r)) (coneHorizontalLift A (x, r)) = 0 := by
    rw [wm.metricInner_comm]
    exact hmetricHR A x r
  have hdirHHH (A B C : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
      (coneHorizontalLift A).dir
          (fun q => wm.metricInner q (coneHorizontalLift B q)
            (coneHorizontalLift C q)) (x, r) =
        (w (r : ℝ)) ^ 2 * A.dir
          (fun p => g.metricInner p (B p) (C p)) x := by
    rw [coneHorizontalLift_dir A
      (wm.metricInner_field_contMDiff (coneHorizontalLift B)
        (coneHorizontalLift C)) (x, r)]
    have hslice :
        (fun p => wm.metricInner (p, r) (coneHorizontalLift B (p, r))
          (coneHorizontalLift C (p, r))) =
          fun p => (w (r : ℝ)) ^ 2 * g.metricInner p (B p) (C p) := by
      funext p
      exact hmetricHH B C p r
    rw [hslice]
    exact A.dir_const_mul ((w (r : ℝ)) ^ 2) x
      (g.metricInner_field_mdifferentiableAt B C x)
  have hdirHR (A : SmoothVectorField I N)
      (V : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal))
      (q : N × ↥positiveReal) :
      V.dir (fun p => wm.metricInner p (coneHorizontalLift A p) (R p)) q = 0 := by
    have hzero :
        (fun p => wm.metricInner p (coneHorizontalLift A p) (R p)) =
          fun _ => 0 := by
      funext p
      exact hmetricHR A p.1 p.2
    rw [hzero, SmoothVectorField.dir, mfderiv_const]
    rfl
  have hdirRH (A : SmoothVectorField I N)
      (V : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal))
      (q : N × ↥positiveReal) :
      V.dir (fun p => wm.metricInner p (R p) (coneHorizontalLift A p)) q = 0 := by
    have hzero :
        (fun p => wm.metricInner p (R p) (coneHorizontalLift A p)) =
          fun _ => 0 := by
      funext p
      exact hmetricRH A p.1 p.2
    rw [hzero, SmoothVectorField.dir, mfderiv_const]
    rfl
  have hdirRadHH (A B : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
      R.dir (fun q => wm.metricInner q (coneHorizontalLift A q)
        (coneHorizontalLift B q)) (x, r) =
        2 * w (r : ℝ) * deriv w (r : ℝ) * g.metricInner x (A x) (B x) := by
    let basePair : N → ℝ := fun p => g.metricInner p (A p) (B p)
    have hbase : ContMDiff I 𝓘(ℝ, ℝ) ∞ basePair :=
      g.metricInner_field_contMDiff A B
    have hshape :
        (fun q => wm.metricInner q (coneHorizontalLift A q)
          (coneHorizontalLift B q)) =
          fun q : N × ↥positiveReal =>
            (w (q.2 : ℝ)) ^ 2 * (basePair ∘ Prod.fst) q := by
      funext q
      exact hmetricHH A B q.1 q.2
    have hwrad : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : N × ↥positiveReal => w (q.2 : ℝ)) :=
      hw.contMDiff.comp (contMDiff_subtype_val_opens.comp contMDiff_snd)
    have hderivw :
        R.dir (fun q : N × ↥positiveReal => w (q.2 : ℝ)) (x, r) =
          deriv w (r : ℝ) := by
      rw [coneRadialField_dir hwrad (x, r)]
      change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (fun s : ↥positiveReal => w (s : ℝ)) r (1 : ℝ) = deriv w (r : ℝ)
      rw [show (fun s : ↥positiveReal => w (s : ℝ)) =
          w ∘ (Subtype.val : ↥positiveReal → ℝ) from rfl,
        mfderiv_comp r (hw.contMDiff.mdifferentiableAt (by simp))
          (contMDiff_subtype_val_opens.mdifferentiableAt (by simp)),
        mfderiv_eq_fderiv, mfderiv_subtype_val_opens]
      change (fderiv ℝ w (r : ℝ)) (1 : ℝ) = deriv w (r : ℝ)
      exact fderiv_apply_one_eq_deriv
    have hderivwsq :
        R.dir (fun q : N × ↥positiveReal => (w (q.2 : ℝ)) ^ 2) (x, r) =
          2 * w (r : ℝ) * deriv w (r : ℝ) := by
      have hsq :
          (fun q : N × ↥positiveReal => (w (q.2 : ℝ)) ^ 2) =
            fun q => w (q.2 : ℝ) * w (q.2 : ℝ) := by
        funext q
        rw [pow_two]
      rw [hsq, R.dir_mul (x, r) (hwrad.mdifferentiableAt (by simp))
        (hwrad.mdifferentiableAt (by simp)), hderivw]
      ring
    rw [hshape, R.dir_mul (x, r)
      ((hwrad.pow 2).mdifferentiableAt (by simp))
      ((hbase.comp contMDiff_fst).mdifferentiableAt (by simp)),
      hderivwsq, coneRadialField_dir_comp_fst hbase]
    simp only [Function.comp_apply]
    dsimp [basePair]
    ring
  have hKHHH (A B C : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
      wm.koszulRHS (coneHorizontalLift B) (coneHorizontalLift A)
          (coneHorizontalLift C) (x, r) =
        (w (r : ℝ)) ^ 2 * g.koszulRHS B A C x := by
    have hbrBC :
        DCLieBracket (coneHorizontalLift B) (coneHorizontalLift C) (x, r) =
          coneHorizontalLift (bracketField B C) (x, r) := by
      change bracketField (coneHorizontalLift B) (coneHorizontalLift C) (x, r) = _
      rw [bracketField_coneHorizontalLift_coneHorizontalLift]
    have hbrAC :
        DCLieBracket (coneHorizontalLift A) (coneHorizontalLift C) (x, r) =
          coneHorizontalLift (bracketField A C) (x, r) := by
      change bracketField (coneHorizontalLift A) (coneHorizontalLift C) (x, r) = _
      rw [bracketField_coneHorizontalLift_coneHorizontalLift]
    have hbrBA :
        DCLieBracket (coneHorizontalLift B) (coneHorizontalLift A) (x, r) =
          coneHorizontalLift (bracketField B A) (x, r) := by
      change bracketField (coneHorizontalLift B) (coneHorizontalLift A) (x, r) = _
      rw [bracketField_coneHorizontalLift_coneHorizontalLift]
    unfold RiemannianMetric.koszulRHS
    rw [hdirHHH B A C x r, hdirHHH A C B x r, hdirHHH C B A x r,
      hbrBC, hbrAC, hbrBA, hmetricHH, hmetricHH, hmetricHH]
    simp only [bracketField_apply]
    ring
  have hKHH_R (A B : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
      wm.koszulRHS (coneHorizontalLift B) (coneHorizontalLift A) R (x, r) =
        -2 * w (r : ℝ) * deriv w (r : ℝ) * g.metricInner x (A x) (B x) := by
    have hbrBR :
        DCLieBracket (coneHorizontalLift B) R (x, r) = 0 := by
      change bracketField (coneHorizontalLift B) R (x, r) = 0
      rw [show R = coneRadialField (I := I) (N := N) from rfl,
        bracketField_coneHorizontalLift_coneRadialField]
      rfl
    have hbrAR :
        DCLieBracket (coneHorizontalLift A) R (x, r) = 0 := by
      change bracketField (coneHorizontalLift A) R (x, r) = 0
      rw [show R = coneRadialField (I := I) (N := N) from rfl,
        bracketField_coneHorizontalLift_coneRadialField]
      rfl
    have hbrBA :
        DCLieBracket (coneHorizontalLift B) (coneHorizontalLift A) (x, r) =
          coneHorizontalLift (bracketField B A) (x, r) := by
      change bracketField (coneHorizontalLift B) (coneHorizontalLift A) (x, r) = _
      rw [bracketField_coneHorizontalLift_coneHorizontalLift]
    unfold RiemannianMetric.koszulRHS
    rw [hdirHR A (coneHorizontalLift B) (x, r),
      hdirRH B (coneHorizontalLift A) (x, r), hdirRadHH B A x r,
      hbrBR, hbrAR, hbrBA, wm.metricInner_zero_left,
      wm.metricInner_zero_left, hmetricHR]
    rw [g.metricInner_comm x (B x) (A x)]
    ring
  apply Prod.ext
  · apply (g.metricInner_eq_iff_eq q.1 _ _).mp
    intro v
    obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq (I := I) q.1 v
    rw [← hZ]
    change g.metricInner q.1
        (((warpedConnection g w hw hp).cov (coneHorizontalLift X)
          (coneHorizontalLift Y)) q).1 (Z q.1) =
      g.metricInner q.1 (((leviCivitaConnectionGeneral g).cov X Y) q.1)
        (Z q.1)
    have hc := wm.koszulDualSection_dual
      (coneHorizontalLift Y) (coneHorizontalLift X)
      (coneHorizontalLift Z) q
    have hb := g.koszulDualSection_dual Y X Z q.1
    change 2 * wm.metricInner q
      (((warpedConnection g w hw hp).cov (coneHorizontalLift X)
        (coneHorizontalLift Y)) q) (coneHorizontalLift Z q) =
        wm.koszulRHS (coneHorizontalLift Y) (coneHorizontalLift X)
          (coneHorizontalLift Z) q at hc
    change 2 * g.metricInner q.1
      (((leviCivitaConnectionGeneral g).cov X Y) q.1) (Z q.1) =
        g.koszulRHS Y X Z q.1 at hb
    rw [warpedMetric_metricInner_prod, coneHorizontalLift_apply] at hc
    simp only [mul_zero, add_zero] at hc
    have hkk : wm.koszulRHS (coneHorizontalLift Y) (coneHorizontalLift X)
        (coneHorizontalLift Z) q =
        (w (q.2 : ℝ)) ^ 2 * g.koszulRHS Y X Z q.1 := by
      simpa using hKHHH X Y Z q.1 q.2
    rw [hkk] at hc
    have hw2 : 0 < (w (q.2 : ℝ)) ^ 2 :=
      sq_pos_of_pos (hp (q.2 : ℝ) q.2.property)
    nlinarith
  · have hc := wm.koszulDualSection_dual
      (coneHorizontalLift Y) (coneHorizontalLift X) R q
    change (((warpedConnection g w hw hp).cov (coneHorizontalLift X)
      (coneHorizontalLift Y)) q).2 =
        -(w q.2 * deriv w q.2 * g.metricInner q.1 (X q.1) (Y q.1))
    change 2 * wm.metricInner q
      (((warpedConnection g w hw hp).cov (coneHorizontalLift X)
        (coneHorizontalLift Y)) q) (R q) =
        wm.koszulRHS (coneHorizontalLift Y) (coneHorizontalLift X) R q at hc
    have hkk : wm.koszulRHS (coneHorizontalLift Y) (coneHorizontalLift X) R q =
        -2 * w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner q.1 (X q.1) (Y q.1) := by
      simpa using hKHH_R X Y q.1 q.2
    rw [hkk] at hc
    rw [warpedMetric_metricInner_prod, coneRadialField_apply] at hc
    rw [g.metricInner_zero_right] at hc
    simp only [mul_zero, mul_one] at hc
    linarith
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
