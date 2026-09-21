import MorganTianLib.Ch01.RiemannianCone
open Set Riemannian TopologicalSpace
open scoped Manifold Topology ContDiff
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I ∞ N]
noncomputable def warpedForm (g : RiemannianMetric I N) (w : ℝ → ℝ) (p : N × ↥positiveReal) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ :=
  ((w (p.2 : ℝ)) ^ 2) •
      DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) g (Prod.fst : N × ↥positiveReal → N) p +
    DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) (opensEuclideanMetric positiveReal)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) p

omit [FiniteDimensional ℝ E] in
/-- **Math.** Evaluation of the warped form on tangent vectors. -/
@[simp] theorem warpedForm_apply (g : RiemannianMetric I N) (w : ℝ → ℝ) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    warpedForm g w p u v =
      (w (p.2 : ℝ)) ^ 2 * g.metricInner p.1
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p v) +
      (opensEuclideanMetric positiveReal).metricInner p.2
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p v) := by
  simp only [warpedForm, add_apply, smul_apply, smul_eq_mul, DCInducedForm_apply]

omit [FiniteDimensional ℝ E] in
theorem warpedForm_symm (g : RiemannianMetric I N) (w : ℝ → ℝ) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) : warpedForm g w p u v = warpedForm g w p v u := by
  rw [warpedForm_apply, warpedForm_apply, g.metricInner_comm,
    (opensEuclideanMetric positiveReal).metricInner_comm]

omit [FiniteDimensional ℝ E] in
theorem warpedForm_self_nonneg (g : RiemannianMetric I N) (w : ℝ → ℝ) (p : N × ↥positiveReal)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) : 0 ≤ warpedForm g w p u u := by
  rw [warpedForm_apply]
  have h₁ : 0 ≤ (w (p.2 : ℝ)) ^ 2 * g.metricInner p.1
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u) :=
    mul_nonneg (sq_nonneg _) (g.metricInner_self_nonneg _ _)
  have h₂ : 0 ≤ (opensEuclideanMetric positiveReal).metricInner p.2
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u) :=
    (opensEuclideanMetric positiveReal).metricInner_self_nonneg _ _
  linarith

omit [FiniteDimensional ℝ E] in
theorem warpedForm_self_pos (g : RiemannianMetric I N) (w : ℝ → ℝ) (hwpos : ∀ r : ℝ, 0 < r → 0 < w r) (p : N × ↥positiveReal)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (hu : u ≠ 0) : 0 < warpedForm g w p u u := by
  have hfst : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) p u = u.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u = u.2 := by
    rw [mfderiv_snd]
    rfl
  rw [warpedForm_apply, hfst, hsnd]
  have hrad : 0 < (w (p.2 : ℝ)) ^ 2 := sq_pos_of_pos (hwpos _ p.2.property)
  have h₁ : 0 ≤ (w (p.2 : ℝ)) ^ 2 * g.metricInner p.1 u.1 u.1 :=
    mul_nonneg (sq_nonneg _) (g.metricInner_self_nonneg _ _)
  have h₂ : 0 ≤ (opensEuclideanMetric positiveReal).metricInner p.2 u.2 u.2 :=
    (opensEuclideanMetric positiveReal).metricInner_self_nonneg _ _
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]
    exact fun h => hu (Prod.ext h.1 h.2)
  rcases hor with h₁u | h₂u
  · have hp : 0 < (w (p.2 : ℝ)) ^ 2 * g.metricInner p.1 u.1 u.1 :=
      mul_pos hrad (g.metricInner_self_pos _ _ h₁u)
    linarith
  · have hp : 0 < (opensEuclideanMetric positiveReal).metricInner p.2 u.2 u.2 :=
      (opensEuclideanMetric positiveReal).metricInner_self_pos _ _ h₂u
    linarith

omit [FiniteDimensional ℝ E] in
theorem warpedForm_contMDiff (g : RiemannianMetric I N) (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p, warpedForm g w p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
  have hrad : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : N × ↥positiveReal ↦ ((w (p.2 : ℝ)) ^ 2)) := by
    exact ((hw.contMDiff.comp (contMDiff_subtype_val_opens.comp contMDiff_snd)).pow 2)
  have htan : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p,
        DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) g
          (Prod.fst : N × ↥positiveReal → N) p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
    exact DCInducedForm_contMDiff g contMDiff_fst
  have hradial : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p,
        DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) (opensEuclideanMetric positiveReal)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
    exact DCInducedForm_contMDiff (opensEuclideanMetric positiveReal) contMDiff_snd
  exact (hrad.smul_section htan).add_section hradial

/-! ### The bundled metric -/

/-- **Math.** The open warped metric over `g`, with pointwise inner product
`⟨(u,a),(v,b)⟩ = w(r)²⟨u,v⟩_g + a b`. -/
noncomputable def warpedMetric (g : RiemannianMetric I N) (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hwpos : ∀ r : ℝ, 0 < r → 0 < w r) :
    RiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) where
  inner p := warpedForm g w p
  symm p u v := warpedForm_symm g w p u v
  pos p u hu := warpedForm_self_pos g w hwpos p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E × ℝ) (warpedForm g w p) (fun u hu => ?_)
    exact warpedForm_self_pos g w hwpos p u hu
  contMDiff := warpedForm_contMDiff g w hw

@[simp] theorem warpedMetric_apply (g : RiemannianMetric I N) (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hwpos : ∀ r : ℝ, 0 < r → 0 < w r) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (warpedMetric g w hw hwpos).metricInner p u v = warpedForm g w p u v :=
  rfl

/-- **Math.** In the product tangent splitting, the warped metric is exactly
`w(r)²⟨u,v⟩_g + a b`. -/
@[simp] theorem warpedMetric_metricInner_mk (g : RiemannianMetric I N) (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hwpos : ∀ r : ℝ, 0 < r → 0 < w r)
    (x : N) (r : ↥positiveReal) (u v : TangentSpace I x) (a b : ℝ) :
    (warpedMetric g w hw hwpos).metricInner (x, r) (u, a) (v, b) =
      (w (r : ℝ)) ^ 2 * g.metricInner x u v + a * b := by
  rw [warpedMetric_apply, warpedForm_apply]
  have hfst_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) (u, a) = u := by
    rw [mfderiv_fst]
    rfl
  have hfst_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) (v, b) = v := by
    rw [mfderiv_fst]
    rfl
  have hsnd_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) (u, a) = a := by
    rw [mfderiv_snd]
    rfl
  have hsnd_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) (v, b) = b := by
    rw [mfderiv_snd]
    rfl
  rw [hfst_u, hfst_v, hsnd_u, hsnd_v, opensEuclideanMetric_apply]
  rw [show (inner ℝ a b : ℝ) = a * b from by simp [inner, mul_comm]]

/-- **Math.** The warped metric on arbitrary product tangent vectors is
`w(r)² g(u_N,v_N) + u_r v_r`. -/
@[simp] theorem warpedMetric_metricInner_prod (g : RiemannianMetric I N) (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hwpos : ∀ r : ℝ, 0 < r → 0 < w r)
    (x : N) (r : ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :
    (warpedMetric g w hw hwpos).metricInner (x, r) u v =
      (w (r : ℝ)) ^ 2 * g.metricInner x u.1 v.1 + u.2 * v.2 := by
  rw [warpedMetric_apply, warpedForm_apply]
  have hfst_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) u = u.1 := by
    rw [mfderiv_fst]
    rfl
  have hfst_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) v = v.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) u = u.2 := by
    rw [mfderiv_snd]
    rfl
  have hsnd_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) v = v.2 := by
    rw [mfderiv_snd]
    rfl
  rw [hfst_u, hfst_v, hsnd_u, hsnd_v, opensEuclideanMetric_apply]
  rw [show (inner ℝ u.2 v.2 : ℝ) = u.2 * v.2 from by simp [inner, mul_comm]]


end MorganTianLib.SurgeryCap
