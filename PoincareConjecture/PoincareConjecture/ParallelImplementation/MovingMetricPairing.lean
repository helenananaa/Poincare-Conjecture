import MorganTianLib.Ch03.RicciFlow.MetricVariation
import MorganTianLib.Ch02.CovDerivAlongCurve

/-!
# Moving metric pairing in a fixed tangent-fiber trivialization

The first local model for a moving-metric pairing fixes a base point `p`.  All
vectors then lie in one actual tangent fiber, and the time-dependent metric is
the curve of continuous bilinear forms `(g t).inner p`.  The coefficient curve
has its own derivative; differentiating its two inputs gives the other two
terms.  This separates the metric-variation term from the usual
metric-compatibility formula for a fixed metric.

The coefficient-curve derivative is an explicit hypothesis in the local
adapter below.  `IsMetricVariationOn` supplies its scalar evaluations, while
the remaining operator-valued producer from `IsSmoothMetricFamilyOn` has not
been constructed in this module.  The Ricci-flow specialization therefore
records the coefficient derivative hypothesis rather than claiming that this
fixed-fiber result handles a moving base curve.
-/

open Filter Riemannian Riemannian.Geodesic Bundle
open MorganTianLib
open scoped Manifold Topology ContDiff Bundle RealInnerProductSpace

noncomputable section

namespace PoincareConjecture.ParallelImplementation.MovingMetricPairing

/-! ### Three-factor rule for continuous bilinear coefficients -/

/-- **Math.** The derivative of an evolving continuous bilinear form evaluated on two
evolving vectors is the sum of the coefficient variation and both vector
variations.  This is the local-trivialization product rule; no pairing
derivative is assumed. -/
theorem continuousBilinear_hasDerivWithinAt_apply_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {J : Set ℝ} {t₀ : ℝ}
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (dB : V →L[ℝ] V →L[ℝ] ℝ)
    (X Y : ℝ → V) (dX dY : V)
    (hB : HasDerivWithinAt B dB J t₀)
    (hX : HasDerivWithinAt X dX J t₀)
    (hY : HasDerivWithinAt Y dY J t₀) :
    HasDerivWithinAt (fun t => B t (X t) (Y t))
      (dB (X t₀) (Y t₀) + B t₀ dX (Y t₀) + B t₀ (X t₀) dY) J t₀ := by
  have hBX := hB.clm_apply hX
  have hBXY := hBX.clm_apply hY
  simpa only [add_apply, add_assoc] using hBXY

/-! ### Actual metric coefficients at a fixed point -/

section MetricFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The coefficient derivative of a metric family on the fixed tangent fiber
at `p` evaluates to the prescribed metric variation.  `UniqueDiffWithinAt`
is needed to identify the pointwise derivatives. -/
theorem metricCoeff_deriv_apply_apply_eq_variation
    (g : ℝ → MorganTianLib.RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    {J : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t₀)
    (hvar : IsMetricVariationOn g h J)
    (p : M)
    (dh : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (hcoeff : HasDerivWithinAt (fun t => (g t).inner p) dh J t₀)
    (x y : TangentSpace I p) :
    dh x y = h t₀ p x y := by
  have hcoeffXY := (hcoeff.clm_apply
      (hasDerivWithinAt_const (s := J) (x := t₀) (c := x))).clm_apply
    (hasDerivWithinAt_const (s := J) (x := t₀) (c := y))
  have hcoeffXY' : HasDerivWithinAt (fun t => (g t).metricInner p x y)
      (dh x y) J t₀ := by
    simpa only [Riemannian.RiemannianMetric.metricInner,
      add_apply, zero_apply, map_zero, add_zero, zero_add] using hcoeffXY
  have hmetricXY := hvar t₀ ht₀ p x y
  exact hJ.eq_deriv _ hcoeffXY' hmetricXY

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Three-term derivative of the actual Riemannian metric pairing in the
fixed-fiber trivialization at `p`.  The first term is the supplied metric
variation; the other two are ordinary derivatives of the fields in this
fixed fiber. -/
theorem riemannianMetric_metricInner_movingFields_hasDerivWithinAt
    (g : ℝ → MorganTianLib.RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    {J : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t₀)
    (hvar : IsMetricVariationOn g h J)
    (p : M)
    (X Y : ℝ → TangentSpace I p) (dX dY : TangentSpace I p)
    (dh : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (hcoeff : HasDerivWithinAt (fun t => (g t).inner p) dh J t₀)
    (hX : HasDerivWithinAt X dX J t₀)
    (hY : HasDerivWithinAt Y dY J t₀) :
    HasDerivWithinAt (fun t => (g t).metricInner p (X t) (Y t))
      (h t₀ p (X t₀) (Y t₀) +
        (g t₀).metricInner p dX (Y t₀) +
        (g t₀).metricInner p (X t₀) dY) J t₀ := by
  have hthree := continuousBilinear_hasDerivWithinAt_apply_apply
    (fun t => (g t).inner p) dh X Y dX dY hcoeff hX hY
  have hvariation := metricCoeff_deriv_apply_apply_eq_variation
    g h ht₀ hJ hvar p dh hcoeff (X t₀) (Y t₀)
  simpa only [Riemannian.RiemannianMetric.metricInner, hvariation,
    add_assoc] using hthree

/-- **Math.** Ricci-flow specialization of the fixed-fiber pairing rule.  The
coefficient curve must be differentiated in the local fiber; its scalar
evaluations are then identified with `-2 Ric` by the existing Ricci-flow
equation. -/
theorem ricciFlow_metricInner_movingFields_hasDerivWithinAt
    (g : ℝ → MorganTianLib.RiemannianMetric I M) {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t₀) (p : M)
    (X Y : ℝ → TangentSpace I p) (dX dY : TangentSpace I p)
    (dh : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (hcoeff : HasDerivWithinAt (fun t => (g t).inner p) dh J t₀)
    (hX : HasDerivWithinAt X dX J t₀)
    (hY : HasDerivWithinAt Y dY J t₀) :
    HasDerivWithinAt (fun t => (g t).metricInner p (X t) (Y t))
      (-2 * ricciTensorAt (g t₀) p (X t₀) (Y t₀) +
        (g t₀).metricInner p dX (Y t₀) +
        (g t₀).metricInner p (X t₀) dY) J t₀ := by
  exact riemannianMetric_metricInner_movingFields_hasDerivWithinAt
    g (fun t p x y => -2 * ricciTensorAt (g t) p x y)
    ht₀ hJ hflow.equation p X Y dX dY dh hcoeff hX hY

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **Math.** Along the constant base curve at `p`, the existing moving-foot
covariant derivative reduces to the ordinary derivative in the fixed tangent
fiber.  The proof uses the existing chart trivialization and the vanishing of
the Christoffel contraction when the chart velocity is zero. -/
theorem constantBase_covDeriv_eq_ordinaryDeriv
    (g : MorganTianLib.RiemannianMetric I M) (p : M)
    (X : ℝ → TangentSpace I p) (t₀ : ℝ)
    (dX dCov : TangentSpace I p)
    (hX : HasDerivAt X dX t₀)
    (hCov : HasCovDerivAlongAt (I := I) g (fun _ : ℝ => p) X t₀ dCov) :
    dCov = dX := by
  have hchart : chartFieldCoord (I := I) p (fun _ : ℝ => p) X = X := by
    funext s
    change chartFiberCoord (I := I) p ⟨p, X s⟩ = X s
    exact chartFiberCoord_mk (I := I) p (X s)
  have hchartDeriv :
      HasDerivAt (chartFieldCoord (I := I) p (fun _ : ℝ => p) X) dX t₀ := by
    simpa only [hchart] using hX
  have hu : HasDerivAt (chartLocalCurve (I := I) (fun _ : ℝ => p) t₀) 0 t₀ := by
    change HasDerivAt (fun _ : ℝ => extChartAt I p p) 0 t₀
    exact hasDerivAt_const (x := t₀) (c := (extChartAt I p p : E))
  obtain ⟨_, v, dV, hv, hV, hformula⟩ := hCov
  have hv0 : v = 0 := hv.unique hu
  subst v
  have hVeq : dV = dX := hV.unique hchartDeriv
  have hformula' : dV = dCov := by
    simpa only [chartChristoffelContraction_zero_left, add_zero] using hformula
  exact hformula'.symm.trans hVeq

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- **Math.** The fixed-metric pairing derivative in a stationary local
trivialization agrees with the existing covariant pairing rule.  Thus the two
field-variation terms above are exactly the covariant terms in this special
case; a moving base curve requires the nonconstant chart adapter. -/
theorem constantBase_metricInner_deriv_eq_covariant
    (g : MorganTianLib.RiemannianMetric I M) (p : M)
    (X Y : ℝ → TangentSpace I p) (t₀ : ℝ)
    (dX dY : TangentSpace I p)
    (hX : HasCovDerivAlongAt (I := I) g (fun _ : ℝ => p) X t₀ dX)
    (hY : HasCovDerivAlongAt (I := I) g (fun _ : ℝ => p) Y t₀ dY) :
    HasDerivAt (fun t => g.metricInner p (X t) (Y t))
      (g.metricInner p dX (Y t₀) + g.metricInner p (X t₀) dY) t₀ := by
  simpa using hX.hasDerivAt_metricInner hY

end MetricFamily

end PoincareConjecture.ParallelImplementation.MovingMetricPairing

end
