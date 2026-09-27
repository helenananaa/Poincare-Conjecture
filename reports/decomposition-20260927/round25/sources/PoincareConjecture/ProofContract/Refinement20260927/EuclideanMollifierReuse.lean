import PoincareConjecture.ProofContract.Refinement20260927.CylinderMollificationLeaves
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology
/-- **Math.** The declared cylinder measure is the product of the two translation-invariant volumes. -/
instance cylinderVolume_leftInvariant :
    (volume : Measure CylinderAmbient).IsAddLeftInvariant := by
  change ((volume : Measure ℝ).prod (volume : Measure (ApproxAmbient 3))).IsAddLeftInvariant
  exact Measure.prod.instIsAddLeftInvariant
/-- **Math.** Negation preserves the same product volume, proved componentwise. -/
instance cylinderVolume_negInvariant : (volume : Measure CylinderAmbient).IsNegInvariant := by
  change ((volume : Measure ℝ).prod (volume : Measure (ApproxAmbient 3))).IsNegInvariant
  constructor
  change Measure.map (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ApproxAmbient 3 → ApproxAmbient 3))
    ((volume : Measure ℝ).prod (volume : Measure (ApproxAmbient 3))) = _
  rw [← Measure.map_prod_map _ _ measurable_neg measurable_neg,
    Measure.map_neg_eq_self, Measure.map_neg_eq_self]
/-- **Math.** This is an actual Haar-measure instance for the already specified product volume. -/
instance cylinderVolume_addHaar : (volume : Measure CylinderAmbient).IsAddHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsAddLeftInvariant := cylinderVolume_leftInvariant
  toIsOpenPosMeasure := inferInstance
/-- **Math.** Existing convolution regularity is consumed directly; no worker is needed for it. -/
theorem euclideanMollify_smooth {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (phi : ContDiffBump (0 : CylinderAmbient))
    (f : CylinderAmbient → F) (hf : Continuous f) : ContDiff ℝ ∞ (euclideanMollify phi f) := by
  have hphi : ContDiff ℝ ∞ (phi.normed (volume : Measure CylinderAmbient)) := by
    change ContDiff ℝ ∞ (fun x => phi x / ∫ y, phi y)
    exact phi.contDiff.div_const _
  exact (phi.hasCompactSupport_normed (μ := (volume : Measure CylinderAmbient))).contDiff_convolution_left
    (μ := (volume : Measure CylinderAmbient)) (lsmul ℝ ℝ) hphi hf.locallyIntegrable
/-- **Math.** The derivative of this same mollification is the same kernel applied to the derivative. -/
theorem euclideanMollify_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (phi : ContDiffBump (0 : CylinderAmbient))
    (f : CylinderAmbient → F) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x : CylinderAmbient) :
    fderiv ℝ (euclideanMollify phi f) x = euclideanMollify phi (fderiv ℝ f) x := by
  have h := hc.hasFDerivAt_convolution_right (μ := (volume : Measure CylinderAmbient)) (lsmul ℝ ℝ)
    (phi.integrable_normed (μ := (volume : Measure CylinderAmbient))).locallyIntegrable hf x
  have he : (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR CylinderAmbient =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (CylinderAmbient →L[ℝ] F) →L[ℝ] (CylinderAmbient →L[ℝ] F)) := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro L
    apply ContinuousLinearMap.ext
    intro v
    rfl
  simpa only [euclideanMollify,he] using h.fderiv
#print axioms cylinderVolume_leftInvariant
#print axioms cylinderVolume_negInvariant
#print axioms cylinderVolume_addHaar
#print axioms euclideanMollify_smooth
#print axioms euclideanMollify_fderiv
end PoincareConjecture.ProofContract.Refinement20260927
