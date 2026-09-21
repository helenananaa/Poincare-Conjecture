import MorganTianLib.Ch02.SurgeryCap.WarpedProduct
import MorganTianLib.Ch02.SurgeryCap.ProfileData
import MorganTianLib.Ch02.EpsilonNeck

open Set Riemannian
open scoped Manifold ContDiff
noncomputable section
namespace MorganTianLib.SurgeryCap

/-- **Math.** The punctured cap is a sphere times the positive radial axis.
The tip is deliberately not part of this manifold. -/
abbrev PuncturedCap := EpsilonNeckSphere × ↥positiveReal
abbrev PuncturedCapModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

/-- **Math.** A genuine smooth metric dr² + w(r)² g_unit on the punctured cap. -/
def RoundCapProfile.puncturedMetric (P : RoundCapProfile) :
    RiemannianMetric PuncturedCapModel PuncturedCap :=
  warpedMetric unitRoundSphereMetric P.w P.smooth P.positive

@[simp] theorem RoundCapProfile.puncturedMetric_apply (P : RoundCapProfile)
    (x : EpsilonNeckSphere) (r : ↥positiveReal)
    (u v : TangentSpace (𝓡 2) x) (a b : ℝ) :
    P.puncturedMetric.metricInner (x, r) (u, a) (v, b) =
      P.w r ^ 2 * unitRoundSphereMetric.metricInner x u v + a * b := by
  exact warpedMetric_metricInner_mk unitRoundSphereMetric P.w P.smooth P.positive x r u v a b

/-- **Math.** The spherical-tip radial formula holds on its full punctured neighborhood. -/
theorem RoundCapProfile.puncturedMetric_tip (P : RoundCapProfile)
    (x : EpsilonNeckSphere) (r : ↥positiveReal) (hr : (r : ℝ) ≤ P.r0)
    (u v : TangentSpace (𝓡 2) x) (a b : ℝ) :
    P.puncturedMetric.metricInner (x, r) (u, a) (v, b) =
      (2 * Real.sin ((r : ℝ) / 2)) ^ 2 * unitRoundSphereMetric.metricInner x u v + a * b := by
  rw [P.puncturedMetric_apply, P.tip r (by rwa [abs_of_pos r.property])]

/-- **Math.** The tail has exactly the round reference-cylinder metric, not
just a comparison or an asymptotic limit. -/
theorem RoundCapProfile.puncturedMetric_tail (P : RoundCapProfile)
    (x : EpsilonNeckSphere) (r : ↥positiveReal) (hr : P.A ≤ (r : ℝ))
    (u v : TangentSpace (𝓡 2) x) (a b : ℝ) :
    P.puncturedMetric.metricInner (x, r) (u, a) (v, b) =
      roundSphereMetric.metricInner x u v + a * b := by
  rw [P.puncturedMetric_apply, P.tail r hr, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rfl

/-- **Math.** Radial tangent vectors have unit speed in geodesic-radius units. -/
@[simp] theorem RoundCapProfile.radial_unit (P : RoundCapProfile)
    (x : EpsilonNeckSphere) (r : ↥positiveReal) :
    P.puncturedMetric.metricInner (x, r) (0, 1) (0, 1) = 1 := by
  rw [P.puncturedMetric_apply]
  simp [Riemannian.RiemannianMetric.metricInner_zero_left]

/-- **Math.** Radial and tangential vectors are orthogonal for the constructed metric. -/
@[simp] theorem RoundCapProfile.horizontal_radial (P : RoundCapProfile)
    (x : EpsilonNeckSphere) (r : ↥positiveReal) (u : TangentSpace (𝓡 2) x) :
    P.puncturedMetric.metricInner (x, r) (u, 0) (0, 1) = 0 := by
  rw [P.puncturedMetric_apply]
  simp [Riemannian.RiemannianMetric.metricInner_zero_right]

/-- **Math.** An unconditional punctured-cap realization from the constructed
profile. Smooth extension across the missing tip is not asserted here. -/
theorem exists_round_tip_cylindrical_punctured_metric :
    ∃ P : RoundCapProfile, ∃ g : RiemannianMetric PuncturedCapModel PuncturedCap,
      (∀ (x : EpsilonNeckSphere) (r : ↥positiveReal)
        (u v : TangentSpace (𝓡 2) x) (a b : ℝ),
        g.metricInner (x, r) (u, a) (v, b) =
          P.w r ^ 2 * unitRoundSphereMetric.metricInner x u v + a * b) ∧
      (∀ (x : EpsilonNeckSphere) (r : ↥positiveReal), P.A ≤ (r : ℝ) →
        ∀ (u v : TangentSpace (𝓡 2) x) (a b : ℝ),
        g.metricInner (x, r) (u, a) (v, b) =
          roundSphereMetric.metricInner x u v + a * b) := by
  let P := standardRoundCapProfile
  exact ⟨P, P.puncturedMetric, P.puncturedMetric_apply, P.puncturedMetric_tail⟩

end MorganTianLib.SurgeryCap
