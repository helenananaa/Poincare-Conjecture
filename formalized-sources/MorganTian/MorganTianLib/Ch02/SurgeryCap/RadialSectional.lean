import MorganTianLib.Ch02.SurgeryCap.PuncturedCap
import MorganTianLib.Ch02.SurgeryCap.WarpedRadialCurvature
open Set Riemannian
open scoped Manifold ContDiff Topology
noncomputable section
namespace MorganTianLib.SurgeryCap

/-- **Math.** The actual canonical connection of the constructed punctured cap. -/
def RoundCapProfile.puncturedConnection (P : RoundCapProfile) :
    AffineConnection PuncturedCapModel PuncturedCap :=
  warpedConnection unitRoundSphereMetric P.w P.smooth P.positive

/-- **Math.** The radial-plane curvature numerator of the actual connection
is the radial coefficient times the squared horizontal length. -/
theorem RoundCapProfile.radial_curvature_pairing (P : RoundCapProfile)
    (X : SmoothVectorField (𝓡 2) EpsilonNeckSphere) (q : PuncturedCap) :
    P.puncturedMetric.metricInner q
      (P.puncturedConnection.curvature (coneHorizontalLift X) coneRadialField
        (coneHorizontalLift X) q) (coneRadialField q) =
      P.radialCoefficient q.2 * P.puncturedMetric.metricInner q
        (coneHorizontalLift X q) (coneHorizontalLift X q) := by
  rcases q with ⟨x, r⟩
  have hc : P.puncturedConnection.IsMetricCompatible P.puncturedMetric :=
    (warpedConnection_isLeviCivita unitRoundSphereMetric P.w P.smooth P.positive).2
  rw [P.puncturedConnection.curvature_inner_antisymm_right P.puncturedMetric hc]
  change -(P.puncturedMetric.metricInner (x, r)
    ((warpedConnection unitRoundSphereMetric P.w P.smooth P.positive).curvature
      (coneHorizontalLift X) coneRadialField coneRadialField (x, r))
    (coneHorizontalLift X (x, r))) = _
  rw [warpedConnection_radial_curvature]
  simp only [RoundCapProfile.puncturedMetric, warpedMetric_metricInner_prod,
    coneHorizontalLift_apply, RiemannianMetric.metricInner_smul_left,
    zero_mul, mul_zero, add_zero, RoundCapProfile.radialCoefficient]
  ring

/-- **Math.** The constructed profile gives nonnegative actual radial-plane curvature. -/
theorem RoundCapProfile.radial_curvature_nonneg (P : RoundCapProfile)
    (X : SmoothVectorField (𝓡 2) EpsilonNeckSphere) (q : PuncturedCap) :
    0 ≤ P.puncturedMetric.metricInner q
      (P.puncturedConnection.curvature (coneHorizontalLift X) coneRadialField
        (coneHorizontalLift X) q) (coneRadialField q) := by
  rw [P.radial_curvature_pairing]
  exact mul_nonneg
    (div_nonneg (neg_nonneg.mpr (P.concave q.2 q.2.property.le))
      (P.positive q.2 q.2.property).le)
    (P.puncturedMetric.metricInner_self_nonneg _ _)

/-- **Math.** The genuine sectional-curvature quotient for a nondegenerate
radial plane is -w''/w; the denominator is not assumed to be normalized. -/
theorem RoundCapProfile.radial_sectional_formula (P : RoundCapProfile)
    (X : SmoothVectorField (𝓡 2) EpsilonNeckSphere) (q : PuncturedCap)
    (hX : X q.1 ≠ 0) :
    P.puncturedMetric.metricInner q
        (P.puncturedConnection.curvature (coneHorizontalLift X) coneRadialField
          (coneHorizontalLift X) q) (coneRadialField q) /
      (P.puncturedMetric.metricInner q (coneHorizontalLift X q) (coneHorizontalLift X q) *
        P.puncturedMetric.metricInner q (coneRadialField q) (coneRadialField q) -
        (P.puncturedMetric.metricInner q (coneHorizontalLift X q) (coneRadialField q))^2)
      = P.radialCoefficient q.2 := by
  have hrr : P.puncturedMetric.metricInner q
      (coneRadialField q) (coneRadialField q) = 1 := by
    simpa only [coneRadialField_apply] using P.radial_unit q.1 q.2
  have hhr : P.puncturedMetric.metricInner q
      (coneHorizontalLift X q) (coneRadialField q) = 0 := by
    simpa only [coneHorizontalLift_apply, coneRadialField_apply] using
      P.horizontal_radial q.1 q.2 (X q.1)
  have hH : coneHorizontalLift X q ≠ 0 := by
    intro hz
    have h := congrArg (fun z : TangentSpace PuncturedCapModel q => z.1) hz
    apply hX
    change X q.1 = 0 at h
    exact h
  have hden := P.puncturedMetric.metricInner_self_pos q (coneHorizontalLift X q) hH
  rw [P.radial_curvature_pairing, hrr, hhr]
  simp only [mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
  exact mul_div_cancel_right₀ _ hden.ne'

end MorganTianLib.SurgeryCap
