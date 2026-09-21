import MorganTianLib.Ch02.SurgeryCap.GlobalCurvatureBound
import MorganTianLib.Ch02.SurgeryCap.GeodesicCompleteness

open Riemannian
open scoped Manifold ContDiff
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** One actually constructed global cap simultaneously has complete
geodesics, orthogonal symmetry, and nonnegative uniformly bounded sectional
curvature. This is initial geometry, not a Ricci-flow or surgery-gluing theorem. -/
theorem exists_complete_nonnegative_bounded_global_cap :
    ∃ (P : RoundCapProfile) (C : ℝ), 0 < C ∧
      Riemannian.Geodesic.IsGeodesicallyComplete P.globalMetric ∧
      (∀ (T : E3 ≃ₗᵢ[ℝ] E3) (x u v : E3),
        P.globalMetric.metricInner (T x) (T u) (T v) = P.globalMetric.metricInner x u v) ∧
      ∀ (X Y : SmoothVectorField (𝓡 3) E3) (x : E3),
        0 ≤ P.globalMetric.metricInner x
          (P.globalMetric.leviCivitaConnection.curvature X Y X x) (Y x) ∧
        P.globalMetric.metricInner x
          (P.globalMetric.leviCivitaConnection.curvature X Y X x) (Y x) ≤
          C * (P.globalMetric.metricInner x (X x) (X x) *
            P.globalMetric.metricInner x (Y x) (Y x) -
            P.globalMetric.metricInner x (X x) (Y x) ^ 2) := by
  let P := standardRoundCapProfile
  obtain ⟨C, hC, hcurv⟩ := P.global_curvature_nonneg_bounded
  exact ⟨P, C, hC, P.globalMetric_geodesicallyComplete,
    P.globalMetric_orthogonal_invariant, hcurv⟩

end MorganTianLib.SurgeryCap
