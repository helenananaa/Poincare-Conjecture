import MorganTianLib.Ch02.SurgeryCap.GlobalCapMetric

open Riemannian
open scoped Manifold ContDiff RealInnerProductSpace
noncomputable section
namespace MorganTianLib.SurgeryCap
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** Fix the global smooth metric constructed from the actual profile. -/
def RoundCapProfile.globalMetric (P : RoundCapProfile) : RiemannianMetric (𝓡 3) E3 :=
  Classical.choose (exists_global_round_tip_metric P)

@[simp] theorem RoundCapProfile.globalMetric_zero (P : RoundCapProfile) (v z : E3) :
    P.globalMetric.metricInner 0 v z = inner ℝ v z :=
  (Classical.choose_spec (exists_global_round_tip_metric P)).1 v z

theorem RoundCapProfile.globalMetric_formula (P : RoundCapProfile)
    (x : E3) (hx : x ≠ 0) (v z : E3) :
    P.globalMetric.metricInner x v z =
      (P.w ‖x‖ / ‖x‖) ^ 2 * inner ℝ v z +
        ((1 - (P.w ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2) * inner ℝ x v * inner ℝ x z :=
  (Classical.choose_spec (exists_global_round_tip_metric P)).2 x hx v z

/-- **Math.** Orthogonal transformations preserve the actual constructed global metric. -/
theorem RoundCapProfile.globalMetric_orthogonal_invariant (P : RoundCapProfile)
    (T : E3 ≃ₗᵢ[ℝ] E3) (x v z : E3) :
    P.globalMetric.metricInner (T x) (T v) (T z) = P.globalMetric.metricInner x v z := by
  by_cases hx : x = 0
  · subst x
    have h0 : T (0 : E3) = (0 : E3) := T.map_zero
    rw [h0, P.globalMetric_zero, P.globalMetric_zero, T.inner_map_map]
  · have hTx : T x ≠ 0 := by simpa using hx
    rw [P.globalMetric_formula (T x) hTx, P.globalMetric_formula x hx,
      T.norm_map, T.inner_map_map, T.inner_map_map, T.inner_map_map]

/-- **Math.** The radial covector is the Euclidean radial covector, despite
non-Euclidean tangential lengths. This identity includes the tip. -/
theorem RoundCapProfile.globalMetric_radial (P : RoundCapProfile) (x v : E3) :
    P.globalMetric.metricInner x x v = inner ℝ x v := by
  by_cases hx : x = 0
  · subst x
    exact P.globalMetric_zero 0 v
  · rw [P.globalMetric_formula x hx x v, real_inner_self_eq_norm_sq]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    field_simp
    <;> ring

/-- **Math.** Tangential vectors at a positive-radius point have the prescribed
warping factor, stated for the actual global metric. -/
theorem RoundCapProfile.globalMetric_tangential (P : RoundCapProfile)
    (x : E3) (hx : x ≠ 0) (u v : E3) (hu : inner ℝ x u = 0) :
    P.globalMetric.metricInner x u v = (P.w ‖x‖ / ‖x‖)^2 * inner ℝ u v := by
  rw [P.globalMetric_formula x hx u v, hu]
  ring

end MorganTianLib.SurgeryCap
