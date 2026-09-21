import MorganTianLib.Ch02.SurgeryCap.LocalMetricNaturality
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]
/-- **Math.** A genuine local metric isometry transports the actual curvature,
with different source and target model spaces permitted. -/
theorem local_metric_map_curvature_related (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (hmetric : ∀ p u v, g.metricInner p u v = h.metricInner (f p)
      (mfderiv I J f p u) (mfderiv I J f p v))
    (X Y Z : SmoothVectorField I M) (X' Y' Z' : SmoothVectorField J N)
    (hX : ∀ p, mfderiv I J f p (X p) = X' (f p))
    (hY : ∀ p, mfderiv I J f p (Y p) = Y' (f p))
    (hZ : ∀ p, mfderiv I J f p (Z p) = Z' (f p)) (p : M) :
    mfderiv I J f p ((leviCivitaConnectionGeneral g).curvature X Y Z p) =
      (leviCivitaConnectionGeneral h).curvature X' Y' Z' (f p) := by
  let ng := leviCivitaConnectionGeneral g
  let nh := leviCivitaConnectionGeneral h
  have hbr : ∀ q, mfderiv I J f q (bracketField X Y q) = bracketField X' Y' (f q) := by
    intro q
    change mfderiv I J f q (DCLieBracket X Y q) = DCLieBracket X' Y' (f q)
    rw [← (leviCivitaConnectionGeneral_isLeviCivita g).1 X Y q,
      ← (leviCivitaConnectionGeneral_isLeviCivita h).1 X' Y' (f q), map_sub]
    rw [local_metric_map_covariant_related f hf g h hmetric X Y X' Y' hX hY q,
      local_metric_map_covariant_related f hf g h hmetric Y X Y' X' hY hX q]
  have hXZ : ∀ q, mfderiv I J f q (ng.cov X Z q) = nh.cov X' Z' (f q) :=
    fun q => local_metric_map_covariant_related f hf g h hmetric X Z X' Z' hX hZ q
  have hYZ : ∀ q, mfderiv I J f q (ng.cov Y Z q) = nh.cov Y' Z' (f q) :=
    fun q => local_metric_map_covariant_related f hf g h hmetric Y Z Y' Z' hY hZ q
  change mfderiv I J f p (ng.curvature X Y Z p) = nh.curvature X' Y' Z' (f p)
  rw [ng.curvature_apply, nh.curvature_apply, map_add, map_sub]
  rw [local_metric_map_covariant_related f hf g h hmetric Y (ng.cov X Z)
      Y' (nh.cov X' Z') hY hXZ p,
    local_metric_map_covariant_related f hf g h hmetric X (ng.cov Y Z)
      X' (nh.cov Y' Z') hX hYZ p,
    local_metric_map_covariant_related f hf g h hmetric (bracketField X Y) Z
      (bracketField X' Y') Z' hbr hZ p]

end MorganTianLib.SurgeryCap
