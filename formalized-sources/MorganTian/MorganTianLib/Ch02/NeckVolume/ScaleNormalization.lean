import MorganTianLib.Ch02.EpsilonNeck

open Set MeasureTheory Riemannian Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [T2Space N]

variable [I.Boundaryless]

/-- **Math.** The defined neck scale is positive and recovers the unnormalized pullback metric. -/
theorem epsilonNeck_scale_pos_and_metric_normalization
    {epsilon : ℝ} {g : RiemannianMetric I N} {x : N}
    (S : EpsilonNeckStructure epsilon g x) :
    0 < S.scale ∧ canonicalScalarCurvature g x * S.scale ^ 2 = 1 ∧
      ∀ (p : epsilonNeckDomain epsilon)
        (v w : TangentSpace EpsilonNeckCylinderModel p),
        g.metricInner (S.phi p)
            (mfderiv EpsilonNeckCylinderModel I S.phi p v)
            (mfderiv EpsilonNeckCylinderModel I S.phi p w) =
          S.scale ^ 2 * S.normalizedPullbackMetric.metricInner p v w := by
/- SWARM_PROOF_BEGIN -/
  let p : epsilonNeckDomain epsilon := S.phi.symm x
  let v : TangentSpace EpsilonNeckCylinderModel p := epsilonNeckAxialUnit
  have hv : v ≠ 0 := by
    intro h
    have h' := congrArg
      (fun z : EuclideanSpace ℝ (Fin (2 + 1)) => z (Fin.last 2)) h
    have hi : finSumFinEquiv.symm (2 : Fin (2 + 1)) = Sum.inr (0 : Fin 1) := by
      decide
    simp [v, epsilonNeckAxialUnit, hi] at h'
  have hnorm : 0 < S.normalizedPullbackMetric.metricInner p v v :=
    S.normalizedPullbackMetric.metricInner_self_pos p v hv
  have hpull : 0 ≤ g.metricInner (S.phi p)
      (mfderiv EpsilonNeckCylinderModel I S.phi p v)
      (mfderiv EpsilonNeckCylinderModel I S.phi p v) :=
    g.metricInner_self_nonneg _ _
  have hrelation : S.normalizedPullbackMetric.metricInner p v v =
      canonicalScalarCurvature g x *
        g.metricInner (S.phi p)
          (mfderiv EpsilonNeckCylinderModel I S.phi p v)
          (mfderiv EpsilonNeckCylinderModel I S.phi p v) := by
    exact S.normalized_pullback p v v
  have hproduct : 0 < canonicalScalarCurvature g x *
      g.metricInner (S.phi p)
        (mfderiv EpsilonNeckCylinderModel I S.phi p v)
        (mfderiv EpsilonNeckCylinderModel I S.phi p v) := by
    rw [← hrelation]
    exact hnorm
  have hscalar : 0 < canonicalScalarCurvature g x :=
    pos_of_mul_pos_left hproduct hpull
  have hsqrt : 0 < Real.sqrt (canonicalScalarCurvature g x) :=
    Real.sqrt_pos.2 hscalar
  have hsq : Real.sqrt (canonicalScalarCurvature g x) ^ 2 =
      canonicalScalarCurvature g x := Real.sq_sqrt hscalar.le
  have hscale : 0 < S.scale := by
    rw [EpsilonNeckStructure.scale]
    exact inv_pos.2 hsqrt
  have hnormal : canonicalScalarCurvature g x * S.scale ^ 2 = 1 := by
    rw [EpsilonNeckStructure.scale]
    nth_rewrite 1 [← hsq]
    field_simp [ne_of_gt hsqrt]
  refine ⟨hscale, hnormal, ?_⟩
  intro p₀ v₀ w₀
  calc
    g.metricInner (S.phi p₀)
        (mfderiv EpsilonNeckCylinderModel I S.phi p₀ v₀)
        (mfderiv EpsilonNeckCylinderModel I S.phi p₀ w₀) =
        (canonicalScalarCurvature g x * S.scale ^ 2) *
          g.metricInner (S.phi p₀)
            (mfderiv EpsilonNeckCylinderModel I S.phi p₀ v₀)
            (mfderiv EpsilonNeckCylinderModel I S.phi p₀ w₀) := by
      rw [hnormal]
      ring
    _ = S.scale ^ 2 *
        (canonicalScalarCurvature g x *
          g.metricInner (S.phi p₀)
            (mfderiv EpsilonNeckCylinderModel I S.phi p₀ v₀)
            (mfderiv EpsilonNeckCylinderModel I S.phi p₀ w₀)) := by
      ring
    _ = S.scale ^ 2 * S.normalizedPullbackMetric.metricInner p₀ v₀ w₀ := by
      rw [S.normalized_pullback]
/- SWARM_PROOF_END -/

end MorganTianLib
