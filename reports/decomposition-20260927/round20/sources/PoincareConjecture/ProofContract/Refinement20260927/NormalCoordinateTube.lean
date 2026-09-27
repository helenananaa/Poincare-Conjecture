import PoincareConjecture.ProofContract.Refinement20260927.NormalTubeLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set Filter
open scoped Topology Manifold ContDiff
/-- **Math.** Parameter charts for the actual normal total space remain to be constructed.
No endpoint inverse, global injectivity or endpoint derivative is a field. -/
structure NormalCoordinateTube {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) where
  total : Type u
  metric : MetricSpace total
  zero : @ContinuousMap N total _ metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  project : @ContinuousMap total N metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _
  endpoint : @ContinuousMap total (ApproxAmbient n) metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _
  project_zero : ∀ p : N, project (zero p) = p
  endpoint_zero : ∀ p : N, endpoint (zero p) = e.map p
  linear : N → (NormalTangent →L[ℝ] ApproxAmbient n)
  linear_injective : ∀ p, Function.Injective (linear p)
  base : N → NormalTangent
  chart : ∀ p : N, @OpenPartialHomeomorph total (NormalSplit (linear p))
    metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _
  zero_source : ∀ p : N, zero p ∈ (chart p).source
  zero_chart : ∀ p : N, chart p (zero p) = (base p,0)
  f : N → NormalTangent → ApproxAmbient n
  P : N → NormalTangent → (ApproxAmbient n →L[ℝ] ApproxAmbient n)
  f_deriv : ∀ p, HasFDerivAt (f p) (linear p) (base p)
  P_deriv : ∀ p, DifferentiableAt ℝ (P p) (base p)
  P_normal : ∀ p (v : NormalFiber (linear p)), P p (base p) v = v
  endpoint_formula : ∀ p, EqOn (endpoint ∘ (chart p).symm)
    (fun z : NormalSplit (linear p) => f p z.1 + P p z.1 z.2) (chart p).target
  smooth_expression : ∀ p, ContDiffOn ℝ ∞
    (fun z : NormalSplit (linear p) => f p z.1 + P p z.1 z.2) (chart p).target
  smooth_projection : ∀ p, ContMDiffOn 𝓘(ℝ,NormalSplit (linear p)) (𝓡 3) ∞
    (project ∘ (chart p).symm) (chart p).target
instance {N : CompactSmoothThree.{u}} {n : ℕ} {e : CompactEuclideanEmbedding N n}
    (T : NormalCoordinateTube e) : MetricSpace T.total := T.metric
/-- **Math.** All three independent leaves are used to produce the same local tubular data. -/
theorem NormalCoordinateTube.toLocal (split : NormalLinearEquivStatement)
    (jet : NormalEndpointJetStatement) (inverse : TubularChartInverseStatement.{u})
    {N : CompactSmoothThree.{u}} {n : ℕ} {e : CompactEuclideanEmbedding N n}
    (T : NormalCoordinateTube e) : Nonempty (LocalTubularData e) := by
  have localCharts : ∀ p : N, ∃ d : OpenPartialHomeomorph T.total (ApproxAmbient n),
      T.zero p ∈ d.source ∧ EqOn d T.endpoint d.source ∧
      ContMDiffOn 𝓘(ℝ,ApproxAmbient n) (𝓡 3) ∞ (T.project ∘ d.symm) d.target := by
    intro p
    obtain ⟨A,hA⟩ := split n (T.linear p) (T.linear_injective p)
    have ht : (T.base p,0) ∈ (T.chart p).target := by
      rw [← T.zero_chart p]
      exact (T.chart p).map_source (T.zero_source p)
    have hd : HasFDerivAt (T.endpoint ∘ (T.chart p).symm)
        A.toContinuousLinearMap (T.chart p (T.zero p)) := by
      rw [hA,T.zero_chart p]
      apply (jet n (T.linear p) (T.base p) (T.f p) (T.P p)
        (T.f_deriv p) (T.P_deriv p) (T.P_normal p)).congr_of_eventuallyEq
      filter_upwards [(T.chart p).open_target.mem_nhds ht] with z hz
      exact T.endpoint_formula p hz
    exact inverse N n T.total (NormalSplit (T.linear p)) (T.chart p) (T.zero p)
      T.endpoint T.project A (T.zero_source p)
      ((T.smooth_expression p).congr (T.endpoint_formula p)) hd (T.smooth_projection p)
  choose chart hzero hagrees hsmooth using localCharts
  exact ⟨{ total := T.total
           metric := T.metric
           zero := T.zero
           project := T.project
           endpoint := T.endpoint
           project_zero := T.project_zero
           endpoint_zero := T.endpoint_zero
           chart := chart
           zero_source := hzero
           chart_agrees := hagrees
           smooth_projection := hsmooth }⟩
/-- **Math.** The constructed retraction still uses the original embedding. -/
theorem NormalCoordinateTube.toRetraction (split : NormalLinearEquivStatement)
    (jet : NormalEndpointJetStatement) (inverse : TubularChartInverseStatement.{u})
    {N : CompactSmoothThree.{u}} {n : ℕ} {e : CompactEuclideanEmbedding N n}
    (T : NormalCoordinateTube e) : ∃ R : SmoothRetractionData N n, R.embed = e.map := by
  obtain ⟨localTube⟩ := T.toLocal split jet inverse
  exact local_tubes_retraction_of_assembly checked_tubular_inverse_assembly localTube
#print axioms NormalCoordinateTube.toLocal
#print axioms NormalCoordinateTube.toRetraction
end PoincareConjecture.ProofContract.Refinement20260927
