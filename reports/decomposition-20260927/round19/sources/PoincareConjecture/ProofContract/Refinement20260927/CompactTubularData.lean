import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTwentyFive
import Mathlib.Geometry.Manifold.WhitneyEmbedding
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff
/-- **Math.** Actual smooth closed immersion; the map remains part of the witness. -/
structure CompactEuclideanEmbedding (N : CompactSmoothThree.{u}) (n : ℕ) where
  map : C(N, ApproxAmbient n)
  smooth : ContMDiff (𝓡 3) 𝓘(ℝ, ApproxAmbient n) ∞ map
  closed : Topology.IsClosedEmbedding map
  injective_deriv : ∀ p : N, Function.Injective (mfderiv (𝓡 3) 𝓘(ℝ, ApproxAmbient n) map p)
/-- **Math.** Genuine existence from the pinned compact Whitney theorem, not a new assumption. -/
theorem compact_euclidean_embedding_exists (N : CompactSmoothThree.{u}) :
    ∃ n : ℕ, Nonempty (CompactEuclideanEmbedding N n) := by
  obtain ⟨n,e,hs,he,hd⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 3) (M := N)
  exact ⟨n,⟨{ map := ⟨e,hs.continuous⟩, smooth := hs, closed := he, injective_deriv := hd }⟩⟩
/-- **Math.** Topological compactness leaf: local injectivity near a compact set, plus
injectivity ON that set, produces one common injective neighborhood. -/
def CompactInjectiveNeighborhoodStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n : ℕ) (f : X → ApproxAmbient n) (K : Set X),
    Continuous f → IsCompact K → InjOn f K →
    (∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U) →
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ InjOn f U
/-- **Math.** Local normal-coordinate data. Construction from an embedded manifold is
still research. No global injectivity, inverse, or retraction is a field. -/
structure LocalTubularData {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) where
  total : Type u
  metric : MetricSpace total
  zero : @ContinuousMap N total _ metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  project : @ContinuousMap total N metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _
  endpoint : @ContinuousMap total (ApproxAmbient n) metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _
  project_zero : ∀ p : N, project (zero p) = p
  endpoint_zero : ∀ p : N, endpoint (zero p) = e.map p
  chart : N → @OpenPartialHomeomorph total (ApproxAmbient n) metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _
  zero_source : ∀ p : N, zero p ∈ (chart p).source
  chart_agrees : ∀ p : N, EqOn (chart p) endpoint (chart p).source
  smooth_projection : ∀ p : N,
    ContMDiffOn 𝓘(ℝ, ApproxAmbient n) (𝓡 3) ∞
      (fun x => project ((chart p).symm x)) (chart p).target
instance {N : CompactSmoothThree.{u}} {n : ℕ} {e : CompactEuclideanEmbedding N n}
    (T : LocalTubularData e) : MetricSpace T.total := T.metric
/-- **Math.** Independent assembly leaf. All charts share the SAME endpoint and
projection, and injectivity is supplied on U, not assumed on the whole bundle. -/
def TubularInverseAssemblyStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n)
    (T : LocalTubularData e) (U : Set T.total), IsOpen U → range T.zero ⊆ U →
      InjOn T.endpoint U → U ⊆ ⋃ p : N, (T.chart p).source →
      ∃ R : SmoothRetractionData N n, R.embed = e.map ∧
        R.domain = T.endpoint '' U ∧ ∀ x ∈ U, R.localRetract (T.endpoint x) = T.project x
theorem local_tubular_data_to_retraction (injectiveNbhd : CompactInjectiveNeighborhoodStatement.{u})
    (assemble : TubularInverseAssemblyStatement.{u}) {N : CompactSmoothThree.{u}} {n : ℕ}
    {e : CompactEuclideanEmbedding N n} (T : LocalTubularData e) :
    ∃ R : SmoothRetractionData N n, R.embed = e.map := by
  have hK : IsCompact (range T.zero) := isCompact_range T.zero.continuous
  have hinj : InjOn T.endpoint (range T.zero) := by
    rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ h
    rw [T.endpoint_zero,T.endpoint_zero] at h
    exact congrArg T.zero (e.closed.injective h)
  obtain ⟨V,hV,hKV,hVI⟩ := injectiveNbhd T.total n T.endpoint (range T.zero)
    T.endpoint.continuous hK hinj (by
      rintro _ ⟨p,rfl⟩
      refine ⟨(T.chart p).source,(T.chart p).open_source,T.zero_source p,?_⟩
      intro x hx y hy hxy
      apply (T.chart p).injOn hx hy
      rw [T.chart_agrees p hx,T.chart_agrees p hy]
      exact hxy)
  let U : Set T.total := V ∩ ⋃ p : N, (T.chart p).source
  have hU : IsOpen U := hV.inter (isOpen_iUnion fun p => (T.chart p).open_source)
  have hKU : range T.zero ⊆ U := by
    rintro _ ⟨p,rfl⟩
    exact ⟨hKV ⟨p,rfl⟩,mem_iUnion.mpr ⟨p,T.zero_source p⟩⟩
  obtain ⟨R,hR,_domain,_inverse⟩ := assemble N n e T U hU hKU
    (hVI.mono inter_subset_left) inter_subset_right
  exact ⟨R,hR⟩
#print axioms compact_euclidean_embedding_exists
#print axioms local_tubular_data_to_retraction
end PoincareConjecture.ProofContract.Refinement20260927
