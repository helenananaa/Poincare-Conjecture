import PoincareConjecture.ProofContract.Refinement20260927.CylinderC1Approximation
import PoincareConjecture.ProofContract.Refinement20260927.AcceptedThirtyEight
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** Additional joint C1 entrance; the old weaker entrances remain available. -/
structure JointC1ApproximationData (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (D : BasedSphereClass N) where
  reference : C(SweepDomain,N)
  ends : EqOn reference (ContinuousMap.const SweepDomain D.base) sweepoutEnds
  correct_class : reference.HomotopicRel D.reference.continuousMap sweepoutEnds
  differentiable : ∀ s : SweepParameter, MDifferentiable (𝓡 2) (𝓡 3) (fun p => reference (s,p))
  integrable : ∀ s : SweepParameter,
    Integrable (sphereEnergyDensity N g (fun p => reference (s,p))) sphereEnergyMeasure
  dimension : ℕ
  embedding : CompactEuclideanEmbedding N dimension
  C : ℝ
  C_nonneg : 0 ≤ C
  derivative_bound : ∀ (s : SweepParameter) p i,
    ‖embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ C
  extension : ℝ × Sphere2 → N
  joint_c1 : ContMDiff SweepModel (𝓡 3) 1 extension
  extension_agrees : ∀ q : SweepDomain, extension ((q.1:ℝ),q.2) = reference q
/-- **Math.** Joint C1 regularity yields the actual raw approximants; no sequence is assumed. -/
theorem JointC1ApproximationData.toAmbient (approx : CylinderC1ApproximationStatement)
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : JointC1ApproximationData N g D) :
    ∃ out : AmbientApproximationData N g D, out.reference = r.reference := by
  refine ⟨{ reference := r.reference
            ends := r.ends
            correct_class := r.correct_class
            differentiable := r.differentiable
            integrable := r.integrable
            dimension := r.dimension
            embedding := r.embedding
            C := r.C
            C_nonneg := r.C_nonneg
            derivative_bound := r.derivative_bound
            raw_approximants := ?_ },rfl⟩
  intro eps heps
  let f : ℝ × Sphere2 → ApproxAmbient r.dimension := r.embedding.map ∘ r.extension
  have hf : ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient r.dimension) 1 f :=
    (r.embedding.smooth.of_le (by simp)).comp r.joint_c1
  obtain ⟨a,ha,hval,hder⟩ := approx r.dimension f hf eps heps
  refine ⟨a,ha,?_,?_⟩
  · intro q
    simpa only [f,Function.comp_apply,r.extension_agrees q] using hval q
  · intro s p i
    have hs : (fun z : Sphere2 => f ((s:ℝ),z)) =
        r.embedding.map ∘ (fun z => r.reference (s,z)) := by
      funext z
      exact congrArg r.embedding.map (r.extension_agrees (s,z))
    have h := hder s p i
    rw [hs] at h
    exact h
/-- **Math.** The retraction and endpoint corrections are already unconditional checked results. -/
theorem JointC1ApproximationData.toEmbedding (approx : CylinderC1ApproximationStatement)
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : JointC1ApproximationData N g D) :
    ∃ out : EmbeddingApproximationData N g D, out.reference = r.reference := by
  obtain ⟨a,ha⟩ := r.toAmbient approx
  obtain ⟨out,hout⟩ := a.toEmbedding_checked
  exact ⟨out,hout.trans ha⟩
#print axioms JointC1ApproximationData.toAmbient
#print axioms JointC1ApproximationData.toEmbedding
end PoincareConjecture.ProofContract.Refinement20260927
