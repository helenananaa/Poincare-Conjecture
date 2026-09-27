import PoincareConjecture.ProofContract.Refinement20260927.C1ReferenceLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff
/-- **Math.** The given C1 representative produces all analytic side conditions and an actual
Whitney embedding. No reference map or relative class is replaced. -/
theorem C1ClassRepresentative.toJoint (density : C1SphereEnergyContinuityStatement.{u})
    (bound : C1AmbientFrameBoundStatement) {N : CompactSmoothThree.{u}}
    {D : BasedSphereClass N} (r : C1ClassRepresentative N D)
    (g : Riemannian.RiemannianMetric (𝓡 3) N) :
    ∃ out : JointC1ApproximationData N g D, out.reference = r.continuousMap := by
  obtain ⟨n,⟨e⟩⟩ := compact_euclidean_embedding_exists N
  have he : ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) 1 (e.map ∘ r.map) :=
    (e.smooth.of_le (by simp)).comp r.c1
  obtain ⟨C,hC,hbound⟩ := bound n (e.map ∘ r.map) he
  have hdensity := density N g r.map r.c1
  refine ⟨{ reference := r.continuousMap
            ends := ?_
            correct_class := r.correct_class
            differentiable := ?_
            integrable := ?_
            dimension := n
            embedding := e
            C := C
            C_nonneg := hC
            derivative_bound := ?_
            extension := r.map
            joint_c1 := r.c1
            extension_agrees := fun q => rfl },rfl⟩
  · intro q hq
    change r.map ((q.1:ℝ),q.2) = D.base
    rcases hq with hzero | hone
    · rw [hzero]; exact (r.ends q.2).1
    · rw [hone]; exact (r.ends q.2).2
  · intro s
    have hs : ContMDiff (𝓡 2) SweepModel 1 (fun p : Sphere2 => ((s:ℝ),p)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (r.c1.comp hs).mdifferentiable (by simp)
  · intro s
    have hs : Continuous (fun p : Sphere2 => ((s:ℝ),p)) :=
      continuous_const.prodMk continuous_id
    have hc : Continuous (sphereEnergyDensity N g (fun p => r.continuousMap (s,p))) :=
      hdensity.comp hs
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro s p i
    exact hbound s p i
/-- **Math.** New scalar side-condition leaves and the two running C1-approximation leaves
suffice to construct the former data with the exact same reference. -/
theorem C1ClassRepresentative.toEmbedding (density : C1SphereEnergyContinuityStatement.{u})
    (bound : C1AmbientFrameBoundStatement) (restrict : CylinderRestrictionEstimateStatement)
    (extend : CylinderCompactExtensionStatement) {N : CompactSmoothThree.{u}}
    {D : BasedSphereClass N} (r : C1ClassRepresentative N D)
    (g : Riemannian.RiemannianMetric (𝓡 3) N) :
    ∃ out : EmbeddingApproximationData N g D, out.reference = r.continuousMap := by
  obtain ⟨j,hj⟩ := r.toJoint density bound g
  obtain ⟨out,hout⟩ := j.toEmbedding (cylinder_c1_after_uniform restrict extend)
  exact ⟨out,hout.trans hj⟩
#print axioms C1ClassRepresentative.toJoint
#print axioms C1ClassRepresentative.toEmbedding
end PoincareConjecture.ProofContract.Refinement20260927
