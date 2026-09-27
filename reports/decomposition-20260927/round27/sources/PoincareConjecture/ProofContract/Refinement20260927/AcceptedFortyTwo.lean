import PoincareConjecture.ProofContract.Refinement20260927.AcceptedFortyOne
import PoincareConjecture.ParallelImplementation.RefinedC1AmbientFrameBound
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
open scoped Manifold ContDiff
/-- **Math.** The fixed frame-bound proof uses the invariant trace, not global frame continuity. -/
theorem checked_c1_ambient_frame_bound : C1AmbientFrameBoundStatement :=
  ParallelImplementation.RefinedC1AmbientFrameBound.c1_ambient_frame_bound
/-- **Math.** Only the compact extension leaf remains for smoothing a given C1 representative. -/
theorem C1ClassRepresentative.approximate_after_bounds (extend : CylinderCompactExtensionStatement)
    {N : CompactSmoothThree.{u}} {D : BasedSphereClass N} (r : C1ClassRepresentative N D)
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (eps : ℝ) (heps : 0 < eps) :
    ∃ h : D.Representative, ∀ s : SweepParameter,
      sphereDirichletEnergy N g (fun p => h.val.map ((s:ℝ),p)) ≤
        sphereDirichletEnergy N g (fun p => r.continuousMap (s,p)) + eps :=
  r.approximate checked_c1_density_continuity checked_c1_ambient_frame_bound
    checked_cylinder_restriction extend g eps heps
/-- **Math.** Same public V1 conclusion; topology and controlled geometric production remain open. -/
theorem public_after_forty_two (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (extend : CylinderCompactExtensionStatement)
    (geometry : C1GeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_forty_one triangulate atlas checked_c1_ambient_frame_bound extend geometry
/-- **Math.** A concrete C1 tensor contraction controls width after only the extension leaf. -/
theorem C1ClassMap.width_after_bounds (extend : CylinderCompactExtensionStatement)
    {source target : IntrinsicSpectrumData.{u}}
    (h : C1ClassMap source.sweepouts target.sweepouts) (t : ℝ)
    (hL : TargetMetricBound (source.metric t) (target.metric t) h.map 1) :
    (target.spectrum checked_sphere_energy_continuity).width t ≤
      (source.spectrum checked_sphere_energy_continuity).width t :=
  h.width_le checked_c1_ambient_frame_bound checked_cylinder_restriction extend t hL
#print axioms C1ClassMap.width_after_bounds
#print axioms checked_c1_ambient_frame_bound
#print axioms C1ClassRepresentative.approximate_after_bounds
#print axioms public_after_forty_two
end PoincareConjecture.ProofContract.Refinement20260927
