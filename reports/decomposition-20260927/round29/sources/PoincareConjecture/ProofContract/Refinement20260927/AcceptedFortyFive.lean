import PoincareConjecture.ProofContract.Refinement20260927.RadialExtensionConstruction
import PoincareConjecture.ParallelImplementation.RefinedRadialLocalSmooth
import PoincareConjecture.ParallelImplementation.RefinedCylinderCutoffGlue
import PoincareConjecture.ParallelImplementation.RefinedCylinderCutoffSupport
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1
open scoped Manifold ContDiff
/-- **Math.** Independently rebuilt local radial witness for the original formula. -/
theorem checked_radial_local_smooth : RadialLocalSmoothStatement :=
  ParallelImplementation.RefinedRadialLocalSmooth.radial_local_smooth
/-- **Math.** The cutoff eliminates the singular axis on an open neighborhood. -/
theorem checked_cylinder_cutoff_glue : CylinderCutoffGlueStatement :=
  ParallelImplementation.RefinedCylinderCutoffGlue.cylinder_cutoff_glue
/-- **Math.** Compact support and exact restriction use the same explicit extension. -/
theorem checked_cylinder_cutoff_support : CylinderCutoffSupportStatement :=
  ParallelImplementation.RefinedCylinderCutoffSupport.cylinder_cutoff_support
/-- **Math.** The previously open extension statement now has no open proof input. -/
theorem checked_cylinder_compact_extension : CylinderCompactExtensionStatement :=
  cylinder_extension_of_radial_leaves checked_radial_local_smooth
    checked_cylinder_cutoff_glue checked_cylinder_cutoff_support
/-- **Math.** Actual uniform value and sphere-derivative approximation for a given C1 map. -/
theorem checked_cylinder_c1_approximation : CylinderC1ApproximationStatement :=
  cylinder_c1_after_restriction checked_cylinder_compact_extension
/-- **Math.** Smooth representatives in the same based class, with one energy error for all slices. -/
theorem C1ClassRepresentative.approximate_checked
    {N : CompactSmoothThree.{u}} {D : BasedSphereClass N} (r : C1ClassRepresentative N D)
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (eps : ℝ) (heps : 0 < eps) :
    ∃ h : D.Representative, ∀ s : SweepParameter,
      sphereDirichletEnergy N g (fun p => h.val.map ((s:ℝ),p)) ≤
        sphereDirichletEnergy N g (fun p => r.continuousMap (s,p)) + eps :=
  r.approximate_after_bounds checked_cylinder_compact_extension g eps heps
/-- **Math.** A supplied C1 class transfer now implies width monotonicity without analytic premises. -/
theorem c1ClassTransfer_width_checked {source target : IntrinsicSpectrumData.{u}}
    {t : ℝ} (h : C1ClassTransfer source target t) :
    (target.spectrum checked_sphere_energy_continuity).width t ≤
      (source.spectrum checked_sphere_energy_continuity).width t :=
  c1ClassTransfer_width_le checked_c1_density_continuity checked_c1_ambient_frame_bound
    checked_cylinder_restriction checked_cylinder_compact_extension h
/-- **Math.** The supplied concrete map and tensor contraction produce the claimed width comparison. -/
theorem C1ClassMap.width_checked {source target : IntrinsicSpectrumData.{u}}
    (h : C1ClassMap source.sweepouts target.sweepouts) (t : ℝ)
    (hL : TargetMetricBound (source.metric t) (target.metric t) h.map 1) :
    (target.spectrum checked_sphere_energy_continuity).width t ≤
      (source.spectrum checked_sphere_energy_continuity).width t :=
  h.width_after_bounds checked_cylinder_compact_extension t hL
/-- **Math.** All subsidiary C1 analysis is discharged; the three research producers remain. -/
theorem public_after_forty_five (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (geometry : C1GeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_after_forty_two triangulate atlas checked_cylinder_compact_extension geometry
#print axioms checked_radial_local_smooth
#print axioms checked_cylinder_cutoff_glue
#print axioms checked_cylinder_cutoff_support
#print axioms checked_cylinder_compact_extension
#print axioms checked_cylinder_c1_approximation
#print axioms C1ClassRepresentative.approximate_checked
#print axioms c1ClassTransfer_width_checked
#print axioms C1ClassMap.width_checked
#print axioms public_after_forty_five
end PoincareConjecture.ProofContract.Refinement20260927
