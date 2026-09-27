import PoincareConjecture.ProofContract.Refinement20260927.C1EnergyApproximation
import PoincareConjecture.ParallelImplementation.RefinedC1SphereEnergyContinuity
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff
/-- **Math.** Independently rebuilt proof for the actual C1 input map. -/
theorem checked_c1_density_continuity : C1SphereEnergyContinuityStatement.{u} :=
  ParallelImplementation.RefinedC1SphereEnergyContinuity.c1_sphere_energy_continuity
/-- **Math.** C1 slices have genuine integrable densities; no default integral value is used. -/
theorem c1_sphere_density_integrable (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (f : Sphere2 → N)
    (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f) :
    Integrable (sphereEnergyDensity N g f) sphereEnergyMeasure := by
  have hs : ContMDiff SweepModel (𝓡 2) 1 (Prod.snd : ℝ × Sphere2 → Sphere2) := contMDiff_snd
  have hc := checked_c1_density_continuity N g (fun q : ℝ × Sphere2 => f q.2) (hf.comp hs)
  have hslice : Continuous (fun p : Sphere2 => ((0:ℝ),p)) := continuous_const.prodMk continuous_id
  have h : Continuous (sphereEnergyDensity N g f) := hc.comp hslice
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
/-- **Math.** The actual integrated energy is continuous in the parameter already at C1. -/
theorem c1_sphere_energy_parameter_continuous (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (f : ℝ × Sphere2 → N)
    (hf : ContMDiff SweepModel (𝓡 3) 1 f) :
    Continuous (fun s : ℝ => sphereDirichletEnergy N g (fun p => f (s,p))) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := sphereEnergyMeasure) (f := fun s p => sphereEnergyDensity N g (fun z => f (s,z)) p)
    (checked_c1_density_continuity N g f hf) isCompact_univ
  simpa only [sphereDirichletEnergy, Measure.restrict_univ] using h
/-- **Math.** Only the three still-running analytic leaves remain here. -/
theorem C1ClassRepresentative.approximate_after_density
    (bound : C1AmbientFrameBoundStatement) (restrict : CylinderRestrictionEstimateStatement)
    (extend : CylinderCompactExtensionStatement) {N : CompactSmoothThree.{u}}
    {D : BasedSphereClass N} (r : C1ClassRepresentative N D)
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (eps : ℝ) (heps : 0 < eps) :
    ∃ h : D.Representative, ∀ s : SweepParameter,
      sphereDirichletEnergy N g (fun p => h.val.map ((s:ℝ),p)) ≤
        sphereDirichletEnergy N g (fun p => r.continuousMap (s,p)) + eps :=
  r.approximate checked_c1_density_continuity bound restrict extend g eps heps
#print axioms checked_c1_density_continuity
#print axioms c1_sphere_density_integrable
#print axioms c1_sphere_energy_parameter_continuous
#print axioms C1ClassRepresentative.approximate_after_density
end PoincareConjecture.ProofContract.Refinement20260927
