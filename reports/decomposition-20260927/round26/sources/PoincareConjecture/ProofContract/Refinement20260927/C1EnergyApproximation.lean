import PoincareConjecture.ProofContract.Refinement20260927.C1ReferenceConstruction
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff
/-- **Math.** Compose the checked approximation interfaces while preserving this reference. -/
theorem C1ClassRepresentative.toRegularization (density : C1SphereEnergyContinuityStatement.{u})
    (bound : C1AmbientFrameBoundStatement) (restrict : CylinderRestrictionEstimateStatement)
    (extend : CylinderCompactExtensionStatement) {N : CompactSmoothThree.{u}}
    {D : BasedSphereClass N} (r : C1ClassRepresentative N D)
    (g : Riemannian.RiemannianMetric (𝓡 3) N) :
    ∃ out : RegularizationData N g D, out.reference = r.continuousMap := by
  obtain ⟨e,he⟩ := r.toEmbedding density bound restrict extend g
  obtain ⟨n,hn⟩ := e.toNormal checked_embedded_normal_coordinates
  obtain ⟨t,ht⟩ := n.toTubular checked_normal_linear_equiv checked_normal_endpoint_jet
    checked_tubular_chart_inverse
  obtain ⟨a,ha⟩ := t.toRetraction checked_tubular_inverse_assembly
  obtain ⟨out,hout⟩ := a.toRegularization checked_smooth_retraction_form
  exact ⟨out,hout.trans (ha.trans (ht.trans (hn.trans he)))⟩
/-- **Math.** A smooth representative in the same based homotopy class with one additive
energy error for every slice. The existence of the initial C1 representative is not asserted. -/
theorem C1ClassRepresentative.approximate (density : C1SphereEnergyContinuityStatement.{u})
    (bound : C1AmbientFrameBoundStatement) (restrict : CylinderRestrictionEstimateStatement)
    (extend : CylinderCompactExtensionStatement) {N : CompactSmoothThree.{u}}
    {D : BasedSphereClass N} (r : C1ClassRepresentative N D)
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (eps : ℝ) (heps : 0 < eps) :
    ∃ h : D.Representative, ∀ s : SweepParameter,
      sphereDirichletEnergy N g (fun p => h.val.map ((s:ℝ),p)) ≤
        sphereDirichletEnergy N g (fun p => r.continuousMap (s,p)) + eps := by
  obtain ⟨out,hout⟩ := r.toRegularization density bound restrict extend g
  obtain ⟨h,hh⟩ := out.approximate checked_relative_retraction checked_sphere_energy_approximation eps heps
  refine ⟨h,?_⟩
  intro s
  simpa only [hout] using hh s
/-- **Math.** Exact slice-energy control by a given C1 representative; no smooth approximation
or coefficient bound is assumed. This is not a global geometric-flow producer. -/
def C1ClassTransfer (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ i : source.sweepouts.Representative,
    ∃ r : C1ClassRepresentative target.space target.sweepouts,
      ∀ s : SweepParameter, sphereDirichletEnergy target.space (target.metric t)
        (fun p => r.continuousMap (s,p)) ≤
          (source.spectrum checked_sphere_energy_continuity).energy i t s
/-- **Math.** The same C1 maps yield smooth transfer in the prescribed relative classes. -/
theorem c1ClassTransfer_to_additive (density : C1SphereEnergyContinuityStatement.{u})
    (bound : C1AmbientFrameBoundStatement) (restrict : CylinderRestrictionEstimateStatement)
    (extend : CylinderCompactExtensionStatement) {source target : IntrinsicSpectrumData.{u}}
    {t : ℝ} (h : C1ClassTransfer source target t) :
    AdditiveRepresentativeTransfer (source.spectrum checked_sphere_energy_continuity)
      (target.spectrum checked_sphere_energy_continuity) t := by
  intro eps heps i
  obtain ⟨r,hr⟩ := h i
  obtain ⟨j,hj⟩ := r.approximate density bound restrict extend (target.metric t) eps heps
  refine ⟨j,?_⟩
  intro s
  exact (hj s).trans (add_le_add ((hr s).trans
    ((source.spectrum checked_sphere_energy_continuity).energy_le_peak i t s)) le_rfl)
/-- **Math.** The min-max width inequality consumes the actual C1 class transfer. -/
theorem c1ClassTransfer_width_le (density : C1SphereEnergyContinuityStatement.{u})
    (bound : C1AmbientFrameBoundStatement) (restrict : CylinderRestrictionEstimateStatement)
    (extend : CylinderCompactExtensionStatement) {source target : IntrinsicSpectrumData.{u}}
    {t : ℝ} (h : C1ClassTransfer source target t) :
    (target.spectrum checked_sphere_energy_continuity).width t ≤
      (source.spectrum checked_sphere_energy_continuity).width t :=
  additiveTransfer_width_le (c1ClassTransfer_to_additive density bound restrict extend h)
#print axioms C1ClassRepresentative.toRegularization
#print axioms C1ClassRepresentative.approximate
#print axioms c1ClassTransfer_to_additive
#print axioms c1ClassTransfer_width_le
end PoincareConjecture.ProofContract.Refinement20260927
