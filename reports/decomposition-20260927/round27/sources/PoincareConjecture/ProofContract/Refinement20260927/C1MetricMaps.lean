import PoincareConjecture.ProofContract.Refinement20260927.C1GeometryRoot
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff BigOperators
/-- **Math.** A given C1 map respects the designated non-null class, not an arbitrary new class. -/
structure C1ClassMap {M N : CompactSmoothThree.{u}}
    (C : BasedSphereClass M) (D : BasedSphereClass N) where
  map : M → N
  c1 : ContMDiff (𝓡 3) (𝓡 3) 1 map
  based : map C.base = D.base
  reference : ((⟨map,c1.continuous⟩ : C(M,N)).comp C.reference.continuousMap).HomotopicRel
    D.reference.continuousMap sweepoutEnds
/-- **Math.** Postcomposition produces a C1 representative in the same prescribed relative class. -/
def C1ClassMap.send {M N : CompactSmoothThree.{u}}
    {C : BasedSphereClass M} {D : BasedSphereClass N} (h : C1ClassMap C D)
    (f : C.Representative) : C1ClassRepresentative N D where
  map := h.map ∘ f.val.map
  c1 := h.c1.comp (f.val.smooth.of_le (by simp))
  ends := by
    intro p
    exact ⟨(congrArg h.map (f.val.ends p).1).trans h.based,
      (congrArg h.map (f.val.ends p).2).trans h.based⟩
  correct_class := by
    have hp := f.property.comp_continuousMap (⟨h.map,h.c1.continuous⟩ : C(M,N))
    exact hp.trans h.reference
/-- **Math.** Older smooth class maps give C1 maps without extra assumptions. -/
def SmoothClassMap.toC1 {M N : CompactSmoothThree.{u}}
    {C : BasedSphereClass M} {D : BasedSphereClass N} (h : SmoothClassMap C D) : C1ClassMap C D where
  map := h.map
  c1 := h.smooth.of_le (by simp)
  based := h.based
  reference := h.reference
/-- **Math.** C1 suffices for the same pointwise chain-rule estimate. -/
theorem c1_sphere_density_postcompose_le {M N : CompactSmoothThree.{u}}
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N)
    (phi : M → N) (hphi : ContMDiff (𝓡 3) (𝓡 3) 1 phi)
    (f : Sphere2 → M) (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f)
    {L : ℝ} (hL : TargetMetricBound gM gN phi L) (p : Sphere2) :
    sphereEnergyDensity N gN (phi ∘ f) p ≤ L * sphereEnergyDensity M gM f p := by
  have hc := mfderiv_comp p (hphi.mdifferentiable (by norm_num) (f p))
    (hf.mdifferentiable (by norm_num) p)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hL (f p) (mfderiv (𝓡 2) (𝓡 3) f p (sphereEnergyFrame p i)))
  simp only [← Finset.mul_sum] at hs
  unfold sphereEnergyDensity
  simp only [hc,ContinuousLinearMap.comp_apply,Function.comp_apply]
  nlinarith
/-- **Math.** Genuine integrability of both C1 densities justifies the integral inequality. -/
theorem c1_sphere_energy_postcompose_le {M N : CompactSmoothThree.{u}}
    (gM : Riemannian.RiemannianMetric (𝓡 3) M) (gN : Riemannian.RiemannianMetric (𝓡 3) N)
    (phi : M → N) (hphi : ContMDiff (𝓡 3) (𝓡 3) 1 phi)
    (f : Sphere2 → M) (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f)
    {L : ℝ} (hL : TargetMetricBound gM gN phi L) :
    sphereDirichletEnergy N gN (phi ∘ f) ≤ L * sphereDirichletEnergy M gM f := by
  have hn := c1_sphere_density_integrable N gN (phi ∘ f) (hphi.comp hf)
  have hm := c1_sphere_density_integrable M gM f hf
  have hi := integral_mono hn (hm.const_mul L)
    (c1_sphere_density_postcompose_le gM gN phi hphi f hf hL)
  simpa only [integral_const_mul,sphereDirichletEnergy] using hi
/-- **Math.** A differential tensor contraction constructs the actual class transfer. -/
theorem C1ClassMap.toClassTransfer {source target : IntrinsicSpectrumData.{u}}
    (h : C1ClassMap source.sweepouts target.sweepouts) (t : ℝ)
    (hL : TargetMetricBound (source.metric t) (target.metric t) h.map 1) :
    C1ClassTransfer source target t := by
  intro i
  refine ⟨h.send i,?_⟩
  intro s
  have hs : ContMDiff (𝓡 2) SweepModel 1 (fun p : Sphere2 => ((s:ℝ),p)) :=
    contMDiff_const.prodMk contMDiff_id
  have hf : ContMDiff (𝓡 2) (𝓡 3) 1 (fun p : Sphere2 => i.val.map ((s:ℝ),p)) :=
    (i.val.smooth.of_le (by simp)).comp hs
  have result := c1_sphere_energy_postcompose_le (source.metric t) (target.metric t)
    h.map h.c1 (fun p => i.val.map ((s:ℝ),p)) hf hL
  change sphereDirichletEnergy target.space (target.metric t)
    (fun p => h.map (i.val.map ((s:ℝ),p))) ≤ _
  simpa only [IntrinsicSpectrumData.spectrum,intrinsicSpectrum,Function.comp_def,one_mul] using result
/-- **Math.** The three remaining analytic proofs turn the concrete C1 map into width monotonicity. -/
theorem C1ClassMap.width_le (bound : C1AmbientFrameBoundStatement)
    (restrict : CylinderRestrictionEstimateStatement) (extend : CylinderCompactExtensionStatement)
    {source target : IntrinsicSpectrumData.{u}} (h : C1ClassMap source.sweepouts target.sweepouts)
    (t : ℝ) (hL : TargetMetricBound (source.metric t) (target.metric t) h.map 1) :
    (target.spectrum checked_sphere_energy_continuity).width t ≤
      (source.spectrum checked_sphere_energy_continuity).width t :=
  c1ClassTransfer_width_le checked_c1_density_continuity bound restrict extend (h.toClassTransfer t hL)
#print axioms C1ClassMap.send
#print axioms SmoothClassMap.toC1
#print axioms c1_sphere_density_postcompose_le
#print axioms c1_sphere_energy_postcompose_le
#print axioms C1ClassMap.toClassTransfer
#print axioms C1ClassMap.width_le
end PoincareConjecture.ProofContract.Refinement20260927
