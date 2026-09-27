import PoincareConjecture.ProofContract.Refinement20260927.IntrinsicEnergyRoot
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff BigOperators
/-- **Math.** A specified smooth map sends the reference to the designated
non-null target class. This is geometry to be supplied, not a choice of a
possibly constant target sweepout. No energy conclusion is stored. -/
structure SmoothClassMap {M N : CompactSmoothThree.{u}}
    (C : BasedSphereClass M) (D : BasedSphereClass N) where
  map : M → N
  smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ map
  based : map C.base = D.base
  reference : ((⟨map, smooth.continuous⟩ : C(M,N)).comp C.reference.continuousMap).HomotopicRel
    D.reference.continuousMap sweepoutEnds
/-- **Math.** Composition retains the two specified endpoint values. -/
def SmoothClassMap.sendSweepout {M N : CompactSmoothThree.{u}}
    {C : BasedSphereClass M} {D : BasedSphereClass N} (h : SmoothClassMap C D)
    (f : SmoothBasedSweepout M C.base) : SmoothBasedSweepout N D.base where
  map := h.map ∘ f.map
  smooth := h.smooth.comp f.smooth
  ends := by
    intro p
    constructor
    · exact (congrArg h.map (f.ends p).1).trans h.based
    · exact (congrArg h.map (f.ends p).2).trans h.based
/-- **Math.** Every representative goes to the SAME prescribed relative class. -/
def SmoothClassMap.send {M N : CompactSmoothThree.{u}}
    {C : BasedSphereClass M} {D : BasedSphereClass N} (h : SmoothClassMap C D)
    (f : C.Representative) : D.Representative := by
  refine ⟨h.sendSweepout f.val, ?_⟩
  have hp := f.property.comp_continuousMap (⟨h.map,h.smooth.continuous⟩ : C(M,N))
  exact hp.trans h.reference
/-- **Math.** Pointwise contraction of the target tensor through a specified map.
The constant is an ENERGY factor, not a distance Lipschitz factor. -/
def TargetMetricBound {M N : CompactSmoothThree.{u}}
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) (f : M → N) (L : ℝ) : Prop :=
  ∀ p : M, ∀ v : TangentSpace (𝓡 3) p,
    gN.metricInner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v)
      (mfderiv (𝓡 3) (𝓡 3) f p v) ≤ L * gM.metricInner p v v
theorem sphere_density_postcompose_le {M N : CompactSmoothThree.{u}}
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N)
    (phi : M → N) (hphi : ContMDiff (𝓡 3) (𝓡 3) ∞ phi)
    (f : Sphere2 → M) (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
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
/-- **Math.** Both actual Bochner integrals are integrable; no default-value shortcut. -/
theorem sphere_energy_postcompose_le (continuousEnergy : SphereEnergyContinuityStatement.{u})
    {M N : CompactSmoothThree.{u}} (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N)
    (phi : M → N) (hphi : ContMDiff (𝓡 3) (𝓡 3) ∞ phi)
    (f : Sphere2 → M) (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
    {L : ℝ} (hL : TargetMetricBound gM gN phi L) :
    sphereDirichletEnergy N gN (phi ∘ f) ≤ L * sphereDirichletEnergy M gM f := by
  have hn := sphere_density_integrable continuousEnergy N gN (phi ∘ f) (hphi.comp hf)
  have hm := sphere_density_integrable continuousEnergy M gM f hf
  have hi := integral_mono hn (hm.const_mul L)
    (sphere_density_postcompose_le gM gN phi hphi f hf hL)
  simpa only [integral_const_mul,sphereDirichletEnergy] using hi
/-- **Math.** An exact contraction respecting the designated relative class
constructs the old transfer record, including its actual representative map. -/
def SmoothClassMap.toTransfer (continuousEnergy : SphereEnergyContinuityStatement.{u})
    {M N : CompactSmoothThree.{u}} {C : BasedSphereClass M} {D : BasedSphereClass N}
    (h : SmoothClassMap C D) (gM : ℝ → Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : ℝ → Riemannian.RiemannianMetric (𝓡 3) N) (t : ℝ)
    (hL : TargetMetricBound (gM t) (gN t) h.map 1) :
    SweepoutTransfer (intrinsicSpectrum continuousEnergy M C gM)
      (intrinsicSpectrum continuousEnergy N D gN) t where
  send := h.send
  reparam := fun _ x => x
  energy_le := by
    intro i x
    have hf : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p => i.val.map ((x:ℝ),p)) :=
      i.val.smooth.comp (contMDiff_const.prodMk contMDiff_id)
    simpa only [intrinsicSpectrum,SmoothClassMap.send,SmoothClassMap.sendSweepout,Function.comp_def,one_mul]
      using sphere_energy_postcompose_le continuousEnergy (gM t) (gN t) h.map h.smooth
        (fun p => i.val.map ((x:ℝ),p)) hf hL
#print axioms SmoothClassMap.sendSweepout
#print axioms SmoothClassMap.send
#print axioms sphere_density_postcompose_le
#print axioms sphere_energy_postcompose_le
#print axioms SmoothClassMap.toTransfer
end PoincareConjecture.ProofContract.Refinement20260927
