import PoincareConjecture.ProofContract.Refinement20260927.IntrinsicSphereEnergy
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff BigOperators
/-- **Math.** Finiteness of the Bochner integral is proved, not inferred from a
possibly nonintegrable integral's default value. -/
theorem sphere_density_integrable (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (M : CompactSmoothThree.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) M)
    (f : Sphere2 → M) (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) :
    Integrable (sphereEnergyDensity M g f) sphereEnergyMeasure := by
  have h := continuousEnergy M g (fun q : ℝ × Sphere2 => f q.2) (hf.comp contMDiff_snd)
  have hc : Continuous (sphereEnergyDensity M g f) :=
    h.comp (continuous_const.prodMk continuous_id : Continuous (fun p : Sphere2 => ((0:ℝ),p)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem sphere_energy_parameter_continuous (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (M : CompactSmoothThree.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) M)
    (f : ℝ × Sphere2 → M) (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ∞ f) :
    Continuous (fun s : ℝ => sphereDirichletEnergy M g (fun p => f (s,p))) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := sphereEnergyMeasure) (f := fun s p => sphereEnergyDensity M g (fun z => f (s,z)) p)
    (continuousEnergy M g f hf) isCompact_univ
  simpa only [sphereDirichletEnergy, Measure.restrict_univ] using h
/-- **Math.** Real based sweepouts, smooth in the parameter and sphere variables. -/
structure SmoothBasedSweepout (M : CompactSmoothThree.{u}) (base : M) where
  map : ℝ × Sphere2 → M
  smooth : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ∞ map
  ends : ∀ p : Sphere2, map (0,p) = base ∧ map (1,p) = base
def SmoothBasedSweepout.continuousMap {M : CompactSmoothThree.{u}} {base : M}
    (f : SmoothBasedSweepout M base) : C(SweepParameter × Sphere2, M) :=
  ⟨fun q => f.map ((q.1:ℝ),q.2), f.smooth.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
def sweepoutEnds : Set (SweepParameter × Sphere2) := {q | (q.1:ℝ)=0 ∨ (q.1:ℝ)=1}
/-- **Math.** Fixed genuinely non-null relative homotopy class. Its existence
and agreement with the desired geometric sweepout theory remain to be proved. -/
structure BasedSphereClass (M : CompactSmoothThree.{u}) where
  base : M
  reference : SmoothBasedSweepout M base
  nontrivial : ¬ reference.continuousMap.HomotopicRel
    (ContinuousMap.const (SweepParameter × Sphere2) base) sweepoutEnds
/-- **Math.** ALL globally parameter-smooth representatives in this fixed class,
not an unrelated freely chosen family of numerical energies. -/
def BasedSphereClass.Representative {M : CompactSmoothThree.{u}} (C : BasedSphereClass M) :=
  {f : SmoothBasedSweepout M C.base // f.continuousMap.HomotopicRel C.reference.continuousMap sweepoutEnds}
instance {M : CompactSmoothThree.{u}} (C : BasedSphereClass M) : Nonempty C.Representative :=
  ⟨⟨C.reference, ContinuousMap.HomotopicRel.refl _⟩⟩
def intrinsicSpectrum (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (M : CompactSmoothThree.{u}) (C : BasedSphereClass M)
    (g : ℝ → Riemannian.RiemannianMetric (𝓡 3) M) : SweepoutSpectrum.{u} where
  index := C.Representative
  nonempty := inferInstance
  energy := fun f t s => sphereDirichletEnergy M (g t) (fun p => f.val.map ((s:ℝ),p))
  nonneg := fun f t s => sphereDirichletEnergy_nonneg M (g t) _
  bounded := by
    intro f t
    have h : Continuous (fun s : SweepParameter => sphereDirichletEnergy M (g t)
        (fun p => f.val.map ((s:ℝ),p))) :=
      (sphere_energy_parameter_continuous continuousEnergy M (g t) f.val.map f.val.smooth).comp continuous_subtype_val
    exact (isCompact_range h).bddAbove
theorem intrinsic_energy_relative (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (M : CompactSmoothThree.{u}) (C : BasedSphereClass M)
    (g : ℝ → Riemannian.RiemannianMetric (𝓡 3) M) {a b t eta : ℝ}
    (hab : a ≤ b) (hg : MorganTianLib.IsSmoothMetricFamilyOn g (Icc a b))
    (ht : t ∈ Icc a b) (he : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc a b, dist s t < r → ∀ i x,
      (1-eta)*(intrinsicSpectrum continuousEnergy M C g).energy i t x ≤
        (intrinsicSpectrum continuousEnergy M C g).energy i s x ∧
      (intrinsicSpectrum continuousEnergy M C g).energy i s x ≤
        (1+eta)*(intrinsicSpectrum continuousEnergy M C g).energy i t x := by
  obtain ⟨r,hr,hcompare⟩ := compare M g a b hab hg t ht eta he
  refine ⟨r,hr,?_⟩
  intro s hs hst i x
  let f : Sphere2 → M := fun p => i.val.map ((x:ℝ),p)
  have hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f := i.val.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hp (p : Sphere2) :
      (1-eta)*sphereEnergyDensity M (g t) f p ≤ sphereEnergyDensity M (g s) f p ∧
      sphereEnergyDensity M (g s) f p ≤ (1+eta)*sphereEnergyDensity M (g t) f p := by
    have hl := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      (hcompare s hs hst (f p) (mfderiv (𝓡 2) (𝓡 3) f p (sphereEnergyFrame p j))).1)
    have hu := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      (hcompare s hs hst (f p) (mfderiv (𝓡 2) (𝓡 3) f p (sphereEnergyFrame p j))).2)
    simp only [← Finset.mul_sum] at hl hu
    unfold sphereEnergyDensity
    constructor <;> nlinarith
  have hit := sphere_density_integrable continuousEnergy M (g t) f hf
  have his := sphere_density_integrable continuousEnergy M (g s) f hf
  have lo := integral_mono (hit.const_mul (1-eta)) his (fun p => (hp p).1)
  have hi := integral_mono his (hit.const_mul (1+eta)) (fun p => (hp p).2)
  simpa only [integral_const_mul, intrinsicSpectrum, sphereDirichletEnergy, f] using And.intro lo hi
/-- **Math.** Intrinsic metric comparison implies continuity of the actual
Dirichlet min-max spectrum on the fixed class, without a chosen minimizer. -/
theorem intrinsic_width_continuous (continuousEnergy : SphereEnergyContinuityStatement.{u})
    (compare : IntrinsicMetricTimeComparisonStatement.{u})
    (M : CompactSmoothThree.{u}) (C : BasedSphereClass M)
    (g : ℝ → Riemannian.RiemannianMetric (𝓡 3) M) {a b : ℝ}
    (hab : a ≤ b) (hg : MorganTianLib.IsSmoothMetricFamilyOn g (Icc a b)) :
    ContinuousOn (intrinsicSpectrum continuousEnergy M C g).width (Icc a b) := by
  let F := intrinsicSpectrum continuousEnergy M C g
  intro t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro e he
  let eta := min (1/2 : ℝ) (e/(F.width t+1))
  have hw := F.width_nonneg t
  have heta : 0 < eta := lt_min (by norm_num) (div_pos he (by linarith))
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hcost : eta * F.width t < e := by
    have h := (le_div_iff₀ (show 0 < F.width t+1 by linarith)).mp
      (min_le_right (1/2 : ℝ) (e/(F.width t+1)))
    change eta*(F.width t+1) ≤ e at h
    nlinarith
  obtain ⟨r,hr,hcompare⟩ := intrinsic_energy_relative continuousEnergy compare M C g hab hg ht heta
  refine ⟨r,hr,?_⟩
  intro s hs hst
  have hbounds := width_sandwich F s t (1-eta) (1+eta) (by linarith) (by linarith)
    (hcompare s hs hst)
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [hbounds.1,hbounds.2,hcost]
#print axioms sphere_density_integrable
#print axioms sphere_energy_parameter_continuous
#print axioms intrinsicSpectrum
#print axioms intrinsic_energy_relative
#print axioms intrinsic_width_continuous
end PoincareConjecture.ProofContract.Refinement20260927
