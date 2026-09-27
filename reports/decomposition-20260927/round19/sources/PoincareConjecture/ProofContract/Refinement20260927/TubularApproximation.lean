import PoincareConjecture.ProofContract.Refinement20260927.CompactTubularReuse
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** Derivatives use the given embedding; a later choice of local
inverse must not replace the map used by the approximating sequence. -/
def embeddedSphereVector {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) (f : Sphere2 → N) (p : Sphere2)
    (i : Fin (Module.finrank ℝ SphereModel)) : ApproxAmbient n :=
  mfderiv (𝓡 2) 𝓘(ℝ, ApproxAmbient n) (e.map ∘ f) p (sphereEnergyFrame p i)
/-- **Math.** Only local inverse charts, not a global tubular retraction, are
required here. Producing these charts and approximants remains research. -/
structure TubularApproximationData (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (D : BasedSphereClass N) where
  reference : C(SweepDomain,N)
  ends : EqOn reference (ContinuousMap.const SweepDomain D.base) sweepoutEnds
  correct_class : reference.HomotopicRel D.reference.continuousMap sweepoutEnds
  differentiable : ∀ s : SweepParameter, MDifferentiable (𝓡 2) (𝓡 3) (fun p => reference (s,p))
  integrable : ∀ s : SweepParameter,
    Integrable (sphereEnergyDensity N g (fun p => reference (s,p))) sphereEnergyMeasure
  dimension : ℕ
  embedding : CompactEuclideanEmbedding N dimension
  localTube : LocalTubularData embedding
  C : ℝ
  C_nonneg : 0 ≤ C
  derivative_bound : ∀ (s : SweepParameter) p i,
    ‖embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ C
  approximants : ∀ delta : ℝ, 0 < delta → ∃ h : SmoothBasedSweepout N D.base,
    (∀ q : SweepDomain, dist (embedding.map (h.continuousMap q))
      (embedding.map (reference q)) < delta) ∧
    ∀ (s : SweepParameter) p i, ‖embeddedSphereVector embedding (fun p => h.map ((s:ℝ),p)) p i -
      embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ delta
/-- **Math.** Build the formerly required global retraction without changing
reference, embedding, or any derivative used in its approximation data. -/
theorem TubularApproximationData.toRetraction (assemble : TubularInverseAssemblyStatement.{u})
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : TubularApproximationData N g D) :
    ∃ R : RetractionApproximationData N g D, R.reference = r.reference := by
  obtain ⟨retraction,he⟩ := local_tubes_retraction_of_assembly assemble r.localTube
  have hv (f : Sphere2 → N) (p : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
      retractionSphereVector retraction.toAmbientRetraction f p i =
        embeddedSphereVector r.embedding f p i := by
    unfold retractionSphereVector embeddedSphereVector
    rw [he]
  refine ⟨{ reference := r.reference
            ends := r.ends
            correct_class := r.correct_class
            differentiable := r.differentiable
            integrable := r.integrable
            dimension := r.dimension
            retraction := retraction
            C := r.C
            C_nonneg := r.C_nonneg
            derivative_bound := ?_
            approximants := ?_ },rfl⟩
  · intro s p i
    rw [hv]
    exact r.derivative_bound s p i
  · intro delta hd
    obtain ⟨h,hclose,hderiv⟩ := r.approximants delta hd
    refine ⟨h,?_,?_⟩
    · intro q
      rw [he]
      exact hclose q
    · intro s p i
      rw [hv,hv]
      exact hderiv s p i
/-- **Math.** A transfer entrance with actual local tubular witnesses. -/
def TubularClassTransfer (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ i : source.sweepouts.Representative,
    ∃ r : TubularApproximationData target.space (target.metric t) target.sweepouts,
      ∀ x : SweepParameter, sphereDirichletEnergy target.space (target.metric t)
        (fun p => r.reference (x,p)) ≤ (source.spectrum checked_sphere_energy_continuity).energy i t x
theorem tubularTransfer_to_retraction (assemble : TubularInverseAssemblyStatement.{u})
    {source target : IntrinsicSpectrumData.{u}} {t : ℝ} (h : TubularClassTransfer source target t) :
    RetractionClassTransfer source target t := by
  intro i
  obtain ⟨r,he⟩ := h i
  obtain ⟨R,hR⟩ := r.toRetraction assemble
  refine ⟨R,?_⟩
  intro x
  rw [hR]
  exact he x
#print axioms TubularApproximationData.toRetraction
#print axioms tubularTransfer_to_retraction
end PoincareConjecture.ProofContract.Refinement20260927
