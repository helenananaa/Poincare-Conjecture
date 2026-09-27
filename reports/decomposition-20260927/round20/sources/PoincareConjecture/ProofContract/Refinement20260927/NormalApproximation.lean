import PoincareConjecture.ProofContract.Refinement20260927.NormalCoordinateTube
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** Parameterized normal data replaces a pre-existing endpoint inverse. -/
structure NormalApproximationData (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (D : BasedSphereClass N) where
  reference : C(SweepDomain,N)
  ends : EqOn reference (ContinuousMap.const SweepDomain D.base) sweepoutEnds
  correct_class : reference.HomotopicRel D.reference.continuousMap sweepoutEnds
  differentiable : ∀ s : SweepParameter, MDifferentiable (𝓡 2) (𝓡 3) (fun p => reference (s,p))
  integrable : ∀ s : SweepParameter,
    Integrable (sphereEnergyDensity N g (fun p => reference (s,p))) sphereEnergyMeasure
  dimension : ℕ
  embedding : CompactEuclideanEmbedding N dimension
  normalTube : NormalCoordinateTube embedding
  C : ℝ
  C_nonneg : 0 ≤ C
  derivative_bound : ∀ (s : SweepParameter) p i,
    ‖embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ C
  approximants : ∀ delta : ℝ, 0 < delta → ∃ h : SmoothBasedSweepout N D.base,
    (∀ q : SweepDomain, dist (embedding.map (h.continuousMap q))
      (embedding.map (reference q)) < delta) ∧
    ∀ (s : SweepParameter) p i, ‖embeddedSphereVector embedding (fun p => h.map ((s:ℝ),p)) p i -
      embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ delta
/-- **Math.** Consume the three proofs without altering the reference or embedding. -/
theorem NormalApproximationData.toTubular (split : NormalLinearEquivStatement)
    (jet : NormalEndpointJetStatement) (inverse : TubularChartInverseStatement.{u})
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : NormalApproximationData N g D) :
    ∃ R : TubularApproximationData N g D, R.reference = r.reference := by
  obtain ⟨localTube⟩ := r.normalTube.toLocal split jet inverse
  exact ⟨{ reference := r.reference
           ends := r.ends
           correct_class := r.correct_class
           differentiable := r.differentiable
           integrable := r.integrable
           dimension := r.dimension
           embedding := r.embedding
           localTube := localTube
           C := r.C
           C_nonneg := r.C_nonneg
           derivative_bound := r.derivative_bound
           approximants := r.approximants },rfl⟩
/-- **Math.** The remaining producer supplies genuine normal parameter charts and approximants. -/
def NormalClassTransfer (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ i : source.sweepouts.Representative,
    ∃ r : NormalApproximationData target.space (target.metric t) target.sweepouts,
      ∀ x : SweepParameter, sphereDirichletEnergy target.space (target.metric t)
        (fun p => r.reference (x,p)) ≤ (source.spectrum checked_sphere_energy_continuity).energy i t x
theorem normalTransfer_to_tubular (split : NormalLinearEquivStatement)
    (jet : NormalEndpointJetStatement) (inverse : TubularChartInverseStatement.{u})
    {source target : IntrinsicSpectrumData.{u}} {t : ℝ} (h : NormalClassTransfer source target t) :
    TubularClassTransfer source target t := by
  intro i
  obtain ⟨r,he⟩ := h i
  obtain ⟨R,hR⟩ := r.toTubular split jet inverse
  refine ⟨R,?_⟩
  intro x
  rw [hR]
  exact he x
#print axioms NormalApproximationData.toTubular
#print axioms normalTransfer_to_tubular
end PoincareConjecture.ProofContract.Refinement20260927
