import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedNormalConstruction
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** The former normalTube input has been removed, not renamed. -/
structure EmbeddingApproximationData (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (D : BasedSphereClass N) where
  reference : C(SweepDomain,N)
  ends : EqOn reference (ContinuousMap.const SweepDomain D.base) sweepoutEnds
  correct_class : reference.HomotopicRel D.reference.continuousMap sweepoutEnds
  differentiable : ∀ s : SweepParameter, MDifferentiable (𝓡 2) (𝓡 3) (fun p => reference (s,p))
  integrable : ∀ s : SweepParameter,
    Integrable (sphereEnergyDensity N g (fun p => reference (s,p))) sphereEnergyMeasure
  dimension : ℕ
  embedding : CompactEuclideanEmbedding N dimension
  C : ℝ
  C_nonneg : 0 ≤ C
  derivative_bound : ∀ (s : SweepParameter) p i,
    ‖embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ C
  approximants : ∀ delta : ℝ, 0 < delta → ∃ h : SmoothBasedSweepout N D.base,
    (∀ q : SweepDomain, dist (embedding.map (h.continuousMap q))
      (embedding.map (reference q)) < delta) ∧
    ∀ (s : SweepParameter) p i, ‖embeddedSphereVector embedding (fun p => h.map ((s:ℝ),p)) p i -
      embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ delta
/-- **Math.** Only the actual embedding and approximating maps are inputs; tube data is constructed. -/
theorem EmbeddingApproximationData.toNormal (coordinates : EmbeddedNormalCoordinatesStatement.{u})
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : EmbeddingApproximationData N g D) :
    ∃ R : NormalApproximationData N g D, R.reference = r.reference := by
  obtain ⟨normalTube⟩ := coordinates N r.dimension r.embedding
  exact ⟨{ reference := r.reference
           ends := r.ends
           correct_class := r.correct_class
           differentiable := r.differentiable
           integrable := r.integrable
           dimension := r.dimension
           embedding := r.embedding
           normalTube := normalTube
           C := r.C
           C_nonneg := r.C_nonneg
           derivative_bound := r.derivative_bound
           approximants := r.approximants },rfl⟩
/-- **Math.** No local tube, normal atlas or retraction is assumed in the transfer data. -/
def EmbeddingClassTransfer (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ i : source.sweepouts.Representative,
    ∃ r : EmbeddingApproximationData target.space (target.metric t) target.sweepouts,
      ∀ x : SweepParameter, sphereDirichletEnergy target.space (target.metric t)
        (fun p => r.reference (x,p)) ≤ (source.spectrum checked_sphere_energy_continuity).energy i t x
theorem embeddingTransfer_to_normal (coordinates : EmbeddedNormalCoordinatesStatement.{u})
    {source target : IntrinsicSpectrumData.{u}} {t : ℝ} (h : EmbeddingClassTransfer source target t) :
    NormalClassTransfer source target t := by
  intro i
  obtain ⟨r,he⟩ := h i
  obtain ⟨R,hR⟩ := r.toNormal coordinates
  refine ⟨R,?_⟩
  intro x
  rw [hR]
  exact he x
#print axioms EmbeddingApproximationData.toNormal
#print axioms embeddingTransfer_to_normal
end PoincareConjecture.ProofContract.Refinement20260927
