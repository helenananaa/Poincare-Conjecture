import PoincareConjecture.ProofContract.Refinement20260927.SmoothRetractionModel
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** Actual derivative of the ambient representative, independent of
any subsequently constructed energy coefficient field. -/
def retractionSphereVector {N : CompactSmoothThree.{u}} {n : ℕ}
    (R : AmbientRetraction N n) (f : Sphere2 → N) (p : Sphere2)
    (i : Fin (Module.finrank ℝ SphereModel)) : ApproxAmbient n :=
  mfderiv (𝓡 2) 𝓘(ℝ, ApproxAmbient n) (R.embed ∘ f) p (sphereEnergyFrame p i)
/-- **Math.** Input has only an actual smooth local retraction and ambient
C1 approximation data. No ambient metric form or coefficient bound is assumed.
Existence of the retraction and approximants remains a geometric obligation. -/
structure RetractionApproximationData (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (D : BasedSphereClass N) where
  reference : C(SweepDomain,N)
  ends : EqOn reference (ContinuousMap.const SweepDomain D.base) sweepoutEnds
  correct_class : reference.HomotopicRel D.reference.continuousMap sweepoutEnds
  differentiable : ∀ s : SweepParameter, MDifferentiable (𝓡 2) (𝓡 3) (fun p => reference (s,p))
  integrable : ∀ s : SweepParameter,
    Integrable (sphereEnergyDensity N g (fun p => reference (s,p))) sphereEnergyMeasure
  dimension : ℕ
  retraction : SmoothRetractionData N dimension
  C : ℝ
  C_nonneg : 0 ≤ C
  derivative_bound : ∀ s p i,
    ‖retractionSphereVector retraction.toAmbientRetraction (fun p => reference (s,p)) p i‖ ≤ C
  approximants : ∀ delta : ℝ, 0 < delta → ∃ h : SmoothBasedSweepout N D.base,
    (∀ q : SweepDomain, dist (retraction.embed (h.continuousMap q))
      (retraction.embed (reference q)) < delta) ∧
    ∀ (s : SweepParameter) p i, ‖retractionSphereVector retraction.toAmbientRetraction (fun p => h.map ((s:ℝ),p)) p i -
      retractionSphereVector retraction.toAmbientRetraction (fun p => reference (s,p)) p i‖ ≤ delta
/-- **Math.** Produces the former coefficient bounds and coefficient errors
from compactness, retaining the same reference and ambient embedding. -/
theorem RetractionApproximationData.toRegularization (forms : SmoothRetractionFormStatement.{u})
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : RetractionApproximationData N g D) :
    ∃ R : RegularizationData N g D, R.reference = r.reference := by
  obtain ⟨A,hA⟩ := energyModel_of_smoothRetraction forms N g r.dimension r.retraction
  obtain ⟨⟨Q,hQ,Qbound⟩,coeffControl⟩ := A.uniform_form_control
  have hv (f : Sphere2 → N) (p : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
      ambientSphereVector A f p i = retractionSphereVector r.retraction.toAmbientRetraction f p i := by
    unfold ambientSphereVector retractionSphereVector
    rw [hA]
  refine ⟨{ reference := r.reference
            ends := r.ends
            correct_class := r.correct_class
            differentiable := r.differentiable
            integrable := r.integrable
            dimension := r.dimension
            model := A
            C := r.C
            Q := Q
            C_nonneg := r.C_nonneg
            Q_nonneg := hQ
            approximants := ?_ },rfl⟩
  intro delta hd
  obtain ⟨rho,hrho,hcoeff⟩ := coeffControl delta hd
  obtain ⟨h,hclose,hderiv⟩ := r.approximants (min rho delta) (lt_min hrho hd)
  refine ⟨h,?_,?_⟩
  · intro q
    rw [hA]
    exact (hclose q).trans_le (min_le_right _ _)
  · intro s p
    refine ⟨Qbound _,?_,?_⟩
    · apply hcoeff
      rw [hA]
      exact (hclose (s,p)).trans_le (min_le_left _ _)
    · intro i
      rw [hv,hv]
      exact ⟨r.derivative_bound s p i,(hderiv s p i).trans (min_le_right _ _)⟩
/-- **Math.** A new construction entrance; old regularized and exact transfer
entrances remain available and are not required to acquire retraction data. -/
def RetractionClassTransfer (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ i : source.sweepouts.Representative,
    ∃ r : RetractionApproximationData target.space (target.metric t) target.sweepouts,
      ∀ x : SweepParameter, sphereDirichletEnergy target.space (target.metric t)
        (fun p => r.reference (x,p)) ≤ (source.spectrum checked_sphere_energy_continuity).energy i t x
theorem retractionTransfer_to_regularized (forms : SmoothRetractionFormStatement.{u})
    {source target : IntrinsicSpectrumData.{u}} {t : ℝ} (h : RetractionClassTransfer source target t) :
    RegularizedClassTransfer source target t := by
  intro i
  obtain ⟨r,he⟩ := h i
  obtain ⟨R,hR⟩ := r.toRegularization forms
  refine ⟨R,?_⟩
  intro x
  rw [hR]
  exact he x
#print axioms RetractionApproximationData.toRegularization
#print axioms retractionTransfer_to_regularized
end PoincareConjecture.ProofContract.Refinement20260927
