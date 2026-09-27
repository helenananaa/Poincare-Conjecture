import PoincareConjecture.ProofContract.Refinement20260927.AcceptedThirtyNine
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Topology Manifold ContDiff
/-- **Math.** C1, not C-infinity, suffices for continuity of the actual Dirichlet density.
No smoothness is asserted for the pointwise selected frame itself. -/
def C1SphereEnergyContinuityStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) N)
    (f : ℝ × Sphere2 → N), ContMDiff SweepModel (𝓡 3) 1 f →
      Continuous (fun q : ℝ × Sphere2 => sphereEnergyDensity N g (fun p => f (q.1,p)) q.2)
/-- **Math.** Actual Euclidean derivatives of a jointly C1 map admit one bound on the compact
parameter strip. The fixed pointwise round-orthonormal frame is not presumed continuous. -/
def C1AmbientFrameBoundStatement : Prop :=
  ∀ (n : ℕ) (f : ℝ × Sphere2 → ApproxAmbient n),
    ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) 1 f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : SweepParameter) p i,
        ‖ambientSliceVector (fun z => f ((s:ℝ),z)) p i‖ ≤ C
/-- **Math.** A given C1 map in the same fixed relative class. No embedding, derivative bound,
integrability, retraction or approximation witness is part of this input. -/
structure C1ClassRepresentative (N : CompactSmoothThree.{u}) (D : BasedSphereClass N) where
  map : ℝ × Sphere2 → N
  c1 : ContMDiff SweepModel (𝓡 3) 1 map
  ends : ∀ p : Sphere2, map (0,p) = D.base ∧ map (1,p) = D.base
  correct_class : (⟨fun q : SweepDomain => map ((q.1:ℝ),q.2), c1.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩ : C(SweepDomain,N)).HomotopicRel
      D.reference.continuousMap sweepoutEnds
def C1ClassRepresentative.continuousMap {N : CompactSmoothThree.{u}} {D : BasedSphereClass N}
    (r : C1ClassRepresentative N D) : C(SweepDomain,N) :=
  ⟨fun q => r.map ((q.1:ℝ),q.2), r.c1.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
theorem C1ClassRepresentative.continuousMap_apply {N : CompactSmoothThree.{u}}
    {D : BasedSphereClass N} (r : C1ClassRepresentative N D) (q : SweepDomain) :
    r.continuousMap q = r.map ((q.1:ℝ),q.2) := rfl
#print axioms C1ClassRepresentative.continuousMap_apply
end PoincareConjecture.ProofContract.Refinement20260927
