import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTwentyTwo
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
abbrev SweepDomain := SweepParameter × Sphere2
abbrev ApproxAmbient (n : ℕ) := EuclideanSpace ℝ (Fin n)
/-- **Math.** Explicit neighborhood retraction data, not an asserted embedding
or tubular-neighborhood existence theorem. The same maps enter the homotopy. -/
structure AmbientRetraction (N : CompactSmoothThree.{u}) (n : ℕ) where
  embed : C(N, ApproxAmbient n)
  domain : Set (ApproxAmbient n)
  open_domain : IsOpen domain
  contains : ∀ p : N, embed p ∈ domain
  retract : C(domain, N)
  retract_embed : ∀ p : N, retract ⟨embed p, contains p⟩ = p
/-- **Math.** Compact-image stability relative to the actual two end spheres.
No target homotopy-class preservation is assumed in this leaf. -/
def RelativeRetractionHomotopyStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (R : AmbientRetraction N n)
    (f : C(SweepDomain, N)), ∃ delta : ℝ, 0 < delta ∧
      ∀ g : C(SweepDomain, N),
        (∀ q, dist (R.embed (g q)) (R.embed (f q)) < delta) →
        EqOn g f sweepoutEnds → g.HomotopicRel f sweepoutEnds
/-- **Math.** Tensor representation through an actual smooth ambient map.
Real geometry must supply this data; no energy approximation is a field. -/
structure AmbientEnergyModel (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (n : ℕ) where
  retraction : AmbientRetraction N n
  smooth_embed : ContMDiff (𝓡 3) 𝓘(ℝ, ApproxAmbient n) ∞ retraction.embed
  form : N → (ApproxAmbient n →L[ℝ] ApproxAmbient n →L[ℝ] ℝ)
  continuous_form : Continuous form
  realizes : ∀ (p : N) (v w : TangentSpace (𝓡 3) p),
    g.metricInner p v w = form p
      (mfderiv (𝓡 3) 𝓘(ℝ, ApproxAmbient n) retraction.embed p v)
      (mfderiv (𝓡 3) 𝓘(ℝ, ApproxAmbient n) retraction.embed p w)
def ambientSphereVector {N : CompactSmoothThree.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) N} {n : ℕ}
    (A : AmbientEnergyModel N g n) (f : Sphere2 → N) (p : Sphere2)
    (i : Fin (Module.finrank ℝ SphereModel)) : ApproxAmbient n :=
  mfderiv (𝓡 2) 𝓘(ℝ, ApproxAmbient n) (A.retraction.embed ∘ f) p (sphereEnergyFrame p i)
/-- **Math.** Uniform first-derivative and coefficient bounds for actual maps.
The pointwise source frame is used only to evaluate traces, never as a smooth global frame. -/
def AmbientC1Bounds {N : CompactSmoothThree.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) N} {n : ℕ}
    (A : AmbientEnergyModel N g n) (f h : Sphere2 → N) (C Q delta : ℝ) : Prop :=
  ∀ p, ‖A.form (f p)‖ ≤ Q ∧ ‖A.form (h p) - A.form (f p)‖ ≤ delta ∧
    ∀ i, ‖ambientSphereVector A f p i‖ ≤ C ∧
      ‖ambientSphereVector A h p i - ambientSphereVector A f p i‖ ≤ delta
/-- **Math.** Direct chain-rule identity for the actual density in ambient data. -/
theorem sphereDensity_ambient {N : CompactSmoothThree.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) N} {n : ℕ}
    (A : AmbientEnergyModel N g n) (f : Sphere2 → N)
    (hf : MDifferentiable (𝓡 2) (𝓡 3) f) (p : Sphere2) :
    sphereEnergyDensity N g f p = (1/2 : ℝ) * ∑ i,
      A.form (f p) (ambientSphereVector A f p i) (ambientSphereVector A f p i) := by
  unfold sphereEnergyDensity ambientSphereVector
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [A.realizes]
  rw [mfderiv_comp p ((A.smooth_embed.mdifferentiable (by norm_num)) (f p)) (hf p)]
  rfl
/-- **Math.** Independent analytic leaf: one C1 tolerance works for all actual
map pairs with these bounds. Integrability of the possibly nonsmooth reference
is explicit, not inferred from the Bochner integral's default value. -/
def SphereEnergyApproximationStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) N)
    (n : ℕ) (A : AmbientEnergyModel N g n) (C Q e : ℝ),
    0 ≤ C → 0 ≤ Q → 0 < e → ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ f h : Sphere2 → N, MDifferentiable (𝓡 2) (𝓡 3) f →
        ContMDiff (𝓡 2) (𝓡 3) ∞ h →
        Integrable (sphereEnergyDensity N g f) sphereEnergyMeasure →
        AmbientC1Bounds A f h C Q delta →
        |sphereDirichletEnergy N g h - sphereDirichletEnergy N g f| ≤ e
#print axioms sphereDensity_ambient
end PoincareConjecture.ProofContract.Refinement20260927
