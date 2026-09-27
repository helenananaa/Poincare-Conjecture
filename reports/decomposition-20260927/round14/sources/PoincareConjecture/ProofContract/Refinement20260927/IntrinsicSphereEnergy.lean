import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTwentyOne
import DoCarmoLib.Riemannian.TensorBundle.SmoothOrthoFrame
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory MorganTianLib Riemannian.Tensor
open scoped Topology Manifold ContDiff BigOperators
abbrev SphereModel := EuclideanSpace ℝ (Fin 2)
instance sphereEnergySphere_nonempty : Nonempty Sphere2 :=
  ⟨⟨EuclideanSpace.single 0 1, by simp [Sphere2]⟩⟩
local instance : NeZero (Module.finrank ℝ SphereModel) := ⟨by simp [SphereModel]⟩
local instance : Riemannian.HasMetric (𝓡 2) Sphere2 := ⟨unitRoundSphereMetric⟩
/-- **Math.** Actual unit-round sphere measure, fixed independently of the target metric. -/
def sphereEnergyMeasure : Measure Sphere2 :=
  riemannianMeasure unitRoundSphereMetric (volume : Measure SphereModel)
instance : IsFiniteMeasure sphereEnergyMeasure := by
  letI : Nonempty EpsilonNeckSphere := sphereEnergySphere_nonempty
  refine ⟨?_⟩
  exact riemannianMeasure_lt_top_of_isCompact (volume : Measure SphereModel)
    unitRoundSphereMetric isCompact_univ
/-- **Math.** Orthonormal at each point, not claimed to be one global smooth frame. -/
def sphereEnergyFrame (p : Sphere2) (i : Fin (Module.finrank ℝ SphereModel)) :
    TangentSpace (𝓡 2) p := smoothOrthoFrame unitRoundSphereMetric p i p
/-- **Math.** Half the round-source trace of the pullback target metric through
this map's ACTUAL manifold differential. No free energy or vector field input. -/
def sphereEnergyDensity (M : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (f : Sphere2 → M) (p : Sphere2) : ℝ :=
  (1/2 : ℝ) * ∑ i : Fin (Module.finrank ℝ SphereModel),
    g.metricInner (f p) (mfderiv (𝓡 2) (𝓡 3) f p (sphereEnergyFrame p i))
      (mfderiv (𝓡 2) (𝓡 3) f p (sphereEnergyFrame p i))
def sphereDirichletEnergy (M : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (f : Sphere2 → M) : ℝ :=
  ∫ p, sphereEnergyDensity M g f p ∂sphereEnergyMeasure
/-- **Math.** This elementary fact does not assert integrability of an arbitrary map. -/
theorem sphereEnergyDensity_nonneg (M : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (f : Sphere2 → M) (p : Sphere2) :
    0 ≤ sphereEnergyDensity M g f p := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  by_cases hv : mfderiv (𝓡 2) (𝓡 3) f p (sphereEnergyFrame p i) = 0
  · simp [hv]
  · exact (g.metricInner_self_pos (f p) _ hv).le
theorem sphereDirichletEnergy_nonneg (M : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (f : Sphere2 → M) :
    0 ≤ sphereDirichletEnergy M g f := integral_nonneg (sphereEnergyDensity_nonneg M g f)
/-- **Math.** A pointwise round-orthonormal basis may be replaced by a fixed
smooth local frame near alpha. No global smooth frame on S2 is assumed. -/
theorem sphereEnergyDensity_local_frame (M : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (f : Sphere2 → M) (alpha p : Sphere2)
    (hp : p ∈ smoothOrthoFrameNbhd (I := 𝓡 2) alpha) :
    sphereEnergyDensity M g f p = (1/2 : ℝ) *
      ∑ i : Fin (Module.finrank ℝ SphereModel),
        g.metricInner (f p) (mfderiv (𝓡 2) (𝓡 3) f p (smoothOrthoFrame unitRoundSphereMetric alpha i p))
          (mfderiv (𝓡 2) (𝓡 3) f p (smoothOrthoFrame unitRoundSphereMetric alpha i p)) := by
  let D := mfderiv (𝓡 2) (𝓡 3) f p
  let B : TangentSpace (𝓡 2) p →ₗ[ℝ] TangentSpace (𝓡 2) p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v w => g.metricInner (f p) (D v) (D w))
      (by intro v w z; simp [map_add, g.metricInner_add_left])
      (by intro r v w; simp [map_smul, g.metricInner_smul_left])
      (by intro v w z; simp [map_add, g.metricInner_add_right])
      (by intro r v w; simp [map_smul, g.metricInner_smul_right])
  unfold sphereEnergyDensity sphereEnergyFrame
  apply congrArg (fun x : ℝ => (1/2:ℝ)*x)
  change (∑ i, B (smoothOrthoFrame unitRoundSphereMetric p i p)
    (smoothOrthoFrame unitRoundSphereMetric p i p)) =
    ∑ i, B (smoothOrthoFrame unitRoundSphereMetric alpha i p)
      (smoothOrthoFrame unitRoundSphereMetric alpha i p)
  exact (sum_diagonal_smoothOrthoFrame_eq_std (I := 𝓡 2) p B).trans
    (sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std (I := 𝓡 2) alpha hp B).symm
/-- **Math.** Independent leaf: continuity for an ACTUAL smooth parameterized
sphere map. It may use local frames; the pointwise chosen frame is not smooth. -/
def SphereEnergyContinuityStatement : Prop :=
  ∀ (M : CompactSmoothThree.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) M)
    (f : ℝ × Sphere2 → M), ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ∞ f →
      Continuous (fun q : ℝ × Sphere2 => sphereEnergyDensity M g (fun p => f (q.1,p)) q.2)
/-- **Math.** Independent leaf: relative comparison for a global tensor on a
compact manifold, without presuming one global coordinate frame. -/
def IntrinsicMetricTimeComparisonStatement : Prop :=
  ∀ (M : CompactSmoothThree.{u}) (g : ℝ → Riemannian.RiemannianMetric (𝓡 3) M)
    (a b : ℝ), a ≤ b → IsSmoothMetricFamilyOn g (Icc a b) →
    ∀ t ∈ Icc a b, ∀ eta : ℝ, 0 < eta → ∃ r : ℝ, 0 < r ∧
      ∀ s ∈ Icc a b, dist s t < r → ∀ p : M, ∀ v : TangentSpace (𝓡 3) p,
        (1-eta)*(g t).metricInner p v v ≤ (g s).metricInner p v v ∧
        (g s).metricInner p v v ≤ (1+eta)*(g t).metricInner p v v
#print axioms sphereEnergyDensity_nonneg
#print axioms sphereDirichletEnergy_nonneg
#print axioms sphereEnergyDensity_local_frame
end PoincareConjecture.ProofContract.Refinement20260927
