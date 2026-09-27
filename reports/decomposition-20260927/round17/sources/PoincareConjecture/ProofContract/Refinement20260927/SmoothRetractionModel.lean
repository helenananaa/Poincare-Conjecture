import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTwentyFour
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** A LOCAL smooth retraction, represented by a total map smooth only
on its declared open domain. No global retraction of Euclidean space is required. -/
structure SmoothRetractionData (N : CompactSmoothThree.{u}) (n : ℕ) extends AmbientRetraction N n where
  smooth_embed : ContMDiff (𝓡 3) 𝓘(ℝ, ApproxAmbient n) ∞ embed
  localRetract : ApproxAmbient n → N
  agrees : ∀ x (hx : x ∈ domain), localRetract x = retract ⟨x,hx⟩
  smooth_localRetract : ContMDiffOn 𝓘(ℝ, ApproxAmbient n) (𝓡 3) ∞ localRetract domain
/-- **Math.** New leaf: build the actual ambient bilinear coefficient field
from the given local retraction and target metric. No such field is assumed. -/
def SmoothRetractionFormStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) N)
    (n : ℕ) (R : SmoothRetractionData N n),
    ∃ A : N → (ApproxAmbient n →L[ℝ] ApproxAmbient n →L[ℝ] ℝ), Continuous A ∧
      ∀ (p : N) (v w : TangentSpace (𝓡 3) p), g.metricInner p v w = A p
        (mfderiv (𝓡 3) 𝓘(ℝ, ApproxAmbient n) R.embed p v)
        (mfderiv (𝓡 3) 𝓘(ℝ, ApproxAmbient n) R.embed p w)
/-- **Math.** Chosen coefficients retain their exact embedding in the formula.
The returned model's retraction is explicitly the supplied R, not an arbitrary choice. -/
theorem energyModel_of_smoothRetraction (produce : SmoothRetractionFormStatement.{u})
    (N : CompactSmoothThree.{u}) (g : Riemannian.RiemannianMetric (𝓡 3) N)
    (n : ℕ) (R : SmoothRetractionData N n) :
    ∃ A : AmbientEnergyModel N g n, A.retraction = R.toAmbientRetraction := by
  obtain ⟨form,hcontinuous,hrealizes⟩ := produce N g n R
  exact ⟨{ retraction := R.toAmbientRetraction
           smooth_embed := R.smooth_embed
           form := form
           continuous_form := hcontinuous
           realizes := hrealizes },rfl⟩
/-- **Math.** Uniform coefficient control is derived from compactness, not
added separately to the approximation data. -/
theorem AmbientEnergyModel.uniform_form_control {N : CompactSmoothThree.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) N} {n : ℕ} (A : AmbientEnergyModel N g n) :
    (∃ Q : ℝ, 0 ≤ Q ∧ ∀ p : N, ‖A.form p‖ ≤ Q) ∧
    (∀ e : ℝ, 0 < e → ∃ rho : ℝ, 0 < rho ∧ ∀ p q : N,
      dist (A.retraction.embed p) (A.retraction.embed q) < rho →
        ‖A.form p - A.form q‖ ≤ e) := by
  constructor
  · obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn A.continuous_form.continuousOn
    exact ⟨max 0 B,le_max_left _ _,fun p => (hB p (mem_univ p)).trans (le_max_right _ _)⟩
  · let e : N → A.retraction.domain := fun p => ⟨A.retraction.embed p,A.retraction.contains p⟩
    have he : Continuous e := A.retraction.embed.continuous.subtype_mk _
    have hK : IsCompact (range e) := isCompact_range he
    let f : A.retraction.domain → (ApproxAmbient n →L[ℝ] ApproxAmbient n →L[ℝ] ℝ) :=
      A.form ∘ A.retraction.retract
    have hf : Continuous f := A.continuous_form.comp A.retraction.retract.continuous
    have hu := hK.uniformContinuousOn_of_continuous hf.continuousOn
    intro delta hd
    obtain ⟨rho,hr,hcontrol⟩ := Metric.uniformContinuousOn_iff.mp hu delta hd
    refine ⟨rho,hr,?_⟩
    intro p q hpq
    have h := hcontrol (e p) ⟨p,rfl⟩ (e q) ⟨q,rfl⟩ hpq
    have hfp : f (e p) = A.form p := by simp [f,e,A.retraction.retract_embed]
    have hfq : f (e q) = A.form q := by simp [f,e,A.retraction.retract_embed]
    rw [hfp,hfq,dist_eq_norm] at h
    exact h.le
#print axioms energyModel_of_smoothRetraction
#print axioms AmbientEnergyModel.uniform_form_control
end PoincareConjecture.ProofContract.Refinement20260927
