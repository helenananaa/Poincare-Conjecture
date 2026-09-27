import PoincareConjecture.ProofContract.Refinement20260927.EuclideanMollifierReuse
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff Convolution
/-- **Math.** The same mollifier approximates both the extension and its actual derivative. -/
theorem cylinder_c1_approximation_of_leaves (uniform : UniformMollificationStatement)
    (restrict : CylinderRestrictionEstimateStatement) (extend : CylinderCompactExtensionStatement) :
    CylinderC1ApproximationStatement := by
  intro n f hf eps heps
  obtain ⟨F,hF,hcompact,hEq⟩ := extend n f hf
  obtain ⟨r0,hr0,h0⟩ := uniform (ApproxAmbient n) F cylinderCompact hF.continuous
    cylinderCompact_isCompact eps heps
  obtain ⟨r1,hr1,h1⟩ := uniform (CylinderAmbient →L[ℝ] ApproxAmbient n) (fderiv ℝ F)
    cylinderCompact (hF.continuous_fderiv one_ne_zero) cylinderCompact_isCompact eps heps
  let r := min r0 r1
  have hr : 0 < r := lt_min hr0 hr1
  let phi : ContDiffBump (0 : CylinderAmbient) :=
    { rIn := r/4, rOut := r/2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hphi0 : phi.rOut < r0 := by
    change r/2 < r0
    have h := min_le_left r0 r1
    change r ≤ r0 at h
    linarith
  have hphi1 : phi.rOut < r1 := by
    change r/2 < r1
    have h := min_le_right r0 r1
    change r ≤ r1 at h
    linarith
  let G := euclideanMollify phi F
  have hG : ContDiff ℝ ∞ G := euclideanMollify_smooth phi F hF.continuous
  let a : ℝ × Sphere2 → ApproxAmbient n := G ∘ cylinderInclusion
  refine ⟨a,hG.contMDiff.comp cylinderInclusion_smooth,?_,?_⟩
  · intro q
    have hx : cylinderInclusion ((q.1:ℝ),q.2) ∈ cylinderCompact :=
      ⟨q.1.property,q.2.property⟩
    have hh := h0 phi hphi0 _ hx
    rw [hEq ((q.1:ℝ),q.2) q.1.property] at hh
    exact hh
  · intro s p i
    have hx : ((s:ℝ),p.val) ∈ cylinderCompact := ⟨s.property,p.property⟩
    have hd : ‖fderiv ℝ G ((s:ℝ),p.val) - fderiv ℝ F ((s:ℝ),p.val)‖ ≤ eps := by
      have hh := (h1 phi hphi1 _ hx).le
      rw [dist_eq_norm] at hh
      change ‖fderiv ℝ (euclideanMollify phi F) ((s:ℝ),p.val) - _‖ ≤ eps
      rw [euclideanMollify_fderiv phi F hF hcompact]
      exact hh
    have result := restrict n G F (s:ℝ) p i eps
      (hG.differentiable (by simp)).differentiableAt
      (hF.differentiable one_ne_zero).differentiableAt heps.le hd
    have hs : (fun z : Sphere2 => F ((s:ℝ),z.val)) = fun z => f ((s:ℝ),z) :=
      funext fun z => hEq ((s:ℝ),z) s.property
    rw [hs] at result
    exact result
#print axioms cylinder_c1_approximation_of_leaves
end PoincareConjecture.ProofContract.Refinement20260927
