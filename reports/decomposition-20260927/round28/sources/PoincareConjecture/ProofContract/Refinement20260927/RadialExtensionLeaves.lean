import PoincareConjecture.ProofContract.Refinement20260927.EuclideanMollifierReuse
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff
/-- **Math.** A total radial direction; its arbitrary value at zero is killed by the cutoff. -/
def radialDirection (x : Euclidean3) : Sphere2 :=
  if hx : x = 0 then Classical.choice sphereEnergySphere_nonempty
  else ⟨(‖x‖⁻¹ : ℝ) • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
def cylinderTimeCut : ContDiffBump (1/2 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def cylinderSpaceCut : ContDiffBump (1 : ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
def cylinderCutoff (z : CylinderAmbient) : ℝ :=
  cylinderTimeCut z.1 * cylinderSpaceCut (‖z.2‖^2)
def radialCylinderExtension {n : ℕ} (f : ℝ × Sphere2 → ApproxAmbient n)
    (z : CylinderAmbient) : ApproxAmbient n :=
  cylinderCutoff z • f (z.1,radialDirection z.2)
/-- **Math.** Local smooth extensions of radial normalization, not a global radial retraction. -/
def RadialLocalSmoothStatement : Prop :=
  ∀ x : Euclidean3, x ≠ 0 → ∃ d : Euclidean3 → Sphere2,
    ContMDiff 𝓘(ℝ,Euclidean3) (𝓡 2) ∞ d ∧
      EqOn d radialDirection (Metric.ball x (‖x‖/4))
/-- **Math.** Independent cutoff gluing: only the off-axis regularity of a is supplied. -/
def CylinderCutoffGlueStatement : Prop :=
  ∀ (n : ℕ) (a : CylinderAmbient → ApproxAmbient n),
    (∀ z : CylinderAmbient, z.2 ≠ 0 → ContDiffAt ℝ 1 a z) →
      ContDiff ℝ 1 (fun z => cylinderCutoff z • a z)
/-- **Math.** Compact support and exact agreement of the SAME explicit extension.
This leaf is independent of all differentiability assumptions. -/
def CylinderCutoffSupportStatement : Prop :=
  ∀ (n : ℕ) (f : ℝ × Sphere2 → ApproxAmbient n),
    HasCompactSupport (radialCylinderExtension f) ∧
      ∀ q : ℝ × Sphere2, q.1 ∈ Icc (0:ℝ) 1 →
        radialCylinderExtension f (cylinderInclusion q) = f q
/-- **Math.** Exact radial formula away from zero. -/
theorem radialDirection_coe (x : Euclidean3) (hx : x ≠ 0) :
    (radialDirection x : Euclidean3) = ‖x‖⁻¹ • x := by
  simp only [radialDirection, dif_neg hx]
/-- **Math.** The radial map is the identity on the specified unit sphere. -/
theorem radialDirection_unit (p : Sphere2) : radialDirection p.val = p := by
  have hp : ‖p.val‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using p.property
  have hn : p.val ≠ 0 := by intro h; simp [h] at hp
  apply Subtype.ext
  rw [radialDirection_coe _ hn, hp, inv_one, one_smul]
#print axioms radialDirection_coe
#print axioms radialDirection_unit
end PoincareConjecture.ProofContract.Refinement20260927
