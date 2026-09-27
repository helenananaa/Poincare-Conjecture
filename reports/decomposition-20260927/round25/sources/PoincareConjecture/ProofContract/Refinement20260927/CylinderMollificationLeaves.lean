import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationRoot
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff BigOperators Convolution
abbrev CylinderAmbient := ℝ × ApproxAmbient 3
def cylinderInclusion (q : ℝ × Sphere2) : CylinderAmbient := (q.1,q.2.val)
def cylinderCompact : Set CylinderAmbient :=
  Icc (0:ℝ) 1 ×ˢ Metric.sphere (0 : ApproxAmbient 3) 1
def euclideanMollify {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : CylinderAmbient)) (f : CylinderAmbient → F) : CylinderAmbient → F :=
  phi.normed (volume : Measure CylinderAmbient) ⋆[lsmul ℝ ℝ, volume] f
/-- **Math.** One radius works on the entire compact set, for every normalized bump of smaller support. -/
def UniformMollificationStatement : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : CylinderAmbient → F) (K : Set CylinderAmbient), Continuous f → IsCompact K →
    ∀ eps : ℝ, 0 < eps → ∃ rho : ℝ, 0 < rho ∧
      ∀ phi : ContDiffBump (0 : CylinderAmbient), phi.rOut < rho →
        ∀ x ∈ K, dist (euclideanMollify phi f x) (f x) < eps
/-- **Math.** The derivative estimate uses the actual round-source frame, not an arbitrary frame norm. -/
def CylinderRestrictionEstimateStatement : Prop :=
  ∀ (n : ℕ) (f g : CylinderAmbient → ApproxAmbient n) (s : ℝ) (p : Sphere2)
    (i : Fin (Module.finrank ℝ SphereModel)) (eps : ℝ),
    DifferentiableAt ℝ f (s,p.val) → DifferentiableAt ℝ g (s,p.val) → 0 ≤ eps →
    ‖fderiv ℝ f (s,p.val) - fderiv ℝ g (s,p.val)‖ ≤ eps →
      ‖ambientSliceVector (fun z => f (s,z.val)) p i -
        ambientSliceVector (fun z => g (s,z.val)) p i‖ ≤ eps
/-- **Math.** Genuine extension of a jointly C1 cylinder map, not an assumed approximating sequence. -/
def CylinderCompactExtensionStatement : Prop :=
  ∀ (n : ℕ) (f : ℝ × Sphere2 → ApproxAmbient n),
    ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) 1 f →
    ∃ F : CylinderAmbient → ApproxAmbient n, ContDiff ℝ 1 F ∧ HasCompactSupport F ∧
      ∀ q : ℝ × Sphere2, q.1 ∈ Icc (0:ℝ) 1 → F (cylinderInclusion q) = f q
/-- **Math.** The public analytic subgoal to be constructed from these three independent leaves. -/
def CylinderC1ApproximationStatement : Prop :=
  ∀ (n : ℕ) (f : ℝ × Sphere2 → ApproxAmbient n),
    ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) 1 f →
    ∀ eps : ℝ, 0 < eps → ∃ a : ℝ × Sphere2 → ApproxAmbient n,
      ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) ∞ a ∧
      (∀ q : SweepDomain, dist (a ((q.1:ℝ),q.2)) (f ((q.1:ℝ),q.2)) < eps) ∧
      ∀ (s : SweepParameter) p i,
        ‖ambientSliceVector (fun z => a ((s:ℝ),z)) p i -
          ambientSliceVector (fun z => f ((s:ℝ),z)) p i‖ ≤ eps
theorem cylinderCompact_isCompact : IsCompact cylinderCompact :=
  isCompact_Icc.prod (isCompact_sphere (0 : ApproxAmbient 3) 1)
theorem cylinderInclusion_smooth :
    ContMDiff SweepModel 𝓘(ℝ,CylinderAmbient) ∞ cylinderInclusion := by
  letI : Fact (Module.finrank ℝ (ApproxAmbient 3) = 2+1) := ⟨by simp [ApproxAmbient]⟩
  have hs : ContMDiff (𝓡 2) 𝓘(ℝ,ApproxAmbient 3) ∞ (fun p : Sphere2 => p.val) :=
    contMDiff_coe_sphere
  have ht : ContMDiff SweepModel 𝓘(ℝ,ℝ) ∞ (Prod.fst : ℝ × Sphere2 → ℝ) := contMDiff_fst
  have hp : ContMDiff SweepModel (𝓡 2) ∞ (Prod.snd : ℝ × Sphere2 → Sphere2) := contMDiff_snd
  exact (contMDiff_prod_module_iff cylinderInclusion).mpr ⟨ht,hs.comp hp⟩
#print axioms cylinderCompact_isCompact
#print axioms cylinderInclusion_smooth
end PoincareConjecture.ProofContract.Refinement20260927
