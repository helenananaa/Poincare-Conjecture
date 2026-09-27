import PoincareConjecture.ProofContract.Refinement20260927.AcceptedThirtyThree
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff BigOperators
abbrev SweepModel := (𝓘(ℝ,ℝ)).prod (𝓡 2)
def ambientSliceVector {n : ℕ} (f : Sphere2 → ApproxAmbient n) (p : Sphere2)
    (i : Fin (Module.finrank ℝ SphereModel)) : ApproxAmbient n :=
  mfderiv (𝓡 2) 𝓘(ℝ,ApproxAmbient n) f p (sphereEnergyFrame p i)
def ambientDirectionalDerivative {n : ℕ} (f : Sphere2 → ApproxAmbient n) (p : Sphere2)
    (v : TangentSpace (𝓡 2) p) : ApproxAmbient n :=
  mfderiv (𝓡 2) 𝓘(ℝ,ApproxAmbient n) f p v
def embeddedRetractMap {N : CompactSmoothThree.{u}} {n : ℕ}
    (R : SmoothRetractionData N n) : ApproxAmbient n → ApproxAmbient n :=
  R.embed ∘ R.localRetract
/-- **Math.** Genuine uniform C1 control on a neighborhood of the compact embedded image.
Q is chosen before the tolerance. No global retraction smoothness is presumed. -/
def CompactRetractionControlStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (R : SmoothRetractionData N n),
    ContDiffOn ℝ ∞ (embeddedRetractMap R) R.domain ∧
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ eta : ℝ, 0 < eta → ∃ rho : ℝ, 0 < rho ∧
      ∀ (x : ApproxAmbient n), x ∈ range R.embed → ∀ y : ApproxAmbient n, dist y x < rho →
        y ∈ R.domain ∧ dist (embeddedRetractMap R y) x < eta ∧
        ‖fderiv ℝ (embeddedRetractMap R) y - fderiv ℝ (embeddedRetractMap R) x‖ ≤ eta ∧
        ‖fderiv ℝ (embeddedRetractMap R) y‖ ≤ Q
/-- **Math.** A pointwise chain-rule estimate; the fixed-point identity is for the reference
map only, not for its perturbation. This leaf is independent of compactness and tubular data. -/
def SphereCompositionEstimateStatement : Prop :=
  ∀ (n : ℕ) (P : ApproxAmbient n → ApproxAmbient n) (a b : Sphere2 → ApproxAmbient n)
    (p : Sphere2) (v : TangentSpace (𝓡 2) p) (Q C delta : ℝ),
    MDifferentiableAt (𝓡 2) 𝓘(ℝ,ApproxAmbient n) a p →
    MDifferentiableAt (𝓡 2) 𝓘(ℝ,ApproxAmbient n) b p →
    DifferentiableAt ℝ P (a p) → DifferentiableAt ℝ P (b p) → P ∘ b = b →
    0 ≤ Q → 0 ≤ C → 0 ≤ delta →
    ‖fderiv ℝ P (a p)‖ ≤ Q → ‖fderiv ℝ P (a p) - fderiv ℝ P (b p)‖ ≤ delta →
    ‖ambientDirectionalDerivative a p v -
      ambientDirectionalDerivative b p v‖ ≤ delta →
    ‖ambientDirectionalDerivative b p v‖ ≤ C →
    ‖ambientDirectionalDerivative (P ∘ a) p v -
      ambientDirectionalDerivative b p v‖ ≤ delta * (Q+C)
/-- **Math.** Explicit endpoint correction; affine weights are bounded on the parameter interval. -/
def correctAmbientEnds {n : ℕ} (a : ℝ × Sphere2 → ApproxAmbient n) (base : ApproxAmbient n)
    (q : ℝ × Sphere2) : ApproxAmbient n :=
  a q - (1-q.1) • (a (0,q.2)-base) - q.1 • (a (1,q.2)-base)
/-- **Math.** Correction doubles, rather than discards, the value and sphere-derivative tolerance. -/
def AmbientEndpointCorrectionStatement : Prop :=
  ∀ (n : ℕ) (a : ℝ × Sphere2 → ApproxAmbient n) (f : C(SweepDomain,ApproxAmbient n))
    (base : ApproxAmbient n) (delta : ℝ), 0 < delta →
    ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) ∞ a →
    EqOn f (ContinuousMap.const SweepDomain base) sweepoutEnds →
    (∀ q : SweepDomain, dist (a ((q.1:ℝ),q.2)) (f q) < delta) →
    (∀ (s : SweepParameter) p i,
      ‖ambientSliceVector (fun z => a ((s:ℝ),z)) p i -
        ambientSliceVector (fun z => f (s,z)) p i‖ ≤ delta) →
    ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) ∞ (correctAmbientEnds a base) ∧
      (∀ p : Sphere2, correctAmbientEnds a base (0,p) = base ∧
        correctAmbientEnds a base (1,p) = base) ∧
      (∀ q : SweepDomain, dist (correctAmbientEnds a base ((q.1:ℝ),q.2)) (f q) < 2*delta) ∧
      ∀ (s : SweepParameter) p i,
        ‖ambientSliceVector (fun z => correctAmbientEnds a base ((s:ℝ),z)) p i -
          ambientSliceVector (fun z => f (s,z)) p i‖ ≤ 2*delta
/-- **Math.** A smooth time cutoff confines the image globally, while fixing the entire [0,1]
strip. Merely extending by a constant without a smooth cutoff is not sufficient. -/
def AmbientSweepoutConfinementStatement : Prop :=
  ∀ (n : ℕ) (a : ℝ × Sphere2 → ApproxAmbient n) (U : Set (ApproxAmbient n)), IsOpen U →
    ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) ∞ a →
    (∀ q : ℝ × Sphere2, q.1 ∈ Icc (0:ℝ) 1 → a q ∈ U) →
    ∃ b : ℝ × Sphere2 → ApproxAmbient n,
      ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient n) ∞ b ∧
      EqOn b a (Icc (0:ℝ) 1 ×ˢ univ) ∧ ∀ q, b q ∈ U
/-- **Math.** The exact endpoint formula holds before any existence argument. -/
theorem correctAmbientEnds_zero {n : ℕ} (a : ℝ × Sphere2 → ApproxAmbient n)
    (base : ApproxAmbient n) (p : Sphere2) : correctAmbientEnds a base (0,p) = base := by
  simp [correctAmbientEnds]
#print axioms correctAmbientEnds_zero
end PoincareConjecture.ProofContract.Refinement20260927
