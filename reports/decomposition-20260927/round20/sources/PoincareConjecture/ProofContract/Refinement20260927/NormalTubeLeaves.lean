import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTwentySeven
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff
abbrev NormalTangent := EuclideanSpace ℝ (Fin 3)
def NormalFiber {n : ℕ} (L : NormalTangent →L[ℝ] ApproxAmbient n) :
    Submodule ℝ (ApproxAmbient n) := (LinearMap.range L.toLinearMap)ᗮ
abbrev NormalSplit {n : ℕ} (L : NormalTangent →L[ℝ] ApproxAmbient n) :=
  NormalTangent × NormalFiber L
def normalBlock {n : ℕ} (L : NormalTangent →L[ℝ] ApproxAmbient n) :
    NormalSplit L →L[ℝ] ApproxAmbient n :=
  L.comp (ContinuousLinearMap.fst ℝ NormalTangent (NormalFiber L)) +
    (NormalFiber L).subtypeL.comp (ContinuousLinearMap.snd ℝ NormalTangent (NormalFiber L))
/-- **Math.** Finite-dimensional normal splitting for the SAME injective tangent map. -/
def NormalLinearEquivStatement : Prop :=
  ∀ (n : ℕ) (L : NormalTangent →L[ℝ] ApproxAmbient n), Function.Injective L →
    ∃ A : NormalSplit L ≃L[ℝ] ApproxAmbient n, A.toContinuousLinearMap = normalBlock L
/-- **Math.** The zero-fiber derivative is derived, not a field of the coordinate data. -/
def NormalEndpointJetStatement : Prop :=
  ∀ (n : ℕ) (L : NormalTangent →L[ℝ] ApproxAmbient n) (x : NormalTangent)
    (f : NormalTangent → ApproxAmbient n)
    (P : NormalTangent → (ApproxAmbient n →L[ℝ] ApproxAmbient n)),
    HasFDerivAt f L x → DifferentiableAt ℝ P x →
    (∀ v : NormalFiber L, P x v = v) →
    HasFDerivAt (fun z : NormalSplit L => f z.1 + P z.1 z.2) (normalBlock L) (x,0)
/-- **Math.** Local inverse function theorem with exact endpoint and projected smoothness.
The supplied chart is a parameter chart, NOT an inverse of the endpoint. -/
def TubularChartInverseStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (X : Type u) [MetricSpace X]
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (c : OpenPartialHomeomorph X F) (x : X) (endpoint : C(X, ApproxAmbient n))
    (project : C(X,N)) (A : F ≃L[ℝ] ApproxAmbient n), x ∈ c.source →
    ContDiffOn ℝ ∞ (endpoint ∘ c.symm) c.target →
    HasFDerivAt (endpoint ∘ c.symm) A.toContinuousLinearMap (c x) →
    ContMDiffOn 𝓘(ℝ,F) (𝓡 3) ∞ (project ∘ c.symm) c.target →
    ∃ d : OpenPartialHomeomorph X (ApproxAmbient n), x ∈ d.source ∧
      EqOn d endpoint d.source ∧
      ContMDiffOn 𝓘(ℝ,ApproxAmbient n) (𝓡 3) ∞ (project ∘ d.symm) d.target
/-- **Math.** Sanity identity for the literal block operator used in both leaves. -/
theorem normalBlock_apply {n : ℕ} (L : NormalTangent →L[ℝ] ApproxAmbient n)
    (z : NormalSplit L) : normalBlock L z = L z.1 + z.2 := rfl
#print axioms normalBlock_apply
end PoincareConjecture.ProofContract.Refinement20260927
