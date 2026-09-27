import PoincareConjecture.ProofContract.Refinement20260927.NormalTubeLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedNormalLinearEquiv
open PoincareConjecture.ProofContract.Refinement20260927
theorem normal_linear_equiv : NormalLinearEquivStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro n L hL
  let K : Submodule ℝ (ApproxAmbient n) := L.toLinearMap.range
  have hK : IsCompl K Kᗮ := K.isCompl_orthogonal
  let eL : NormalTangent ≃ₗ[ℝ] K := LinearEquiv.ofInjective L.toLinearMap hL
  let d : (K × Kᗮ) ≃ₗ[ℝ] ApproxAmbient n := K.prodEquivOfIsCompl Kᗮ hK
  let e : NormalSplit L ≃ₗ[ℝ] ApproxAmbient n :=
    (eL.prodCongr (LinearEquiv.refl ℝ (NormalFiber L))).trans d
  have he : e.toLinearMap = (normalBlock L).toLinearMap := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨v, w⟩
    rfl
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  change e z = normalBlock L z
  have hx := congrArg (fun f : NormalSplit L →ₗ[ℝ] ApproxAmbient n => f z) he
  simpa using hx
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedNormalLinearEquiv
