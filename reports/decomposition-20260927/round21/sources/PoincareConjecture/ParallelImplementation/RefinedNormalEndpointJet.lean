import PoincareConjecture.ProofContract.Refinement20260927.NormalTubeLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedNormalEndpointJet
open PoincareConjecture.ProofContract.Refinement20260927
theorem normal_endpoint_jet : NormalEndpointJetStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro n L x f P hf hP hnormal
  let S := NormalSplit L
  let fst : S →L[ℝ] NormalTangent := ContinuousLinearMap.fst ℝ _ _
  let snd : S →L[ℝ] NormalFiber L := ContinuousLinearMap.snd ℝ _ _
  let snd' : S →L[ℝ] ApproxAmbient n := (NormalFiber L).subtypeL.comp snd
  let q : S := (x, 0)
  have hfst : HasFDerivAt (fun z : S => z.1) fst q := fst.hasFDerivAt
  have hsnd' : HasFDerivAt (fun z : S => (z.2 : ApproxAmbient n)) snd' q :=
    snd'.hasFDerivAt
  have hf' : HasFDerivAt (fun z : S => f z.1) (L.comp fst) q := by
    have h := hf.comp q hfst
    convert h using 1 <;> rfl
  have hP' : HasFDerivAt (fun z : S => P z.1)
      ((fderiv ℝ P x).comp fst) q := by
    have h := hP.hasFDerivAt.comp q hfst
    convert h using 1 <;> rfl
  have hprod : HasFDerivAt (fun z : S => P z.1 z.2)
      ((P x).comp snd' + ((fderiv ℝ P x).comp fst).flip (0 : ApproxAmbient n)) q := by
    simpa [q] using hP'.clm_apply hsnd'
  have hsum := hf'.add hprod
  convert hsum using 1
  all_goals try rfl
  ext z
  all_goals simp_all [normalBlock_apply, fst, snd, snd',
    ContinuousLinearMap.comp_apply]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedNormalEndpointJet
