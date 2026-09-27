import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedNormalFrames
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedNormalBundleParametrization
open PoincareConjecture.ProofContract.Refinement20260927
theorem normal_bundle_parametrization : NormalBundleParametrizationStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro N n e p F hF
  let X := EmbeddedNormalTotal e
  let S : Set X := {z | z.1.1 ∈ F.baseChart.source}
  let T : Set (NormalTangent × ↥(NormalFiber F.linear)) :=
    F.baseChart.target ×ˢ Set.univ
  let backwardFiber : X → NormalFiber F.linear := fun z =>
    if hq : z.1.1 ∈ F.baseChart.source then
      ⟨normalFrameBackward F z.1.1 z.1.2,
        hF.backward_mem z.1.1 hq z.1.2 z.2⟩
    else 0
  let forward : X → (NormalTangent × ↥(NormalFiber F.linear)) := fun z =>
    if hq : z.1.1 ∈ F.baseChart.source then
      (F.baseChart z.1.1, backwardFiber z)
    else (0, 0)
  let backward : (NormalTangent × ↥(NormalFiber F.linear)) → X := fun z =>
    if hx : z.1 ∈ F.baseChart.target then
      ⟨(F.baseChart.symm z.1,
        normalFrameForward F (F.baseChart.symm z.1) z.2),
        hF.forward_mem (F.baseChart.symm z.1) (F.baseChart.map_target hx)
          z.2 z.2.property⟩
    else embeddedNormalZero e p
  have hsource : IsOpen S := by
    dsimp [S]
    exact F.baseChart.open_source.preimage (continuous_fst.comp continuous_subtype_val)
  have htarget : IsOpen T := by
    dsimp [T]
    exact F.baseChart.open_target.prod isOpen_univ
  have hq_cont : ContinuousOn (fun z : X => z.1.1) S := by fun_prop
  have hv_cont : ContinuousOn (fun z : X => z.1.2) S := by fun_prop
  have hchart_cont : ContinuousOn (fun z : X => F.baseChart z.1.1) S :=
    F.baseChart.continuousOn_toFun.comp hq_cont (by intro z hz; exact hz)
  have hback_op_cont : ContinuousOn (fun z : X => normalFrameBackward F z.1.1) S :=
    hF.continuous_backward.comp hq_cont (by intro z hz; exact hz)
  have hback_val_cont :
      ContinuousOn (fun z : X => normalFrameBackward F z.1.1 z.1.2) S :=
    hback_op_cont.clm_apply hv_cont
  have hback_fiber_val_cont :
      ContinuousOn (fun z : X => (backwardFiber z : ApproxAmbient n)) S := by
    apply hback_val_cont.congr
    intro z hz
    change z.1.1 ∈ F.baseChart.source at hz
    simp [backwardFiber, hz]
  have hback_fiber_cont : ContinuousOn backwardFiber S := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    simpa [Function.comp_def] using hback_fiber_val_cont
  have hforward_cont : ContinuousOn forward S := by
    apply (hchart_cont.prodMk hback_fiber_cont).congr
    intro z hz
    change z.1.1 ∈ F.baseChart.source at hz
    simp [forward, backwardFiber, hz]
  have hx_cont :
      ContinuousOn (fun z : NormalTangent × ↥(NormalFiber F.linear) => z.1) T := by
    fun_prop
  have hw_cont :
      ContinuousOn (fun z : NormalTangent × ↥(NormalFiber F.linear) =>
        (z.2 : ApproxAmbient n)) T := by
    fun_prop
  have hsymm_cont :
      ContinuousOn (fun z : NormalTangent × ↥(NormalFiber F.linear) =>
        F.baseChart.symm z.1) T :=
    F.baseChart.continuousOn_invFun.comp hx_cont (by
      intro z hz
      change z.1 ∈ F.baseChart.target ∧ z.2 ∈ Set.univ at hz
      exact hz.1)
  have hforward_op_cont :
      ContinuousOn
        (fun z : NormalTangent × ↥(NormalFiber F.linear) =>
          normalFrameForward F (F.baseChart.symm z.1)) T := by
    have h := hF.smooth_forward.continuousOn.comp hx_cont
      (by
        intro z hz
        change z.1 ∈ F.baseChart.target ∧ z.2 ∈ Set.univ at hz
        exact hz.1)
    simpa [Function.comp_def] using h
  have hforward_val_cont :
      ContinuousOn
        (fun z : NormalTangent × ↥(NormalFiber F.linear) =>
          normalFrameForward F (F.baseChart.symm z.1) (z.2 : ApproxAmbient n)) T :=
    hforward_op_cont.clm_apply hw_cont
  have hbackward_cont : ContinuousOn backward T := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    change ContinuousOn (fun z : NormalTangent × ↥(NormalFiber F.linear) =>
      (backward z).1) T
    apply (hsymm_cont.prodMk hforward_val_cont).congr
    intro z hz
    change z.1 ∈ F.baseChart.target ∧ z.2 ∈ Set.univ at hz
    simp [backward, hz.1]
  let pe : PartialEquiv X (NormalTangent × ↥(NormalFiber F.linear)) :=
    { toFun := forward
      invFun := backward
      source := S
      target := T
      map_source' := by
        intro z hz
        change z.1.1 ∈ F.baseChart.source at hz
        change (forward z).1 ∈ F.baseChart.target ∧ (forward z).2 ∈ Set.univ
        simp [forward, backwardFiber, hz, F.baseChart.map_source hz]
      map_target' := by
        intro z hz
        change z.1 ∈ F.baseChart.target ∧ z.2 ∈ Set.univ at hz
        change (backward z).1.1 ∈ F.baseChart.source
        simp [backward, hz.1]
      left_inv' := by
        intro z hz
        change z.1.1 ∈ F.baseChart.source at hz
        have hmap := F.baseChart.map_source hz
        simp only [forward, backwardFiber, dif_pos hz,
          backward, dif_pos hmap]
        apply Subtype.ext
        apply Prod.ext
        · exact F.baseChart.left_inv hz
        · change normalFrameForward F
            (F.baseChart.symm (F.baseChart z.1.1))
            ((normalFrameBackward F z.1.1) z.1.2) = z.1.2
          rw [F.baseChart.left_inv hz]
          exact hF.forward_backward z.1.1 hz z.1.2 z.2
      right_inv' := by
        intro z hz
        change z.1 ∈ F.baseChart.target ∧ z.2 ∈ Set.univ at hz
        have hq := F.baseChart.map_target hz.1
        simp only [backward, dif_pos hz.1, forward,
          backwardFiber, dif_pos hq]
        apply Prod.ext
        · exact F.baseChart.right_inv hz.1
        · apply Subtype.ext
          exact hF.backward_forward (F.baseChart.symm z.1) hq z.2 z.2.property }
  let ph : PartialHomeomorph X (NormalTangent × ↥(NormalFiber F.linear)) :=
    { toPartialEquiv := pe
      continuousOn_toFun := hforward_cont
      continuousOn_invFun := hbackward_cont }
  let chart : OpenPartialHomeomorph X (NormalSplit F.linear) := ⟨ph, hsource, htarget⟩
  refine ⟨chart, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · have hp : p ∈ F.baseChart.source := F.point_source
    change forward (embeddedNormalZero e p) = (F.baseChart p, 0)
    simp [forward, backwardFiber, embeddedNormalZero, hp]
  · intro z hz
    change z.1 ∈ F.baseChart.target ∧ z.2 ∈ Set.univ at hz
    change (backward z).1.1 = F.baseChart.symm z.1
    simp [backward, hz.1]
  · intro z hz
    change z.1 ∈ F.baseChart.target ∧ z.2 ∈ Set.univ at hz
    change (backward z).1.2 =
      normalFrameForward F (F.baseChart.symm z.1) (z.2 : ApproxAmbient n)
    simp [backward, hz.1]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedNormalBundleParametrization
