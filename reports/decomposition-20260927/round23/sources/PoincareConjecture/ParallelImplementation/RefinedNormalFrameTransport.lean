import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedNormalFrames
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedNormalFrameTransport
open PoincareConjecture.ProofContract.Refinement20260927
theorem normal_frame_transport : NormalFrameTransportStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
open scoped Topology Manifold ContDiff BigOperators in by
  intro N n e p F
  classical
  have hframe_mem (q : N) (hq : q ∈ F.baseChart.source) (i : Fin F.count) :
      F.frame i q ∈ embeddedNormalSpace e q := by
    rw [← F.spans q hq]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hforward_apply (q : N) (v : ApproxAmbient n) :
      normalFrameForward F q v =
        ∑ i : Fin F.count, (innerSL ℝ (F.frame i p) v) • F.frame i q := by
    simp [normalFrameForward, innerSL_apply_apply]
  have hbackward_apply (q : N) (v : ApproxAmbient n) :
      normalFrameBackward F q v =
        ∑ i : Fin F.count, (innerSL ℝ (F.frame i q) v) • F.frame i p := by
    simp [normalFrameBackward, innerSL_apply_apply]
  have hrepresentation (q : N) (hq : q ∈ F.baseChart.source) (v : ApproxAmbient n)
      (hv : v ∈ embeddedNormalSpace e q) :
      (∑ i : Fin F.count, (innerSL ℝ (F.frame i q) v) • F.frame i q) = v := by
    have hrepr (x : ApproxAmbient n) (hx : x ∈ Submodule.span ℝ (Set.range (F.frame · q))) :
        (∑ i : Fin F.count, (innerSL ℝ (F.frame i q) x) • F.frame i q) = x := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have hor := F.orthonormal q hq
        simp [innerSL_apply_apply, orthonormal_iff_ite.mp hor]
      | zero => simp
      | add x y _ _ hx hy =>
        have hx' : (∑ i : Fin F.count, inner ℝ (F.frame i q) x • F.frame i q) = x := by
          simpa only [innerSL_apply_apply] using hx
        have hy' : (∑ i : Fin F.count, inner ℝ (F.frame i q) y • F.frame i q) = y := by
          simpa only [innerSL_apply_apply] using hy
        simp only [innerSL_apply_apply, inner_add_right, add_smul]
        rw [Finset.sum_add_distrib, hx', hy']
      | smul a x _ hx =>
        calc
          (∑ i : Fin F.count, (innerSL ℝ (F.frame i q) (a • x)) • F.frame i q) =
              a • ∑ i : Fin F.count, (innerSL ℝ (F.frame i q) x) • F.frame i q := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            simp [innerSL_apply_apply, inner_smul_right, mul_smul]
          _ = a • x := by rw [hx]
    have hmemspan : v ∈ Submodule.span ℝ (Set.range (F.frame · q)) := by
      rw [F.spans q hq]
      exact hv
    exact hrepr v hmemspan
  refine {
    continuous_forward := ?_
    continuous_backward := ?_
    smooth_forward := ?_
    forward_mem := ?_
    backward_mem := ?_
    backward_forward := ?_
    forward_backward := ?_
    center_identity := ?_ }
  · have hterm (i : Fin F.count) :
        ContinuousOn (fun q : N => (innerSL ℝ (F.frame i p)).smulRight (F.frame i q))
          F.baseChart.source := by
      exact ((ContinuousLinearMap.smulRightL ℝ (ApproxAmbient n) (ApproxAmbient n)
        (innerSL ℝ (F.frame i p))).continuous).comp_continuousOn (F.continuous_frame i)
    have hs : ContinuousOn (fun q : N =>
        ∑ i : Fin F.count, (innerSL ℝ (F.frame i p)).smulRight (F.frame i q))
        F.baseChart.source := by
      apply continuousOn_finsetSum Finset.univ
      intro i hi
      exact hterm i
    have heq (q : N) : normalFrameForward F q =
        ∑ i : Fin F.count, (innerSL ℝ (F.frame i p)).smulRight (F.frame i q) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
      exact hforward_apply q v
    exact hs.congr (fun q hq => heq q)
  · have hterm (i : Fin F.count) :
        ContinuousOn (fun q : N => (innerSL ℝ (F.frame i q)).smulRight (F.frame i p))
          F.baseChart.source := by
      have hvec : ContinuousOn (fun q : N => F.frame i q) F.baseChart.source :=
        F.continuous_frame i
      have hdual : ContinuousOn (fun q : N => innerSL ℝ (F.frame i q))
          F.baseChart.source := by
        have hflip : ContinuousOn (fun q : N => innerSLFlip ℝ (F.frame i q))
            F.baseChart.source := (innerSLFlip ℝ).continuous.comp_continuousOn hvec
        exact hflip.congr (fun q hq => by
          ext w
          rw [innerSL_apply_apply, innerSLFlip_apply_apply]
          exact real_inner_comm _ _)
      have hbil :=
        (ContinuousLinearMap.smulRightL ℝ (ApproxAmbient n) (ApproxAmbient n)).continuous₂
      exact hbil.comp_continuousOn (hdual.prodMk continuousOn_const)
    have hs : ContinuousOn (fun q : N =>
        ∑ i : Fin F.count, (innerSL ℝ (F.frame i q)).smulRight (F.frame i p))
        F.baseChart.source := by
      apply continuousOn_finsetSum Finset.univ
      intro i hi
      exact hterm i
    have heq (q : N) : normalFrameBackward F q =
        ∑ i : Fin F.count, (innerSL ℝ (F.frame i q)).smulRight (F.frame i p) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
      exact hbackward_apply q v
    exact hs.congr (fun q hq => heq q)
  · change ContDiffOn ℝ ((⊤ : WithTop ℕ) : WithTop (WithTop ℕ))
        (fun z : NormalTangent =>
        ∑ i : Fin F.count,
          (innerSL ℝ (F.frame i p)).smulRight (F.frame i (F.baseChart.symm z)))
        F.baseChart.target
    apply ContDiffOn.sum
    intro i hi
    have hc : ContDiffOn ℝ ((⊤ : WithTop ℕ) : WithTop (WithTop ℕ))
        (fun _ : NormalTangent => innerSL ℝ (F.frame i p)) F.baseChart.target :=
      contDiffOn_const
    exact hc.smulRight (F.smooth_frame i)
  · intro q hq v hv
    rw [hforward_apply]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (hframe_mem q hq i)
  · intro q hq v hv
    rw [hbackward_apply]
    apply Submodule.sum_mem
    intro i hi
    rw [← F.center_normal]
    exact Submodule.smul_mem _ _ (hframe_mem p F.point_source i)
  · intro q hq v hv
    have hcoeff (i : Fin F.count) :
        innerSL ℝ (F.frame i q) (normalFrameForward F q v) =
          innerSL ℝ (F.frame i p) v := by
      rw [hforward_apply, innerSL_apply_apply]
      simpa only [innerSL_apply_apply] using
        (F.orthonormal q hq).inner_right_fintype
          (fun j : Fin F.count => innerSL ℝ (F.frame j p) v) i
    rw [hbackward_apply]
    simp_rw [hcoeff]
    exact hrepresentation p F.point_source v (by rw [F.center_normal]; exact hv)
  · intro q hq v hv
    have hcoeff (i : Fin F.count) :
        innerSL ℝ (F.frame i p) (normalFrameBackward F q v) =
          innerSL ℝ (F.frame i q) v := by
      rw [hbackward_apply, innerSL_apply_apply]
      simpa only [innerSL_apply_apply] using
        (F.orthonormal p F.point_source).inner_right_fintype
          (fun j : Fin F.count => innerSL ℝ (F.frame j q) v) i
    rw [hforward_apply]
    simp_rw [hcoeff]
    exact hrepresentation q hq v hv
  · intro v
    rw [hforward_apply]
    exact hrepresentation p F.point_source v.1 (by rw [F.center_normal]; exact v.2)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedNormalFrameTransport
