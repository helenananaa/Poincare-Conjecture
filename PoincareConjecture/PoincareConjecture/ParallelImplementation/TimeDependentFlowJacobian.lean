import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TimeDependentFlowJacobian
open Set
open scoped ContDiff Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual Jacobian variational equation on an open flow chart.
The time derivative of the spatial differential is derived from the ODE. -/
theorem hasDerivAt_spatial_jacobian_of_flow_ode
    (F V : ℝ × E3 → E3) (J : Set ℝ) (U : Set E3)
    (hJ : IsOpen J) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F (J ×ˢ U))
    (hV : ContDiff ℝ 1 V)
    (hODE : ∀ t ∈ J, ∀ x ∈ U,
      HasDerivAt (fun s : ℝ => F (s,x)) (V (t,F (t,x))) t) :
    ∀ t ∈ J, ∀ x ∈ U,
      HasDerivAt (fun s : ℝ => fderiv ℝ (fun y : E3 => F (s,y)) x)
        ((fderiv ℝ (fun y : E3 => V (t,y)) (F (t,x))).comp
          (fderiv ℝ (fun y : E3 => F (t,y)) x)) t :=
/- SWARM_PROOF_BEGIN -/
by
  intro t ht x hx
  let S : Set (ℝ × E3) := J ×ˢ U
  have hS : IsOpen S := hJ.prod hU
  have hp : (t, x) ∈ S := by simp [S, ht, hx]
  have hFAt : ContDiffAt ℝ 2 F (t, x) :=
    hF.contDiffAt (hS.mem_nhds hp)
  have hFHas : HasFDerivAt F (fderiv ℝ F (t, x)) (t, x) :=
    (hFAt.differentiableAt (by norm_num)).hasFDerivAt
  have hFderivOn : ContDiffOn ℝ 1 (fderiv ℝ F) S :=
    hF.fderiv_of_isOpen hS (by norm_num)
  have hFderivHas : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) (t, x)) (t, x) :=
    ((hFderivOn.contDiffAt (hS.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hNear : ∀ᶠ q in 𝓝 (t, x),
      HasFDerivAt F (fderiv ℝ F q) q := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact (((hF q hq).contDiffAt (hS.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt
  have hSym := second_derivative_symmetric_of_eventually hNear hFderivHas

  have hSlice : HasFDerivAt (fun y : E3 => F (t, y))
      ((fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) x := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp (x := x) (hg := hFHas)
        (hf := hasFDerivAt_prodMk_right t x)
  have hSliceJac : fderiv ℝ (fun y : E3 => F (t, y)) x =
      (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3) := hSlice.fderiv

  have hTime (y : E3) (hy : y ∈ U) :
      fderiv ℝ F (t, y) (1, 0) = V (t, F (t, y)) := by
    have hAt : ContDiffAt ℝ 2 F (t, y) := by
      apply hF.contDiffAt
      apply hS.mem_nhds
      simp [S, ht, hy]
    have hpath : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) t := by
      simpa using (hasDerivAt_id t).prodMk
        (hasDerivAt_const (c := y) (x := t))
    have hcurve : HasDerivAt (fun s : ℝ => F (s, y))
        (fderiv ℝ F (t, y) (1, 0)) t := by
      simpa [Function.comp_def] using
        HasFDerivAt.comp_hasDerivAt
          (hl := (hAt.differentiableAt (by norm_num)).hasFDerivAt) (hf := hpath)
    exact hcurve.unique (hODE t ht y hy)

  let K : E3 →L[ℝ] E3 :=
    ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3)).flip (1, 0)
  have hK : K =
      (fderiv ℝ (fderiv ℝ F) (t, x) (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E3) := by
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ (fderiv ℝ F) (t, x) (0, v) (1, 0) =
      fderiv ℝ (fderiv ℝ F) (t, x) (1, 0) (0, v)
    exact hSym (0, v) (1, 0)

  have hH : HasFDerivAt (fun y : E3 => fderiv ℝ F (t, y) (1, 0)) K x := by
    have hA : HasFDerivAt (fun y : E3 => fderiv ℝ F (t, y))
        ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) x := by
      simpa [Function.comp_def] using
        HasFDerivAt.comp (x := x) (hg := hFderivHas)
          (hf := hasFDerivAt_prodMk_right t x)
    simpa [K] using HasFDerivAt.clm_apply hA
      (hasFDerivAt_const (c := (1, 0)) (x := x))

  have hVAt : ContDiffAt ℝ 1 V (t, F (t, x)) :=
    hV.contDiffAt (x := (t, F (t, x)))
  have hVSlice : HasFDerivAt (fun z : E3 => V (t, z))
      (fderiv ℝ (fun z : E3 => V (t, z)) (F (t, x))) (F (t, x)) := by
    have h := HasFDerivAt.comp
      (x := F (t, x))
      (hg := (hVAt.differentiableAt (by norm_num)).hasFDerivAt)
      (hf := hasFDerivAt_prodMk_right t (F (t, x)))
    exact h.differentiableAt.hasFDerivAt
  have hR : HasFDerivAt (fun y : E3 => V (t, F (t, y)))
      ((fderiv ℝ (fun z : E3 => V (t, z)) (F (t, x))).comp
        (fderiv ℝ (fun y : E3 => F (t, y)) x)) x :=
    by
      have hR0 := HasFDerivAt.comp (x := x) (hg := hVSlice) (hf := hSlice)
      simpa only [Function.comp_def, ← hSliceJac] using hR0
  have hODEnear : (fun y : E3 => V (t, F (t, y))) =ᶠ[𝓝 x]
      (fun y : E3 => fderiv ℝ F (t, y) (1, 0)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hTime y hy).symm
  have hH' := hH.congr_of_eventuallyEq hODEnear
  have hMixed : K =
      (fderiv ℝ (fun z : E3 => V (t, z)) (F (t, x))).comp
        (fderiv ℝ (fun y : E3 => F (t, y)) x) := hH'.unique hR

  have hpath : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t := by
    simpa using (hasDerivAt_id t).prodMk
      (hasDerivAt_const (c := x) (x := t))
  have hA : HasDerivAt (fun s : ℝ => fderiv ℝ F (s, x))
      (fderiv ℝ (fderiv ℝ F) (t, x) (1, 0)) t := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt (hl := hFderivHas) (hf := hpath)
  have hJacComp : HasDerivAt
      (fun s : ℝ => (fderiv ℝ F (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3))
      ((fderiv ℝ (fderiv ℝ F) (t, x) (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) t := by
    have h := HasDerivAt.clm_comp hA
      (hasDerivAt_const (c := ContinuousLinearMap.inr ℝ ℝ E3) (x := t))
    simpa using h

  have hSliceAt (s : ℝ) (hs : s ∈ J) :
      fderiv ℝ (fun y : E3 => F (s, y)) x =
        (fderiv ℝ F (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3) := by
    have hAt : ContDiffAt ℝ 2 F (s, x) := by
      apply hF.contDiffAt
      apply hS.mem_nhds
      simp [S, hs, hx]
    have h := HasFDerivAt.comp (x := x)
      (hg := (hAt.differentiableAt (by norm_num)).hasFDerivAt)
      (hf := hasFDerivAt_prodMk_right s x)
    simpa [Function.comp_def] using h.fderiv
  have hJac : HasDerivAt (fun s : ℝ => fderiv ℝ (fun y : E3 => F (s, y)) x)
      ((fderiv ℝ (fderiv ℝ F) (t, x) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ E3)) t := by
    apply hJacComp.congr_of_eventuallyEq
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact hSliceAt s hs
  exact hJac.congr_deriv (hK.symm.trans hMixed)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TimeDependentFlowJacobian
