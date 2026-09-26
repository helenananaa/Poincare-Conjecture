import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothFixedPointDependence
open scoped ContDiff Topology
/-- Smoothness of the SAME given continuous fixed-point branch. The small
state derivative gives invertibility; no smoothness of the branch is assumed. -/
theorem contDiffAt_of_small_state_derivative
    {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : P × Y → Y) (u : P → Y) (a : P)
    (hF : ContDiffAt ℝ ∞ F (a, u a)) (hu : ContinuousAt u a)
    (hfixed : ∀ᶠ p in 𝓝 a, u p = F (p, u p))
    (hsmall : ‖(fderiv ℝ F (a, u a)).comp (ContinuousLinearMap.inr ℝ P Y)‖ < 1) :
    ContDiffAt ℝ ∞ u a :=
/- SWARM_PROOF_BEGIN -/
by
  let x₀ : P × Y := (a, u a)
  have hfix : u a = F (a, u a) := by
    have hfix' : u =ᶠ[𝓝 a] fun p => F (p, u p) := hfixed
    exact hfix'.eq_of_nhds
  let dF : (P × Y) →L[ℝ] Y := fderiv ℝ F x₀
  have hdF : HasFDerivAt F dF x₀ :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let A : P →L[ℝ] Y := dF.comp (ContinuousLinearMap.inl ℝ P Y)
  let B : Y →L[ℝ] Y := dF.comp (ContinuousLinearMap.inr ℝ P Y)
  have hB : ‖B‖ < 1 := by simpa [B, x₀] using hsmall
  let U : (Y →L[ℝ] Y)ˣ := Units.oneSub B hB
  let C : Y →L[ℝ] Y := (↑(U⁻¹) : Y →L[ℝ] Y)
  let D : Y →L[ℝ] Y := (↑U : Y →L[ℝ] Y)
  have hD : D = ContinuousLinearMap.id ℝ Y - B := by
    simp [D, U, B, ContinuousLinearMap.one_def]
  have hCD : C.comp D = ContinuousLinearMap.id ℝ Y := by
    change C * D = 1
    exact Units.inv_val U
  have hDC : D.comp C = ContinuousLinearMap.id ℝ Y := by
    change D * C = 1
    exact Units.val_inv U
  have hsplit (z : P × Y) : dF z = A z.1 + B z.2 := by
    have hz : z = ContinuousLinearMap.inl ℝ P Y z.1 +
        ContinuousLinearMap.inr ℝ P Y z.2 := by
      ext <;> simp [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
    calc
      dF z = dF (ContinuousLinearMap.inl ℝ P Y z.1 +
          ContinuousLinearMap.inr ℝ P Y z.2) := congrArg dF hz
      _ = dF (ContinuousLinearMap.inl ℝ P Y z.1) +
          dF (ContinuousLinearMap.inr ℝ P Y z.2) := map_add dF _ _
      _ = A z.1 + B z.2 := by simp [A, B, ContinuousLinearMap.comp_apply]
  let H : P × Y → P × Y := fun z => z - ContinuousLinearMap.inr ℝ P Y (F z)
  let L : (P × Y) →L[ℝ] (P × Y) :=
    ContinuousLinearMap.id ℝ (P × Y) -
      (ContinuousLinearMap.inr ℝ P Y).comp dF
  let K : (P × Y) →L[ℝ] Y :=
    C.comp (A.comp (ContinuousLinearMap.fst ℝ P Y) +
      ContinuousLinearMap.snd ℝ P Y)
  let J : (P × Y) →L[ℝ] (P × Y) :=
    (ContinuousLinearMap.fst ℝ P Y).prod K
  have hLJ : L.comp J = ContinuousLinearMap.id ℝ (P × Y) := by
    apply ContinuousLinearMap.ext
    intro z
    rcases z with ⟨p, q⟩
    apply Prod.ext
    · simp [L, J, K]
    · have hpoint : D (C (A p + q)) = A p + q := by
        have := congrArg (fun f : Y →L[ℝ] Y => f (A p + q)) hDC
        simpa [ContinuousLinearMap.comp_apply] using this
      change C (A p + q) - dF (p, C (A p + q)) = q
      rw [hsplit]
      have hpoint' : C (A p + q) - B (C (A p + q)) = A p + q := by
        simpa only [hD, sub_apply,
          ContinuousLinearMap.id_apply] using hpoint
      calc
        C (A p + q) - (A p + B (C (A p + q))) =
            (C (A p + q) - B (C (A p + q))) - A p := by abel
        _ = q := by rw [hpoint']; abel
  have hJL : J.comp L = ContinuousLinearMap.id ℝ (P × Y) := by
    apply ContinuousLinearMap.ext
    intro z
    rcases z with ⟨p, q⟩
    apply Prod.ext
    · simp [L, J, K]
    · have hpoint : C (D q) = q := by
        have := congrArg (fun f : Y →L[ℝ] Y => f q) hCD
        simpa [ContinuousLinearMap.comp_apply] using this
      simp only [J, K, L, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', sub_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.inr_apply]
      change C (A ((p, q) - (0, dF (p, q))).1 +
        ((p, q) - (0, dF (p, q))).2) = q
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
      have harg : A p + (q - dF (p, q)) = D q := by
        rw [hsplit]
        have hDq : D q = q - B q := by
          rw [hD]
          simp
        rw [hDq]
        abel
      rw [harg, hpoint]
  have hinj : L.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    have hx : (J.comp L) x = x := by
      have := congrArg (fun f : (P × Y) →L[ℝ] (P × Y) => f x) hJL
      simpa [ContinuousLinearMap.comp_apply] using this
    have hy : (J.comp L) y = y := by
      have := congrArg (fun f : (P × Y) →L[ℝ] (P × Y) => f y) hJL
      simpa [ContinuousLinearMap.comp_apply] using this
    calc
      x = (J.comp L) x := hx.symm
      _ = J (L y) := by
        exact congrArg J hxy
      _ = (J.comp L) y := by rw [ContinuousLinearMap.comp_apply]
      _ = y := hy
  have hsurj : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro z
    exact ⟨J z, by
      have := congrArg (fun f : (P × Y) →L[ℝ] (P × Y) => f z) hLJ
      simpa [ContinuousLinearMap.comp_apply] using this⟩
  let e : (P × Y) ≃L[ℝ] (P × Y) := ContinuousLinearEquiv.ofBijective L hinj hsurj
  have hHderiv : HasFDerivAt H (e : (P × Y) →L[ℝ] (P × Y)) x₀ := by
    have houter : HasFDerivAt (fun y : Y => ContinuousLinearMap.inr ℝ P Y y)
        (ContinuousLinearMap.inr ℝ P Y) (F x₀) :=
      (ContinuousLinearMap.inr ℝ P Y).hasFDerivAt
    have h := (hasFDerivAt_id x₀).sub (HasFDerivAt.comp x₀ houter hdF)
    have he : (e : (P × Y) →L[ℝ] (P × Y)) = L :=
      ContinuousLinearEquiv.coe_ofBijective L hinj hsurj
    have hEq : H =ᶠ[𝓝 x₀] (id - fun z : P × Y => (0, F z)) := by
      filter_upwards with z
      simp [H]
    have h₂ : HasFDerivAt H L x₀ := by
      simpa [L, Function.comp_def] using h.congr_of_eventuallyEq hEq
    simpa [he] using h₂
  have hHdiff : ContDiffAt ℝ ∞ H x₀ := by
    apply ContDiffAt.sub contDiffAt_id
    exact ContDiff.comp_contDiffAt x₀
      (ContinuousLinearMap.inr ℝ P Y).contDiff hF
  have hH₀ : H x₀ = (a, 0) := by
    change (a, u a) - (0, F (a, u a)) = (a, 0)
    rw [← hfix]
    simp
  have hinv : ContDiffAt ℝ ∞ (hHdiff.localInverse hHderiv (by simp)) (a, 0) := by
    simpa [hH₀] using hHdiff.to_localInverse hHderiv (by simp)
  let g : P → Y := fun p => (hHdiff.localInverse hHderiv (by simp) (p, 0)).2
  have hg : ContDiffAt ℝ ∞ g a := by
    have hinput : ContDiffAt ℝ ∞ (fun p : P => (p, (0 : Y))) a := by
      exact contDiffAt_id.prodMk contDiffAt_const
    have hcomp : ContDiffAt ℝ ∞
        (fun p : P => hHdiff.localInverse hHderiv (by simp) (p, 0)) a := by
      exact hinv.comp a hinput
    exact (ContinuousLinearMap.snd ℝ P Y).contDiff.contDiffAt.comp a hcomp
  have hgraph : ContinuousAt (fun p : P => (p, u p)) a :=
    continuousAt_id.prodMk hu
  have hleft : ∀ᶠ p in 𝓝 a,
      hHdiff.localInverse hHderiv (by simp) (H (p, u p)) = (p, u p) := by
    have hleft' : ∀ᶠ z in 𝓝 x₀,
        hHdiff.localInverse hHderiv (by simp) (H z) = z := by
      exact (hHdiff.hasStrictFDerivAt' hHderiv (by simp)).eventually_left_inverse
    exact hgraph.tendsto.eventually hleft'
  have hbranch : g =ᶠ[𝓝 a] u := by
    filter_upwards [hleft, hfixed] with p hp hfp
    have hHp : H (p, u p) = (p, 0) := by
      change (p, u p) - (0, F (p, u p)) = (p, 0)
      rw [hfp.symm]
      simp
    rw [hHp] at hp
    simpa [g] using congrArg Prod.snd hp
  exact hg.congr_of_eventuallyEq hbranch.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothFixedPointDependence
