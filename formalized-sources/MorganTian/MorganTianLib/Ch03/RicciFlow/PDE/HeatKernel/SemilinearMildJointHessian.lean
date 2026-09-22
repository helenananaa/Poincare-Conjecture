import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildRestart
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FreeHeatJointHessian
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullHessianJointContinuity
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.MildSourceUniformHolder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelRestart
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelTerminalQuotient
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.CompactSpatialDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedNemytskiiOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual spatial second derivatives of a mild solution are jointly continuous at positive times. -/
theorem semilinear_mild_joint_hessian_continuity (f : E3 →ᵇ ℝ) (N : ℝ → ℝ)
    (L T : ℝ) (hL : 0≤L) (hT : 0<T)
    (hN : ∀ a b : ℝ, |N a-N b|≤L*|a-b|) (u : (ℝ × E3) →ᵇ ℝ)
    (hu : ∀ t : ℝ, 0<t → t≤T → ∀ x : E3,
      u (t,x)=(∫ y : E3, euclideanHeatKernel 3 t y*f (x-y))+
        ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y*N (u (s,x-y)))
    (i j : Fin 3) :
    ContinuousOn (fun p : ℝ × E3 => fderiv ℝ (fun z : E3 =>
      fderiv ℝ (fun w : E3 => u (p.1,w)) z (EuclideanSpace.single i 1)) p.2
        (EuclideanSpace.single j 1)) (Ioo (0:ℝ) T ×ˢ (univ : Set E3)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rintro ⟨t₀, x₀⟩ hp
  have ht₀ : 0 < t₀ := hp.1.1
  have ht₀T : t₀ < T := hp.1.2
  let S : ℝ := t₀ / 2
  have hS : 0 < S := by
    dsimp [S]
    linarith
  have hSt₀ : S < t₀ := by
    dsimp [S]
    linarith
  have hST : S ≤ T := by
    dsimp [S]
    linarith
  have hTS : 0 < T - S := by
    dsimp [S]
    linarith
  obtain ⟨B, hB, -, -⟩ := bounded_nemytskii_operator N L hL hN
  let uS : E3 →ᵇ ℝ := u.compContinuous
    ⟨fun y : E3 => (S, y), continuous_const.prodMk continuous_id⟩
  let F : (ℝ × E3) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => (B u) (S + p.1, p.2))
      ((B u).continuous.comp
        ((continuous_const.add continuous_fst).prodMk continuous_snd))
      ‖B u‖ (by
        intro p
        exact (B u).norm_coe_le_norm (S + p.1, p.2))
  have hF_apply (s : ℝ) (x : E3) : F (s, x) = N (u (S + s, x)) := by
    dsimp [F]
    exact hB u (S + s, x)
  obtain ⟨C, hC, hHolder⟩ :=
    mild_source_uniform_holder_away_zero f N L T hL hT.le hN u hu
      S (1 / 2 : ℝ) hS hST (by norm_num) (by norm_num)
  have hFHolder : ∀ s ∈ Icc (0 : ℝ) (T - S), ∀ x y : E3,
      |F (s, x) - F (s, y)| ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    intro s hs x y
    have hsST : S + s ∈ Icc S T := by
      constructor
      · linarith [hs.1]
      · linarith [hs.2]
    calc
      |F (s, x) - F (s, y)| =
          |N (u (S + s, x)) - N (u (S + s, y))| := by
            rw [hF_apply, hF_apply]
      _ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) := hHolder (S + s) hsST x y
  obtain ⟨Cfull, hCfull, hfull⟩ :=
    full_duhamel_spatial_C2 (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let Kfree : (ℝ × E3) → ℝ := fun q => ∫ y : E3,
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 q.1) z
      (EuclideanSpace.single i 1)) (q.2 - y) (EuclideanSpace.single j 1) * uS y
  let Kduh : (ℝ × E3) → ℝ := fun q => ∫ s in (0 : ℝ)..q.1, ∫ y : E3,
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (q.1 - s)) z
      (EuclideanSpace.single i 1)) (q.2 - y) (EuclideanSpace.single j 1) * F (s, y)
  have hKfree_cont : ContinuousOn Kfree
      (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
    simpa [Kfree] using free_heat_joint_hessian_continuity uS i j
  have hKduh_cont : ContinuousOn Kduh
      (Ioo (0 : ℝ) (T - S) ×ˢ (univ : Set E3)) := by
    simpa [Kduh] using
      full_hessian_joint_continuity F (1 / 2 : ℝ) C (T - S)
        (by norm_num) (by norm_num) hC hTS hFHolder i j
  have hreflect (k g : E3 → ℝ) (x : E3) :
      (∫ y : E3, k y * g (x - y)) = ∫ y : E3, k (x - y) * g y := by
    let p : E3 → ℝ := fun y => k y * g (x - y)
    have hmap :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding p
    calc
      (∫ y : E3, k y * g (x - y)) = ∫ y : E3, p y := by rfl
      _ = ∫ y : E3, p (x - y) := hmap.symm
      _ = ∫ y : E3, k (x - y) * g y := by
        congr 1
        funext y
        dsimp [p]
        rw [sub_sub_cancel]
  let Hactual : (ℝ × E3) → ℝ := fun q => fderiv ℝ (fun z : E3 =>
      fderiv ℝ (fun w : E3 => u (q.1, w)) z (EuclideanSpace.single i 1)) q.2
        (EuclideanSpace.single j 1)
  let Hformula : (ℝ × E3) → ℝ := fun q =>
    Kfree (q.1 - S, q.2) + Kduh (q.1 - S, q.2)
  let V : Set (ℝ × E3) := Ioo S T ×ˢ (univ : Set E3)
  have hV : V ∈ 𝓝 (t₀, x₀) := by
    apply (isOpen_Ioo.prod isOpen_univ).mem_nhds
    exact ⟨⟨hSt₀, ht₀T⟩, mem_univ _⟩
  have hphi : Continuous (fun q : ℝ × E3 => (q.1 - S, q.2)) := by
    fun_prop
  have hKfree_at : ContinuousAt Kfree (t₀ - S, x₀) :=
    hKfree_cont.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        ⟨sub_pos.mpr hSt₀, mem_univ _⟩)
  have hKduh_at : ContinuousAt Kduh (t₀ - S, x₀) :=
    hKduh_cont.continuousAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨⟨sub_pos.mpr hSt₀, by linarith [ht₀T]⟩,
          mem_univ _⟩)
  have hHformula_at : ContinuousAt Hformula (t₀, x₀) := by
    have hfree_shift : ContinuousAt (fun q : ℝ × E3 => Kfree (q.1 - S, q.2))
        (t₀, x₀) :=
      ContinuousAt.comp' (f := fun q : ℝ × E3 => (q.1 - S, q.2))
        (g := Kfree) hKfree_at hphi.continuousAt
    have hduh_shift : ContinuousAt (fun q : ℝ × E3 => Kduh (q.1 - S, q.2))
        (t₀, x₀) :=
      ContinuousAt.comp' (f := fun q : ℝ × E3 => (q.1 - S, q.2))
        (g := Kduh) hKduh_at hphi.continuousAt
    change ContinuousAt
      ((fun q : ℝ × E3 => Kfree (q.1 - S, q.2)) +
        (fun q : ℝ × E3 => Kduh (q.1 - S, q.2))) (t₀, x₀)
    exact hfree_shift.add hduh_shift
  have hEqOn : ∀ q ∈ V, Hactual q = Hformula q := by
    intro q hq
    let τ : ℝ := q.1 - S
    have hτ : 0 < τ := by
      dsimp [τ]
      linarith [hq.1.1]
    have hτTS : τ ≤ T - S := by
      dsimp [τ]
      linarith [hq.1.2.le]
    let freeR : E3 → ℝ := fun x => ∫ y : E3,
      euclideanHeatKernel 3 τ y * uS (x - y)
    let duhR : E3 → ℝ := fun x => ∫ r in (0 : ℝ)..τ, ∫ y : E3,
      euclideanHeatKernel 3 (τ - r) y * F (r, x - y)
    let freeC : E3 → ℝ := fun x => ∫ y : E3,
      euclideanHeatKernel 3 τ (x - y) * uS y
    let duhC : E3 → ℝ := fun x => ∫ r in (0 : ℝ)..τ, ∫ y : E3,
      euclideanHeatKernel 3 (τ - r) (x - y) * F (r, y)
    have hfree_fun : freeR = freeC := by
      funext x
      exact hreflect (euclideanHeatKernel 3 τ) uS x
    have hduh_fun : duhR = duhC := by
      funext x
      apply intervalIntegral.integral_congr
      intro r hr
      exact hreflect (euclideanHeatKernel 3 (τ - r)) (fun y : E3 => F (r, y)) x
    have hholderτ : ∀ s ∈ Icc (0 : ℝ) τ, ∀ x y : E3,
        |F (s, x) - F (s, y)| ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
      intro s hs x y
      exact hFHolder s ⟨hs.1, hs.2.trans hτTS⟩ x y
    have hC2duh : ContDiff ℝ 2 duhC :=
      (hfull F C τ hC hτ hholderτ).1
    have hC2duhR : ContDiff ℝ 2 duhR := by
      rw [hduh_fun]
      exact hC2duh
    have hfree_id : ∀ x : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ freeR z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
          Kfree (τ, x) := by
      intro x
      have hraw :=
        (euclideanHeatKernel_bounded_hessian_identification uS hτ).2 x i j
      rw [hfree_fun]
      have hchange :
          (∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ
            (euclideanHeatKernel 3 τ) z (EuclideanSpace.single i 1)) y
              (EuclideanSpace.single j 1) * uS (x - y)) = Kfree (τ, x) := by
        exact hreflect
          (fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ
            (euclideanHeatKernel 3 τ) z (EuclideanSpace.single i 1)) y
              (EuclideanSpace.single j 1)) uS x
      simpa [Kfree, freeC] using hraw.trans hchange
    have hduh_id : ∀ x : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ duhR z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
          Kduh (τ, x) := by
      intro x
      have hraw := ((hfull F C τ hC hτ hholderτ).2 x i j).1
      rw [hduh_fun]
      have hchange :
          (∫ s in (0 : ℝ)..τ, ∫ y : E3,
            fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (τ - s)) z
              (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) *
                F (s, x - y)) = Kduh (τ, x) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact hreflect
          (fun y : E3 => fderiv ℝ (fun z : E3 =>
            fderiv ℝ (euclideanHeatKernel 3 (τ - s)) z
              (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1))
          (fun y : E3 => F (s, y)) x
      simpa [duhC, Kduh] using hraw.trans hchange
    have hfreeC2 : ContDiff ℝ 2 freeR := by
      rw [hfree_fun]
      exact (euclideanHeatKernel_bounded_hessian_identification uS hτ).1
    have hfreeGrad : ContDiff ℝ 1
        (fun z : E3 => fderiv ℝ freeR z (EuclideanSpace.single i 1)) :=
      (hfreeC2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hduhGrad : ContDiff ℝ 1
        (fun z : E3 => fderiv ℝ duhR z (EuclideanSpace.single i 1)) := by
      exact (hC2duhR.fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiff_const : ContDiff ℝ 1
          (fun _ : E3 => (EuclideanSpace.single i 1 : E3)))
    have hsum_hessian (z₀ : E3) :
        fderiv ℝ (fun z : E3 => fderiv ℝ (fun w : E3 =>
          freeR w + duhR w) z (EuclideanSpace.single i 1)) z₀
            (EuclideanSpace.single j 1) =
          fderiv ℝ (fun z : E3 => fderiv ℝ freeR z
            (EuclideanSpace.single i 1)) z₀ (EuclideanSpace.single j 1) +
          fderiv ℝ (fun z : E3 => fderiv ℝ duhR z
            (EuclideanSpace.single i 1)) z₀ (EuclideanSpace.single j 1) := by
      have hfirst : (fun z : E3 => fderiv ℝ (fun w : E3 =>
          freeR w + duhR w) z (EuclideanSpace.single i 1)) =
          (fun z : E3 => fderiv ℝ freeR z (EuclideanSpace.single i 1) +
            fderiv ℝ duhR z (EuclideanSpace.single i 1)) := by
        funext z
        have h := fderiv_fun_add (hfreeC2.differentiable (by norm_num) z)
          (hC2duhR.differentiable (by norm_num) z)
        simpa only [Pi.add_apply, add_apply] using
          congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) h
      rw [hfirst]
      have h := fderiv_fun_add (hfreeGrad.differentiable (by norm_num) z₀)
        (hduhGrad.differentiable (by norm_num) z₀)
      simpa only [Pi.add_apply, add_apply] using
        congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) h
    have hrestart (x : E3) :=
      semilinear_mild_restart f N L T hL hN u hu S τ hS hτ
        (by dsimp [τ]; linarith [hq.1.2.le]) x
    have hduh_shift : ∀ x : E3,
        (∫ s in S..(S + τ), ∫ y : E3,
          euclideanHeatKernel 3 (S + τ - s) y * N (u (s, x - y))) = duhR x := by
      intro x
      let qfun : ℝ → ℝ := fun s => ∫ y : E3,
        euclideanHeatKernel 3 (S + τ - s) y * N (u (s, x - y))
      calc
        (∫ s in S..(S + τ), ∫ y : E3,
            euclideanHeatKernel 3 (S + τ - s) y * N (u (s, x - y))) =
            ∫ r in (0 : ℝ)..τ, qfun (r + S) := by
              have h := intervalIntegral.integral_comp_add_right
                (f := qfun) (a := (0 : ℝ)) (b := τ) S
              change (∫ s in S..(S + τ), qfun s) =
                ∫ r in (0 : ℝ)..τ, qfun (r + S)
              symm
              simpa only [zero_add, add_comm τ S] using h
        _ = duhR x := by
          apply intervalIntegral.integral_congr
          intro r hr
          apply integral_congr_ae
          filter_upwards [] with y
          rw [hF_apply]
          rw [add_comm r S]
          have htime : S + τ - (S + r) = τ - r := by ring
          rw [htime]
    have hfun : (fun z : E3 => u (q.1, z)) =
        (fun z : E3 => freeR z + duhR z) := by
      funext z
      calc
        u (q.1, z) = u (S + τ, z) := by
          congr 1
          dsimp [τ]
          ring
        _ = (∫ y : E3, euclideanHeatKernel 3 τ y * u (S, z - y)) +
            ∫ s in S..(S + τ), ∫ y : E3,
              euclideanHeatKernel 3 (S + τ - s) y * N (u (s, z - y)) :=
          hrestart z
        _ = freeR z + duhR z := by
          rw [hduh_shift]
          rfl
    calc
      Hactual q = fderiv ℝ (fun z : E3 => fderiv ℝ (fun w : E3 =>
          u (q.1, w)) z (EuclideanSpace.single i 1)) q.2
            (EuclideanSpace.single j 1) := rfl
      _ = fderiv ℝ (fun z : E3 => fderiv ℝ (fun w : E3 =>
          freeR w + duhR w) z (EuclideanSpace.single i 1)) q.2
            (EuclideanSpace.single j 1) := by rw [hfun]
      _ = Kfree (τ, q.2) + Kduh (τ, q.2) := by
        rw [hsum_hessian q.2]
        rw [hfree_id, hduh_id]
      _ = Hformula q := by
        dsimp [Hformula, τ]
  have hEq_nhds : Hactual =ᶠ[𝓝 (t₀, x₀)] Hformula := by
    filter_upwards [hV] with q hq
    exact hEqOn q hq
  apply hHformula_at.continuousWithinAt.congr_of_eventuallyEq
    (hEq_nhds.filter_mono inf_le_left)
  exact hEqOn (t₀, x₀) ⟨⟨by linarith [hS], ht₀T⟩, mem_univ _⟩
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
