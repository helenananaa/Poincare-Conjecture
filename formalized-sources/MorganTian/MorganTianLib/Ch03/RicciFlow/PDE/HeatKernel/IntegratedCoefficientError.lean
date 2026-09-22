import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatCoefficientCommutator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The true coefficient-freezing error is small after time integration. -/
theorem integrated_coefficient_freezing_error (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : E3 → ℝ, Continuous a → ∀ L : ℝ, 0 ≤ L →
      (∀ x y : E3, |a x-a y| ≤ L*‖x-y‖^alpha) →
      ∀ (F : (ℝ × E3) →ᵇ ℝ) (T : ℝ), 0 ≤ T → ∀ (x : E3) (i j : Fin 3),
        IntervalIntegrable (fun s => ∫ y : E3, (a x-a (x-y))*
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)) volume 0 T ∧
        |∫ s in (0:ℝ)..T, ∫ y : E3, (a x-a (x-y))*
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)|
          ≤ C*L*‖F‖*T^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₀, hC₀, hspatial⟩ :=
    heat_hessian_coefficient_commutator alpha ha ha1
  let C : ℝ := (2 / alpha) * C₀
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a ha_cont L hL hholder F T hT x i j
  by_cases hT0 : T = 0
  · subst T
    simp
    positivity
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    let g : ℝ → ℝ := fun s =>
      ∫ y : E3, (a x-a (x-y)) *
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y)
    let H : ℝ → E3 → ℝ := fun r y =>
      (y i * y j / (4 * r ^ 2) - (if i = j then 1 / (2 * r) else 0)) *
        euclideanHeatKernel 3 r y
    let g₀ : ℝ → ℝ := fun s =>
      ∫ y : E3, (a x-a (x-y)) * H (T-s) y * F (s,x-y)
    let w : ℝ → ℝ := fun s => C₀ * L * ‖F‖ * (T-s) ^ (alpha / 2 - 1)
    have hconvolution_eq : ∀ s ∈ Ioc (0 : ℝ) T, s ≠ T →
        g s = g₀ s := by
      intro s hs hst
      have hts : 0 < T - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
      have hderiv : ∀ y : E3,
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) =
            H (T-s) y := by
        intro y
        simpa [H] using
          (euclideanHeatKernel_three_hessian_formula hts y i j)
      dsimp [g, g₀]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        change (a x-a (x-y)) *
            fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
              (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y) =
          (a x-a (x-y)) * H (T-s) y * F (s,x-y)
        rw [hderiv y])
    have hkernel_meas : Measurable (fun p : ℝ × E3 =>
        (a x-a (x-p.2)) * H (T-p.1) p.2 * F (p.1,x-p.2)) := by
      have mt : Measurable (fun p : ℝ × E3 => T-p.1) := measurable_const.sub measurable_fst
      have mc (k : Fin 3) : Measurable (fun p : ℝ × E3 => p.2 k) := by
        exact (show Continuous (fun p : ℝ × E3 => p.2 k) from by fun_prop).measurable
      have mk (k : Fin 3) : Measurable (fun p : ℝ × E3 =>
          gaussianHeatKernel (T-p.1) (p.2 k)) := by
        unfold gaussianHeatKernel
        exact ((measurable_const.mul mt).sqrt.inv).mul
          (((mc k).pow_const 2).neg.div (measurable_const.mul mt)).exp
      have mp : Measurable (fun p : ℝ × E3 => euclideanHeatKernel 3 (T-p.1) p.2) := by
        have hm := (mk 0).mul ((mk 1).mul (mk 2))
        change Measurable (fun p : ℝ × E3 => gaussianHeatKernel (T-p.1) (p.2 0) *
          (gaussianHeatKernel (T-p.1) (p.2 1) * gaussianHeatKernel (T-p.1) (p.2 2))) at hm
        simpa [euclideanHeatKernel, Fin.prod_univ_succ] using hm
      have md : Measurable (fun p : ℝ × E3 => if i=j then 1/(2*(T-p.1)) else 0) := by
        by_cases hij : i=j
        · simp only [if_pos hij]
          exact measurable_const.div (measurable_const.mul mt)
        · simp only [if_neg hij]
          exact measurable_const
      have ma : Measurable (fun p : ℝ × E3 =>
          p.2 i * p.2 j / (4*(T-p.1)^2) - (if i=j then 1/(2*(T-p.1)) else 0)) :=
        ((mc i).mul (mc j) |>.div (measurable_const.mul (mt.pow_const 2))).sub md
      have mf : Measurable (fun p : ℝ × E3 => F (p.1,x-p.2)) :=
        F.measurable.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
      have mcoef : Measurable (fun p : ℝ × E3 => a x-a (x-p.2)) :=
        measurable_const.sub (ha_cont.measurable.comp (measurable_const.sub measurable_snd))
      exact (mcoef.mul (ma.mul mp)).mul mf
    have hg₀_sm : StronglyMeasurable g₀ := by
      exact hkernel_meas.stronglyMeasurable.integral_prod_right' (ν := volume)
    have hga : g =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] g₀ := by
      refine (ae_restrict_iff' (μ := volume) (s := Ioc (0 : ℝ) T)
        (p := fun s : ℝ => g s = g₀ s) measurableSet_Ioc).2 ?_
      exact (volume.ae_ne T).mono (fun s hst hs => hconvolution_eq s hs hst)
    obtain ⟨hwt, hweq⟩ :=
      holderTimeKernel_integrable_integral (alpha := alpha) (T := T) ha
    have hwint : IntervalIntegrable w volume 0 T := by
      simpa [w] using hwt.const_mul (C₀ * L * ‖F‖)
    have hgbound : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) T →
        ‖g₀ s‖ ≤ w s := by
      filter_upwards [volume.ae_ne T] with s hst hs
      have hslt : s < T := lt_of_le_of_ne hs.2 hst
      have hFs : Continuous (fun y : E3 => F (s,y)) := by
        exact F.continuous.comp (continuous_const.prodMk continuous_id)
      let fs : E3 →ᵇ ℝ :=
        ⟨⟨fun y : E3 => F (s,y), hFs⟩, ⟨2 * ‖F‖, by
          intro u v
          exact F.dist_le_two_norm (s,u) (s,v)⟩⟩
      have hfs_norm : ‖fs‖ ≤ ‖F‖ := by
        apply (BoundedContinuousFunction.norm_le (f := fs) (norm_nonneg _)).2
        intro y
        change |F (s,y)| ≤ ‖F‖
        simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s,y)
      have hholder_s : ∀ u v : E3,
          |a u - a v| ≤ L * ‖u-v‖^alpha := by
        intro u v
        exact hholder u v
      obtain ⟨_, hb⟩ := hspatial a ha_cont L hL hholder_s fs
        (T-s) (sub_pos.mpr hslt) x i j
      change ‖g₀ s‖ ≤ w s
      rw [Real.norm_eq_abs, ← hconvolution_eq s hs hst]
      change |∫ y : E3, (a x-a (x-y)) *
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y)| ≤
        C₀ * L * ‖F‖ * (T-s) ^ (alpha / 2 - 1)
      calc
        |∫ y : E3, (a x-a (x-y)) *
            fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
              (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y)| =
            |∫ y : E3, (a x-a (x-y)) *
              fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
                (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * fs (x-y)| := by
                  rfl
        _ ≤ C₀ * L * ‖fs‖ * (T-s) ^ (alpha / 2 - 1) := hb
        _ ≤ C₀ * L * ‖F‖ * (T-s) ^ (alpha / 2 - 1) := by
          calc
            C₀ * L * ‖fs‖ * (T-s) ^ (alpha / 2 - 1) =
                (C₀ * L * (T-s) ^ (alpha / 2 - 1)) * ‖fs‖ := by ring
            _ ≤ (C₀ * L * (T-s) ^ (alpha / 2 - 1)) * ‖F‖ :=
              mul_le_mul_of_nonneg_left hfs_norm (by positivity)
            _ = C₀ * L * ‖F‖ * (T-s) ^ (alpha / 2 - 1) := by ring
    have hgbound' : (fun s => ‖g₀ s‖) ≤ᵐ[volume.restrict (uIoc 0 T)] w := by
      rw [uIoc_of_le hT]
      exact (ae_restrict_iff' measurableSet_Ioc).2 hgbound
    have hg₀int : IntervalIntegrable g₀ volume 0 T := by
      exact hwint.mono_fun' hg₀_sm.aestronglyMeasurable hgbound'
    have hga' : g =ᵐ[volume.restrict (uIoc (0 : ℝ) T)] g₀ := by
      rw [uIoc_of_le hT]
      exact hga
    have gint : IntervalIntegrable g volume 0 T :=
      hg₀int.congr_ae hga'.symm
    refine ⟨?_, ?_⟩
    · change IntervalIntegrable g volume 0 T
      exact gint
    · have hnorm := intervalIntegral.norm_integral_le_of_norm_le hT
        hgbound hwint
      have hconst : (∫ s in (0 : ℝ)..T, w s) =
          C₀ * L * ‖F‖ * ((2 / alpha) * T ^ (alpha / 2)) := by
        dsimp [w]
        rw [intervalIntegral.integral_const_mul, hweq]
      have hforward : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) T → g s = g₀ s :=
        (ae_restrict_iff' (μ := volume) (s := Ioc (0 : ℝ) T)
          (p := fun s : ℝ => g s = g₀ s) measurableSet_Ioc).1 hga
      have hreverse : ∀ᵐ s ∂volume, s ∈ Ioc T (0 : ℝ) → g s = g₀ s :=
        Eventually.of_forall (fun s hs => by
          exact (not_lt_of_ge hT (lt_of_lt_of_le hs.1 hs.2)).elim)
      have hIntEq : (∫ s in (0 : ℝ)..T, g s) =
          ∫ s in (0 : ℝ)..T, g₀ s :=
        intervalIntegral.integral_congr_ae' (μ := volume) (a := (0 : ℝ)) (b := T)
          (f := g) (g := g₀) hforward hreverse
      calc
        |∫ s in (0 : ℝ)..T, g s| = ‖∫ s in (0 : ℝ)..T, g s‖ := by rfl
        _ = ‖∫ s in (0 : ℝ)..T, g₀ s‖ := congrArg norm hIntEq
        _ ≤ ∫ s in (0 : ℝ)..T, w s := hnorm
        _ = C₀ * L * ‖F‖ * ((2 / alpha) * T ^ (alpha / 2)) := hconst
        _ = C * L * ‖F‖ * T ^ (alpha / 2) := by
          dsimp [C]
          ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
