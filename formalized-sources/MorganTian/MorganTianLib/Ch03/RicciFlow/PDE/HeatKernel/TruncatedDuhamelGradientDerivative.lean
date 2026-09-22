import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.CompactSpatialDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatFirstFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction RealInnerProductSpace
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Differentiate the truncated gradient integral to obtain the actual Hessian integral. -/
theorem truncated_duhamel_gradient_derivative (F : (ℝ × E3) →ᵇ ℝ) (T eps : ℝ)
    (heps : 0<eps) (hT : eps≤T) (x : E3) (i : Fin 3) :
    HasFDerivAt (fun z : E3 => ∫ s in (0:ℝ)..(T-eps), ∫ y : E3,
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) (z-y) (EuclideanSpace.single i 1)*F (s,y))
      (∑ j : Fin 3, (∫ s in (0:ℝ)..(T-eps), ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y)) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)) x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hTpos : 0 < T := lt_of_lt_of_le heps hT
  let b : ℝ := T - eps
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith
  let R : ℝ := ‖x‖ + 1
  obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
    compact_time_spatial_derivative_dominator eps T R heps hT (by
      dsimp [R]
      positivity)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hR_ball (z : E3) (hz : z ∈ Metric.ball x 1) : ‖z‖ ≤ R := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    dsimp [R]
    have hzx : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      calc
        ‖z‖ = ‖(z - x) + x‖ := by congr 1 <;> abel
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    exact hzx.trans (by linarith)
  let fs : ℝ → E3 →ᵇ ℝ := fun s =>
    ⟨⟨fun y : E3 => F (s, y),
      F.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      ⟨2 * ‖F‖, by
        intro u v
        rw [Real.dist_eq]
        calc
          |F (s, u) - F (s, v)| ≤ |F (s, u)| + |F (s, v)| := abs_sub _ _
          _ ≤ ‖F‖ + ‖F‖ := add_le_add
            (by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, u))
            (by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, v))
          _ = 2 * ‖F‖ := by ring⟩⟩
  have hfs_norm (s : ℝ) : ‖fs s‖ ≤ ‖F‖ := by
    apply (BoundedContinuousFunction.norm_le (f := fs s) (norm_nonneg _)).2
    intro y
    change |F (s, y)| ≤ ‖F‖
    simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, y)
  let A : E3 → ℝ → ℝ := fun z s =>
    ∫ y : E3, fderiv ℝ (euclideanHeatKernel 3 (T-s)) (z-y)
      (EuclideanSpace.single i 1) * F (s, y)
  let A' : E3 → ℝ → E3 →L[ℝ] ℝ := fun z s =>
    ∑ j : Fin 3, (∫ y : E3, fderiv ℝ (fun q : E3 =>
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) q (EuclideanSpace.single i 1))
        (z-y) (EuclideanSpace.single j 1) * F (s, y)) •
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)
  let A₀ : E3 → ℝ → ℝ := fun z s =>
    ∫ y : E3, (-(z-y : E3) i / (2 * (T-s))) *
      euclideanHeatKernel 3 (T-s) (z-y) * F (s, y)
  let H₀ : E3 → ℝ → Fin 3 → E3 →L[ℝ] ℝ := fun z s j =>
    (∫ y : E3, ((z-y : E3) i * (z-y : E3) j /
        (4 * (T-s)^2) - (if i = j then 1 / (2 * (T-s)) else 0)) *
      euclideanHeatKernel 3 (T-s) (z-y) * F (s, y)) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)
  let A₀' : E3 → ℝ → E3 →L[ℝ] ℝ := fun z s =>
    ∑ j : Fin 3, H₀ z s j
  have hkernel_meas (z : E3) : Measurable (fun p : ℝ × E3 =>
      euclideanHeatKernel 3 (T-p.1) (z-p.2)) := by
    have mt : Measurable (fun p : ℝ × E3 => T-p.1) :=
      measurable_const.sub measurable_fst
    have mc (k : Fin 3) : Measurable (fun p : ℝ × E3 => (z-p.2) k) := by
      exact (show Continuous (fun p : ℝ × E3 => (z-p.2) k) by fun_prop).measurable
    have mk (k : Fin 3) : Measurable (fun p : ℝ × E3 =>
        gaussianHeatKernel (T-p.1) ((z-p.2) k)) := by
      unfold gaussianHeatKernel
      exact ((measurable_const.mul mt).sqrt.inv).mul
        (((mc k).pow_const 2).neg.div (measurable_const.mul mt)).exp
    have hm := (mk 0).mul ((mk 1).mul (mk 2))
    change Measurable (fun p : ℝ × E3 => gaussianHeatKernel (T-p.1) ((z-p.2) 0) *
      (gaussianHeatKernel (T-p.1) ((z-p.2) 1) *
        gaussianHeatKernel (T-p.1) ((z-p.2) 2))) at hm
    simpa [euclideanHeatKernel, Fin.prod_univ_succ] using hm
  have hF_meas (z : E3) : Measurable (fun p : ℝ × E3 => F (p.1, p.2)) := by
    exact F.measurable.comp (measurable_fst.prodMk measurable_snd)
  have hgrad_meas (z : E3) : Measurable (fun p : ℝ × E3 =>
      (-(z-p.2 : E3) i / (2 * (T-p.1))) *
        euclideanHeatKernel 3 (T-p.1) (z-p.2) * F (p.1, p.2)) := by
    have mt : Measurable (fun p : ℝ × E3 => T-p.1) :=
      measurable_const.sub measurable_fst
    have mc (k : Fin 3) : Measurable (fun p : ℝ × E3 => (z-p.2) k) := by
      exact (show Continuous (fun p : ℝ × E3 => (z-p.2) k) by fun_prop).measurable
    have hcoef : Measurable (fun p : ℝ × E3 =>
        -(z-p.2 : E3) i / (2 * (T-p.1))) := by
      exact (mc i).neg.div (measurable_const.mul mt)
    exact (hcoef.mul (hkernel_meas z)).mul (hF_meas z)
  have hhess_meas (z : E3) (j : Fin 3) : Measurable (fun p : ℝ × E3 =>
      (((z-p.2 : E3) i * (z-p.2 : E3) j /
        (4 * (T-p.1)^2) - (if i = j then 1 / (2 * (T-p.1)) else 0)) *
          euclideanHeatKernel 3 (T-p.1) (z-p.2) * F (p.1, p.2))) := by
    have mt : Measurable (fun p : ℝ × E3 => T-p.1) :=
      measurable_const.sub measurable_fst
    have mc (k : Fin 3) : Measurable (fun p : ℝ × E3 => (z-p.2) k) := by
      exact (show Continuous (fun p : ℝ × E3 => (z-p.2) k) by fun_prop).measurable
    have hdiag : Measurable (fun p : ℝ × E3 =>
        if i = j then 1 / (2 * (T-p.1)) else 0) := by
      by_cases hij : i = j
      · simp only [if_pos hij]
        exact measurable_const.div (measurable_const.mul mt)
      · simp only [if_neg hij]
        exact measurable_const
    have hcoef : Measurable (fun p : ℝ × E3 =>
        (z-p.2 : E3) i * (z-p.2 : E3) j /
          (4 * (T-p.1)^2) - (if i = j then 1 / (2 * (T-p.1)) else 0)) :=
      ((mc i).mul (mc j)).div (measurable_const.mul (mt.pow_const 2)) |>.sub hdiag
    exact (hcoef.mul (hkernel_meas z)).mul (hF_meas z)
  have hA₀_sm (z : E3) : StronglyMeasurable (A₀ z) := by
    exact (hgrad_meas z).stronglyMeasurable.integral_prod_right' (ν := volume)
  have hH₀_sm (z : E3) (j : Fin 3) :
      StronglyMeasurable (fun s =>
        ∫ y : E3, (((z-y : E3) i * (z-y : E3) j /
          (4 * (T-s)^2) - (if i = j then 1 / (2 * (T-s)) else 0)) *
            euclideanHeatKernel 3 (T-s) (z-y) * F (s, y))) := by
    exact (hhess_meas z j).stronglyMeasurable.integral_prod_right' (ν := volume)
  have hA_eq (z : E3) : ∀ᵐ s ∂volume.restrict (uIoc (0 : ℝ) b),
      A z s = A₀ z s := by
    rw [uIoc_of_le hb]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ ?_)
    intro s hs
    have hts : 0 < T-s := by
      have : eps ≤ T-s := by
        dsimp [b] at hs
        linarith [hs.2]
      exact lt_of_lt_of_le heps this
    dsimp [A, A₀]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by
      change fderiv ℝ (euclideanHeatKernel 3 (T-s)) (z-y)
          (EuclideanSpace.single i 1) * F (s, y) = _
      rw [euclideanHeatKernel_three_gradient_formula hts (z-y) i]
      simp only [PiLp.sub_apply]
      ring)
  have hH_eq (z : E3) (j : Fin 3) : ∀ᵐ s ∂volume.restrict (uIoc (0 : ℝ) b),
      (∫ y : E3, fderiv ℝ (fun q : E3 =>
        fderiv ℝ (euclideanHeatKernel 3 (T-s)) q (EuclideanSpace.single i 1))
          (z-y) (EuclideanSpace.single j 1) * F (s, y)) =
        ∫ y : E3, (((z-y : E3) i * (z-y : E3) j /
          (4 * (T-s)^2) - (if i = j then 1 / (2 * (T-s)) else 0)) *
            euclideanHeatKernel 3 (T-s) (z-y) * F (s, y)) := by
    rw [uIoc_of_le hb]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ ?_)
    intro s hs
    have hts : 0 < T-s := by
      have : eps ≤ T-s := by
        dsimp [b] at hs
        linarith [hs.2]
      exact lt_of_lt_of_le heps this
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by
      change fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
          (EuclideanSpace.single i 1)) (z-y) (EuclideanSpace.single j 1) *
          F (s, y) = _
      rw [euclideanHeatKernel_three_hessian_formula hts (z-y) i j])
  have hA_bound (s : ℝ) (z : E3) (hs : s ∈ Ioc (0 : ℝ) b)
      (hz : z ∈ Metric.ball x 1) : ‖A z s‖ ≤ ‖F‖ * (∫ y : E3, g y) := by
    have htIcc : T-s ∈ Icc eps T := by
      constructor
      · dsimp [b] at hs
        calc
          eps = T - (T - eps) := by ring
          _ ≤ T - s := sub_le_sub_left hs.2 T
      · exact sub_le_self T hs.1.le
    have hmajor : Integrable (fun y : E3 => ‖F‖ * g y) volume :=
      hg.const_mul ‖F‖
    have hnorm := norm_integral_le_of_norm_le hmajor (by
      filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_mul]
      have hderiv := (hdom (T-s) htIcc z y (hR_ball z hz)).2.1 i
      calc
        |fderiv ℝ (euclideanHeatKernel 3 (T-s)) (z-y)
            (EuclideanSpace.single i 1)| * |F (s, y)| ≤ g y * ‖F‖ :=
          mul_le_mul hderiv (by
            simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, y))
            (abs_nonneg _) (hg_nonneg y)
        _ = ‖F‖ * g y := by ring)
    dsimp [A] at hnorm ⊢
    calc
      ‖∫ (y : E3), (fderiv ℝ (euclideanHeatKernel 3 (T-s)) (z-y))
          (EuclideanSpace.single i 1) * F (s, y)‖ ≤
          ∫ y : E3, ‖F‖ * g y := hnorm
      _ = ‖F‖ * (∫ y : E3, g y) := by
        rw [integral_const_mul]
  have hH_bound (s : ℝ) (z : E3) (j : Fin 3) (hs : s ∈ Ioc (0 : ℝ) b)
      (hz : z ∈ Metric.ball x 1) :
      |∫ y : E3, fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
        (EuclideanSpace.single i 1)) (z-y) (EuclideanSpace.single j 1) * F (s, y)| ≤
        ‖F‖ * (∫ y : E3, g y) := by
    have htIcc : T-s ∈ Icc eps T := by
      constructor
      · dsimp [b] at hs
        calc
          eps = T - (T - eps) := by ring
          _ ≤ T - s := sub_le_sub_left hs.2 T
      · exact sub_le_self T hs.1.le
    have hmajor : Integrable (fun y : E3 => ‖F‖ * g y) volume :=
      hg.const_mul ‖F‖
    have hnorm := norm_integral_le_of_norm_le hmajor (by
      filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_mul]
      have hderiv := (hdom (T-s) htIcc z y (hR_ball z hz)).2.2 i j
      calc
        |fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
            (EuclideanSpace.single i 1)) (z-y) (EuclideanSpace.single j 1)| *
              |F (s, y)| ≤ g y * ‖F‖ :=
          mul_le_mul hderiv (by
            simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s, y))
            (abs_nonneg _) (hg_nonneg y)
        _ = ‖F‖ * g y := by ring)
    calc
      |∫ y : E3, (fderiv ℝ (fun q : E3 => fderiv ℝ
          (euclideanHeatKernel 3 (T-s)) q (EuclideanSpace.single i 1)) (z-y)
            (EuclideanSpace.single j 1) * F (s, y))| ≤
          ∫ y : E3, ‖F‖ * g y := by
            simpa [Real.norm_eq_abs] using hnorm
      _ = ‖F‖ * (∫ y : E3, g y) := by
        rw [integral_const_mul]
  have hC0 : 0 ≤ ‖F‖ * (∫ y : E3, g y) := by
    exact mul_nonneg (norm_nonneg _) (integral_nonneg hg_nonneg)
  have hLdecomp (L : E3 →L[ℝ] ℝ) :
      L = ∑ j : Fin 3, (L (EuclideanSpace.single j 1)) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) := by
    ext v
    have hv : v = ∑ j : Fin 3, v j • EuclideanSpace.single j 1 := by
      apply PiLp.ext
      intro k
      simp [Pi.single_apply]
    calc
      L v = L (∑ j : Fin 3, v j • EuclideanSpace.single j 1) := by rw [← hv]
      _ = ∑ j : Fin 3, v j • L (EuclideanSpace.single j 1) := by
        simp only [map_sum, map_smul]
      _ = ∑ j : Fin 3, (L (EuclideanSpace.single j 1)) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) v := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [PiLp.proj_apply]
        simp [smul_eq_mul, mul_comm]
  have hA'_bound (s : ℝ) (z : E3) (hs : s ∈ Ioc (0 : ℝ) b)
      (hz : z ∈ Metric.ball x 1) : ‖A' z s‖ ≤ 3 * (‖F‖ * (∫ y : E3, g y)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [hLdecomp (A' z s)]
    calc
      ‖∑ j : Fin 3,
          (A' z s (EuclideanSpace.single j 1)) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) v‖ ≤
          ∑ j : Fin 3, ‖(A' z s (EuclideanSpace.single j 1)) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) v‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, (‖F‖ * (∫ y : E3, g y)) * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, PiLp.proj_apply]
        have hjbound : |A' z s (EuclideanSpace.single j 1)| ≤
            ‖F‖ * (∫ y : E3, g y) := by
          change |∑ k : Fin 3, (∫ y : E3, fderiv ℝ (fun q : E3 =>
            fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
              (EuclideanSpace.single i 1)) (z-y) (EuclideanSpace.single k 1) *
              F (s, y)) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k)
              (EuclideanSpace.single j 1)| ≤ ‖F‖ * (∫ y : E3, g y)
          simpa [PiLp.proj_apply] using hH_bound s z j hs hz
        exact mul_le_mul hjbound (by
          simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v j))
          (abs_nonneg _) hC0
      _ = 3 * (‖F‖ * (∫ y : E3, g y)) * ‖v‖ := by simp; ring
  have hA'_meas : AEStronglyMeasurable (A' x) (volume.restrict (uIoc (0 : ℝ) b)) := by
    have hsum : StronglyMeasurable (A₀' x) := by
      dsimp [A₀']
      apply Finset.stronglyMeasurable_fun_sum
      intro j hj
      dsimp [H₀]
      exact (hH₀_sm x j).smul_const _
    have heqs : ∀ᵐ s ∂volume.restrict (uIoc (0:ℝ) b), ∀ j : Fin 3,
        (∫ y : E3, fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s,y)) =
        (∫ y : E3, (((x-y : E3) i * (x-y : E3) j / (4*(T-s)^2) -
          (if i=j then 1/(2*(T-s)) else 0)) * euclideanHeatKernel 3 (T-s) (x-y) * F (s,y))) :=
      ae_all_iff.mpr (fun j => hH_eq x j)
    apply (hsum.aestronglyMeasurable : AEStronglyMeasurable (A₀' x)
      (volume.restrict (uIoc (0:ℝ) b))).congr
    filter_upwards [heqs] with s hs
    dsimp [A', A₀']
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [H₀]
    rw [hs j]
    simp only [PiLp.sub_apply]
  have hA_meas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (A z) (volume.restrict (uIoc (0 : ℝ) b)) := by
    filter_upwards [] with z
    have hm : AEStronglyMeasurable (A₀ z) (volume.restrict (uIoc (0:ℝ) b)) :=
      (hA₀_sm z).aestronglyMeasurable
    have heq : A₀ z =ᵐ[volume.restrict (uIoc (0 : ℝ) b)] A z :=
      (hA_eq z).mono (fun s h => h.symm)
    exact hm.congr heq
  have hA_int : IntervalIntegrable (A x) volume 0 b := by
    have hc : IntervalIntegrable (fun _ : ℝ => ‖F‖ * (∫ y : E3, g y)) volume 0 b :=
      intervalIntegrable_const
    apply hc.mono_fun' (by
      simpa [uIoc_of_le hb] using (show AEStronglyMeasurable (A x)
        (volume.restrict (uIoc (0 : ℝ) b)) from
        (hA₀_sm x).aestronglyMeasurable.restrict.congr
          (show A₀ x =ᵐ[volume.restrict (uIoc (0 : ℝ) b)] A x from
            (hA_eq x).mono (fun s h => h.symm))))
    rw [uIoc_of_le hb]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ ?_)
    intro s hs
    exact hA_bound s x hs (Metric.mem_ball_self one_pos)
  have hbound_int : IntervalIntegrable
      (fun _ : ℝ => 3 * (‖F‖ * (∫ y : E3, g y))) volume 0 b :=
    intervalIntegrable_const
  have hdiff : ∀ᵐ s ∂volume.restrict (uIoc (0 : ℝ) b), ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (A · s) (A' z s) z := by
    rw [uIoc_of_le hb]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ ?_)
    intro s hs z hz
    have hts : 0 < T-s := by
      have : eps ≤ T-s := by
        dsimp [b] at hs
        linarith [hs.2]
      exact lt_of_lt_of_le heps this
    simpa [A, A', fs] using (bounded_heat_gradient_fderiv (fs s) hts z i)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (μ := (volume : Measure ℝ)) (F := A) (F' := A') (x₀ := x) (s := Metric.ball x 1)
      (a := (0 : ℝ)) (b := b)
      (bound := fun _ : ℝ => 3 * (‖F‖ * (∫ y : E3, g y)))
      (Metric.ball_mem_nhds x one_pos) hA_meas hA_int hA'_meas
      (by
        rw [uIoc_of_le hb]
        exact (ae_restrict_iff' measurableSet_Ioc).2
          (ae_of_all _ fun s hs z hz => hA'_bound s z hs hz))
      hbound_int
      hdiff
  have hcoeff_int (j : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      ∫ y : E3, fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s, y))
      volume 0 b := by
    have hc : IntervalIntegrable (fun _ : ℝ => ‖F‖ * (∫ y : E3, g y)) volume 0 b :=
      intervalIntegrable_const
    have hmeas : AEStronglyMeasurable (fun s : ℝ =>
        ∫ y : E3, fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s, y))
        (volume.restrict (uIoc (0 : ℝ) b)) := by
      have heq : (fun s : ℝ =>
          ∫ y : E3, (((x-y : E3) i * (x-y : E3) j /
            (4 * (T-s)^2) - (if i = j then 1 / (2 * (T-s)) else 0)) *
              euclideanHeatKernel 3 (T-s) (x-y) * F (s, y))) =ᵐ[
          volume.restrict (uIoc (0 : ℝ) b)] (fun s : ℝ =>
          ∫ y : E3, fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
            (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s, y)) :=
        (hH_eq x j).mono (fun s h => h.symm)
      exact (hH₀_sm x j).aestronglyMeasurable.restrict.congr heq
    apply hc.mono_fun' hmeas
    rw [uIoc_of_le hb]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ ?_)
    intro s hs
    exact hH_bound s x j hs (Metric.mem_ball_self one_pos)
  have hIntegral_expand : (∫ s in (0 : ℝ)..b, A' x s) =
      ∑ j : Fin 3, (∫ s in (0 : ℝ)..b,
        ∫ y : E3, fderiv ℝ (fun q : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s, y)) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) := by
    rw [show (fun s : ℝ => A' x s) = (fun s : ℝ =>
        ∑ j : Fin 3, (∫ y : E3, fderiv ℝ (fun q : E3 =>
          fderiv ℝ (euclideanHeatKernel 3 (T-s)) q
            (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s, y)) •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)) by
      funext s
      rfl]
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_smul_const]
    · intro j hj
      exact ⟨(hcoeff_int j).1.smul_const _, (hcoeff_int j).2.smul_const _⟩
  rw [hIntegral_expand] at hmain
  simpa [A, b] using hmain
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
