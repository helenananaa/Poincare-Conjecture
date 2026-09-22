import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideTranslationL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedClassicalIVP
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatTimeEquation
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- An L1 estimate for the actual heat kernel at two positive times. -/
theorem heat_kernel_time_difference_L1 : ∃ C : ℝ, 0 < C ∧
    ∀ s t : ℝ, 0 < s → s ≤ t →
      Integrable (fun y : E3 => euclideanHeatKernel 3 t y-euclideanHeatKernel 3 s y) volume ∧
      (∫ y : E3, |euclideanHeatKernel 3 t y-euclideanHeatKernel 3 s y|) ≤
        min 2 (C*(t-s)/s) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, htime⟩ := euclideanHeatKernel_three_time_derivative_L1
  refine ⟨C, hC, ?_⟩
  intro s t hs hst
  let K : ℝ → E3 → ℝ := fun r y => euclideanHeatKernel 3 r y
  obtain ⟨hKs, hKsmass⟩ := (euclideanHeatKernel_mass_semigroup 3).1 s hs
  have ht : 0 < t := lt_of_lt_of_le hs hst
  obtain ⟨hKt, hKtmass⟩ := (euclideanHeatKernel_mass_semigroup 3).1 t ht
  have hdiff : Integrable (fun y : E3 => K t y - K s y) volume := by
    have hKt' : Integrable (K t) volume := by simpa [K] using hKt
    have hKs' : Integrable (K s) volume := by simpa [K] using hKs
    exact hKt'.sub hKs'
  have hmass : (∫ y : E3, |K t y - K s y|) ≤ 2 := by
    have habs : Integrable (fun y : E3 => |K t y - K s y|) volume := by
      simpa [Real.norm_eq_abs] using hdiff.norm
    have hKt' : Integrable (K t) volume := by simpa [K] using hKt
    have hKs' : Integrable (K s) volume := by simpa [K] using hKs
    have hsum : Integrable (fun y : E3 => K t y + K s y) volume := hKt'.add hKs'
    have hpoint (y : E3) : |K t y - K s y| ≤ K t y + K s y := by
      calc
        |K t y - K s y| ≤ |K t y| + |K s y| := abs_sub _ _
        _ = K t y + K s y := by
          rw [abs_of_pos (euclideanHeatKernel_pos 3 ht y),
            abs_of_pos (euclideanHeatKernel_pos 3 hs y)]
    have hi := integral_mono habs hsum hpoint
    rw [integral_add (by simpa [K] using hKt) (by simpa [K] using hKs),
      hKtmass, hKsmass] at hi
    norm_num at hi
    exact hi
  by_cases heq : s = t
  · subst t
    simp
  ·
    obtain ⟨g, hg, hg_nonneg, hdom⟩ :=
      euclideanHeatKernel_time_derivative_dominator s t 0 hs hst (by norm_num)
    let G : E3 → ℝ := fun y => g (-y)
    have hG : Integrable G volume := by
      have h := (Measure.measurePreserving_neg (volume : Measure E3)).integrable_comp_of_integrable hg
      simpa [G, Function.comp_def] using h
    have hG_nonneg : ∀ y, 0 ≤ G y := by
      intro y
      exact hg_nonneg (-y)
    let D : ℝ × E3 → ℝ := fun p =>
      (‖p.2‖ ^ 2 / (4 * p.1 ^ 2) - 3 / (2 * p.1)) * K p.1 p.2
    let F : ℝ → E3 → ℝ := fun r y => |D (r, y)|
    have hDcont : ContinuousOn D (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
      have hKcont : ContinuousOn (fun p : ℝ × E3 => K p.1 p.2)
          (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
        simpa [K] using (euclideanHeatKernel_joint_smooth 3).continuousOn
      have hA : ContinuousOn
          (fun p : ℝ × E3 => ‖p.2‖ ^ 2 / (4 * p.1 ^ 2))
          (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro p hp
          have hp0 : 0 < p.1 := hp.1
          positivity
      have hB : ContinuousOn
          (fun p : ℝ × E3 => 3 / (2 * p.1))
          (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro p hp
          have hp0 : 0 < p.1 := hp.1
          positivity
      exact (hA.sub hB).mul hKcont
    have hFcont : ContinuousOn F.uncurry (Ioc s t ×ˢ (univ : Set E3)) := by
      have hsub : Ioc s t ×ˢ (univ : Set E3) ⊆
          Ioi (0 : ℝ) ×ˢ (univ : Set E3) := by
        intro p hp
        exact ⟨lt_of_lt_of_le hs (le_of_lt hp.1.1), hp.2⟩
      change ContinuousOn (fun p : ℝ × E3 => |D p|)
        (Ioc s t ×ˢ (univ : Set E3))
      exact (hDcont.mono hsub).abs
    have hFmeas : AEStronglyMeasurable F.uncurry
        ((volume.restrict (Ioc s t)).prod (volume : Measure E3)) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hFcont.aestronglyMeasurable
        (measurableSet_Ioc.prod MeasurableSet.univ)
    have hD_formula (r : ℝ) (hr : 0 < r) (y : E3) :
        deriv (fun q => K q y) r = D (r, y) := by
      simpa [D, K] using (euclideanHeatKernel_three_time_formula hr y).deriv
    have hFslice (r : ℝ) (hrpos : 0 < r) :
        Integrable (fun y : E3 => F r y) volume := by
      have h := (htime r hrpos).1.norm
      have heq : (fun y : E3 => F r y) =
          (fun y : E3 => |deriv (fun q => K q y) r|) := by
        funext y
        dsimp [F]
        rw [hD_formula r hrpos y]
      rw [heq]
      simpa only [Real.norm_eq_abs] using h
    have hFdom (r : ℝ) (hr : r ∈ Icc s t) (y : E3) :
        F r y ≤ G y := by
      have hd : |deriv (fun q => K q y) r| ≤ G y := by
        simpa [G, K] using
          (hdom r (0 : E3) (-y) hr (by norm_num)).2
      rw [hD_formula r (lt_of_lt_of_le hs hr.1) y] at hd
      simpa [F] using hd
    have hinner_bound (r : ℝ) (hr : r ∈ Icc s t) :
        (∫ y : E3, F r y) ≤ C / s := by
      have hrpos : 0 < r := lt_of_lt_of_le hs hr.1
      have h := (htime r hrpos).2
      have heq : (fun y : E3 => F r y) =
          (fun y : E3 => |deriv (fun q => K q y) r|) := by
        funext y
        dsimp [F]
        rw [hD_formula r hrpos y]
      rw [heq]
      calc
        (∫ y : E3, |deriv (fun q => K q y) r|) ≤ C / r := h
        _ ≤ C / s := by
          have hone : 1 / r ≤ (1 / s : ℝ) :=
            one_div_le_one_div_of_le hs hr.1
          calc
            C / r = C * (1 / r) := by ring
            _ ≤ C * (1 / s) := mul_le_mul_of_nonneg_left hone hC.le
            _ = C / s := by ring
    have hinner_int : Integrable
        (fun r : ℝ => ∫ y : E3, ‖F.uncurry (r, y)‖)
        (volume.restrict (Ioc s t)) := by
      have hmeas := hFmeas.norm.integral_prod_right'
      let M : ℝ := ∫ y : E3, G y
      have hconst : Integrable (fun _ : ℝ => M)
          (volume.restrict (Ioc s t)) := by
        exact (integrableOn_const (μ := volume) (s := Ioc s t)
          (C := M) (by simp)).integrable
      apply hconst.mono hmeas
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hrpos : 0 < r := lt_of_lt_of_le hs (le_of_lt hr.1)
      have hi := integral_mono (hFslice r hrpos) hG
        (hFdom r (Ioc_subset_Icc_self hr))
      have hI : 0 ≤ ∫ y : E3, |D (r, y)| := by
        apply integral_nonneg_of_ae
        filter_upwards [] with y
        exact abs_nonneg _
      have hGint : 0 ≤ ∫ y : E3, G y := by
        exact integral_nonneg_of_ae (Filter.Eventually.of_forall hG_nonneg)
      have hi' : abs (∫ y : E3, |D (r, y)|) ≤ abs (∫ y : E3, G y) := by
        rw [abs_of_nonneg hI, abs_of_nonneg hGint]
        exact hi
      have hi'' : abs (∫ y : E3, |D (r, y)|) ≤ abs M := by
        simpa [M] using hi'
      simpa [F, Real.norm_eq_abs, M] using hi''
    have hFprod : Integrable F.uncurry
        ((volume.restrict (Ioc s t)).prod (volume : Measure E3)) := by
      apply (integrable_prod_iff hFmeas).2
      refine ⟨?_, hinner_int⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFslice r (lt_of_lt_of_le hs (le_of_lt hr.1))
    have hFinner_int : IntervalIntegrable
        (fun r : ℝ => ∫ y : E3, F r y) volume s t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
      change Integrable (fun r : ℝ => ∫ y : E3, F r y)
        (volume.restrict (Ioc s t))
      have h := hFprod.integral_norm_prod_left
      simpa [F, Real.norm_eq_abs] using h
    have hFinner_y : Integrable
        (fun y : E3 => ∫ r in s..t, F r y) volume := by
      have h := hFprod.swap.integral_norm_prod_left
      simpa [intervalIntegral.integral_of_le hst, F, Real.norm_eq_abs,
        abs_nonneg, Function.comp_def] using h
    have hFswap :
        (∫ y : E3, ∫ r in s..t, F r y) =
          ∫ r in s..t, ∫ y : E3, F r y := by
      symm
      apply intervalIntegral_integral_swap
      rw [uIoc_of_le hst]
      exact hFprod
    have hDint (y : E3) : IntervalIntegrable
        (fun r : ℝ => D (r, y)) volume s t := by
      have hline : ContinuousOn (fun r : ℝ => (r, y)) (Icc s t) := by
        fun_prop
      have hmap : MapsTo (fun r : ℝ => (r, y)) (Icc s t)
          (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
        intro r hr
        exact ⟨lt_of_lt_of_le hs hr.1, mem_univ _⟩
      have h := hDcont.comp hline hmap
      have hi : IntervalIntegrable (D ∘ (fun r : ℝ => (r, y)))
          (volume : Measure ℝ) s t := h.intervalIntegrable_of_Icc hst
      exact hi.congr (fun r hr => rfl)
    have hpoint (y : E3) :
        |K t y - K s y| ≤ ∫ r in s..t, F r y := by
      have hcont : ContinuousOn (fun r : ℝ => K r y) (Icc s t) := by
        have h := (euclideanHeatKernel_joint_smooth 3).continuousOn
        have hline : ContinuousOn (fun r : ℝ => (r, y)) (Icc s t) := by
          fun_prop
        have hmap : MapsTo (fun r : ℝ => (r, y)) (Icc s t)
            (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) := by
          intro r hr
          exact ⟨lt_of_lt_of_le hs hr.1, mem_univ _⟩
        have hc := h.comp hline hmap
        change ContinuousOn ((fun p : ℝ × E3 =>
          euclideanHeatKernel 3 p.1 p.2) ∘ (fun r : ℝ => (r, y))) (Icc s t)
        exact hc
      have hderiv : ∀ r ∈ Ioo s t,
          HasDerivAt (fun q => K q y) (D (r, y)) r := by
        intro r hr
        simpa [D, K] using
          euclideanHeatKernel_three_time_formula (lt_of_lt_of_le hs hr.1.le) y
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        hst hcont hderiv (hDint y)
      calc
        |K t y - K s y| = |∫ r in s..t, D (r, y)| := by rw [hFTC]
        _ ≤ ∫ r in s..t, |D (r, y)| :=
          intervalIntegral.abs_integral_le_integral_abs hst
        _ = ∫ r in s..t, F r y := by
          apply intervalIntegral.integral_congr
          intro r hr
          rfl
    have hlinear : (∫ y : E3, |K t y - K s y|) ≤ C * (t - s) / s := by
      have hi := integral_mono
        (by simpa [Real.norm_eq_abs] using hdiff.norm) hFinner_y hpoint
      rw [hFswap] at hi
      have hconst : IntervalIntegrable (fun _ : ℝ => C / s) volume s t := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
        exact (integrableOn_const (μ := volume) (s := Ioc s t)
          (C := C / s) (by simp)).integrable
      have hrate := intervalIntegral.integral_mono_on hst hFinner_int hconst
        hinner_bound
      calc
        (∫ y : E3, |K t y - K s y|) ≤ ∫ r in s..t, ∫ y : E3, F r y := hi
        _ ≤ ∫ r in s..t, C / s := hrate
        _ = C * (t - s) / s := by
          rw [intervalIntegral.integral_const]
          ring
    refine ⟨?_, ?_⟩
    · simpa only [K] using hdiff
    · simpa only [K] using le_min hmass hlinear
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
