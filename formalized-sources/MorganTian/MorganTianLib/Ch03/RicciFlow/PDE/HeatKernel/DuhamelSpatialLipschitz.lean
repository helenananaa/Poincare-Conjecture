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
/-- Spatial Lipschitz regularity of the actual Duhamel integral of bounded continuous forcing. -/
theorem duhamel_spatial_lipschitz : ∃ C : ℝ, 0 < C ∧
    ∀ (F : (ℝ × E3) →ᵇ ℝ) (T : ℝ), 0 ≤ T → ∀ x z : E3,
      |(∫ s in (0:ℝ)..T, ∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,x-y)) -
        (∫ s in (0:ℝ)..T, ∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,z-y))|
        ≤ C*‖F‖*Real.sqrt T*‖x-z‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₀, hC₀, htrans⟩ := euclideanHeatKernel_three_translation_L1
  let C : ℝ := 2 * C₀
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro F T hT x z
  by_cases hT0 : T = 0
  · subst T
    simp
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    let g : ℝ → ℝ := fun s =>
      (∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,x-y)) -
        (∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,z-y))
    have hxi := euclideanHeatKernel_three_bounded_duhamel F T hT x
    have hzi := euclideanHeatKernel_three_bounded_duhamel F T hT z
    have hgint : IntervalIntegrable g volume 0 T := by
      dsimp [g]
      exact hxi.1.sub hzi.1
    let w : ℝ → ℝ := fun s => (T-s) ^ (-(1 / 2 : ℝ))
    have hwint : IntervalIntegrable w volume 0 T := by
      have hp : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) volume 0 T :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      have hcomp := hp.comp_sub_left T
      have hcomp' := hcomp.symm
      simpa [w] using hcomp'
    have hw_integral : (∫ s in (0 : ℝ)..T, w s) = 2 * Real.sqrt T := by
      calc
        (∫ s in (0 : ℝ)..T, w s) =
            ∫ s in (0 : ℝ)..T, (T-s) ^ (-(1 / 2 : ℝ)) := by rfl
        _ = ∫ u in T-T..T-0, u ^ (-(1 / 2 : ℝ)) := by
          exact intervalIntegral.integral_comp_sub_left
            (f := fun u : ℝ => u ^ (-(1 / 2 : ℝ))) T
        _ = ∫ u in (0 : ℝ)..T, u ^ (-(1 / 2 : ℝ)) := by ring_nf
        _ = 2 * Real.sqrt T := by
          rw [integral_rpow (a := (0 : ℝ)) (b := T) (r := -(1 / 2 : ℝ))
            (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
          rw [Real.sqrt_eq_rpow]
          norm_num
          ring
    have hspace : ∀ s : ℝ, 0 < T-s →
        |(∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,x-y)) -
          (∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,z-y))| ≤
          ‖F‖ * (∫ y : E3, |euclideanHeatKernel 3 (T-s) (y+(x-z)) -
            euclideanHeatKernel 3 (T-s) y|) := by
      intro s hs
      let K : E3 → ℝ := euclideanHeatKernel 3 (T-s)
      have hKint : Integrable K volume := by
        simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 (T-s) hs |>.1
      have hKcomp (a : E3) : Integrable (fun y : E3 => K (a-y)) volume := by
        have hmap := (Measure.measurePreserving_sub_left (volume : Measure E3) a).integrable_comp_of_integrable
          hKint
        simpa [K, Function.comp_def] using hmap
      have hconv (a : E3) :
          Integrable (fun y : E3 => K (a-y) * F (s,y)) volume := by
        apply hKcomp a |>.mul_bdd (F.continuous.comp (by fun_prop)).aestronglyMeasurable
        exact Filter.Eventually.of_forall (fun y => F.norm_coe_le_norm (s,y))
      have hdiffK :
          Integrable (fun y : E3 => K (y+(x-z)) - K y) volume := by
        simpa [K] using (htrans (T-s) hs (x-z)).1
      have hdiffK_bound :
          (∫ y : E3, |K (y+(x-z)) - K y|) ≤
            min 2 (C₀ * ‖x-z‖ / Real.sqrt (T-s)) := by
        simpa [K] using (htrans (T-s) hs (x-z)).2
      let q : E3 → ℝ := fun y =>
        (K (y+(x-z)) - K y) * F (s,z-y)
      have hq : Integrable q volume := by
        apply hdiffK.mul_bdd
        · exact (F.continuous.comp (by fun_prop)).aestronglyMeasurable
        · exact Filter.Eventually.of_forall (fun y => F.norm_coe_le_norm (s,z-y))
      have hmajor : Integrable (fun y : E3 => ‖F‖ *
          |K (y+(x-z)) - K y|) volume := by
        simpa [Real.norm_eq_abs, mul_comm] using hdiffK.norm.const_mul ‖F‖
      have hq_bound : ∀ᵐ y : E3 ∂(volume : Measure E3),
          ‖q y‖ ≤ ‖F‖ * |K (y+(x-z)) - K y| := by
        filter_upwards [] with y
        dsimp [q]
        rw [abs_mul]
        calc
          |K (y+(x-z)) - K y| * |F (s,z-y)| ≤
              |K (y+(x-z)) - K y| * ‖F‖ :=
            mul_le_mul_of_nonneg_left (F.norm_coe_le_norm (s,z-y)) (abs_nonneg _)
          _ = ‖F‖ * |K (y+(x-z)) - K y| := by ring
      have hq_integral_bound : |∫ y : E3, q y| ≤ ‖F‖ *
          (∫ y : E3, |K (y+(x-z)) - K y|) := by
        have hh := norm_integral_le_of_norm_le hmajor hq_bound
        calc
          |∫ y : E3, q y| ≤ ∫ y : E3, ‖F‖ *
              |K (y+(x-z)) - K y| := by
            simpa [Real.norm_eq_abs] using hh
          _ = ‖F‖ * (∫ y : E3, |K (y+(x-z)) - K y|) := by
            rw [integral_const_mul]
      have htarget (a : E3) :
          (∫ y : E3, K y * F (s,a-y)) =
            ∫ y : E3, K (a-y) * F (s,y) := by
        let p : E3 → ℝ := fun y => K y * F (s,a-y)
        have hp : Integrable p volume := by
          apply hKint.mul_bdd
          · exact (F.continuous.comp (by fun_prop)).aestronglyMeasurable
          · exact Filter.Eventually.of_forall (fun y => F.norm_coe_le_norm (s,a-y))
        have hmap :=
          (Measure.measurePreserving_sub_left (volume : Measure E3) a).integral_comp
            (MeasurableEquiv.subLeft a).measurableEmbedding p
        calc
          (∫ y : E3, K y * F (s,a-y)) = ∫ y : E3, p y := by rfl
          _ = ∫ y : E3, p (a-y) := hmap.symm
          _ = ∫ y : E3, K (a-y) * F (s,y) := by
            congr 1
            funext y
            dsimp [p]
            rw [sub_sub_cancel]
      have hchange :
          (∫ y : E3, K (x-y) * F (s,y) - K (z-y) * F (s,y)) =
            ∫ y : E3, q y := by
        have hmap :=
          (Measure.measurePreserving_sub_left (volume : Measure E3) z).integral_comp
            (MeasurableEquiv.subLeft z).measurableEmbedding q
        calc
          (∫ y : E3, K (x-y) * F (s,y) - K (z-y) * F (s,y)) =
              ∫ y : E3, q (z-y) := by
            congr 1
            funext y
            dsimp [q]
            have hxy : (z-y) + (x-z) = x-y := by abel
            rw [hxy, sub_sub_cancel]
            ring
          _ = ∫ y : E3, q y := hmap
      rw [htarget x, htarget z, ← integral_sub (hconv x) (hconv z), hchange]
      exact hq_integral_bound
    have hpoint : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) T →
        ‖g s‖ ≤ C₀ * ‖F‖ * ‖x-z‖ * w s := by
      filter_upwards [volume.ae_ne T] with s hne hs
      have hslt : s < T := lt_of_le_of_ne hs.2 hne
      have hts : 0 < T-s := sub_pos.mpr hslt
      have hsp := hspace s hts
      have htrans' := (htrans (T-s) hts (x-z)).2.trans (min_le_right _ _)
      have hpow : w s = 1 / Real.sqrt (T-s) := by
        dsimp [w]
        rw [Real.rpow_neg (le_of_lt hts), ← Real.sqrt_eq_rpow]
        simp [one_div]
      rw [hpow]
      dsimp [g]
      calc
        |(∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,x-y)) -
            (∫ y : E3, euclideanHeatKernel 3 (T-s) y * F (s,z-y))| ≤
            ‖F‖ * (∫ y : E3, |euclideanHeatKernel 3 (T-s) (y+(x-z)) -
              euclideanHeatKernel 3 (T-s) y|) := hsp
        _ ≤ C₀ * ‖F‖ * ‖x-z‖ * (1 / Real.sqrt (T-s)) := by
          calc
            ‖F‖ * (∫ y : E3, |euclideanHeatKernel 3 (T-s) (y+(x-z)) -
                euclideanHeatKernel 3 (T-s) y|) ≤
                ‖F‖ * (C₀ * ‖x-z‖ / Real.sqrt (T-s)) :=
              mul_le_mul_of_nonneg_left htrans' (norm_nonneg _)
            _ = C₀ * ‖F‖ * ‖x-z‖ * (1 / Real.sqrt (T-s)) := by
              simp [div_eq_mul_inv]
              ring
    have houter :
        (∫ s in (0 : ℝ)..T, ∫ y : E3,
            euclideanHeatKernel 3 (T-s) y * F (s,x-y)) -
          (∫ s in (0 : ℝ)..T, ∫ y : E3,
            euclideanHeatKernel 3 (T-s) y * F (s,z-y)) =
          ∫ s in (0 : ℝ)..T, g s := by
      symm
      simpa [g] using intervalIntegral.integral_sub hxi.1 hzi.1
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hT hpoint
      (hwint.const_mul (C₀ * ‖F‖ * ‖x-z‖))
    rw [houter]
    calc
      |∫ s in (0 : ℝ)..T, g s| = ‖∫ s in (0 : ℝ)..T, g s‖ := by rfl
      _ ≤ ∫ s in (0 : ℝ)..T, C₀ * ‖F‖ * ‖x-z‖ * w s := hnorm
      _ = (C₀ * ‖F‖ * ‖x-z‖) * (∫ s in (0 : ℝ)..T, w s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = C * ‖F‖ * Real.sqrt T * ‖x-z‖ := by
        rw [hw_integral]
        dsimp [C]
        ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
