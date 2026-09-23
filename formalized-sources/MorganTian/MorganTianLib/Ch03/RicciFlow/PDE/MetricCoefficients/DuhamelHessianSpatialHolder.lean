import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.IntegratedSchauderModulus
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.HeatHessianSchauderModulus
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SchauderTimeSplit
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** duhamel hessian spatial holder. -/
theorem duhamel_hessian_spatial_holder 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ), 0 ≤ L → 0 ≤ T →
      (∀ s ∈ Icc (0:ℝ) T, ∀ x z : E3, |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) →
      ∀ (x z : E3) (i j : Fin 3),
        |(∫ s in (0:ℝ)..T, ∫ y : E3, heatHessian3 (T-s) i j y*F (s,x-y))-
         (∫ s in (0:ℝ)..T, ∫ y : E3, heatHessian3 (T-s) i j y*F (s,z-y))| ≤
          C*L*‖x-z‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₀, hC₀, hheat⟩ := heat_hessian_schauder_modulus alpha ha ha1
  obtain ⟨_, _, hduhamel⟩ :=
    MorganTianLib.ParabolicPDE.euclideanHeatKernel_three_duhamel_hessian_control
      alpha ha ha1
  let C : ℝ := C₀ * (2 / alpha + 2 / (1 - alpha))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro F L T hL hT hholder x z i j
  by_cases hx : x = z
  · subst z
    simp [Real.zero_rpow (ne_of_gt ha)]
  · by_cases hT0 : T = 0
    · subst T
      simp
      positivity
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hFbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ y : E3,
          |F (s,y)| ≤ ‖F‖ := by
        intro s hs y
        simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s,y)
      let q : E3 → ℝ → ℝ := fun a s =>
        ∫ y : E3,
          fderiv ℝ (fun w : E3 => fderiv ℝ
            (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s)) w
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,a-y)
      let G : ℝ → E3 → ℝ := fun r a =>
        ∫ y : E3, heatHessian3 r i j y * F (T-r,a-y)
      have hqint (a : E3) : IntervalIntegrable (fun s => q a s) volume 0 T := by
        obtain ⟨hactual, _⟩ := hduhamel (F : ℝ × E3 → ℝ) F.continuous
          ‖F‖ L T (norm_nonneg F) hL hT hFbound hholder i j a
        simpa [q] using hactual
      have hqcomp (a : E3) (r : ℝ) : q a (T-r) = G r a := by
        dsimp [q, G, heatHessian3]
        have htime : T - (T-r) = r := by ring
        rw [htime]
      have hGint (a : E3) : IntervalIntegrable (fun r => G r a) volume 0 T := by
        have hcomp : IntervalIntegrable (fun r => q a (T-r)) volume 0 T :=
          by simpa only [sub_self, sub_zero] using (hqint a).comp_sub_left T |>.symm
        exact hcomp.congr (fun r _ => hqcomp a r)
      have hmod : ∀ r ∈ Ioo (0 : ℝ) T, ∀ a b : E3,
          |G r a - G r b| ≤ C₀ * L *
            min (r^(alpha/2-1)) (‖a-b‖*r^(alpha/2-3/2)) := by
        intro r hr a b
        have hFrcont : Continuous (fun y : E3 => F (T-r,y)) := by
          exact F.continuous.comp (continuous_const.prodMk continuous_id)
        let Fr : E3 →ᵇ ℝ :=
          ⟨⟨fun y : E3 => F (T-r,y), hFrcont⟩,
            ⟨2 * ‖F‖, by
              intro u v
              rw [Real.dist_eq]
              calc
                |F (T-r,u) - F (T-r,v)| ≤
                    |F (T-r,u)| + |F (T-r,v)| := abs_sub _ _
                _ ≤ ‖F‖ + ‖F‖ := add_le_add
                  (by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (T-r,u))
                  (by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (T-r,v))
                _ = 2 * ‖F‖ := by ring⟩⟩
        have hFrholder : ∀ u v : E3,
            |Fr u - Fr v| ≤ L * ‖u-v‖^alpha := by
          intro u v
          change |F (T-r,u) - F (T-r,v)| ≤ L * ‖u-v‖^alpha
          exact hholder (T-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩ u v
        have hb := hheat Fr L hL hFrholder r hr.1 a b i j
        simpa [G, Fr] using hb
      have hIntegrated := integrated_schauder_modulus alpha C₀ L T ha ha1
        hC₀.le hL hT G hGint hmod
      have htarget (a : E3) :
          (∫ s in (0 : ℝ)..T, ∫ y : E3,
            heatHessian3 (T-s) i j y * F (s,a-y)) =
            ∫ r in (0 : ℝ)..T, G r a := by
        calc
          (∫ s in (0 : ℝ)..T, ∫ y : E3,
              heatHessian3 (T-s) i j y * F (s,a-y)) =
              ∫ s in (0 : ℝ)..T, q a s := by
                apply intervalIntegral.integral_congr
                intro s hs
                dsimp [q, heatHessian3]
          _ = ∫ r in (0 : ℝ)..T, q a (T-r) := by
                symm
                rw [intervalIntegral.integral_comp_sub_left
                  (f := fun r : ℝ => q a r) T]
                simp
          _ = ∫ r in (0 : ℝ)..T, G r a := by
                apply intervalIntegral.integral_congr
                intro r hr
                exact hqcomp a r
      have hIntX := htarget x
      have hIntZ := htarget z
      have hbound := hIntegrated x z
      calc
        |(∫ s in (0 : ℝ)..T, ∫ y : E3,
            heatHessian3 (T-s) i j y * F (s,x-y)) -
          (∫ s in (0 : ℝ)..T, ∫ y : E3,
            heatHessian3 (T-s) i j y * F (s,z-y))| =
          |(∫ r in (0 : ℝ)..T, G r x) - (∫ r in (0 : ℝ)..T, G r z)| := by
            rw [hIntX, hIntZ]
        _ ≤ C₀ * L * (2 / alpha + 2 / (1-alpha)) * ‖x-z‖^alpha := hbound
        _ = C * L * ‖x-z‖^alpha := by
            dsimp [C]
            ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
