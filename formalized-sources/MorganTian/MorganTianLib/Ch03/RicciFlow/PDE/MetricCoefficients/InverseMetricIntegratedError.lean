import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseCoefficientHolder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.IntegratedCoefficientError
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ

/-- **Math.** inverse metric integrated freezing error. -/
theorem inverse_metric_integrated_freezing_error (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A0 : E3 →L[ℝ] E3) (G : E3 → (E3 →L[ℝ] E3)),
      Continuous G → ∀ (c L : ℝ), 0 < c → 0 ≤ L →
      (∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v) →
      (∀ x : E3, ‖G x-A0‖ ≤ c/2) →
      (∀ x y : E3, ‖G x-G y‖ ≤ L*‖x-y‖^alpha) →
      ∀ (F : (ℝ × E3) →ᵇ ℝ) (T : ℝ), 0 ≤ T → ∀ (x : E3) (i j p q : Fin 3),
        let a : E3 → ℝ := fun z => ((G z).inverse (EuclideanSpace.single q 1)) p;
        IntervalIntegrable (fun s => ∫ y : E3, (a x-a (x-y))*
          fderiv ℝ (fun z : E3 => fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)) volume 0 T ∧
        |∫ s in (0:ℝ)..T, ∫ y : E3, (a x-a (x-y))*fderiv ℝ (fun z : E3 =>
          fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s)) z (EuclideanSpace.single i 1)) y
            (EuclideanSpace.single j 1)*F (s,x-y)| ≤ (C*L/c^2)*‖F‖*T^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₀, hC₀, hfreeze⟩ :=
    MorganTianLib.ParabolicPDE.integrated_coefficient_freezing_error alpha ha ha1
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro A0 G hG c L hc hL hA hball hholder F T hT x i j p q
  dsimp only
  let a : E3 → ℝ := fun z => ((G z).inverse (EuclideanSpace.single q 1)) p
  have haHolder := inverse_coefficient_holder A0 G c L alpha hc hL hA hball hholder
  have haHolder' : ∀ u v : E3,
      |a u - a v| ≤ (4 * L / c ^ 2) * ‖u - v‖ ^ alpha := by
    intro u v
    exact haHolder u v p q
  let K : ℝ := 4 * L / c ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcont_a : Continuous a := by
    rw [continuous_iff_continuousAt]
    intro z
    apply Metric.continuousAt_iff'.2
    intro ε hε
    have hpow : ContinuousAt (fun y : E3 => ‖y - z‖ ^ alpha) z := by
      have hr : ContinuousAt (fun r : ℝ => r ^ alpha) 0 :=
        Real.continuousAt_rpow_const 0 alpha (Or.inr ha.le)
      have hn : ContinuousAt (fun y : E3 => ‖y - z‖) z := by fun_prop
      simpa [Function.comp_def, ha.ne'] using hr.comp_of_eq hn (by simp)
    have hmajor : ContinuousAt (fun y : E3 => K * ‖y - z‖ ^ alpha) z :=
      continuousAt_const.mul hpow
    have hmajor_tendsto :
        Tendsto (fun y : E3 => K * ‖y - z‖ ^ alpha) (𝓝 z) (𝓝 0) := by
      simpa [ha.ne'] using hmajor.tendsto
    have hevent := hmajor_tendsto.eventually (Iio_mem_nhds hε)
    filter_upwards [hevent] with y hy
    calc
      dist (a y) (a z) = |a y - a z| := Real.dist_eq _ _
      _ ≤ K * ‖y - z‖ ^ alpha := by
        simpa [K] using haHolder' y z
      _ < ε := hy
  obtain ⟨hint, hbound⟩ := hfreeze a hcont_a K hK haHolder' F T hT x i j
  refine ⟨?_, ?_⟩
  · simpa [a] using hint
  · calc
      |∫ s in (0 : ℝ)..T, ∫ y : E3, (a x - a (x - y)) *
          fderiv ℝ (fun z : E3 => fderiv ℝ
            (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y)|
          ≤ C₀ * K * ‖F‖ * T ^ (alpha / 2) := hbound
      _ = (4 * C₀ * L / c ^ 2) * ‖F‖ * T ^ (alpha / 2) := by
        dsimp [K]
        ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
