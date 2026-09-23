import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseCoefficientHolder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatCoefficientCommutator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped BoundedContinuousFunction Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- **Math.** inverse metric heat commutator. -/
theorem inverse_metric_heat_commutator (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A0 : E3 →L[ℝ] E3) (G : E3 → (E3 →L[ℝ] E3)),
      Continuous G → ∀ (c L : ℝ), 0 < c → 0 ≤ L →
      (∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v) →
      (∀ x : E3, ‖G x-A0‖ ≤ c/2) →
      (∀ x y : E3, ‖G x-G y‖ ≤ L*‖x-y‖^alpha) →
      ∀ (f : E3 →ᵇ ℝ) (t : ℝ), 0 < t → ∀ (x : E3) (i j p q : Fin 3),
        let a : E3 → ℝ := fun z => ((G z).inverse (EuclideanSpace.single q 1)) p;
        MeasureTheory.Integrable (fun y : E3 => (a x-a (x-y))*
          fderiv ℝ (fun z : E3 => fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*f (x-y)) MeasureTheory.volume ∧
        |∫ y : E3, (a x-a (x-y))*fderiv ℝ (fun z : E3 =>
          fderiv ℝ (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t) z (EuclideanSpace.single i 1)) y
            (EuclideanSpace.single j 1)*f (x-y)| ≤ (C*L/c^2)*‖f‖*t^(alpha/2-1) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₀, hC₀, hcomm⟩ :=
    MorganTianLib.ParabolicPDE.heat_hessian_coefficient_commutator alpha ha ha1
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro A0 G hG c L hc hL hA hball hholder f t ht x i j p q
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
  obtain ⟨hint, hbound⟩ := hcomm a hcont_a K hK haHolder' f t ht x i j
  refine ⟨?_, ?_⟩
  · simpa [a] using hint
  · calc
      |∫ y : E3, (a x - a (x - y)) *
          fderiv ℝ (fun z : E3 => fderiv ℝ
            (MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * f (x - y)|
          ≤ C₀ * K * ‖f‖ * t ^ (alpha / 2 - 1) := hbound
      _ = (4 * C₀ * L / c ^ 2) * ‖f‖ * t ^ (alpha / 2 - 1) := by
        dsimp [K]
        ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
