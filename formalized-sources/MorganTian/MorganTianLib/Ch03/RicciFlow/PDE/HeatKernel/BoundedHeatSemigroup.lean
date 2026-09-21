import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import Mathlib.Analysis.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The actual bounded heat operators obey the semigroup composition law. -/
theorem exists_three_dimensional_bounded_heat_semigroup :
    ∃ A : ℝ → ((E3 →ᵇ ℝ) →L[ℝ] (E3 →ᵇ ℝ)),
      (∀ t : ℝ, 0 < t → ‖A t‖ ≤ 1 ∧ ∀ (f : E3 →ᵇ ℝ) (x : E3),
        Integrable (fun y : E3 => euclideanHeatKernel 3 t y * f (x - y)) volume ∧
        A t f x = ∫ y : E3, euclideanHeatKernel 3 t y * f (x - y)) ∧
      ∀ s t : ℝ, 0 < s → 0 < t → A (s + t) = (A s).comp (A t) := by
/- SWARM_PROOF_BEGIN -/
  classical
  obtain ⟨A, hA⟩ := exists_three_dimensional_bounded_heat_operator
  let k : ℝ → E3 → ℝ := fun r => euclideanHeatKernel 3 r
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hkint (r : ℝ) (hr : 0 < r) : Integrable (k r) volume := by
    simpa [k] using (euclideanHeatKernel_mass_semigroup 3).1 r hr |>.1
  have hkcont (r : ℝ) (hr : 0 < r) : Continuous (k r) := by
    simpa [k] using (euclideanHeatKernel_three_heat_equation hr).1.continuous
  have hkconv (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (z : E3) :
      MeasureTheory.convolution (k s) (k t) L volume z = k (s + t) z := by
    change (∫ y : E3, k s y * k t (z - y)) = k (s + t) z
    simpa [k, mul_comm, add_comm] using
      (euclideanHeatKernel_mass_semigroup 3).2 t s ht hs z |>.2
  refine ⟨A, ?_, ?_⟩
  · intro t ht
    exact hA t ht
  · intro s t hs ht
    apply ContinuousLinearMap.ext
    intro f
    apply BoundedContinuousFunction.ext
    intro x
    change A (s + t) f x = A s (A t f) x
    have hfg : ∀ᵐ y : E3 ∂(volume : Measure E3),
        MeasureTheory.ConvolutionExistsAt (k s) (k t) y L volume := by
      filter_upwards [] with y
      change Integrable (fun z : E3 => k s z * k t (y - z)) volume
      simpa [k, mul_comm] using
        (euclideanHeatKernel_mass_semigroup 3).2 t s ht hs y |>.1
    have hgk : ∀ᵐ y : E3 ∂(volume : Measure E3),
        MeasureTheory.ConvolutionExistsAt (k t) (f : E3 → ℝ) y L volume := by
      filter_upwards [] with y
      change Integrable (fun z : E3 => k t z * f (y - z)) volume
      simpa [k] using (hA t ht).2 f y |>.1
    have hdouble :
        Integrable
          (Function.uncurry fun u y : E3 => k s y * (k t (u - y) * f (x - u)))
          ((volume : Measure E3).prod volume) := by
      have hbase :
          Integrable (Function.uncurry fun u y : E3 => k s y * k t (u - y))
            ((volume : Measure E3).prod volume) := by
        change Integrable
          (fun p : E3 × E3 => k s p.2 * k t (p.1 - p.2))
          ((volume : Measure E3).prod volume)
        exact (hkint s hs).convolution_integrand L (hkint t ht)
      have hmajor :
          Integrable
            (fun p : E3 × E3 => (k s p.2 * k t (p.1 - p.2)) * ‖f‖)
            ((volume : Measure E3).prod volume) :=
        hbase.mul_const ‖f‖
      refine hmajor.mono' ?_ ?_
      · have hfs : Continuous (f : E3 → ℝ) := f.continuous
        fun_prop
      · filter_upwards [] with p
        rcases p with ⟨u, y⟩
        change ‖k s y * (k t (u - y) * f (x - u))‖ ≤
          (k s y * k t (u - y)) * ‖f‖
        have hks : 0 ≤ k s y := by
          simpa [k] using (euclideanHeatKernel_pos 3 hs y).le
        have hkt : 0 ≤ k t (u - y) := by
          simpa [k] using (euclideanHeatKernel_pos 3 ht (u - y)).le
        rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hks,
          Real.norm_eq_abs, abs_of_nonneg hkt]
        calc
          k s y * (k t (u - y) * ‖f (x - u)‖) =
              (k s y * k t (u - y)) * ‖f (x - u)‖ := by ring
          _ ≤ (k s y * k t (u - y)) * ‖f‖ :=
            mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x - u))
              (mul_nonneg hks hkt)
    have hassoc :=
      MeasureTheory.convolution_assoc' (f := k s) (g := k t)
        (k := (f : E3 → ℝ)) (L := L) (L₂ := L) (L₃ := L) (L₄ := L)
        (x₀ := x) (by
          intro a b c
          dsimp [L]
          ring) hfg hgk hdouble
    have hinner :
        MeasureTheory.convolution (k t) (f : E3 → ℝ) L volume =
          (A t f : E3 → ℝ) := by
      funext y
      simpa [MeasureTheory.convolution_def, k, L] using ((hA t ht).2 f y).2.symm
    calc
      A (s + t) f x = ∫ y : E3, k (s + t) y * f (x - y) := by
        simpa [k] using ((hA (s + t) (by linarith)).2 f x).2
      _ = MeasureTheory.convolution
          (MeasureTheory.convolution (k s) (k t) L volume)
          (f : E3 → ℝ) L volume x := by
        rw [MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [L]
        rw [hkconv s t hs ht y]
      _ = MeasureTheory.convolution (k s)
          (MeasureTheory.convolution (k t) (f : E3 → ℝ) L volume) L volume x :=
        hassoc
      _ = A s (A t f) x := by
        rw [MeasureTheory.convolution_def, hinner]
        simpa [k, L] using ((hA s hs).2 (A t f) x).2.symm
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
