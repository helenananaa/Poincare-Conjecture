import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelGradientTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Uniform terminal-tail limits for the first and second differentiated-kernel integrals. -/
theorem duhamel_uniform_derivative_limits (alpha : ℝ) (ha : 0<alpha) (ha1 : alpha<1)
    (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ) (hL : 0≤L) (hT : 0<T)
    (hF : ∀ s∈Icc (0:ℝ) T, ∀ x y : E3, |F (s,x)-F (s,y)|≤L*‖x-y‖^alpha) :
    (∀ i : Fin 3, TendstoUniformly (fun n : ℕ => fun x : E3 =>
      ∫ s in (0:ℝ)..(T-T/((n:ℝ)+2)), ∫ y : E3,
        fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y) (EuclideanSpace.single i 1)*F (s,y))
      (fun x : E3 => ∫ s in (0:ℝ)..T, ∫ y : E3,
        fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y) (EuclideanSpace.single i 1)*F (s,y)) atTop) ∧
    (∀ i j : Fin 3, TendstoUniformly (fun n : ℕ => fun x : E3 =>
      ∫ s in (0:ℝ)..(T-T/((n:ℝ)+2)), ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y))
      (fun x : E3 => ∫ s in (0:ℝ)..T, ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y)) atTop) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨Cg, hCg, hgrad⟩ := duhamel_gradient_terminal_tail
  obtain ⟨Ch, hCh, hhess⟩ := duhamel_hessian_terminal_tail alpha ha ha1
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    simpa using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2))
  have htime : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => T) atTop (𝓝 T)).div_atTop hden
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (T / ((n : ℝ) + 2))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp htime
  have halpha : 0 < alpha / 2 := by linarith
  have hrpow : Tendsto (fun n : ℕ => (T / ((n : ℝ) + 2)) ^ (alpha / 2))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow halpha.ne'] using
      (Real.continuous_rpow_const halpha.le).tendsto 0 |>.comp htime
  have heps : ∀ n : ℕ, 0 ≤ T / ((n : ℝ) + 2) := by
    intro n
    positivity
  have hepsT : ∀ n : ℕ, T / ((n : ℝ) + 2) ≤ T := by
    intro n
    have hn : 1 ≤ (n : ℝ) + 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).2
    nlinarith [mul_le_mul_of_nonneg_left hn hT.le]
  constructor
  · intro i
    have hlim : Tendsto
        (fun n : ℕ => Cg * ‖F‖ * Real.sqrt (T / ((n : ℝ) + 2)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds.mul hsqrt) : Tendsto
          (fun n : ℕ => (Cg * ‖F‖) * Real.sqrt (T / ((n : ℝ) + 2)))
          atTop (𝓝 ((Cg * ‖F‖) * 0)))
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hsmall := hlim.eventually (eventually_lt_nhds hε)
    filter_upwards [hsmall] with n hn
    intro x
    let q : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
        (EuclideanSpace.single i 1)*F (s,y)
    let r : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) y
        (EuclideanSpace.single i 1)*F (s,x-y)
    have hreflect : ∀ s : ℝ, q s = r s := by
      intro s
      have h := (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding
        (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)*F (s,x-z))
      simpa [q, r, sub_sub_cancel] using h
    obtain ⟨hfullr, _⟩ := hgrad F T T hT.le le_rfl x i
    obtain ⟨htailr, htailbound⟩ := hgrad F T (T / ((n : ℝ) + 2))
      (heps n) (hepsT n) x i
    have hfull : IntervalIntegrable q volume 0 T := by
      have hr : IntervalIntegrable r volume 0 T := by simpa [r] using hfullr
      exact hr.congr (fun s _ => (hreflect s).symm)
    have htail : IntervalIntegrable q volume (T - T / ((n : ℝ) + 2)) T := by
      have hr : IntervalIntegrable r volume (T - T / ((n : ℝ) + 2)) T := by
        simpa [r] using htailr
      exact hr.congr (fun s _ => (hreflect s).symm)
    have hmem : T - T / ((n : ℝ) + 2) ∈ uIcc (0 : ℝ) T := by
      rw [mem_uIcc]
      exact Or.inl ⟨sub_nonneg.mpr (hepsT n), sub_le_self T (heps n)⟩
    have hsplit := (IntervalIntegrable.trans_iff hmem).mp hfull
    have hdiff :
        (∫ s in (0 : ℝ)..T, q s) -
            ∫ s in (0 : ℝ)..(T - T / ((n : ℝ) + 2)), q s =
          ∫ s in (T - T / ((n : ℝ) + 2))..T, q s :=
      intervalIntegral.integral_interval_sub_left hfull hsplit.1
    have htail_eq :
        (∫ s in (T - T / ((n : ℝ) + 2))..T, q s) =
          ∫ s in (T - T / ((n : ℝ) + 2))..T, r s := by
      exact intervalIntegral.integral_congr (fun s _ => hreflect s)
    have hbound :
        |(∫ s in (0 : ℝ)..T, q s) -
            ∫ s in (0 : ℝ)..(T - T / ((n : ℝ) + 2)), q s| ≤
          Cg * ‖F‖ * Real.sqrt (T / ((n : ℝ) + 2)) := by
      rw [hdiff, htail_eq]
      simpa [r] using htailbound
    change dist
      (∫ s in (0 : ℝ)..T, ∫ y : E3,
        fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
          (EuclideanSpace.single i 1)*F (s,y))
      (∫ s in (0 : ℝ)..(T-T/((n:ℝ)+2)), ∫ y : E3,
        fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
          (EuclideanSpace.single i 1)*F (s,y)) < ε
    simpa [q, Real.dist_eq] using hbound.trans_lt hn
  · intro i j
    have hlim : Tendsto
        (fun n : ℕ => Ch * L * (T / ((n : ℝ) + 2)) ^ (alpha / 2))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds.mul hrpow) : Tendsto
          (fun n : ℕ => (Ch * L) * (T / ((n : ℝ) + 2)) ^ (alpha / 2))
          atTop (𝓝 ((Ch * L) * 0)))
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hsmall := hlim.eventually (eventually_lt_nhds hε)
    filter_upwards [hsmall] with n hn
    intro x
    let q : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y)
    let r : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)
    have hreflect : ∀ s : ℝ, q s = r s := by
      intro s
      have h := (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding
        (fun z : E3 =>
          fderiv ℝ (fun w : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) w
            (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)*F (s,x-z))
      simpa [q, r, sub_sub_cancel] using h
    obtain ⟨hfullr, _⟩ := hhess F L T T hL hT.le le_rfl hF x i j
    obtain ⟨htailr, htailbound⟩ := hhess F L T (T / ((n : ℝ) + 2)) hL
      (heps n) (hepsT n) hF x i j
    have hfull : IntervalIntegrable q volume 0 T := by
      have hr : IntervalIntegrable r volume 0 T := by simpa [r] using hfullr
      exact hr.congr (fun s _ => (hreflect s).symm)
    have htail : IntervalIntegrable q volume (T - T / ((n : ℝ) + 2)) T := by
      have hr : IntervalIntegrable r volume (T - T / ((n : ℝ) + 2)) T := by
        simpa [r] using htailr
      exact hr.congr (fun s _ => (hreflect s).symm)
    have hmem : T - T / ((n : ℝ) + 2) ∈ uIcc (0 : ℝ) T := by
      rw [mem_uIcc]
      exact Or.inl ⟨sub_nonneg.mpr (hepsT n), sub_le_self T (heps n)⟩
    have hsplit := (IntervalIntegrable.trans_iff hmem).mp hfull
    have hdiff :
        (∫ s in (0 : ℝ)..T, q s) -
            ∫ s in (0 : ℝ)..(T - T / ((n : ℝ) + 2)), q s =
          ∫ s in (T - T / ((n : ℝ) + 2))..T, q s :=
      intervalIntegral.integral_interval_sub_left hfull hsplit.1
    have htail_eq :
        (∫ s in (T - T / ((n : ℝ) + 2))..T, q s) =
          ∫ s in (T - T / ((n : ℝ) + 2))..T, r s := by
      exact intervalIntegral.integral_congr (fun s _ => hreflect s)
    have hbound :
        |(∫ s in (0 : ℝ)..T, q s) -
            ∫ s in (0 : ℝ)..(T - T / ((n : ℝ) + 2)), q s| ≤
          Ch * L * (T / ((n : ℝ) + 2)) ^ (alpha / 2) := by
      rw [hdiff, htail_eq]
      simpa [r] using htailbound
    change dist
      (∫ s in (0 : ℝ)..T, ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y))
      (∫ s in (0 : ℝ)..(T-T/((n:ℝ)+2)), ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1)*F (s,y)) < ε
    simpa [q, Real.dist_eq] using hbound.trans_lt hn
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
