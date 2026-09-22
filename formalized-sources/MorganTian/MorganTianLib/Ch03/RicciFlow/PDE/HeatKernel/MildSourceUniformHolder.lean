import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildSpatialRegularization
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearLocalMildIVP
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- One Holder constant controls the nonlinear source on every positive-time compact interval. -/
theorem mild_source_uniform_holder_away_zero (f : E3 →ᵇ ℝ) (N : ℝ → ℝ) (L T : ℝ) (hL : 0≤L) (hT : 0≤T)
    (hN : ∀ a b : ℝ, |N a-N b|≤L*|a-b|) (u : (ℝ × E3) →ᵇ ℝ)
    (hu : ∀ t : ℝ, 0<t → t≤T → ∀ x : E3,
      u (t,x)=(∫ y : E3, euclideanHeatKernel 3 t y*f (x-y))+
        ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y*N (u (s,x-y))) (a alpha : ℝ)
    (ha : 0<a) (haT : a≤T) (halpha : 0<alpha) (halpha1 : alpha<1) :
    ∃ C : ℝ, 0≤C ∧ ∀ s∈Icc a T, ∀ x y : E3,
      |N (u (s,x))-N (u (s,y))| ≤ C*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₀, hC₀, hreg⟩ := semilinear_mild_spatial_regularization
  let A : ℝ := C₀ *
    (‖f‖ / Real.sqrt a + (|N 0| + L * ‖u‖) * Real.sqrt T) * L
  let B : ℝ := 2 * L * ‖u‖
  let C : ℝ := max A B
  have hsqrt_a : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hA : 0 ≤ A := by
    dsimp [A]
    have htime : 0 ≤ ‖f‖ / Real.sqrt a +
        (|N 0| + L * ‖u‖) * Real.sqrt T := by positivity
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact hA.trans (le_max_left _ _)
  intro s hs x y
  have hspos : 0 < s := lt_of_lt_of_le ha hs.1
  have hsqrt_le : Real.sqrt s ≤ Real.sqrt T := by
    exact Real.sqrt_le_sqrt hs.2
  have hrecip : 1 / Real.sqrt s ≤ 1 / Real.sqrt a := by
    apply (one_div_le_one_div_of_le hsqrt_a)
    exact Real.sqrt_le_sqrt hs.1
  have htime : ‖f‖ / Real.sqrt s +
      (|N 0| + L * ‖u‖) * Real.sqrt s ≤
      ‖f‖ / Real.sqrt a +
        (|N 0| + L * ‖u‖) * Real.sqrt T := by
    have hsource : 0 ≤ |N 0| + L * ‖u‖ := by positivity
    have hfree : ‖f‖ / Real.sqrt s ≤ ‖f‖ / Real.sqrt a := by
      calc
        ‖f‖ / Real.sqrt s = ‖f‖ * (1 / Real.sqrt s) := by ring
        _ ≤ ‖f‖ * (1 / Real.sqrt a) :=
          mul_le_mul_of_nonneg_left hrecip (norm_nonneg _)
        _ = ‖f‖ / Real.sqrt a := by ring
    have hsource' : (|N 0| + L * ‖u‖) * Real.sqrt s ≤
        (|N 0| + L * ‖u‖) * Real.sqrt T :=
      mul_le_mul_of_nonneg_left hsqrt_le hsource
    exact add_le_add hfree hsource'
  have hreg' := hreg f N L T hL hT hN u hu s hspos hs.2 x y
  have hsmall : |N (u (s,x)) - N (u (s,y))| ≤ A * ‖x-y‖ := by
    have hNu := hN (u (s,x)) (u (s,y))
    have hmain : |N (u (s,x)) - N (u (s,y))| ≤
        L * (C₀ * (‖f‖ / Real.sqrt s +
          (|N 0| + L * ‖u‖) * Real.sqrt s) * ‖x-y‖) := by
      calc
        |N (u (s,x)) - N (u (s,y))| ≤ L * |u (s,x)-u (s,y)| := hNu
        _ ≤ L * (C₀ * (‖f‖ / Real.sqrt s +
            (|N 0| + L * ‖u‖) * Real.sqrt s) * ‖x-y‖) := by
          exact mul_le_mul_of_nonneg_left hreg' hL
    dsimp [A]
    have hdist : 0 ≤ ‖x-y‖ := norm_nonneg _
    have hcoef : L * (C₀ *
        (‖f‖ / Real.sqrt s + (|N 0| + L * ‖u‖) * Real.sqrt s)) ≤
        L * (C₀ *
        (‖f‖ / Real.sqrt a + (|N 0| + L * ‖u‖) * Real.sqrt T)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htime hC₀.le) hL
    calc
      |N (u (s,x)) - N (u (s,y))| ≤
          L * (C₀ * (‖f‖ / Real.sqrt s +
            (|N 0| + L * ‖u‖) * Real.sqrt s) * ‖x-y‖) := hmain
      _ = (L * (C₀ * (‖f‖ / Real.sqrt s +
            (|N 0| + L * ‖u‖) * Real.sqrt s))) * ‖x-y‖ := by ring
      _ ≤ (L * (C₀ * (‖f‖ / Real.sqrt a +
            (|N 0| + L * ‖u‖) * Real.sqrt T))) * ‖x-y‖ :=
        mul_le_mul_of_nonneg_right hcoef hdist
      _ = A * ‖x-y‖ := by ring
  by_cases hdist : ‖x-y‖ ≤ 1
  · have hpow : ‖x-y‖ ≤ ‖x-y‖ ^ alpha := by
      by_cases hzero : ‖x-y‖ = 0
      · rw [hzero]
        exact (Real.zero_rpow halpha.ne').ge
      · calc
          ‖x-y‖ = ‖x-y‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ ‖x-y‖ ^ alpha :=
            Real.rpow_le_rpow_of_exponent_ge
              (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hdist halpha1.le
    have hA_mul : A * ‖x-y‖ ≤ A * ‖x-y‖ ^ alpha :=
      mul_le_mul_of_nonneg_left hpow hA
    calc
      |N (u (s,x)) - N (u (s,y))| ≤ A * ‖x-y‖ := hsmall
      _ ≤ A * ‖x-y‖ ^ alpha := hA_mul
      _ ≤ C * ‖x-y‖ ^ alpha := by
        gcongr
        exact le_max_left _ _
  · have hdist1 : 1 ≤ ‖x-y‖ := le_of_not_ge hdist
    have hlarge : |N (u (s,x)) - N (u (s,y))| ≤ B := by
      have hNu := hN (u (s,x)) (u (s,y))
      have htri : |u (s,x)-u (s,y)| ≤ 2 * ‖u‖ := by
        calc
          |u (s,x)-u (s,y)| ≤ |u (s,x)| + |u (s,y)| := abs_sub _ _
          _ ≤ ‖u‖ + ‖u‖ := by
            exact add_le_add
              (by simpa only [Real.norm_eq_abs] using
                (BoundedContinuousFunction.norm_coe_le_norm u (s,x)))
              (by simpa only [Real.norm_eq_abs] using
                (BoundedContinuousFunction.norm_coe_le_norm u (s,y)))
          _ = 2 * ‖u‖ := by ring
      dsimp [B]
      calc
        |N (u (s,x)) - N (u (s,y))| ≤ L * |u (s,x)-u (s,y)| := hNu
        _ ≤ L * (2 * ‖u‖) := by gcongr
        _ = 2 * L * ‖u‖ := by ring
    have hpow1 : 1 ≤ ‖x-y‖ ^ alpha := by
      exact Real.one_le_rpow hdist1 halpha.le
    calc
      |N (u (s,x)) - N (u (s,y))| ≤ B := hlarge
      _ = B * 1 := by ring
      _ ≤ B * ‖x-y‖ ^ alpha := mul_le_mul_of_nonneg_left hpow1 hB
      _ ≤ C * ‖x-y‖ ^ alpha := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg _) _)
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
