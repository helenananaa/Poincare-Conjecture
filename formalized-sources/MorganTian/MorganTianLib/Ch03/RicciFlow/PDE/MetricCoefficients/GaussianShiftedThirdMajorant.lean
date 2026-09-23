import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianThirdDirectionalBound
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ScaledGaussianMoment
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianShiftPolynomial
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianThirdDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianParabolicShift
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** gaussian shifted third majorant. -/
theorem gaussian_shifted_third_majorant 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∃ D : E3 → ℝ,
      Integrable D volume ∧ (∀ y : E3, 0 ≤ D y) ∧
      (∫ y : E3, D y) ≤ C*t^(alpha/2-3/2) ∧
      ∀ y h v : E3, ‖h‖ ≤ Real.sqrt t → ∀ i j : Fin 3,
        |fderiv ℝ (heatHessian3 t i j) (y+h) v| * ‖y‖^alpha ≤ D y*‖v‖ :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C0, hC0, hM0⟩ :=
    scaled_gaussian_moment alpha alpha (le_of_lt ha)
  obtain ⟨C1, hC1, hM1⟩ :=
    scaled_gaussian_moment alpha (alpha + 1) (by linarith)
  obtain ⟨C2, hC2, hM2⟩ :=
    scaled_gaussian_moment alpha (alpha + 2) (by linarith)
  obtain ⟨C3, hC3, hM3⟩ :=
    scaled_gaussian_moment alpha (alpha + 3) (by linarith)
  let C : ℝ := 96 * Real.exp 1 * (2 * C0 + 4 * C1 + 3 * C2 + C3)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  rcases hM0 t ht with ⟨hI0, hInt0⟩
  rcases hM1 t ht with ⟨hI1, hInt1⟩
  rcases hM2 t ht with ⟨hI2, hInt2⟩
  rcases hM3 t ht with ⟨hI3, hInt3⟩
  let M0 : E3 → ℝ := scaledGaussianMoment alpha alpha t
  let M1 : E3 → ℝ := scaledGaussianMoment alpha (alpha + 1) t
  let M2 : E3 → ℝ := scaledGaussianMoment alpha (alpha + 2) t
  let M3 : E3 → ℝ := scaledGaussianMoment alpha (alpha + 3) t
  have hI0' : Integrable M0 volume := by simpa [M0] using hI0
  have hI1' : Integrable M1 volume := by simpa [M1] using hI1
  have hI2' : Integrable M2 volume := by simpa [M2] using hI2
  have hI3' : Integrable M3 volume := by simpa [M3] using hI3
  have hInt0' : (∫ y : E3, M0 y) ≤ C0 * t^(alpha/2-3/2) := by
    simpa [M0] using hInt0
  have hInt1' : (∫ y : E3, M1 y) ≤ C1 * t^(alpha/2-3/2) := by
    simpa [M1] using hInt1
  have hInt2' : (∫ y : E3, M2 y) ≤ C2 * t^(alpha/2-3/2) := by
    simpa [M2] using hInt2
  have hInt3' : (∫ y : E3, M3 y) ≤ C3 * t^(alpha/2-3/2) := by
    simpa [M3] using hInt3
  have hsumInt : Integrable
      (fun y : E3 => 2 * M0 y + 4 * M1 y + 3 * M2 y + M3 y) volume := by
    exact (((hI0'.const_mul 2).add (hI1'.const_mul 4)).add
      (hI2'.const_mul 3)).add hI3'
  have hsum01 : Integrable (fun y : E3 => 2 * M0 y + 4 * M1 y) volume :=
    (hI0'.const_mul 2).add (hI1'.const_mul 4)
  have hsum012 : Integrable
      (fun y : E3 => 2 * M0 y + 4 * M1 y + 3 * M2 y) volume :=
    hsum01.add (hI2'.const_mul 3)
  have hkernel0 (y : E3) :
      0 ≤ MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2*t) y :=
    (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 (by positivity) y).le
  have hMnonneg (beta : ℝ) (y : E3) :
      0 ≤ scaledGaussianMoment alpha beta t y := by
    unfold scaledGaussianMoment
    apply div_nonneg
    · exact mul_nonneg (hkernel0 y) (Real.rpow_nonneg (norm_nonneg y) beta)
    · exact (Real.rpow_pos_of_pos ht _).le
  have hM0nonneg (y : E3) : 0 ≤ M0 y := by
    simpa [M0] using hMnonneg alpha y
  have hM1nonneg (y : E3) : 0 ≤ M1 y := by
    simpa [M1] using hMnonneg (alpha + 1) y
  have hM2nonneg (y : E3) : 0 ≤ M2 y := by
    simpa [M2] using hMnonneg (alpha + 2) y
  have hM3nonneg (y : E3) : 0 ≤ M3 y := by
    simpa [M3] using hMnonneg (alpha + 3) y
  let D : E3 → ℝ := fun y =>
    96 * Real.exp 1 * (2 * M0 y + 4 * M1 y + 3 * M2 y + M3 y)
  have hDint : Integrable D volume := by
    simpa [D] using hsumInt.const_mul (96 * Real.exp 1)
  have hweights :
      2 * (∫ y : E3, M0 y) + 4 * (∫ y : E3, M1 y) +
          3 * (∫ y : E3, M2 y) + (∫ y : E3, M3 y) ≤
        (2 * C0 + 4 * C1 + 3 * C2 + C3) * t^(alpha/2-3/2) := by
    have h0 := mul_le_mul_of_nonneg_left hInt0' (by norm_num : (0:ℝ) ≤ 2)
    have h1 := mul_le_mul_of_nonneg_left hInt1' (by norm_num : (0:ℝ) ≤ 4)
    have h2 := mul_le_mul_of_nonneg_left hInt2' (by norm_num : (0:ℝ) ≤ 3)
    calc
      _ ≤ 2 * (C0 * t^(alpha/2-3/2)) +
          4 * (C1 * t^(alpha/2-3/2)) +
          3 * (C2 * t^(alpha/2-3/2)) + C3 * t^(alpha/2-3/2) := by
        linarith
      _ = (2 * C0 + 4 * C1 + 3 * C2 + C3) * t^(alpha/2-3/2) := by ring
  have hDintegral :
      (∫ y : E3, D y) = 96 * Real.exp 1 *
          (2 * (∫ y : E3, M0 y) + 4 * (∫ y : E3, M1 y) +
            3 * (∫ y : E3, M2 y) + (∫ y : E3, M3 y)) := by
    calc
      (∫ y : E3, D y) = 96 * Real.exp 1 *
          (∫ y : E3, 2 * M0 y + 4 * M1 y + 3 * M2 y + M3 y) := by
        simp only [D, integral_const_mul]
      _ = 96 * Real.exp 1 *
          (2 * (∫ y : E3, M0 y) + 4 * (∫ y : E3, M1 y) +
            3 * (∫ y : E3, M2 y) + (∫ y : E3, M3 y)) := by
        congr 1
        rw [integral_add hsum012 hI3', integral_add hsum01 (hI2'.const_mul 3),
          integral_add (hI0'.const_mul 2) (hI1'.const_mul 4)]
        simp only [integral_const_mul]
  have hDintBound : (∫ y : E3, D y) ≤ C * t^(alpha/2-3/2) := by
    calc
      (∫ y : E3, D y) ≤ 96 * Real.exp 1 *
          ((2 * C0 + 4 * C1 + 3 * C2 + C3) * t^(alpha/2-3/2)) := by
        rw [hDintegral]
        exact mul_le_mul_of_nonneg_left hweights (by positivity)
      _ = C * t^(alpha/2-3/2) := by
        dsimp [C]
        ring
  refine ⟨D, hDint, ?_, hDintBound, ?_⟩
  · intro y
    dsimp [D]
    positivity [hM0nonneg y, hM1nonneg y, hM2nonneg y, hM3nonneg y]
  · intro y h v hh i j
    let a : ℝ := ‖y‖
    let b : ℝ := ‖y + h‖
    let q : ℝ := a^alpha
    let P : ℝ := b/t^2 + b^3/t^3
    let P' : ℝ := (a + Real.sqrt t)/t^2 + (a + Real.sqrt t)^3/t^3
    let K : ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t (y+h)
    let K0 : ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (2*t) y
    let V : ℝ := ‖v‖
    have hAlpha : 0 < alpha := ha
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hq : 0 ≤ q := by
      dsimp [q, a]
      exact Real.rpow_nonneg (norm_nonneg y) alpha
    have hV : 0 ≤ V := by dsimp [V]; positivity
    have hK : 0 ≤ K := by
      dsimp [K]
      exact (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 ht (y+h)).le
    have hK0 : 0 ≤ K0 := by
      dsimp [K0]
      exact hkernel0 y
    have hnorm : b ≤ a + Real.sqrt t := by
      dsimp [a, b]
      calc
        ‖y + h‖ ≤ ‖y‖ + ‖h‖ := norm_add_le _ _
        _ ≤ ‖y‖ + Real.sqrt t := by linarith [hh]
    have hP : P ≤ P' := by
      have h1 : b / t^2 ≤ (a + Real.sqrt t) / t^2 :=
        div_le_div_of_nonneg_right hnorm (sq_nonneg t)
      have h3 : b^3 ≤ (a + Real.sqrt t)^3 := by
        exact pow_le_pow_left₀ hb hnorm 3
      have h2 : b^3 / t^3 ≤ (a + Real.sqrt t)^3 / t^3 :=
        div_le_div_of_nonneg_right h3 (pow_nonneg (le_of_lt ht) 3)
      dsimp [P, P']
      exact add_le_add h1 h2
    have hPnonneg : 0 ≤ P := by
      dsimp [P]
      positivity
    have hP'nonneg : 0 ≤ P' := by
      dsimp [P']
      positivity
    have hkernelShift : K ≤ (8 * Real.exp 1) * K0 := by
      dsimp [K, K0]
      exact gaussian_parabolic_shift t ht y h hh
    have hpoly := gaussian_shift_polynomial a t alpha ha ht hAlpha
    have hmonomials :
        (2 * a^alpha / t^((3:ℝ)/2) +
          4 * a^(alpha+1) / t^2 +
          3 * a^(alpha+2) / t^((5:ℝ)/2) +
          a^(alpha+3) / t^3) * K0 =
          2 * M0 y + 4 * M1 y + 3 * M2 y + M3 y := by
      dsimp [M0, M1, M2, M3]
      simp only [scaledGaussianMoment]
      rw [show (alpha - alpha + 3) / 2 = (3:ℝ)/2 by ring,
        show (alpha + 1 - alpha + 3) / 2 = (2:ℝ) by ring,
        show (alpha + 2 - alpha + 3) / 2 = (5:ℝ)/2 by ring,
        show (alpha + 3 - alpha + 3) / 2 = (3:ℝ) by ring]
      dsimp [K0]
      rw [show alpha + 1 = 1 + alpha by ring,
        show alpha + 2 = 2 + alpha by ring,
        show alpha + 3 = 3 + alpha by ring]
      dsimp [a]
      have ht2 : t ^ (2:ℝ) = t ^ (2:ℕ) := by
        simpa using Real.rpow_natCast t 2
      have ht3 : t ^ (3:ℝ) = t ^ (3:ℕ) := by
        simpa using Real.rpow_natCast t 3
      rw [ht2, ht3]
      ring
    have hdir := gaussian_third_directional_bound t ht (y+h) v i j
    have hdir' :
        |fderiv ℝ (heatHessian3 t i j) (y+h) v| * q ≤
          (12 * P * K * V) * q := by
      have hmul := mul_le_mul_of_nonneg_right hdir hq
      dsimp [P, K, V, q, b] at hmul ⊢
      simpa [a, mul_assoc] using hmul
    have hPq : P * q ≤ P' * q := mul_le_mul_of_nonneg_right hP hq
    have hKV : K * V ≤ ((8 * Real.exp 1) * K0) * V :=
      mul_le_mul_of_nonneg_right hkernelShift hV
    have hstep1 : (12 * (P * q)) * (K * V) ≤
        (12 * (P' * q)) * (K * V) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPq (by norm_num)) (mul_nonneg hK hV)
    have hstep2 : (12 * (P' * q)) * (K * V) ≤
        (12 * (P' * q)) * (((8 * Real.exp 1) * K0) * V) :=
      mul_le_mul_of_nonneg_left hKV (by positivity)
    calc
      |fderiv ℝ (heatHessian3 t i j) (y+h) v| * ‖y‖^alpha ≤
          (12 * P * K * V) * q := by simpa [a, q] using hdir'
      _ = (12 * (P * q)) * (K * V) := by ring
      _ ≤ (12 * (P' * q)) * (K * V) := hstep1
      _ ≤ (12 * (P' * q)) * (((8 * Real.exp 1) * K0) * V) := hstep2
      _ = 96 * Real.exp 1 * ((P' * q) * K0) * V := by ring
      _ = 96 * Real.exp 1 * (2 * M0 y + 4 * M1 y + 3 * M2 y + M3 y) * V := by
        rw [show P' * q =
          (2 * a^alpha / t^((3:ℝ)/2) +
            4 * a^(alpha+1) / t^2 +
            3 * a^(alpha+2) / t^((5:ℝ)/2) +
            a^(alpha+3) / t^3) by
              dsimp [P', q]
              exact hpoly]
        rw [hmonomials]
      _ = D y * ‖v‖ := by
        dsimp [D, V]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
