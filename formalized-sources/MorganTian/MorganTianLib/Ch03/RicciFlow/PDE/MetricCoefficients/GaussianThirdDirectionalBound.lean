import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianThirdDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** gaussian third directional bound. -/
theorem gaussian_third_directional_bound 
    (t : ℝ) (ht : 0 < t) (x v : E3) (i j : Fin 3) :
    |fderiv ℝ (heatHessian3 t i j) x v| ≤
      (12*(‖x‖/t^2+‖x‖^3/t^3))*
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t x*‖v‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : ℝ := MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 t x
  let A : ℝ := ‖x‖
  let L : ℝ := A / t^2
  let M : ℝ := A^3 / t^3
  let S : ℝ := L + M
  let B : ℝ := 3 * L + M
  let C : Fin 3 → ℝ := fun k =>
    (((if i = j then x k else 0) + (if i = k then x j else 0) +
        (if j = k then x i else 0)) / (4 * t^2) -
      x i * x j * x k / (8 * t^3))
  have hdecomp : v = ∑ k : Fin 3, (v k) • EuclideanSpace.single k (1 : ℝ) := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  have hlin : fderiv ℝ (heatHessian3 t i j) x v =
      ∑ k : Fin 3, (v k) *
        fderiv ℝ (heatHessian3 t i j) x (EuclideanSpace.single k (1 : ℝ)) := by
    calc
      fderiv ℝ (heatHessian3 t i j) x v =
          fderiv ℝ (heatHessian3 t i j) x
            (∑ k : Fin 3, (v k) • EuclideanSpace.single k (1 : ℝ)) := by
              congr 1
      _ = ∑ k : Fin 3,
          fderiv ℝ (heatHessian3 t i j) x ((v k) • EuclideanSpace.single k (1 : ℝ)) :=
            map_sum _ _ _
      _ = ∑ k : Fin 3, (v k) *
          fderiv ℝ (heatHessian3 t i j) x (EuclideanSpace.single k (1 : ℝ)) := by
            simp [smul_eq_mul]
  have hrepr : fderiv ℝ (heatHessian3 t i j) x v =
      ∑ k : Fin 3, (v k) * (C k * K) := by
    rw [hlin]
    apply Finset.sum_congr rfl
    intro k hk
    rw [gaussian_third_derivative ht x i j k]
  have hxcoord (q : Fin 3) : |x q| ≤ A := by
    simpa [A, Real.norm_eq_abs] using (PiLp.norm_apply_le x q)
  have hvcoord (q : Fin 3) : |v q| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v q)
  have hK : 0 ≤ K := by
    exact (MorganTianLib.ParabolicPDE.euclideanHeatKernel_pos 3 ht x).le
  have hA : 0 ≤ A := by simp [A]
  have hL : 0 ≤ L := by positivity [L, A]
  have hM : 0 ≤ M := by positivity [M, A]
  have hS : 0 ≤ S := by positivity [S, L, M]
  have hB : 0 ≤ B := by positivity [B, L, M]
  have hBS : B ≤ 4 * S := by
    dsimp [B, S]
    nlinarith [hL, hM]
  have hden1 : 0 < 4 * t^2 := by positivity
  have hden2 : 0 < 8 * t^3 := by positivity
  have hcoeff (k : Fin 3) : |C k| ≤ B := by
    have h1 : |(if i = j then x k else 0)| ≤ A := by
      by_cases h : i = j
      · simpa [h] using hxcoord k
      · simp [h, hA]
    have h2 : |(if i = k then x j else 0)| ≤ A := by
      by_cases h : i = k
      · simpa [h] using hxcoord j
      · simp [h, hA]
    have h3 : |(if j = k then x i else 0)| ≤ A := by
      by_cases h : j = k
      · simpa [h] using hxcoord i
      · simp [h, hA]
    have hnum :
        |(if i = j then x k else 0) + (if i = k then x j else 0) +
            (if j = k then x i else 0)| ≤ 3 * A := by
      calc
        _ ≤ |(if i = j then x k else 0)| +
            |(if i = k then x j else 0)| + |(if j = k then x i else 0)| := by
              calc
                _ ≤ |(if i = j then x k else 0) + (if i = k then x j else 0)| +
                    |(if j = k then x i else 0)| := abs_add_le _ _
                _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
        _ ≤ 3 * A := by nlinarith [h1, h2, h3]
    have hprod : |x i * x j * x k| ≤ A^3 := by
      calc
        |x i * x j * x k| = |x i| * |x j| * |x k| := by rw [abs_mul, abs_mul]
        _ ≤ A * A * A := by
          calc
            |x i| * |x j| * |x k| ≤ (A * A) * A := by
              exact mul_le_mul
                (mul_le_mul (hxcoord i) (hxcoord j) (abs_nonneg _) hA)
                (hxcoord k) (abs_nonneg _) (mul_nonneg hA hA)
            _ = A * A * A := by ring
        _ = A^3 := by ring
    have hlinScale : (3 * A) / (4 * t^2) ≤ 3 * L := by
      dsimp [L]
      calc
        (3 * A) / (4 * t^2) = ((3 * A) / 4) / t^2 := by ring
        _ ≤ (3 * A) / t^2 := by
          exact div_le_div_of_nonneg_right (by nlinarith [hA]) (sq_nonneg t)
        _ = 3 * (A / t^2) := by ring
    have hcubScale : A^3 / (8 * t^3) ≤ M := by
      dsimp [M]
      calc
        A^3 / (8 * t^3) = (A^3 / 8) / t^3 := by ring
        _ ≤ A^3 / t^3 := by
          exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg A])
            (pow_nonneg ht.le 3)
    dsimp [C, B]
    calc
      |((if i = j then x k else 0) + (if i = k then x j else 0) +
          (if j = k then x i else 0)) / (4 * t^2) -
          x i * x j * x k / (8 * t^3)|
          ≤ |((if i = j then x k else 0) + (if i = k then x j else 0) +
              (if j = k then x i else 0)) / (4 * t^2)| +
            |x i * x j * x k / (8 * t^3)| := by
              calc
                _ ≤ |((if i = j then x k else 0) + (if i = k then x j else 0) +
                    (if j = k then x i else 0)) / (4 * t^2)| +
                    |-(x i * x j * x k / (8 * t^3))| := by
                      simpa only [sub_eq_add_neg] using
                        (abs_add_le
                          (((if i = j then x k else 0) + (if i = k then x j else 0) +
                            (if j = k then x i else 0)) / (4 * t^2))
                          (-(x i * x j * x k / (8 * t^3))))
                _ = _ := by rw [abs_neg]
      _ = |(if i = j then x k else 0) + (if i = k then x j else 0) +
              (if j = k then x i else 0)| / (4 * t^2) +
            |x i * x j * x k| / (8 * t^3) := by
              rw [abs_div, abs_of_pos hden1, abs_div, abs_of_pos hden2]
      _ ≤ (3 * A) / (4 * t^2) + A^3 / (8 * t^3) := by
            exact add_le_add
              (div_le_div_of_nonneg_right hnum hden1.le)
              (div_le_div_of_nonneg_right hprod hden2.le)
      _ ≤ 3 * L + M := add_le_add hlinScale hcubScale
  have hterm (k : Fin 3) :
      |(v k) * (C k * K)| ≤ ‖v‖ * (B * K) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hK]
    have hinner : |C k| * K ≤ B * K :=
      mul_le_mul_of_nonneg_right (hcoeff k) hK
    exact mul_le_mul (hvcoord k) hinner
      (mul_nonneg (abs_nonneg _) hK) (norm_nonneg v)
  change |fderiv ℝ (heatHessian3 t i j) x v| ≤ 12 * S * K * ‖v‖
  rw [hrepr]
  calc
    |∑ k : Fin 3, (v k) * (C k * K)| ≤
        ∑ k : Fin 3, |(v k) * (C k * K)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin 3, ‖v‖ * (B * K) :=
      Finset.sum_le_sum (fun k hk => hterm k)
    _ = 3 * (‖v‖ * (B * K)) := by simp
    _ ≤ 12 * S * K * ‖v‖ := by
      have h1 : B * K ≤ (4 * S) * K := mul_le_mul_of_nonneg_right hBS hK
      have h2 : ‖v‖ * (B * K) ≤ ‖v‖ * ((4 * S) * K) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg v)
      calc
        3 * (‖v‖ * (B * K)) ≤ 3 * (‖v‖ * ((4 * S) * K)) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 12 * S * K * ‖v‖ := by ring
  
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
