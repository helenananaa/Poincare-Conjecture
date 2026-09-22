import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The two Christoffel-product terms in the coordinate Ricci contraction. -/
def quadraticRicciProduct (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (i j : Fin 3) : ℝ := ∑ k : Fin 3, ∑ l : Fin 3,
      (coordinateChristoffel A P k k l*coordinateChristoffel A P l i j-
        coordinateChristoffel A P k j l*coordinateChristoffel A P l i k)
/-- The actual quadratic connection term has a uniform first-jet bound. -/
theorem quadratic_ricci_product_bound (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (i j : Fin 3) :
    |quadraticRicciProduct A P i j| ≤ (300/c^2)*(∑ l : Fin 3, ‖P l‖)^2 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S : ℝ := ∑ l : Fin 3, ‖P l‖
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hPi : ∀ r : Fin 3, ‖P r‖ ≤ S := by
    intro r
    dsimp [S]
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun l : Fin 3 => ‖P l‖) (fun l _ => norm_nonneg _) (Finset.mem_univ r)
  have hcoeff : ∀ k a b : Fin 3,
      |coordinateChristoffel A P k a b| ≤ (7 / (2 * c)) * S := by
    intro k a b
    have hbase := coordinate_christoffel_bound A c hc hA P k a b
    calc
      |coordinateChristoffel A P k a b| ≤
          (1 / (2 * c)) * (3 * ‖P a‖ + 3 * ‖P b‖ + ∑ l : Fin 3, ‖P l‖) := hbase
      _ ≤ (1 / (2 * c)) * (7 * S) := by
        have hinner : 3 * ‖P a‖ + 3 * ‖P b‖ + ∑ l : Fin 3, ‖P l‖ ≤
            7 * S := by
          calc
            3 * ‖P a‖ + 3 * ‖P b‖ + ∑ l : Fin 3, ‖P l‖ ≤
                3 * S + 3 * S + S := by
              exact add_le_add (add_le_add
                (mul_le_mul_of_nonneg_left (hPi a) (by norm_num))
                (mul_le_mul_of_nonneg_left (hPi b) (by norm_num)))
                (le_refl S)
            _ = 7 * S := by ring
        exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (7 / (2 * c)) * S := by ring
  have hprod : ∀ k l a b d e : Fin 3,
      |coordinateChristoffel A P k a b * coordinateChristoffel A P l d e| ≤
        ((7 / (2 * c)) * S)^2 := by
    intro k l a b d e
    have hK : 0 ≤ (7 / (2 * c)) * S := by positivity
    rw [abs_mul]
    calc
      |coordinateChristoffel A P k a b| *
          |coordinateChristoffel A P l d e| ≤
          ((7 / (2 * c)) * S) * ((7 / (2 * c)) * S) := by
        exact mul_le_mul (hcoeff k a b) (hcoeff l d e) (abs_nonneg _) hK
      _ = ((7 / (2 * c)) * S)^2 := by ring
  rw [quadraticRicciProduct]
  calc
    |∑ k : Fin 3, ∑ l : Fin 3,
        (coordinateChristoffel A P k k l * coordinateChristoffel A P l i j -
          coordinateChristoffel A P k j l * coordinateChristoffel A P l i k)| ≤
        ∑ k : Fin 3, |∑ l : Fin 3,
          (coordinateChristoffel A P k k l * coordinateChristoffel A P l i j -
            coordinateChristoffel A P k j l * coordinateChristoffel A P l i k)| := by
      simpa [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k : Fin 3 =>
          ∑ l : Fin 3,
            (coordinateChristoffel A P k k l * coordinateChristoffel A P l i j -
              coordinateChristoffel A P k j l * coordinateChristoffel A P l i k)))
    _ ≤ ∑ k : Fin 3, ∑ l : Fin 3,
        (|coordinateChristoffel A P k k l * coordinateChristoffel A P l i j| +
          |coordinateChristoffel A P k j l * coordinateChristoffel A P l i k|) := by
      gcongr with k hk
      calc
        |∑ l : Fin 3,
            (coordinateChristoffel A P k k l * coordinateChristoffel A P l i j -
              coordinateChristoffel A P k j l * coordinateChristoffel A P l i k)| ≤
            ∑ l : Fin 3,
              |coordinateChristoffel A P k k l * coordinateChristoffel A P l i j -
                coordinateChristoffel A P k j l * coordinateChristoffel A P l i k| := by
          simpa [Real.norm_eq_abs] using
            (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun l : Fin 3 =>
              coordinateChristoffel A P k k l * coordinateChristoffel A P l i j -
                coordinateChristoffel A P k j l * coordinateChristoffel A P l i k))
        _ ≤ ∑ l : Fin 3,
            (|coordinateChristoffel A P k k l * coordinateChristoffel A P l i j| +
              |coordinateChristoffel A P k j l * coordinateChristoffel A P l i k|) := by
          gcongr with l hl
          calc
            |coordinateChristoffel A P k k l * coordinateChristoffel A P l i j -
                coordinateChristoffel A P k j l * coordinateChristoffel A P l i k| =
                |coordinateChristoffel A P k k l * coordinateChristoffel A P l i j +
                  (-(coordinateChristoffel A P k j l * coordinateChristoffel A P l i k))| := by
                    congr 1
            _ ≤ |coordinateChristoffel A P k k l * coordinateChristoffel A P l i j| +
                |-(coordinateChristoffel A P k j l * coordinateChristoffel A P l i k)| :=
              abs_add_le _ _
            _ = |coordinateChristoffel A P k k l * coordinateChristoffel A P l i j| +
                |coordinateChristoffel A P k j l * coordinateChristoffel A P l i k| := by
              rw [abs_neg]
    _ ≤ ∑ k : Fin 3, ∑ l : Fin 3, (2 * ((7 / (2 * c)) * S)^2) := by
      gcongr with k hk l hl
      calc
        |coordinateChristoffel A P k k l * coordinateChristoffel A P l i j| +
            |coordinateChristoffel A P k j l * coordinateChristoffel A P l i k| ≤
            ((7 / (2 * c)) * S)^2 + ((7 / (2 * c)) * S)^2 :=
          add_le_add (hprod k l k l i j) (hprod k l j l i k)
        _ = 2 * ((7 / (2 * c)) * S)^2 := by ring
    _ = 18 * ((7 / (2 * c)) * S)^2 := by
      norm_num
      ring
    _ ≤ (300 / c^2) * S^2 := by
      have hc2 : 0 < c^2 := sq_pos_of_pos hc
      have hsq : 0 ≤ S^2 := sq_nonneg S
      field_simp [ne_of_gt hc2]
      nlinarith
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
