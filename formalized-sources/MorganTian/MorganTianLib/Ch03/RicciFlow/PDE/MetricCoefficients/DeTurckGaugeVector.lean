import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual flat-background DeTurck gauge vector in standard coordinates. -/
def coordinateDeTurckGauge (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (k : Fin 3) : ℝ := ∑ p : Fin 3, ∑ q : Fin 3,
      ((A.inverse (EuclideanSpace.single q 1)) p * coordinateChristoffel A P k p q)
/-- Explicit gauge-vector bound in terms of genuine inverse metric and first jets. -/
theorem coordinate_deturck_gauge_bound (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (k : Fin 3) :
    |coordinateDeTurckGauge A P k| ≤ (40/c^2)*(∑ l : Fin 3, ‖P l‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨e, he, he_inv⟩ := coercive_operator_inverse A c hc hA
  have hAi : A.inverse = e.symm.toContinuousLinearMap := by
    rw [← he]
    exact ContinuousLinearMap.inverse_equiv e
  have hcoord : ∀ x : E3, ∀ q : Fin 3, ‖x q‖ ≤ ‖x‖ := by
    intro x q
    rw [EuclideanSpace.norm_eq]
    have hnonneg : 0 ≤ ∑ r : Fin 3, ‖x.ofLp r‖ ^ 2 :=
      Finset.sum_nonneg (fun r _ => sq_nonneg _)
    apply (Real.le_sqrt (norm_nonneg _) hnonneg).2
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun r : Fin 3 => ‖x.ofLp r‖ ^ 2)
      (fun r _ => sq_nonneg _) (Finset.mem_univ q)
  have hAcoef : ∀ q p : Fin 3,
      |A.inverse (EuclideanSpace.single q 1) p| ≤ 1 / c := by
    intro q p
    calc
      |A.inverse (EuclideanSpace.single q 1) p| =
          ‖A.inverse (EuclideanSpace.single q 1) p‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖A.inverse (EuclideanSpace.single q 1)‖ := hcoord _ _
      _ ≤ ‖A.inverse‖ * ‖EuclideanSpace.single q (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse‖ := by simp
      _ ≤ 1 / c := by simpa [hAi] using he_inv
  let S : ℝ := ∑ l : Fin 3, ‖P l‖
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hP : ∀ r : Fin 3, ‖P r‖ ≤ S := by
    intro r
    dsimp [S]
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun l : Fin 3 => ‖P l‖) (fun l _ => norm_nonneg _)
      (Finset.mem_univ r)
  have hgamma : ∀ p q : Fin 3,
      |coordinateChristoffel A P k p q| ≤ (7 / (2 * c)) * S := by
    intro p q
    have hinside : 3 * ‖P p‖ + 3 * ‖P q‖ + S ≤ 7 * S := by
      nlinarith [hP p, hP q]
    calc
      |coordinateChristoffel A P k p q| ≤
          (1 / (2 * c)) *
            (3 * ‖P p‖ + 3 * ‖P q‖ + ∑ l : Fin 3, ‖P l‖) :=
        coordinate_christoffel_bound A c hc hA P k p q
      _ = (1 / (2 * c)) * (3 * ‖P p‖ + 3 * ‖P q‖ + S) := by rfl
      _ ≤ (1 / (2 * c)) * (7 * S) := by
        gcongr
      _ = (7 / (2 * c)) * S := by ring
  have hprod : ∀ p q : Fin 3,
      |A.inverse (EuclideanSpace.single q 1) p *
          coordinateChristoffel A P k p q| ≤
        (7 / (2 * c^2)) * S := by
    intro p q
    rw [abs_mul]
    calc
      |A.inverse (EuclideanSpace.single q 1) p| *
          |coordinateChristoffel A P k p q| ≤
          (1 / c) * ((7 / (2 * c)) * S) := by
        exact mul_le_mul (hAcoef q p) (hgamma p q) (abs_nonneg _) (by positivity)
      _ = (7 / (2 * c^2)) * S := by field_simp
  rw [coordinateDeTurckGauge]
  calc
    |∑ p : Fin 3, ∑ q : Fin 3,
        (A.inverse (EuclideanSpace.single q 1) p *
          coordinateChristoffel A P k p q)| ≤
        ∑ p : Fin 3, ∑ q : Fin 3,
          |A.inverse (EuclideanSpace.single q 1) p *
            coordinateChristoffel A P k p q| := by
      simpa [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun p : Fin 3 =>
          ∑ q : Fin 3,
            A.inverse (EuclideanSpace.single q 1) p *
              coordinateChristoffel A P k p q)).trans
          (by
            gcongr with p hp
            simpa [Real.norm_eq_abs] using
              (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun q : Fin 3 =>
                A.inverse (EuclideanSpace.single q 1) p *
                  coordinateChristoffel A P k p q)))
    _ ≤ ∑ p : Fin 3, ∑ q : Fin 3, (7 / (2 * c^2)) * S := by
      gcongr with p hp q hq
      exact hprod p q
    _ = 9 * ((7 / (2 * c^2)) * S) := by simp; ring
    _ ≤ (40 / c^2) * S := by
      have hc2 : 0 < c^2 := sq_pos_of_pos hc
      have hcoeff : 9 * (7 / (2 * c^2)) ≤ 40 / c^2 := by
        field_simp [ne_of_gt hc2]
        norm_num
      calc
        9 * ((7 / (2 * c^2)) * S) =
            (9 * (7 / (2 * c^2))) * S := by ring
        _ ≤ (40 / c^2) * S :=
          mul_le_mul_of_nonneg_right hcoeff hS
    _ = (40 / c^2) * (∑ l : Fin 3, ‖P l‖) := by rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
