import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeVector
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LoweredGaugeJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Explicit first-jet quadratic correction in the full flat-background gauge Lie expression. -/
def deturckLieLowerOrder (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (i j : Fin 3) : ℝ := loweredGaugeJet A P i j+loweredGaugeJet A P j i+
      (∑ k : Fin 3, coordinateDeTurckGauge A P k *
        ((P k (EuclideanSpace.single j 1)) i -
         (P i (EuclideanSpace.single k 1)) j - (P j (EuclideanSpace.single k 1)) i))
/-- All remaining gauge-Lie terms are bounded quadratically in first derivatives. -/
theorem deturck_lie_lower_order_bound (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (i j : Fin 3) :
    |deturckLieLowerOrder A P i j| ≤ (400/c^2)*(∑ l : Fin 3, ‖P l‖)^2 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S : ℝ := ∑ l : Fin 3, ‖P l‖
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hP : ∀ r : Fin 3, ‖P r‖ ≤ S := by
    intro r
    dsimp [S]
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun l : Fin 3 => ‖P l‖) (fun l _ => norm_nonneg _)
      (Finset.mem_univ r)
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hPcoef : ∀ r l q : Fin 3,
      |(P r (EuclideanSpace.single l 1)) q| ≤ ‖P r‖ := by
    intro r l q
    calc
      |(P r (EuclideanSpace.single l 1)) q| =
          ‖(P r (EuclideanSpace.single l 1)) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖P r (EuclideanSpace.single l 1)‖ := by
        rw [EuclideanSpace.norm_eq]
        have hnonneg : 0 ≤ ∑ s : Fin 3, ‖(P r (EuclideanSpace.single l 1)).ofLp s‖ ^ 2 :=
          Finset.sum_nonneg (fun s _ => sq_nonneg _)
        apply (Real.le_sqrt (norm_nonneg _) hnonneg).2
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun s : Fin 3 => ‖(P r (EuclideanSpace.single l 1)).ofLp s‖ ^ 2)
          (fun s _ => sq_nonneg _) (Finset.mem_univ q)
      _ ≤ ‖P r‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖P r‖ := by simp
  have hbracket : ∀ k : Fin 3,
      |(P k (EuclideanSpace.single j 1)) i -
          (P i (EuclideanSpace.single k 1)) j -
            (P j (EuclideanSpace.single k 1)) i| ≤
        ‖P k‖ + ‖P i‖ + ‖P j‖ := by
    intro k
    calc
      |(P k (EuclideanSpace.single j 1)) i -
          (P i (EuclideanSpace.single k 1)) j -
            (P j (EuclideanSpace.single k 1)) i| ≤
          |(P k (EuclideanSpace.single j 1)) i| +
            |(P i (EuclideanSpace.single k 1)) j| +
              |(P j (EuclideanSpace.single k 1)) i| := by
        calc
          |(P k (EuclideanSpace.single j 1)) i -
              (P i (EuclideanSpace.single k 1)) j -
                (P j (EuclideanSpace.single k 1)) i| =
              |(P k (EuclideanSpace.single j 1)) i +
                (-(P i (EuclideanSpace.single k 1)) j) +
                  (-(P j (EuclideanSpace.single k 1)) i)| := by
                    congr 1
          _ ≤ |(P k (EuclideanSpace.single j 1)) i +
                (-(P i (EuclideanSpace.single k 1)) j)| +
                |-(P j (EuclideanSpace.single k 1)) i| := abs_add_le _ _
          _ = |(P k (EuclideanSpace.single j 1)) i +
                (-(P i (EuclideanSpace.single k 1)) j)| +
                |(P j (EuclideanSpace.single k 1)) i| := by rw [abs_neg]
          _ ≤ |(P k (EuclideanSpace.single j 1)) i| +
                |(P i (EuclideanSpace.single k 1)) j| +
                |(P j (EuclideanSpace.single k 1)) i| := by
            calc
              |(P k (EuclideanSpace.single j 1)) i +
                  (-(P i (EuclideanSpace.single k 1)) j)| +
                    |(P j (EuclideanSpace.single k 1)) i| ≤
                  (|(P k (EuclideanSpace.single j 1)) i| +
                    |-(P i (EuclideanSpace.single k 1)) j|) +
                      |(P j (EuclideanSpace.single k 1)) i| :=
                add_le_add (abs_add_le
                  ((P k (EuclideanSpace.single j 1)) i)
                  (-(P i (EuclideanSpace.single k 1)) j)) (le_refl _)
              _ = |(P k (EuclideanSpace.single j 1)) i| +
                    |(P i (EuclideanSpace.single k 1)) j| +
                      |(P j (EuclideanSpace.single k 1)) i| := by
                rw [abs_neg]
      _ ≤ ‖P k‖ + ‖P i‖ + ‖P j‖ := by
        exact add_le_add (add_le_add (hPcoef k j i) (hPcoef i k j))
          (hPcoef j k i)
  have hga : ∀ k : Fin 3,
      |coordinateDeTurckGauge A P k| ≤ (40 / c ^ 2) * S := by
    intro k
    simpa [S] using coordinate_deturck_gauge_bound A P c hc hA k
  have hsum :
      |∑ k : Fin 3, coordinateDeTurckGauge A P k *
        ((P k (EuclideanSpace.single j 1)) i -
          (P i (EuclideanSpace.single k 1)) j -
            (P j (EuclideanSpace.single k 1)) i)| ≤
        (280 / c ^ 2) * S ^ 2 := by
    calc
      |∑ k : Fin 3, coordinateDeTurckGauge A P k *
          ((P k (EuclideanSpace.single j 1)) i -
            (P i (EuclideanSpace.single k 1)) j -
              (P j (EuclideanSpace.single k 1)) i)| ≤
          ∑ k : Fin 3, |coordinateDeTurckGauge A P k *
            ((P k (EuclideanSpace.single j 1)) i -
              (P i (EuclideanSpace.single k 1)) j -
                (P j (EuclideanSpace.single k 1)) i)| := by
        simpa [Real.norm_eq_abs] using
          (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k : Fin 3 =>
            coordinateDeTurckGauge A P k *
              ((P k (EuclideanSpace.single j 1)) i -
                (P i (EuclideanSpace.single k 1)) j -
                  (P j (EuclideanSpace.single k 1)) i)))
      _ ≤ ∑ k : Fin 3, (40 / c ^ 2) * S *
          (‖P k‖ + ‖P i‖ + ‖P j‖) := by
        gcongr with k hk
        rw [abs_mul]
        exact (mul_le_mul (hga k) (hbracket k) (abs_nonneg _) (by positivity))
      _ = (40 / c ^ 2) * S * (S + 3 * ‖P i‖ + 3 * ‖P j‖) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        simp [S, Finset.sum_const]
      _ ≤ (280 / c ^ 2) * S ^ 2 := by
        have hinside : S + 3 * ‖P i‖ + 3 * ‖P j‖ ≤ 7 * S := by
          nlinarith [hP i, hP j]
        have hcoef : 0 ≤ (40 / c ^ 2) * S := by positivity
        calc
          (40 / c ^ 2) * S * (S + 3 * ‖P i‖ + 3 * ‖P j‖) ≤
              (40 / c ^ 2) * S * (7 * S) := by
            gcongr
          _ = (280 / c ^ 2) * S ^ 2 := by ring
  have hjet : ∀ r q : Fin 3,
      |loweredGaugeJet A P r q| ≤ (10 / c ^ 2) * S ^ 2 := by
    intro r q
    calc
      |loweredGaugeJet A P r q| ≤ (10 / c ^ 2) * ‖P r‖ * S := by
        simpa [S] using lowered_gauge_jet_bound A P c hc hA r q
      _ ≤ (10 / c ^ 2) * S * S := by
        gcongr
        exact hP r
      _ = (10 / c ^ 2) * S ^ 2 := by ring
  rw [deturckLieLowerOrder]
  calc
    |loweredGaugeJet A P i j + loweredGaugeJet A P j i +
        ∑ k : Fin 3, coordinateDeTurckGauge A P k *
          ((P k (EuclideanSpace.single j 1)) i -
            (P i (EuclideanSpace.single k 1)) j -
              (P j (EuclideanSpace.single k 1)) i)| ≤
        |loweredGaugeJet A P i j| + |loweredGaugeJet A P j i| +
          |∑ k : Fin 3, coordinateDeTurckGauge A P k *
            ((P k (EuclideanSpace.single j 1)) i -
              (P i (EuclideanSpace.single k 1)) j -
                (P j (EuclideanSpace.single k 1)) i)| := by
      calc
        |loweredGaugeJet A P i j + loweredGaugeJet A P j i +
            ∑ k : Fin 3, coordinateDeTurckGauge A P k *
              ((P k (EuclideanSpace.single j 1)) i -
                (P i (EuclideanSpace.single k 1)) j -
                  (P j (EuclideanSpace.single k 1)) i)| ≤
            |loweredGaugeJet A P i j + loweredGaugeJet A P j i| +
              |∑ k : Fin 3, coordinateDeTurckGauge A P k *
                ((P k (EuclideanSpace.single j 1)) i -
                  (P i (EuclideanSpace.single k 1)) j -
                    (P j (EuclideanSpace.single k 1)) i)| := abs_add_le _ _
        _ ≤ _ := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (10 / c ^ 2) * S ^ 2 + (10 / c ^ 2) * S ^ 2 +
          (280 / c ^ 2) * S ^ 2 := by
      gcongr
      exact hjet i j
      exact hjet j i
    _ = (300 / c ^ 2) * S ^ 2 := by ring
    _ ≤ (400 / c ^ 2) * S ^ 2 := by
      gcongr
      norm_num
    _ = (400 / c ^ 2) * (∑ l : Fin 3, ‖P l‖) ^ 2 := by rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
