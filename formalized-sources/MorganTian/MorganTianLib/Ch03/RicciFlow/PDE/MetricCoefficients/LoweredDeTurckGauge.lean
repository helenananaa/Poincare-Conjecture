import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The lowered flat-background gauge expression, to be linked to the actual vector separately. -/
def loweredDeTurckGauge (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (j : Fin 3) : ℝ := (1/2:ℝ)*(∑ p : Fin 3, ∑ q : Fin 3,
      ((A.inverse (EuclideanSpace.single q 1)) p *
        ((P p (EuclideanSpace.single q 1)) j +
         (P q (EuclideanSpace.single p 1)) j - (P j (EuclideanSpace.single q 1)) p)))
/-- A quantitative lowered-gauge estimate without postulated gauge identities. -/
theorem lowered_deturck_gauge_bound (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (j : Fin 3) :
    |loweredDeTurckGauge A P j| ≤ (10/c)*(∑ l : Fin 3, ‖P l‖) :=
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
  have hAcoef : ∀ l q : Fin 3,
      |A.inverse (EuclideanSpace.single l 1) q| ≤ 1 / c := by
    intro l q
    calc
      |A.inverse (EuclideanSpace.single l 1) q| =
          ‖A.inverse (EuclideanSpace.single l 1) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖A.inverse (EuclideanSpace.single l 1)‖ := hcoord _ _
      _ ≤ ‖A.inverse‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse‖ := by simp
      _ ≤ 1 / c := by simpa [hAi] using he_inv
  have hPcoef : ∀ r l q : Fin 3,
      |(P r (EuclideanSpace.single l 1)) q| ≤ ‖P r‖ := by
    intro r l q
    calc
      |(P r (EuclideanSpace.single l 1)) q| =
          ‖(P r (EuclideanSpace.single l 1)) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖P r (EuclideanSpace.single l 1)‖ := hcoord _ _
      _ ≤ ‖P r‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖P r‖ := by simp
  have hbracket : ∀ p q : Fin 3,
      |(P p (EuclideanSpace.single q 1)) j +
          (P q (EuclideanSpace.single p 1)) j -
            (P j (EuclideanSpace.single q 1)) p| ≤
        ‖P p‖ + ‖P q‖ + ‖P j‖ := by
    intro p q
    calc
      |(P p (EuclideanSpace.single q 1)) j +
          (P q (EuclideanSpace.single p 1)) j -
            (P j (EuclideanSpace.single q 1)) p| ≤
          |(P p (EuclideanSpace.single q 1)) j| +
            |(P q (EuclideanSpace.single p 1)) j| +
              |(P j (EuclideanSpace.single q 1)) p| := by
        calc
          |(P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p| =
              |((P p (EuclideanSpace.single q 1)) j +
                (P q (EuclideanSpace.single p 1)) j) +
                  (-((P j (EuclideanSpace.single q 1)) p))| := by
            congr 1
          _ ≤ |(P p (EuclideanSpace.single q 1)) j +
                (P q (EuclideanSpace.single p 1)) j| +
                |-(P j (EuclideanSpace.single q 1)) p| := abs_add_le _ _
          _ = |(P p (EuclideanSpace.single q 1)) j +
                (P q (EuclideanSpace.single p 1)) j| +
                |(P j (EuclideanSpace.single q 1)) p| := by rw [abs_neg]
          _ ≤ |(P p (EuclideanSpace.single q 1)) j| +
                |(P q (EuclideanSpace.single p 1)) j| +
                |(P j (EuclideanSpace.single q 1)) p| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ ‖P p‖ + ‖P q‖ + ‖P j‖ := by
        exact add_le_add (add_le_add (hPcoef p q j) (hPcoef q p j))
          (hPcoef j q p)
  have hterm : ∀ p q : Fin 3,
      |(A.inverse (EuclideanSpace.single q 1)) p *
          ((P p (EuclideanSpace.single q 1)) j +
            (P q (EuclideanSpace.single p 1)) j -
              (P j (EuclideanSpace.single q 1)) p)| ≤
        (1 / c) * (‖P p‖ + ‖P q‖ + ‖P j‖) := by
    intro p q
    rw [abs_mul]
    exact mul_le_mul (hAcoef q p) (hbracket p q) (abs_nonneg _) (by positivity)
  have hsum :
      |∑ p : Fin 3, ∑ q : Fin 3,
          (A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)| ≤
        ∑ p : Fin 3, ∑ q : Fin 3,
          |(A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)| := by
    calc
      |∑ p : Fin 3, ∑ q : Fin 3,
          (A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)| =
          ‖∑ p : Fin 3, ∑ q : Fin 3,
            (A.inverse (EuclideanSpace.single q 1)) p *
              ((P p (EuclideanSpace.single q 1)) j +
                (P q (EuclideanSpace.single p 1)) j -
                  (P j (EuclideanSpace.single q 1)) p)‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∑ p : Fin 3, ‖∑ q : Fin 3,
          (A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p : Fin 3, ∑ q : Fin 3,
          ‖(A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)‖ := by
          gcongr with p hp
          exact norm_sum_le _ _
      _ = ∑ p : Fin 3, ∑ q : Fin 3,
          |(A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)| := by
          simp only [Real.norm_eq_abs]
  rw [loweredDeTurckGauge]
  calc
    |(1 / 2 : ℝ) * ∑ p : Fin 3, ∑ q : Fin 3,
        (A.inverse (EuclideanSpace.single q 1)) p *
          ((P p (EuclideanSpace.single q 1)) j +
            (P q (EuclideanSpace.single p 1)) j -
              (P j (EuclideanSpace.single q 1)) p)| =
        (1 / 2 : ℝ) * |∑ p : Fin 3, ∑ q : Fin 3,
          (A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)| := by
      rw [abs_mul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * ∑ p : Fin 3, ∑ q : Fin 3,
        |(A.inverse (EuclideanSpace.single q 1)) p *
          ((P p (EuclideanSpace.single q 1)) j +
            (P q (EuclideanSpace.single p 1)) j -
              (P j (EuclideanSpace.single q 1)) p)| := by
      gcongr
    _ ≤ (1 / 2 : ℝ) * ∑ p : Fin 3, ∑ q : Fin 3,
        (1 / c) * (‖P p‖ + ‖P q‖ + ‖P j‖) := by
      gcongr with p hp q hq
      exact hterm p q
    _ = (1 / 2 : ℝ) * ((3 / c) * (∑ l : Fin 3, ‖P l‖) +
          (3 / c) * (∑ l : Fin 3, ‖P l‖) + (9 / c) * ‖P j‖) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      simp [Finset.sum_const, Finset.card_fin]
      ring
    _ ≤ (1 / 2 : ℝ) * ((15 / c) * (∑ l : Fin 3, ‖P l‖)) := by
      have hj : ‖P j‖ ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.single_le_sum (fun l _ => norm_nonneg _) (Finset.mem_univ j)
      have hsum_nonneg : 0 ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.sum_nonneg (fun l _ => norm_nonneg _)
      have h9 : (9 / c) * ‖P j‖ ≤ (9 / c) * (∑ l : Fin 3, ‖P l‖) :=
        mul_le_mul_of_nonneg_left hj (by positivity)
      have hinside :
          (3 / c) * (∑ l : Fin 3, ‖P l‖) +
              (3 / c) * (∑ l : Fin 3, ‖P l‖) + (9 / c) * ‖P j‖ ≤
            (15 / c) * (∑ l : Fin 3, ‖P l‖) := by
        calc
          _ ≤ (3 / c) * (∑ l : Fin 3, ‖P l‖) +
                (3 / c) * (∑ l : Fin 3, ‖P l‖) +
                (9 / c) * (∑ l : Fin 3, ‖P l‖) := add_le_add_right h9 _
          _ = (15 / c) * (∑ l : Fin 3, ‖P l‖) := by ring
      exact mul_le_mul_of_nonneg_left hinside (by positivity)
    _ ≤ (10 / c) * (∑ l : Fin 3, ‖P l‖) := by
      have hsum_nonneg : 0 ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.sum_nonneg (fun l _ => norm_nonneg _)
      have hcinv : 0 ≤ 1 / c := by positivity
      have hprod : 0 ≤ (1 / c) * (∑ l : Fin 3, ‖P l‖) :=
        mul_nonneg hcinv hsum_nonneg
      calc
        (1 / 2 : ℝ) * ((15 / c) * (∑ l : Fin 3, ‖P l‖)) =
            (15 / 2 : ℝ) * ((1 / c) * (∑ l : Fin 3, ‖P l‖)) := by ring
        _ ≤ 10 * ((1 / c) * (∑ l : Fin 3, ‖P l‖)) := by nlinarith
        _ = (10 / c) * (∑ l : Fin 3, ‖P l‖) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
