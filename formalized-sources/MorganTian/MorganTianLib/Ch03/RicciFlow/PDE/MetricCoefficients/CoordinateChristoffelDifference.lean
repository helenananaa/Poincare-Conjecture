import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseQuadraticRemainder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalPartDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Local quantitative control of connection coefficients in both metric and first jets. -/
theorem coordinate_christoffel_difference (A0 A B : E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA0 : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v)
    (hA : ‖A-A0‖≤c/2) (hB : ‖B-A0‖≤c/2)
    (P Q : Fin 3 → E3 →L[ℝ] E3) (k i j : Fin 3) :
    |coordinateChristoffel A P k i j-coordinateChristoffel B Q k i j| ≤
      (7/c)*(∑ l : Fin 3, ‖P l-Q l‖) +
      (14/c^2)*‖A-B‖*(∑ l : Fin 3, ‖Q l‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨a, b, ha, hb, ha_inv, hb_inv, hab_inv⟩ :=
    positive_ball_inverse_control A0 c hc hA0 A B hA hB
  have hAi : A.inverse = a.symm.toContinuousLinearMap := by
    rw [← ha]
    exact ContinuousLinearMap.inverse_equiv a
  have hBi : B.inverse = b.symm.toContinuousLinearMap := by
    rw [← hb]
    exact ContinuousLinearMap.inverse_equiv b
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
      |A.inverse (EuclideanSpace.single l 1) q| ≤ 2 / c := by
    intro l q
    calc
      |A.inverse (EuclideanSpace.single l 1) q| =
          ‖A.inverse (EuclideanSpace.single l 1) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖A.inverse (EuclideanSpace.single l 1)‖ := hcoord _ _
      _ ≤ ‖A.inverse‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse‖ := by simp
      _ ≤ 2 / c := by simpa [hAi] using ha_inv
  have hABcoef : ∀ l q : Fin 3,
      |(A.inverse - B.inverse) (EuclideanSpace.single l 1) q| ≤
        (4 / c^2) * ‖A - B‖ := by
    intro l q
    calc
      |(A.inverse - B.inverse) (EuclideanSpace.single l 1) q| =
          ‖(A.inverse - B.inverse) (EuclideanSpace.single l 1) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖(A.inverse - B.inverse) (EuclideanSpace.single l 1)‖ := hcoord _ _
      _ ≤ ‖A.inverse - B.inverse‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse - B.inverse‖ := by simp
      _ ≤ (4 / c^2) * ‖A - B‖ := by simpa [hAi, hBi] using hab_inv
  have hPcoef : ∀ r l q : Fin 3,
      |((P r - Q r) (EuclideanSpace.single l 1)) q| ≤ ‖P r - Q r‖ := by
    intro r l q
    calc
      |((P r - Q r) (EuclideanSpace.single l 1)) q| =
          ‖((P r - Q r) (EuclideanSpace.single l 1)) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖(P r - Q r) (EuclideanSpace.single l 1)‖ := hcoord _ _
      _ ≤ ‖P r - Q r‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖P r - Q r‖ := by simp
  have hQcoef : ∀ r l q : Fin 3,
      |(Q r (EuclideanSpace.single l 1)) q| ≤ ‖Q r‖ := by
    intro r l q
    calc
      |(Q r (EuclideanSpace.single l 1)) q| =
          ‖(Q r (EuclideanSpace.single l 1)) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖Q r (EuclideanSpace.single l 1)‖ := hcoord _ _
      _ ≤ ‖Q r‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖Q r‖ := by simp
  have hbracketQ : ∀ l : Fin 3,
      |(Q i (EuclideanSpace.single l 1)) j +
          (Q j (EuclideanSpace.single l 1)) i -
            (Q l (EuclideanSpace.single j 1)) i| ≤
        ‖Q i‖ + ‖Q j‖ + ‖Q l‖ := by
    intro l
    calc
      |(Q i (EuclideanSpace.single l 1)) j +
          (Q j (EuclideanSpace.single l 1)) i -
            (Q l (EuclideanSpace.single j 1)) i| ≤
          |(Q i (EuclideanSpace.single l 1)) j| +
            |(Q j (EuclideanSpace.single l 1)) i| +
              |(Q l (EuclideanSpace.single j 1)) i| := by
        calc
          |(Q i (EuclideanSpace.single l 1)) j +
              (Q j (EuclideanSpace.single l 1)) i -
                (Q l (EuclideanSpace.single j 1)) i| =
              |((Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i) +
                  (-((Q l (EuclideanSpace.single j 1)) i))| := by
            congr 1
          _ ≤ |(Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i| +
                |-(Q l (EuclideanSpace.single j 1)) i| := abs_add_le _ _
          _ = |(Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i| +
                |(Q l (EuclideanSpace.single j 1)) i| := by rw [abs_neg]
          _ ≤ |(Q i (EuclideanSpace.single l 1)) j| +
                |(Q j (EuclideanSpace.single l 1)) i| +
                |(Q l (EuclideanSpace.single j 1)) i| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ ‖Q i‖ + ‖Q j‖ + ‖Q l‖ := by
        exact add_le_add (add_le_add (hQcoef i l j) (hQcoef j l i)) (hQcoef l j i)
  have hbracketdiff : ∀ l : Fin 3,
      |((P i (EuclideanSpace.single l 1)) j +
          (P j (EuclideanSpace.single l 1)) i -
            (P l (EuclideanSpace.single j 1)) i) -
        ((Q i (EuclideanSpace.single l 1)) j +
          (Q j (EuclideanSpace.single l 1)) i -
            (Q l (EuclideanSpace.single j 1)) i)| ≤
        ‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖ := by
    intro l
    calc
      |((P i (EuclideanSpace.single l 1)) j +
          (P j (EuclideanSpace.single l 1)) i -
            (P l (EuclideanSpace.single j 1)) i) -
        ((Q i (EuclideanSpace.single l 1)) j +
          (Q j (EuclideanSpace.single l 1)) i -
            (Q l (EuclideanSpace.single j 1)) i)| =
          |((P i - Q i) (EuclideanSpace.single l 1)) j +
            ((P j - Q j) (EuclideanSpace.single l 1)) i -
              ((P l - Q l) (EuclideanSpace.single j 1)) i| := by
        congr 1
        simp only [sub_apply, Pi.sub_apply, map_sub]
        change
          (P i (EuclideanSpace.single l 1)) j +
              (P j (EuclideanSpace.single l 1)) i -
                (P l (EuclideanSpace.single j 1)) i -
              ((Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i -
                  (Q l (EuclideanSpace.single j 1)) i) =
            ((P i (EuclideanSpace.single l 1)) j -
                (Q i (EuclideanSpace.single l 1)) j) +
              ((P j (EuclideanSpace.single l 1)) i -
                (Q j (EuclideanSpace.single l 1)) i) -
              ((P l (EuclideanSpace.single j 1)) i -
                (Q l (EuclideanSpace.single j 1)) i)
        ring
      _ ≤ |((P i - Q i) (EuclideanSpace.single l 1)) j| +
            |((P j - Q j) (EuclideanSpace.single l 1)) i| +
              |((P l - Q l) (EuclideanSpace.single j 1)) i| := by
        calc
          |((P i - Q i) (EuclideanSpace.single l 1)) j +
              ((P j - Q j) (EuclideanSpace.single l 1)) i -
                ((P l - Q l) (EuclideanSpace.single j 1)) i| ≤
              |((P i - Q i) (EuclideanSpace.single l 1)) j +
                  ((P j - Q j) (EuclideanSpace.single l 1)) i| +
                |-( ((P l - Q l) (EuclideanSpace.single j 1)) i)| := by
            simpa only [sub_eq_add_neg] using
              (abs_add_le
                (((P i - Q i) (EuclideanSpace.single l 1)) j +
                  ((P j - Q j) (EuclideanSpace.single l 1)) i)
                (-((P l - Q l) (EuclideanSpace.single j 1)) i))
          _ = |((P i - Q i) (EuclideanSpace.single l 1)) j +
                ((P j - Q j) (EuclideanSpace.single l 1)) i| +
                |((P l - Q l) (EuclideanSpace.single j 1)) i| := by rw [abs_neg]
          _ ≤ |((P i - Q i) (EuclideanSpace.single l 1)) j| +
                |((P j - Q j) (EuclideanSpace.single l 1)) i| +
                |((P l - Q l) (EuclideanSpace.single j 1)) i| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ ‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖ := by
        exact add_le_add (add_le_add (hPcoef i l j) (hPcoef j l i)) (hPcoef l j i)
  have hterm : ∀ l : Fin 3,
      |(A.inverse (EuclideanSpace.single l 1)) k *
          ((P i (EuclideanSpace.single l 1)) j +
            (P j (EuclideanSpace.single l 1)) i -
              (P l (EuclideanSpace.single j 1)) i) -
        (B.inverse (EuclideanSpace.single l 1)) k *
          ((Q i (EuclideanSpace.single l 1)) j +
            (Q j (EuclideanSpace.single l 1)) i -
              (Q l (EuclideanSpace.single j 1)) i)| ≤
        (2 / c) * (‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖) +
          (4 / c^2) * ‖A - B‖ *
            (‖Q i‖ + ‖Q j‖ + ‖Q l‖) := by
    intro l
    let p := (P i (EuclideanSpace.single l 1)) j +
      (P j (EuclideanSpace.single l 1)) i -
        (P l (EuclideanSpace.single j 1)) i
    let q := (Q i (EuclideanSpace.single l 1)) j +
      (Q j (EuclideanSpace.single l 1)) i -
        (Q l (EuclideanSpace.single j 1)) i
    have hpq : |p - q| ≤ ‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖ := by
      simpa [p, q] using hbracketdiff l
    have hq : |q| ≤ ‖Q i‖ + ‖Q j‖ + ‖Q l‖ := by
      simpa [q] using hbracketQ l
    calc
      |(A.inverse (EuclideanSpace.single l 1)) k * p -
          (B.inverse (EuclideanSpace.single l 1)) k * q| =
          |(A.inverse (EuclideanSpace.single l 1)) k * (p - q) +
            ((A.inverse - B.inverse) (EuclideanSpace.single l 1)) k * q| := by
        congr 1
        simp only [sub_apply, Pi.sub_apply, map_sub]
        change
          (A.inverse (EuclideanSpace.single l 1)) k * p -
              (B.inverse (EuclideanSpace.single l 1)) k * q =
            (A.inverse (EuclideanSpace.single l 1)) k * (p - q) +
              ((A.inverse (EuclideanSpace.single l 1)) k -
                (B.inverse (EuclideanSpace.single l 1)) k) * q
        ring
      _ ≤ |(A.inverse (EuclideanSpace.single l 1)) k * (p - q)| +
          |((A.inverse - B.inverse) (EuclideanSpace.single l 1)) k * q| :=
        abs_add_le _ _
      _ = |(A.inverse (EuclideanSpace.single l 1)) k| * |p - q| +
          |((A.inverse - B.inverse) (EuclideanSpace.single l 1)) k| * |q| := by
        rw [abs_mul, abs_mul]
      _ ≤ (2 / c) * (‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖) +
          (4 / c^2) * ‖A - B‖ * (‖Q i‖ + ‖Q j‖ + ‖Q l‖) := by
        gcongr
        · exact hAcoef l k
        · exact hABcoef l k
  rw [coordinateChristoffel, coordinateChristoffel]
  have hsum :
      ‖∑ l : Fin 3,
          ((A.inverse (EuclideanSpace.single l 1)) k *
              ((P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i -
                  (P l (EuclideanSpace.single j 1)) i) -
            (B.inverse (EuclideanSpace.single l 1)) k *
              ((Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i -
                  (Q l (EuclideanSpace.single j 1)) i))‖ ≤
      ∑ l : Fin 3,
        ((2 / c) * (‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖) +
          (4 / c^2) * ‖A - B‖ *
            (‖Q i‖ + ‖Q j‖ + ‖Q l‖)) := by
    calc
      _ ≤ ∑ l : Fin 3,
          ‖(A.inverse (EuclideanSpace.single l 1)) k *
              ((P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i -
                  (P l (EuclideanSpace.single j 1)) i) -
            (B.inverse (EuclideanSpace.single l 1)) k *
              ((Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i -
                  (Q l (EuclideanSpace.single j 1)) i)‖ := norm_sum_le _ _
      _ ≤ ∑ l : Fin 3,
          ((2 / c) * (‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖) +
            (4 / c^2) * ‖A - B‖ *
              (‖Q i‖ + ‖Q j‖ + ‖Q l‖)) := by
        gcongr with l hl
        exact hterm l
  calc
    |(1 / 2 : ℝ) * ∑ l : Fin 3,
        (A.inverse (EuclideanSpace.single l 1)) k *
          ((P i (EuclideanSpace.single l 1)) j +
            (P j (EuclideanSpace.single l 1)) i -
              (P l (EuclideanSpace.single j 1)) i) -
      (1 / 2 : ℝ) * ∑ l : Fin 3,
        (B.inverse (EuclideanSpace.single l 1)) k *
          ((Q i (EuclideanSpace.single l 1)) j +
            (Q j (EuclideanSpace.single l 1)) i -
              (Q l (EuclideanSpace.single j 1)) i)| =
        |(1 / 2 : ℝ) * ∑ l : Fin 3,
          ((A.inverse (EuclideanSpace.single l 1)) k *
              ((P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i -
                  (P l (EuclideanSpace.single j 1)) i) -
            (B.inverse (EuclideanSpace.single l 1)) k *
              ((Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i -
                  (Q l (EuclideanSpace.single j 1)) i))| := by
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ (1 / 2 : ℝ) * ∑ l : Fin 3,
        |(A.inverse (EuclideanSpace.single l 1)) k *
              ((P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i -
                  (P l (EuclideanSpace.single j 1)) i) -
            (B.inverse (EuclideanSpace.single l 1)) k *
              ((Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i -
                  (Q l (EuclideanSpace.single j 1)) i)| := by
      rw [abs_mul]
      rw [show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun l : Fin 3 =>
          ((A.inverse (EuclideanSpace.single l 1)) k *
              ((P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i -
                  (P l (EuclideanSpace.single j 1)) i) -
            (B.inverse (EuclideanSpace.single l 1)) k *
              ((Q i (EuclideanSpace.single l 1)) j +
                (Q j (EuclideanSpace.single l 1)) i -
                  (Q l (EuclideanSpace.single j 1)) i))))
    _ ≤ (1 / 2 : ℝ) * ∑ l : Fin 3,
        ((2 / c) * (‖P i - Q i‖ + ‖P j - Q j‖ + ‖P l - Q l‖) +
          (4 / c^2) * ‖A - B‖ * (‖Q i‖ + ‖Q j‖ + ‖Q l‖)) := by
      gcongr with l hl
      exact hterm l
    _ = (1 / c) *
          (3 * ‖P i - Q i‖ + 3 * ‖P j - Q j‖ +
            ∑ l : Fin 3, ‖P l - Q l‖) +
        (2 / c^2) * ‖A - B‖ *
          (3 * ‖Q i‖ + 3 * ‖Q j‖ + ∑ l : Fin 3, ‖Q l‖) := by
      simp_rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ (7 / c) * (∑ l : Fin 3, ‖P l - Q l‖) +
        (14 / c^2) * ‖A - B‖ * (∑ l : Fin 3, ‖Q l‖) := by
      have hsumP : 3 * ‖P i - Q i‖ + 3 * ‖P j - Q j‖ +
          ∑ l : Fin 3, ‖P l - Q l‖ ≤
          7 * (∑ l : Fin 3, ‖P l - Q l‖) := by
        calc
          _ ≤ 3 * (∑ l : Fin 3, ‖P l - Q l‖) +
              3 * (∑ l : Fin 3, ‖P l - Q l‖) +
                ∑ l : Fin 3, ‖P l - Q l‖ := by
            gcongr
            · exact Finset.single_le_sum
                (s := (Finset.univ : Finset (Fin 3)))
                (f := fun l : Fin 3 => ‖P l - Q l‖)
                (fun l _ => norm_nonneg _) (Finset.mem_univ i)
            · exact Finset.single_le_sum
                (s := (Finset.univ : Finset (Fin 3)))
                (f := fun l : Fin 3 => ‖P l - Q l‖)
                (fun l _ => norm_nonneg _) (Finset.mem_univ j)
          _ = 7 * (∑ l : Fin 3, ‖P l - Q l‖) := by ring
      have hsumQ : 3 * ‖Q i‖ + 3 * ‖Q j‖ +
          ∑ l : Fin 3, ‖Q l‖ ≤
          7 * (∑ l : Fin 3, ‖Q l‖) := by
        calc
          _ ≤ 3 * (∑ l : Fin 3, ‖Q l‖) +
              3 * (∑ l : Fin 3, ‖Q l‖) +
                ∑ l : Fin 3, ‖Q l‖ := by
            gcongr
            · exact Finset.single_le_sum
                (s := (Finset.univ : Finset (Fin 3)))
                (f := fun l : Fin 3 => ‖Q l‖)
                (fun l _ => norm_nonneg _) (Finset.mem_univ i)
            · exact Finset.single_le_sum
                (s := (Finset.univ : Finset (Fin 3)))
                (f := fun l : Fin 3 => ‖Q l‖)
                (fun l _ => norm_nonneg _) (Finset.mem_univ j)
          _ = 7 * (∑ l : Fin 3, ‖Q l‖) := by ring
      have hnonneg : 0 ≤ (4 / c^2) * ‖A - B‖ := by positivity
      have hnonneg2 : 0 ≤ (2 / c^2) * ‖A - B‖ := by positivity
      have hcpos : 0 ≤ (1 / c) := by positivity
      calc
        (1 / c) *
              (3 * ‖P i - Q i‖ + 3 * ‖P j - Q j‖ +
                ∑ l : Fin 3, ‖P l - Q l‖) +
            (2 / c^2) * ‖A - B‖ *
              (3 * ‖Q i‖ + 3 * ‖Q j‖ + ∑ l : Fin 3, ‖Q l‖) ≤
          (1 / c) * (7 * (∑ l : Fin 3, ‖P l - Q l‖)) +
            (2 / c^2) * ‖A - B‖ * (7 * (∑ l : Fin 3, ‖Q l‖)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hsumP hcpos)
            (mul_le_mul_of_nonneg_left hsumQ hnonneg2)
        _ = (7 / c) * (∑ l : Fin 3, ‖P l - Q l‖) +
            (14 / c^2) * ‖A - B‖ * (∑ l : Fin 3, ‖Q l‖) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
