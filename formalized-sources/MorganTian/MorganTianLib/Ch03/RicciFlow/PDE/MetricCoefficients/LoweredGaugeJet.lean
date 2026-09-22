import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Inverse-metric differentiation in the lowered gauge; genuinely quadratic in first jets. -/
def loweredGaugeJet (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (r j : Fin 3) : ℝ := (1/2:ℝ)*(∑ p : Fin 3, ∑ q : Fin 3,
      (((-(A.inverse.comp ((P r).comp A.inverse))) (EuclideanSpace.single q 1)) p *
        ((P p (EuclideanSpace.single q 1)) j +
         (P q (EuclideanSpace.single p 1)) j - (P j (EuclideanSpace.single q 1)) p)))
/-- The inverse-differentiation contribution is controlled without any second derivatives. -/
theorem lowered_gauge_jet_bound (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (r j : Fin 3) :
    |loweredGaugeJet A P r j| ≤ (10/c^2)*‖P r‖*(∑ l : Fin 3, ‖P l‖) :=
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
  have hAcoef : ∀ p q : Fin 3,
      |((-(A.inverse.comp ((P r).comp A.inverse)))
          (EuclideanSpace.single q 1)) p| ≤
        (1 / c) ^ 2 * ‖P r‖ := by
    intro p q
    calc
      |((-(A.inverse.comp ((P r).comp A.inverse)))
          (EuclideanSpace.single q 1)) p| =
          ‖((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single q 1)) p‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single q 1))‖ := hcoord _ _
      _ ≤ ‖(-(A.inverse.comp ((P r).comp A.inverse)))‖ *
            ‖EuclideanSpace.single q (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse.comp ((P r).comp A.inverse)‖ := by simp
      _ ≤ ‖A.inverse‖ * ‖(P r).comp A.inverse‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A.inverse‖ * (‖P r‖ * ‖A.inverse‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / c) * (‖P r‖ * (1 / c)) := by
        have hAinv : ‖A.inverse‖ ≤ 1 / c := by
          simpa [hAi] using he_inv
        gcongr
      _ = (1 / c) ^ 2 * ‖P r‖ := by ring
  have hPcoef : ∀ s l q : Fin 3,
      |(P s (EuclideanSpace.single l 1)) q| ≤ ‖P s‖ := by
    intro s l q
    calc
      |(P s (EuclideanSpace.single l 1)) q| =
          ‖(P s (EuclideanSpace.single l 1)) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖P s (EuclideanSpace.single l 1)‖ := hcoord _ _
      _ ≤ ‖P s‖ * ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖P s‖ := by simp
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
      |((-(A.inverse.comp ((P r).comp A.inverse)))
          (EuclideanSpace.single q 1)) p *
          ((P p (EuclideanSpace.single q 1)) j +
            (P q (EuclideanSpace.single p 1)) j -
              (P j (EuclideanSpace.single q 1)) p)| ≤
        ((1 / c) ^ 2 * ‖P r‖) *
          (‖P p‖ + ‖P q‖ + ‖P j‖) := by
    intro p q
    rw [abs_mul]
    exact mul_le_mul (hAcoef p q) (hbracket p q) (abs_nonneg _) (by positivity)
  rw [loweredGaugeJet]
  calc
    |(1 / 2 : ℝ) * ∑ p : Fin 3, ∑ q : Fin 3,
        ((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single q 1)) p *
          ((P p (EuclideanSpace.single q 1)) j +
            (P q (EuclideanSpace.single p 1)) j -
              (P j (EuclideanSpace.single q 1)) p)| =
        (1 / 2 : ℝ) * |∑ p : Fin 3, ∑ q : Fin 3,
          ((-(A.inverse.comp ((P r).comp A.inverse)))
              (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)| := by
      rw [abs_mul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * ∑ p : Fin 3, ∑ q : Fin 3,
        |((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single q 1)) p *
          ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
              (P j (EuclideanSpace.single q 1)) p)| := by
      gcongr
      calc
        |∑ p : Fin 3, ∑ q : Fin 3,
            ((-(A.inverse.comp ((P r).comp A.inverse)))
                (EuclideanSpace.single q 1)) p *
              ((P p (EuclideanSpace.single q 1)) j +
                (P q (EuclideanSpace.single p 1)) j -
                  (P j (EuclideanSpace.single q 1)) p)| ≤
            ∑ p : Fin 3, |∑ q : Fin 3,
              ((-(A.inverse.comp ((P r).comp A.inverse)))
                  (EuclideanSpace.single q 1)) p *
                ((P p (EuclideanSpace.single q 1)) j +
                  (P q (EuclideanSpace.single p 1)) j -
                    (P j (EuclideanSpace.single q 1)) p)| := by
              simpa [Real.norm_eq_abs] using
                (norm_sum_le (Finset.univ : Finset (Fin 3))
                  (fun p : Fin 3 => ∑ q : Fin 3,
                    ((-(A.inverse.comp ((P r).comp A.inverse)))
                        (EuclideanSpace.single q 1)) p *
                      ((P p (EuclideanSpace.single q 1)) j +
                        (P q (EuclideanSpace.single p 1)) j -
                          (P j (EuclideanSpace.single q 1)) p)))
        _ ≤ ∑ p : Fin 3, ∑ q : Fin 3,
            |((-(A.inverse.comp ((P r).comp A.inverse)))
                (EuclideanSpace.single q 1)) p *
              ((P p (EuclideanSpace.single q 1)) j +
                (P q (EuclideanSpace.single p 1)) j -
                  (P j (EuclideanSpace.single q 1)) p)| := by
              gcongr with p hp
              simpa [Real.norm_eq_abs] using
                (norm_sum_le (Finset.univ : Finset (Fin 3))
                  (fun q : Fin 3 =>
                    ((-(A.inverse.comp ((P r).comp A.inverse)))
                        (EuclideanSpace.single q 1)) p *
                      ((P p (EuclideanSpace.single q 1)) j +
                        (P q (EuclideanSpace.single p 1)) j -
                          (P j (EuclideanSpace.single q 1)) p)))
    _ ≤ (1 / 2 : ℝ) * ∑ p : Fin 3, ∑ q : Fin 3,
        ((1 / c) ^ 2 * ‖P r‖) *
          (‖P p‖ + ‖P q‖ + ‖P j‖) := by
      gcongr with p hp q hq
      exact hterm p q
    _ = (1 / (2 * c ^ 2)) * ‖P r‖ *
        (3 * (∑ p : Fin 3, ‖P p‖) +
          3 * (∑ q : Fin 3, ‖P q‖) + 9 * ‖P j‖) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ (10 / c ^ 2) * ‖P r‖ * (∑ l : Fin 3, ‖P l‖) := by
      have hsum : 0 ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.sum_nonneg (fun l _ => norm_nonneg _)
      have hPj : ‖P j‖ ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun l : Fin 3 => ‖P l‖)
          (fun l _ => norm_nonneg _) (Finset.mem_univ j)
      have hinside : 3 * (∑ p : Fin 3, ‖P p‖) +
          3 * (∑ q : Fin 3, ‖P q‖) + 9 * ‖P j‖ ≤
          15 * (∑ l : Fin 3, ‖P l‖) := by
        nlinarith
      have hcoef : (1 / (2 * c ^ 2)) * 15 ≤ 10 / c ^ 2 := by
        have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
        field_simp
        nlinarith
      calc
        (1 / (2 * c ^ 2)) * ‖P r‖ *
            (3 * (∑ p : Fin 3, ‖P p‖) +
              3 * (∑ q : Fin 3, ‖P q‖) + 9 * ‖P j‖) ≤
            (1 / (2 * c ^ 2)) * ‖P r‖ *
              (15 * (∑ l : Fin 3, ‖P l‖)) := by
                gcongr
        _ = ((1 / (2 * c ^ 2)) * 15) * ‖P r‖ *
              (∑ l : Fin 3, ‖P l‖) := by ring
        _ ≤ (10 / c ^ 2) * ‖P r‖ *
              (∑ l : Fin 3, ‖P l‖) := by
                gcongr
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
