import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The inverse-differentiation part of the actual Christoffel spatial derivative. -/
def lowerConnectionJet (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (r k i j : Fin 3) : ℝ := (1/2:ℝ)*∑ l : Fin 3,
      (((-(A.inverse.comp ((P r).comp A.inverse))) (EuclideanSpace.single l 1)) k *
        ((P i (EuclideanSpace.single l 1)) j+(P j (EuclideanSpace.single l 1)) i-
          (P l (EuclideanSpace.single j 1)) i))
/-- Uniform quadratic-in-first-jets control with an explicit coercivity constant. -/
theorem lower_connection_jet_bound (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (r k i j : Fin 3) :
    |lowerConnectionJet A P r k i j| ≤ (5/c^2)*‖P r‖*(∑ l : Fin 3, ‖P l‖) :=
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
  have hAinv : ‖A.inverse‖ ≤ 1 / c := by
    simpa [hAi] using he_inv
  have hAcoef : ∀ l q : Fin 3,
      |((-(A.inverse.comp ((P r).comp A.inverse)))
          (EuclideanSpace.single l 1)) q| ≤
        (1 / c) ^ 2 * ‖P r‖ := by
    intro l q
    calc
      |((-(A.inverse.comp ((P r).comp A.inverse)))
          (EuclideanSpace.single l 1)) q| =
          ‖((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single l 1)) q‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single l 1))‖ := hcoord _ _
      _ ≤ ‖(-(A.inverse.comp ((P r).comp A.inverse)))‖ *
            ‖EuclideanSpace.single l (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse.comp ((P r).comp A.inverse)‖ := by simp
      _ ≤ ‖A.inverse‖ * ‖(P r).comp A.inverse‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A.inverse‖ * (‖P r‖ * ‖A.inverse‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / c) * (‖P r‖ * (1 / c)) := by
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
  have hbracket : ∀ l : Fin 3,
      |(P i (EuclideanSpace.single l 1)) j +
          (P j (EuclideanSpace.single l 1)) i -
            (P l (EuclideanSpace.single j 1)) i| ≤
        ‖P i‖ + ‖P j‖ + ‖P l‖ := by
    intro l
    calc
      |(P i (EuclideanSpace.single l 1)) j +
          (P j (EuclideanSpace.single l 1)) i -
            (P l (EuclideanSpace.single j 1)) i| ≤
          |(P i (EuclideanSpace.single l 1)) j| +
            |(P j (EuclideanSpace.single l 1)) i| +
              |(P l (EuclideanSpace.single j 1)) i| := by
        calc
          |(P i (EuclideanSpace.single l 1)) j +
              (P j (EuclideanSpace.single l 1)) i -
                (P l (EuclideanSpace.single j 1)) i| =
              |((P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i) +
                  (-((P l (EuclideanSpace.single j 1)) i))| := by
            congr 1
          _ ≤ |(P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i| +
                |-(P l (EuclideanSpace.single j 1)) i| := abs_add_le _ _
          _ = |(P i (EuclideanSpace.single l 1)) j +
                (P j (EuclideanSpace.single l 1)) i| +
                |(P l (EuclideanSpace.single j 1)) i| := by rw [abs_neg]
          _ ≤ |(P i (EuclideanSpace.single l 1)) j| +
                |(P j (EuclideanSpace.single l 1)) i| +
                |(P l (EuclideanSpace.single j 1)) i| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ ‖P i‖ + ‖P j‖ + ‖P l‖ := by
        exact add_le_add (add_le_add (hPcoef i l j) (hPcoef j l i))
          (hPcoef l j i)
  have hterm : ∀ l : Fin 3,
      |((-(A.inverse.comp ((P r).comp A.inverse)))
          (EuclideanSpace.single l 1)) k *
          ((P i (EuclideanSpace.single l 1)) j +
            (P j (EuclideanSpace.single l 1)) i -
              (P l (EuclideanSpace.single j 1)) i)| ≤
        ((1 / c) ^ 2 * ‖P r‖) *
          (‖P i‖ + ‖P j‖ + ‖P l‖) := by
    intro l
    rw [abs_mul]
    exact mul_le_mul (hAcoef l k) (hbracket l) (abs_nonneg _) (by positivity)
  rw [lowerConnectionJet]
  calc
    |(1 / 2 : ℝ) * ∑ l : Fin 3,
        ((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single l 1)) k *
          ((P i (EuclideanSpace.single l 1)) j +
            (P j (EuclideanSpace.single l 1)) i -
              (P l (EuclideanSpace.single j 1)) i)| =
        (1 / 2 : ℝ) * |∑ l : Fin 3,
          ((-(A.inverse.comp ((P r).comp A.inverse)))
              (EuclideanSpace.single l 1)) k *
            ((P i (EuclideanSpace.single l 1)) j +
              (P j (EuclideanSpace.single l 1)) i -
                (P l (EuclideanSpace.single j 1)) i)| := by
      rw [abs_mul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * ∑ l : Fin 3,
        |((-(A.inverse.comp ((P r).comp A.inverse)))
            (EuclideanSpace.single l 1)) k *
          ((P i (EuclideanSpace.single l 1)) j +
            (P j (EuclideanSpace.single l 1)) i -
              (P l (EuclideanSpace.single j 1)) i)| := by
      gcongr
      simpa [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun l : Fin 3 =>
          ((-(A.inverse.comp ((P r).comp A.inverse)))
              (EuclideanSpace.single l 1)) k *
            ((P i (EuclideanSpace.single l 1)) j +
              (P j (EuclideanSpace.single l 1)) i -
                (P l (EuclideanSpace.single j 1)) i)))
    _ ≤ (1 / 2 : ℝ) * ∑ l : Fin 3,
        ((1 / c) ^ 2 * ‖P r‖) *
          (‖P i‖ + ‖P j‖ + ‖P l‖) := by
      gcongr with l hl
      exact hterm l
    _ = (1 / (2 * c ^ 2)) * ‖P r‖ *
        (3 * ‖P i‖ + 3 * ‖P j‖ + ∑ l : Fin 3, ‖P l‖) := by
      rw [← Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ (5 / c ^ 2) * ‖P r‖ * (∑ l : Fin 3, ‖P l‖) := by
      have hsum : 0 ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.sum_nonneg (fun l _ => norm_nonneg _)
      have hPi : ‖P i‖ ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun l : Fin 3 => ‖P l‖)
          (fun l _ => norm_nonneg _) (Finset.mem_univ i)
      have hPj : ‖P j‖ ≤ ∑ l : Fin 3, ‖P l‖ :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun l : Fin 3 => ‖P l‖)
          (fun l _ => norm_nonneg _) (Finset.mem_univ j)
      have hinside : 3 * ‖P i‖ + 3 * ‖P j‖ +
          ∑ l : Fin 3, ‖P l‖ ≤ 7 * (∑ l : Fin 3, ‖P l‖) := by
        nlinarith
      have hcoef : (1 / (2 * c ^ 2)) * 7 ≤ 5 / c ^ 2 := by
        have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
        field_simp
        nlinarith
      calc
        (1 / (2 * c ^ 2)) * ‖P r‖ *
            (3 * ‖P i‖ + 3 * ‖P j‖ + ∑ l : Fin 3, ‖P l‖) ≤
            (1 / (2 * c ^ 2)) * ‖P r‖ *
              (7 * (∑ l : Fin 3, ‖P l‖)) := by
                gcongr
        _ = ((1 / (2 * c ^ 2)) * 7) * ‖P r‖ *
              (∑ l : Fin 3, ‖P l‖) := by ring
        _ ≤ (5 / c ^ 2) * ‖P r‖ *
              (∑ l : Fin 3, ‖P l‖) := by
                gcongr
  
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
