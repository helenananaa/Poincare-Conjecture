import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Quantitative control of the actual six-component principal coefficient contraction. -/
theorem inverse_metric_principal_difference (A0 A B : E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA0 : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v)
    (hA : ‖A-A0‖ ≤ c/2) (hB : ‖B-A0‖ ≤ c/2)
    (Q R : Fin 3 → Fin 3 → E6) :
    ‖(∑ i : Fin 3, ∑ j : Fin 3, (A.inverse (EuclideanSpace.single j 1)) i • Q i j)-
      (∑ i : Fin 3, ∑ j : Fin 3, (B.inverse (EuclideanSpace.single j 1)) i • R i j)‖ ≤
      (2/c)*(∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j-R i j‖)+
      (4/c^2)*‖A-B‖*(∑ i : Fin 3, ∑ j : Fin 3, ‖R i j‖) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨a, b, ha, hb, ha_inv, hb_inv, hab_inv⟩ :=
    positive_ball_inverse_control A0 c hc hA0 A B hA hB
  have hAi : A.inverse = a.symm.toContinuousLinearMap := by
    rw [← ha]
    exact ContinuousLinearMap.inverse_equiv a
  have hBi : B.inverse = b.symm.toContinuousLinearMap := by
    rw [← hb]
    exact ContinuousLinearMap.inverse_equiv b
  have hcoord : ∀ x : E3, ∀ i : Fin 3, ‖x i‖ ≤ ‖x‖ := by
    intro x i
    rw [EuclideanSpace.norm_eq]
    have hnonneg : 0 ≤ ∑ k : Fin 3, ‖x.ofLp k‖ ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    apply (Real.le_sqrt (norm_nonneg _) hnonneg).2
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun k : Fin 3 => ‖x.ofLp k‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hAcoef : ∀ i j : Fin 3, ‖A.inverse (EuclideanSpace.single j 1) i‖ ≤ 2 / c := by
    intro i j
    calc
      ‖A.inverse (EuclideanSpace.single j 1) i‖ ≤
          ‖A.inverse (EuclideanSpace.single j 1)‖ := hcoord _ _
      _ ≤ ‖A.inverse‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse‖ := by simp
      _ ≤ 2 / c := by simpa [hAi] using ha_inv
  have hBcoef : ∀ i j : Fin 3, ‖B.inverse (EuclideanSpace.single j 1) i‖ ≤ 2 / c := by
    intro i j
    calc
      ‖B.inverse (EuclideanSpace.single j 1) i‖ ≤
          ‖B.inverse (EuclideanSpace.single j 1)‖ := hcoord _ _
      _ ≤ ‖B.inverse‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖B.inverse‖ := by simp
      _ ≤ 2 / c := by simpa [hBi] using hb_inv
  have hABcoef : ∀ i j : Fin 3,
      ‖(A.inverse - B.inverse) (EuclideanSpace.single j 1) i‖ ≤
        (4 / c^2) * ‖A - B‖ := by
    intro i j
    calc
      ‖(A.inverse - B.inverse) (EuclideanSpace.single j 1) i‖ ≤
          ‖(A.inverse - B.inverse) (EuclideanSpace.single j 1)‖ :=
        hcoord _ _
      _ ≤ ‖A.inverse - B.inverse‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse - B.inverse‖ := by simp
      _ ≤ (4 / c^2) * ‖A - B‖ := by simpa [hAi, hBi] using hab_inv
  have hterm : ∀ i j : Fin 3,
      ‖A.inverse (EuclideanSpace.single j 1) i • Q i j -
          B.inverse (EuclideanSpace.single j 1) i • R i j‖ ≤
        (2 / c) * ‖Q i j - R i j‖ +
          (4 / c^2) * ‖A - B‖ * ‖R i j‖ := by
    intro i j
    calc
      ‖A.inverse (EuclideanSpace.single j 1) i • Q i j -
          B.inverse (EuclideanSpace.single j 1) i • R i j‖ =
          ‖A.inverse (EuclideanSpace.single j 1) i • (Q i j - R i j) +
            (A.inverse (EuclideanSpace.single j 1) i -
              B.inverse (EuclideanSpace.single j 1) i) • R i j‖ := by
        congr 1
        module
      _ ≤ ‖A.inverse (EuclideanSpace.single j 1) i • (Q i j - R i j)‖ +
          ‖(A.inverse (EuclideanSpace.single j 1) i -
            B.inverse (EuclideanSpace.single j 1) i) • R i j‖ := norm_add_le _ _
      _ = ‖A.inverse (EuclideanSpace.single j 1) i‖ * ‖Q i j - R i j‖ +
          ‖(A.inverse - B.inverse) (EuclideanSpace.single j 1) i‖ * ‖R i j‖ := by
        rw [norm_smul, norm_smul]
        congr 2
      _ ≤ (2 / c) * ‖Q i j - R i j‖ +
          (4 / c^2) * ‖A - B‖ * ‖R i j‖ := by
        gcongr
        · exact hAcoef i j
        · exact hABcoef i j
  have hsum :
      ‖∑ i : Fin 3, ∑ j : Fin 3,
          (A.inverse (EuclideanSpace.single j 1) i • Q i j -
            B.inverse (EuclideanSpace.single j 1) i • R i j)‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((2 / c) * ‖Q i j - R i j‖ +
            (4 / c^2) * ‖A - B‖ * ‖R i j‖) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
          (A.inverse (EuclideanSpace.single j 1) i • Q i j -
            B.inverse (EuclideanSpace.single j 1) i • R i j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ‖A.inverse (EuclideanSpace.single j 1) i • Q i j -
            B.inverse (EuclideanSpace.single j 1) i • R i j‖ := by
        gcongr with i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ((2 / c) * ‖Q i j - R i j‖ +
            (4 / c^2) * ‖A - B‖ * ‖R i j‖) := by
        gcongr with i hi j hj
        exact hterm i j
  have hrewrite :
      (∑ i : Fin 3, ∑ j : Fin 3,
          A.inverse (EuclideanSpace.single j 1) i • Q i j) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          B.inverse (EuclideanSpace.single j 1) i • R i j) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (A.inverse (EuclideanSpace.single j 1) i • Q i j -
          B.inverse (EuclideanSpace.single j 1) i • R i j) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext i
    rw [← Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    ‖∑ i : Fin 3, ∑ j : Fin 3,
        (A.inverse (EuclideanSpace.single j 1) i • Q i j -
          B.inverse (EuclideanSpace.single j 1) i • R i j)‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((2 / c) * ‖Q i j - R i j‖ +
            (4 / c^2) * ‖A - B‖ * ‖R i j‖) := hsum
    _ = (2 / c) * (∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j-R i j‖)+
          (4/c^2)*‖A-B‖*(∑ i : Fin 3, ∑ j : Fin 3, ‖R i j‖) := by
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
