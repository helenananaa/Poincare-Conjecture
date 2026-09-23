import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalPartDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- **Math.** frozen principal difference. -/
theorem frozen_principal_difference (A0 A B : E3 →L[ℝ] E3) (c : ℝ) (hc : 0 < c)
    (hA0 : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v)
    (hA : ‖A-A0‖ ≤ c/2) (hB : ‖B-A0‖ ≤ c/2)
    (Q R : Fin 3 → Fin 3 → E6) :
    ‖(∑ i : Fin 3, ∑ j : Fin 3, ((A.inverse-A0.inverse) (EuclideanSpace.single j 1)) i • Q i j) -
      (∑ i : Fin 3, ∑ j : Fin 3, ((B.inverse-A0.inverse) (EuclideanSpace.single j 1)) i • R i j)‖ ≤
      (4/c^2)*‖A-A0‖*(∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j-R i j‖) +
      (4/c^2)*‖A-B‖*(∑ i : Fin 3, ∑ j : Fin 3, ‖R i j‖) :=
/- SWARM_PROOF_BEGIN -/
by
  have hA0ball : ‖A0 - A0‖ ≤ c / 2 := by
    simpa using (le_of_lt (half_pos hc))
  obtain ⟨a, a0, ha, ha0, ha_inv, ha0_inv, haa0_inv⟩ :=
    positive_ball_inverse_control A0 c hc hA0 A A0 hA hA0ball
  obtain ⟨a', b, ha', hb, ha'_inv, hb_inv, hab_inv⟩ :=
    positive_ball_inverse_control A0 c hc hA0 A B hA hB
  have hAi : A.inverse = a.symm.toContinuousLinearMap := by
    rw [← ha]
    exact ContinuousLinearMap.inverse_equiv a
  have hA'i : A.inverse = a'.symm.toContinuousLinearMap := by
    rw [← ha']
    exact ContinuousLinearMap.inverse_equiv a'
  have hA0i : A0.inverse = a0.symm.toContinuousLinearMap := by
    rw [← ha0]
    exact ContinuousLinearMap.inverse_equiv a0
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
  have hA0coef : ∀ i j : Fin 3,
      ‖(A.inverse - A0.inverse) (EuclideanSpace.single j 1) i‖ ≤
        (4 / c^2) * ‖A - A0‖ := by
    intro i j
    calc
      ‖(A.inverse - A0.inverse) (EuclideanSpace.single j 1) i‖ ≤
          ‖(A.inverse - A0.inverse) (EuclideanSpace.single j 1)‖ := hcoord _ _
      _ ≤ ‖A.inverse - A0.inverse‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse - A0.inverse‖ := by simp
      _ ≤ (4 / c^2) * ‖A - A0‖ := by simpa [hAi, hA0i] using haa0_inv
  have hABcoef : ∀ i j : Fin 3,
      ‖(A.inverse - B.inverse) (EuclideanSpace.single j 1) i‖ ≤
        (4 / c^2) * ‖A - B‖ := by
    intro i j
    calc
      ‖(A.inverse - B.inverse) (EuclideanSpace.single j 1) i‖ ≤
          ‖(A.inverse - B.inverse) (EuclideanSpace.single j 1)‖ := hcoord _ _
      _ ≤ ‖A.inverse - B.inverse‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖A.inverse - B.inverse‖ := by simp
      _ ≤ (4 / c^2) * ‖A - B‖ := by simpa [hA'i, hBi] using hab_inv
  have hterm : ∀ i j : Fin 3,
      ‖((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j -
          ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j‖ ≤
        (4 / c^2) * ‖A - A0‖ * ‖Q i j - R i j‖ +
          (4 / c^2) * ‖A - B‖ * ‖R i j‖ := by
    intro i j
    have hcoeff :
        ((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i -
            ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i =
          ((A.inverse - B.inverse) (EuclideanSpace.single j 1)) i := by
      have hvec :
          (A.inverse - A0.inverse) (EuclideanSpace.single j 1) -
              (B.inverse - A0.inverse) (EuclideanSpace.single j 1) =
            (A.inverse - B.inverse) (EuclideanSpace.single j 1) := by
        simp only [ContinuousLinearMap.sub_apply]
        abel
      exact congrArg (fun x : E3 => x i) hvec
    calc
      ‖((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j -
          ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j‖ =
          ‖((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • (Q i j - R i j) +
            (((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i -
              ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i) • R i j‖ := by
        congr 1
        module
      _ ≤ ‖((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • (Q i j - R i j)‖ +
          ‖(((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i -
            ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i) • R i j‖ := norm_add_le _ _
      _ = ‖((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i‖ * ‖Q i j - R i j‖ +
          ‖((A.inverse - B.inverse) (EuclideanSpace.single j 1)) i‖ * ‖R i j‖ := by
        rw [norm_smul, norm_smul]
        rw [hcoeff]
      _ ≤ (4 / c^2) * ‖A - A0‖ * ‖Q i j - R i j‖ +
          (4 / c^2) * ‖A - B‖ * ‖R i j‖ := by
        gcongr
        · exact hA0coef i j
        · exact hABcoef i j
  have hsum :
      ‖∑ i : Fin 3, ∑ j : Fin 3,
          (((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j -
            ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j)‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((4 / c^2) * ‖A - A0‖ * ‖Q i j - R i j‖ +
            (4 / c^2) * ‖A - B‖ * ‖R i j‖) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
          (((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j -
            ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ‖((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j -
            ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j‖ := by
        gcongr with i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ((4 / c^2) * ‖A - A0‖ * ‖Q i j - R i j‖ +
            (4 / c^2) * ‖A - B‖ * ‖R i j‖) := by
        gcongr with i hi j hj
        exact hterm i j
  have hrewrite :
      (∑ i : Fin 3, ∑ j : Fin 3,
          ((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j -
          ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext i
    rw [← Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    ‖∑ i : Fin 3, ∑ j : Fin 3,
        (((A.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q i j -
          ((B.inverse - A0.inverse) (EuclideanSpace.single j 1)) i • R i j)‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((4 / c^2) * ‖A - A0‖ * ‖Q i j - R i j‖ +
            (4 / c^2) * ‖A - B‖ * ‖R i j‖) := hsum
    _ = (4 / c^2) * ‖A - A0‖ *
          (∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j - R i j‖) +
        (4 / c^2) * ‖A - B‖ *
          (∑ i : Fin 3, ∑ j : Fin 3, ‖R i j‖) := by
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
