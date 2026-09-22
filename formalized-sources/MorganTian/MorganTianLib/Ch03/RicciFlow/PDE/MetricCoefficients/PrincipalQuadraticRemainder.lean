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
/-- Quantitative Taylor remainder of the actual principal contraction in both inputs. -/
theorem principal_quadratic_remainder (A H : E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hH : ‖H‖≤c/2) (Q R : Fin 3 → Fin 3 → E6) :
    ‖(∑ i : Fin 3, ∑ j : Fin 3, ((A+H).inverse (EuclideanSpace.single j 1)) i • (Q i j+R i j)) -
      (∑ i : Fin 3, ∑ j : Fin 3, (A.inverse (EuclideanSpace.single j 1)) i • Q i j) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        (((-(A.inverse.comp (H.comp A.inverse))) (EuclideanSpace.single j 1)) i • Q i j +
        (A.inverse (EuclideanSpace.single j 1)) i • R i j))‖ ≤
      (2/c^3)*‖H‖^2*(∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j‖) +
      (2/c^2)*‖H‖*(∑ i : Fin 3, ∑ j : Fin 3, ‖R i j‖) :=
/- SWARM_PROOF_BEGIN -/
by
  have hAH : ∀ v : E3, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ ((A + H) v) v := by
    apply coercivity_survives_operator_perturbation A (A + H) c hc hA
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hH
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨a, ha, ha_bound⟩ := coercive_operator_inverse A c hc hA
  obtain ⟨b, hb, hb_bound⟩ := coercive_operator_inverse (A + H) (c / 2) hc2 hAH
  have hAinv : ContinuousLinearMap.IsInvertible A := ⟨a, ha⟩
  have hAHinv : ContinuousLinearMap.IsInvertible (A + H) := ⟨b, hb⟩
  have hA_bound : ‖A.inverse‖ ≤ 1 / c := by
    rw [← ha]
    simpa using ha_bound
  have hAH_bound : ‖(A + H).inverse‖ ≤ 2 / c := by
    rw [← hb]
    rw [ContinuousLinearMap.inverse_equiv]
    calc
      ‖b.symm.toContinuousLinearMap‖ ≤ 1 / (c / 2) := hb_bound
      _ = 2 / c := by field_simp
  have hresolvent :
      A.inverse = (A + H).inverse +
        A.inverse.comp (H.comp (A + H).inverse) := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      A.inverse x = A.inverse ((A + H) ((A + H).inverse x)) := by
        rw [hAHinv.self_apply_inverse]
      _ = A.inverse (A ((A + H).inverse x)) +
          A.inverse (H ((A + H).inverse x)) := by
        simp only [map_add, add_apply]
      _ = (A + H).inverse x + A.inverse (H ((A + H).inverse x)) := by
        rw [hAinv.inverse_apply_self]
      _ = ((A + H).inverse +
          A.inverse.comp (H.comp (A + H).inverse)) x := by
        simp only [add_apply, ContinuousLinearMap.comp_apply]
  have hdiff :
      ‖(A + H).inverse - A.inverse‖ ≤ (2 / c^2) * ‖H‖ := by
    have heq :
        (A + H).inverse - A.inverse =
          -(A.inverse.comp (H.comp (A + H).inverse)) := by
      calc
        (A + H).inverse - A.inverse =
            (A + H).inverse -
              ((A + H).inverse + A.inverse.comp (H.comp (A + H).inverse)) :=
          congrArg (fun T => (A + H).inverse - T) hresolvent
        _ = -(A.inverse.comp (H.comp (A + H).inverse)) := by abel
    rw [heq, norm_neg]
    calc
      ‖A.inverse.comp (H.comp (A + H).inverse)‖ ≤
          ‖A.inverse‖ * ‖H.comp (A + H).inverse‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A.inverse‖ * (‖H‖ * ‖(A + H).inverse‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / c) * (‖H‖ * ‖(A + H).inverse‖) :=
        mul_le_mul_of_nonneg_right hA_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ (1 / c) * (‖H‖ * (2 / c)) := by
        gcongr
      _ = (2 / c^2) * ‖H‖ := by field_simp
  have hquad :
      ‖(A + H).inverse - A.inverse +
          A.inverse.comp (H.comp A.inverse)‖ ≤
        (2 / c^3) * ‖H‖^2 :=
    coercive_inverse_quadratic_remainder A H c hc hA hH
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
  have hQcoef : ∀ i j : Fin 3,
      ‖((A + H).inverse - A.inverse +
          A.inverse.comp (H.comp A.inverse))
          (EuclideanSpace.single j 1) i‖ ≤
        (2 / c^3) * ‖H‖^2 := by
    intro i j
    calc
      ‖((A + H).inverse - A.inverse +
          A.inverse.comp (H.comp A.inverse))
          (EuclideanSpace.single j 1) i‖ ≤
          ‖((A + H).inverse - A.inverse +
            A.inverse.comp (H.comp A.inverse))
            (EuclideanSpace.single j 1)‖ := hcoord _ _
      _ ≤ ‖(A + H).inverse - A.inverse +
            A.inverse.comp (H.comp A.inverse)‖ *
            ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖(A + H).inverse - A.inverse +
            A.inverse.comp (H.comp A.inverse)‖ := by simp
      _ ≤ (2 / c^3) * ‖H‖^2 := hquad
  have hRcoef : ∀ i j : Fin 3,
      ‖((A + H).inverse - A.inverse)
          (EuclideanSpace.single j 1) i‖ ≤
        (2 / c^2) * ‖H‖ := by
    intro i j
    calc
      ‖((A + H).inverse - A.inverse)
          (EuclideanSpace.single j 1) i‖ ≤
          ‖((A + H).inverse - A.inverse)
            (EuclideanSpace.single j 1)‖ := hcoord _ _
      _ ≤ ‖(A + H).inverse - A.inverse‖ *
            ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖(A + H).inverse - A.inverse‖ := by simp
      _ ≤ (2 / c^2) * ‖H‖ := hdiff
  have hterm : ∀ i j : Fin 3,
      ‖((A + H).inverse - A.inverse +
          A.inverse.comp (H.comp A.inverse))
          (EuclideanSpace.single j 1) i • Q i j +
        ((A + H).inverse - A.inverse)
          (EuclideanSpace.single j 1) i • R i j‖ ≤
        (2 / c^3) * ‖H‖^2 * ‖Q i j‖ +
          (2 / c^2) * ‖H‖ * ‖R i j‖ := by
    intro i j
    calc
      ‖((A + H).inverse - A.inverse +
          A.inverse.comp (H.comp A.inverse))
          (EuclideanSpace.single j 1) i • Q i j +
        ((A + H).inverse - A.inverse)
          (EuclideanSpace.single j 1) i • R i j‖ ≤
          ‖((A + H).inverse - A.inverse +
              A.inverse.comp (H.comp A.inverse))
              (EuclideanSpace.single j 1) i • Q i j‖ +
            ‖((A + H).inverse - A.inverse)
              (EuclideanSpace.single j 1) i • R i j‖ := norm_add_le _ _
      _ = ‖((A + H).inverse - A.inverse +
              A.inverse.comp (H.comp A.inverse))
              (EuclideanSpace.single j 1) i‖ * ‖Q i j‖ +
            ‖((A + H).inverse - A.inverse)
              (EuclideanSpace.single j 1) i‖ * ‖R i j‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ (2 / c^3) * ‖H‖^2 * ‖Q i j‖ +
          (2 / c^2) * ‖H‖ * ‖R i j‖ := by
        gcongr
        · exact hQcoef i j
        · exact hRcoef i j
  have hsum :
      ‖∑ i : Fin 3, ∑ j : Fin 3,
          (((A + H).inverse - A.inverse +
              A.inverse.comp (H.comp A.inverse))
              (EuclideanSpace.single j 1) i • Q i j +
            ((A + H).inverse - A.inverse)
              (EuclideanSpace.single j 1) i • R i j)‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((2 / c^3) * ‖H‖^2 * ‖Q i j‖ +
            (2 / c^2) * ‖H‖ * ‖R i j‖) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
          (((A + H).inverse - A.inverse +
              A.inverse.comp (H.comp A.inverse))
              (EuclideanSpace.single j 1) i • Q i j +
            ((A + H).inverse - A.inverse)
              (EuclideanSpace.single j 1) i • R i j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ‖((A + H).inverse - A.inverse +
              A.inverse.comp (H.comp A.inverse))
              (EuclideanSpace.single j 1) i • Q i j +
            ((A + H).inverse - A.inverse)
              (EuclideanSpace.single j 1) i • R i j‖ := by
        gcongr with i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          ((2 / c^3) * ‖H‖^2 * ‖Q i j‖ +
            (2 / c^2) * ‖H‖ * ‖R i j‖) := by
        gcongr with i hi j hj
        exact hterm i j
  have hrewrite :
      (∑ i : Fin 3, ∑ j : Fin 3,
          ((A + H).inverse (EuclideanSpace.single j 1)) i •
            (Q i j + R i j)) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          (A.inverse (EuclideanSpace.single j 1)) i • Q i j) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          (((-(A.inverse.comp (H.comp A.inverse)))
              (EuclideanSpace.single j 1)) i • Q i j +
            (A.inverse (EuclideanSpace.single j 1)) i • R i j)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (((A + H).inverse - A.inverse +
            A.inverse.comp (H.comp A.inverse))
            (EuclideanSpace.single j 1) i • Q i j +
          ((A + H).inverse - A.inverse)
            (EuclideanSpace.single j 1) i • R i j) := by
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext i
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext j
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      smul_add, WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_neg,
      Pi.neg_apply]
    change _ =
      (((A + H).inverse (EuclideanSpace.single j 1)).ofLp i -
          (A.inverse (EuclideanSpace.single j 1)).ofLp i +
          (A.inverse (H (A.inverse (EuclideanSpace.single j 1)))).ofLp i) •
          Q i j +
        (((A + H).inverse (EuclideanSpace.single j 1)).ofLp i -
          (A.inverse (EuclideanSpace.single j 1)).ofLp i) • R i j
    module
  rw [hrewrite]
  calc
    ‖∑ i : Fin 3, ∑ j : Fin 3,
        (((A + H).inverse - A.inverse +
            A.inverse.comp (H.comp A.inverse))
            (EuclideanSpace.single j 1) i • Q i j +
          ((A + H).inverse - A.inverse)
            (EuclideanSpace.single j 1) i • R i j)‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((2 / c^3) * ‖H‖^2 * ‖Q i j‖ +
            (2 / c^2) * ‖H‖ * ‖R i j‖) := hsum
    _ = (2 / c^3) * ‖H‖^2 *
          (∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j‖) +
        (2 / c^2) * ‖H‖ *
          (∑ i : Fin 3, ∑ j : Fin 3, ‖R i j‖) := by
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
