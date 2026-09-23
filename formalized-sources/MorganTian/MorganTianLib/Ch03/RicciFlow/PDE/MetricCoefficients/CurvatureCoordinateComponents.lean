import MorganTianLib.Ch01.CurvatureCommutation
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BilinearEvaluationDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** curvature coordinate components. -/
theorem curvature_coordinate_components (Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3) (x : E3)
    (hΓ : DifferentiableAt ℝ Γ x) (i j l k : Fin 3) :
    let e := fun a : Fin 3 => EuclideanSpace.single a (1 : ℝ);
    (MorganTianLib.christoffelCurvature Γ x (e i) (e j) (e l)) k =
      fderiv ℝ (fun y : E3 => (Γ y (e j) (e l)) k) x (e i) -
      fderiv ℝ (fun y : E3 => (Γ y (e i) (e l)) k) x (e j) +
      ∑ m : Fin 3, ((Γ x (e i) (e m)) k * (Γ x (e j) (e l)) m -
        (Γ x (e j) (e m)) k * (Γ x (e i) (e l)) m) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  rw [bilinear_evaluation_fderiv Γ x (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) hΓ k]
  rw [bilinear_evaluation_fderiv Γ x (EuclideanSpace.single j (1 : ℝ))
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) hΓ k]
  unfold christoffelCurvature
  have hdecomp (v : E3) :
      v = ∑ m : Fin 3, (v m) • EuclideanSpace.single m (1 : ℝ) := by
    ext a
    simp [Pi.single_apply]
  have hfirst :
      (Γ x (EuclideanSpace.single i (1 : ℝ))
        (Γ x (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)))) k =
      ∑ m : Fin 3,
        ((Γ x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single m (1 : ℝ))) k *
          (Γ x (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ))) m) := by
    calc
      _ = (Γ x (EuclideanSpace.single i (1 : ℝ))
            (∑ m : Fin 3,
              (Γ x (EuclideanSpace.single j (1 : ℝ))
                (EuclideanSpace.single l (1 : ℝ))) m • EuclideanSpace.single m (1 : ℝ))) k := by
          conv_lhs =>
            rw [hdecomp (Γ x (EuclideanSpace.single j (1 : ℝ))
              (EuclideanSpace.single l (1 : ℝ)))]
      _ = ∑ m : Fin 3,
            ((Γ x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single m (1 : ℝ))) k *
              (Γ x (EuclideanSpace.single j (1 : ℝ))
                (EuclideanSpace.single l (1 : ℝ))) m) := by
          simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro m hm
          ring
  have hsecond :
      (Γ x (EuclideanSpace.single j (1 : ℝ))
        (Γ x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)))) k =
      ∑ m : Fin 3,
        ((Γ x (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single m (1 : ℝ))) k *
          (Γ x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ))) m) := by
    calc
      _ = (Γ x (EuclideanSpace.single j (1 : ℝ))
            (∑ m : Fin 3,
              (Γ x (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single l (1 : ℝ))) m • EuclideanSpace.single m (1 : ℝ))) k := by
          conv_lhs =>
            rw [hdecomp (Γ x (EuclideanSpace.single i (1 : ℝ))
              (EuclideanSpace.single l (1 : ℝ)))]
      _ = ∑ m : Fin 3,
            ((Γ x (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single m (1 : ℝ))) k *
              (Γ x (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single l (1 : ℝ))) m) := by
          simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro m hm
          ring
  simp only [WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply]
  rw [hfirst, hsecond]
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
