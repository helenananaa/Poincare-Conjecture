import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The ordinary coordinate formula for the Lie derivative of a metric field. -/
def coordinateLieMetricExpr (G : E3 → (E3 →L[ℝ] E3)) (W : E3 → E3)
    (x : E3) (i j : Fin 3) : ℝ :=
    (fderiv ℝ G x (W x) (EuclideanSpace.single j 1)) i +
      (∑ k : Fin 3,
        ((G x (EuclideanSpace.single k 1)) j * (fderiv ℝ W x (EuclideanSpace.single i 1)) k +
         (G x (EuclideanSpace.single k 1)) i * (fderiv ℝ W x (EuclideanSpace.single j 1)) k))
/-- Product differentiation rewrites the actual coordinate Lie expression using the lowered field. -/
theorem coordinate_lie_metric_lowering (G : E3 → (E3 →L[ℝ] E3)) (W : E3 → E3)
    (x : E3) (hG : DifferentiableAt ℝ G x) (hW : DifferentiableAt ℝ W x)
    (i j : Fin 3) :
    coordinateLieMetricExpr G W x i j =
      fderiv ℝ (fun y : E3 => (G y (W y)) j) x (EuclideanSpace.single i 1) +
      fderiv ℝ (fun y : E3 => (G y (W y)) i) x (EuclideanSpace.single j 1) +
      (∑ k : Fin 3, W x k *
        ((fderiv ℝ G x (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)) i -
         (fderiv ℝ G x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)) j -
         (fderiv ℝ G x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)) i)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : Fin 3 → E3 := fun k => EuclideanSpace.single k 1
  have hexpand (v : E3) : v = ∑ k : Fin 3, v k • e k := by
    symm
    simpa [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hGW : HasFDerivAt (fun y : E3 => G y (W y))
      ((G x).comp (fderiv ℝ W x) + (fderiv ℝ G x).flip (W x)) x :=
    hG.hasFDerivAt.clm_apply hW.hasFDerivAt
  have hcoord (a b : Fin 3) :
      fderiv ℝ (fun y : E3 => (G y (W y)) a) x (e b) =
        (fderiv ℝ G x (e b) (W x)) a +
          ∑ k : Fin 3, (G x (e k)) a * (fderiv ℝ W x (e b)) k := by
    have hp :=
      ((hasFDerivAt_const (x := x) (c := EuclideanSpace.proj a)).clm_apply hGW).fderiv
    have hp' := congrArg (fun L : E3 →L[ℝ] ℝ => L (e b)) hp
    rw [show (fun y : E3 => (EuclideanSpace.proj a) (G y (W y))) =
        (fun y : E3 => (G y (W y)) a) by rfl] at hp'
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, zero_apply, add_zero] at hp'
    rw [hexpand (fderiv ℝ W x (e b))] at hp'
    simpa [e, ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.flip_apply, map_sum, map_smul, smul_eq_mul,
      ContinuousLinearMap.proj_apply, add_comm, mul_comm] using hp'
  have hGexpandDir (a b : Fin 3) :
      (fderiv ℝ G x (W x) (e b)) a =
        ∑ k : Fin 3, W x k * (fderiv ℝ G x (e k) (e b)) a := by
    conv_lhs => rw [hexpand (W x)]
    simp [map_sum, map_smul, smul_eq_mul]
  have hGexpandVec (a b : Fin 3) :
      (fderiv ℝ G x (e b) (W x)) a =
        ∑ k : Fin 3, W x k * (fderiv ℝ G x (e b) (e k)) a := by
    conv_lhs => rw [hexpand (W x)]
    simp [map_sum, map_smul, smul_eq_mul]
  dsimp [coordinateLieMetricExpr]
  rw [hcoord j i, hcoord i j, hGexpandDir i j,
    hGexpandVec j i, hGexpandVec i j]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  dsimp [e]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
