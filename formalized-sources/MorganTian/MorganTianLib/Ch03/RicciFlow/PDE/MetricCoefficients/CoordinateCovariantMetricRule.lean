import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionMetricTrilinear
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricJetSymmetry
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateConnectionVector
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Metric compatibility holds for actual differentiable metric and vector fields. -/
theorem coordinate_covariant_metric_rule (G : E3 → (E3 →L[ℝ] E3))
    (Y Z : E3 → E3) (x V : E3) (c : ℝ) (hc : 0<c)
    (hG : DifferentiableAt ℝ G x) (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w=inner ℝ v (G y w)) :
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)
    fderiv ℝ (fun y : E3 => inner ℝ (G y (Y y)) (Z y)) x V =
      inner ℝ (G x (fderiv ℝ Y x V+connectionVector (G x) P V (Y x))) (Z x) +
      inner ℝ (G x (Y x)) (fderiv ℝ Z x V+connectionVector (G x) P V (Z x)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let P : Fin 3 → E3 →L[ℝ] E3 := fun r =>
    fderiv ℝ G x (EuclideanSpace.single r 1)
  change fderiv ℝ (fun y : E3 => inner ℝ (G y (Y y)) (Z y)) x V =
    inner ℝ (G x (fderiv ℝ Y x V + connectionVector (G x) P V (Y x))) (Z x) +
      inner ℝ (G x (Y x))
        (fderiv ℝ Z x V + connectionVector (G x) P V (Z x))
  have hself : ∀ h a b : E3,
      inner ℝ ((fderiv ℝ G x h) a) b =
        inner ℝ a ((fderiv ℝ G x h) b) :=
    metric_jet_selfadjoint G x hG hsym
  have hcompat := coordinate_metric_compatibility (G x) c hc (hpos) (hsym x)
      P (fun r v w => hself (EuclideanSpace.single r 1) v w)
  have h_expand : ∀ u : E3,
      (∑ i : Fin 3, u i • EuclideanSpace.single i (1 : ℝ)) = u := by
    intro u
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr u
  have h_expand_coord : ∀ u : E3, ∀ i : Fin 3,
      (∑ j : Fin 3, u j • EuclideanSpace.single j (1 : ℝ)) i = u i := by
    intro u i
    exact congrArg (fun z : E3 => z i) (h_expand u)
  have hderiv : ∀ d : E3,
      fderiv ℝ G x d = ∑ r : Fin 3, d r • P r := by
    intro d
    calc
      fderiv ℝ G x d = fderiv ℝ G x
          (∑ r : Fin 3, d r • EuclideanSpace.single r (1 : ℝ)) := by
            rw [h_expand d]
      _ = ∑ r : Fin 3, d r • fderiv ℝ G x (EuclideanSpace.single r 1) := by
        simp only [map_sum, map_smul]
      _ = ∑ r : Fin 3, d r • P r := by rfl
  have hmetric : ∀ d a b : E3,
      inner ℝ ((fderiv ℝ G x d) a) b =
        inner ℝ (G x (connectionVector (G x) P d a)) b +
          inner ℝ (G x a) (connectionVector (G x) P d b) := by
    intro d a b
    rw [hderiv d]
    exact connection_metric_trilinear (G x) P c hc hpos (hsym x)
      (fun r v w => hself (EuclideanSpace.single r 1) v w) d a b
  have hprod := fderiv_inner_apply ℝ (hG.clm_apply hY) hZ V
  rw [fderiv_clm_apply hG hY] at hprod
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hprod
  calc
    fderiv ℝ (fun y : E3 => inner ℝ (G y (Y y)) (Z y)) x V =
        inner ℝ (G x (fderiv ℝ Y x V)) (Z x) +
          inner ℝ ((fderiv ℝ G x V) (Y x)) (Z x) +
            inner ℝ (G x (Y x)) (fderiv ℝ Z x V) := by
      simpa [inner_add_left, add_assoc, add_left_comm, add_comm] using hprod
    _ = inner ℝ (G x (fderiv ℝ Y x V +
          connectionVector (G x) P V (Y x))) (Z x) +
          inner ℝ (G x (Y x)) (fderiv ℝ Z x V +
            connectionVector (G x) P V (Z x)) := by
      rw [hmetric V (Y x) (Z x)]
      simp only [map_add, inner_add_left, inner_add_right]
      abel
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
